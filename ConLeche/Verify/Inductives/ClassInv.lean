module

public import ConLeche.Kernel.Inductives.ClassCheck
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.InstTypeInv

public section

/-!
# The class check's run, inverted ONCE (PROOFPLAN T1)

The class checker (`ConLeche/Kernel/Inductives/ClassCheck.lean`,
`classRecCheck`) read back declaratively, at any pure operations
`ops : CheckerOps CheckM` (the model instantiates the fueled ones;
`ClassDatF.lean` moves the pure install's run there).  This file is the
only place that unfolds a stage of the class check; every proof about
it reads the records below.

* `FieldD` — the FLAT field derivation of check 3 (`classPos`,
  `classFields`): a reduct that mentions no member and no hole
  (`const`), a `Π` with a hole-free domain (`pi`), a leaf at a MEMBER
  hole (the block's parameters, then hole-free indices, full arity) or at
  a CLASS hole (hole-free indices, full arity).  No frames, no
  containers: every class occurrence is a hole before the whnf runs (R1).
  The whnf step is a premise of every field rule, at the ABSTRACTED term.
* `ClassKeyOk` — check 1 at one class (`classInfo`): one constructor per
  arm (a member / a container instance), R2/R3 read off `nestInstType`
  (`ClassKeyOk.idxFree`, `ClassKeyOk.sortEquiv`).
* `ClassCtorRun` — checks 3 and 4 at one constructor (`classCtor`): the
  abstracted crest typed at the holes' context, its telescope derived,
  U4, the result the class's own hole with hole-free indices, U2/M3/M2′
  at a member's constructors, and the output (R4: the kinds; R5: the
  walked telescope read back).
* `ClassRun` — the whole check (`classRecCheck_run`): the classes, R6,
  the crests (instantiated, then abstracted: syntactic tier, then the
  per-component defeq tier), the aliases' and same-pairs' defeqs,
  reachability, every constructor's `ClassCtorRun`, check 5 (the kinds
  re-pointed at the inductive hypotheses' classes), the elimination
  guard, and check 6 as its two runs (inverted in the recursor lane).
-/

namespace ConLeche

open Expr

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
        | exact nomatch $h)

/-! ## Generic run lemmas -/

/-- A successful `mapM` in `Except` is a pointwise run. -/
theorem except_mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {as : List α} {bs : List β}, as.mapM f = .ok bs →
      bs.length = as.length ∧ ∀ (i : Nat) (a : α), as[i]? = some a → ∃ b, bs[i]? = some b ∧ f a = .ok b
  | [], bs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | a :: as, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨bs', hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := except_mapM_ok hbs
    refine ⟨by simp [hl], fun i a' ha => ?_⟩
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ⊢; subst ha; exact ⟨b, rfl, hb⟩
    | succ i => simpa using hall i a' (by simpa using ha)

/-- An invariant of a `for` loop over a list in `Except`. -/
theorem except_forIn_inv {ε α σ : Type} (P : σ → Prop) {f : α → σ → Except ε (ForInStep σ)} :
    ∀ {l : List α} {init r : σ},
      P init → (∀ a ∈ l, ∀ s s', P s → f a s = .ok s' → P s'.value) →
      forIn l init f = .ok r → P r
  | [], init, r, h0, _, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ h0
  | a :: l, init, r, h0, hf, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := exceptBind_ok h
    have hP := hf a List.mem_cons_self init s h0 hs
    cases s with
    | done b =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hP
    | yield b =>
      exact except_forIn_inv P hP (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h

/-- Peel an `unless c do throw e` whose continuation is a join point. -/
theorem unless_jp_ok {α : Type} {c : Bool} {e : CheckError} {k : Unit → CheckM α} {b : α}
    (h : (have jp := k; if c = true then jp () else (do let r ← throw e; jp r)) = .ok b) :
    c = true ∧ k () = .ok b := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at h
    exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])

/-- Peel an `if c then throw e` whose continuation is a join point. -/
theorem when_jp_ok {α : Type} {c : Bool} {e : CheckError} {k : Unit → CheckM α} {b : α}
    (h : (have jp := k; if c = true then (do let r ← throw e; jp r) else jp ()) = .ok b) :
    c = false ∧ k () = .ok b := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte] at h
    exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
  · simp only [hc, ↓reduceIte, Bool.false_eq_true] at h; exact ⟨by simpa using hc, h⟩

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-! ## Check 3: the flat field derivation -/

/-- The judgments of check 3. -/
inductive ClassJ where
  /-- the term `e` (a field's type, or a `Π` body `kb` binders in), walked at
  depth `dep`, is of kind `k` with the walk's normal form `nf` -/
  | field (dep kb : Nat) (e : Expr) (k : ClassField) (nf : Expr)
  /-- the telescope `cur` has `nF` walked fields from field `j`, each opened
  at `base + j`; `res` what remains -/
  | tele (base nF j : Nat) (cur : Expr) (ks : List ClassField) (nds : List (Expr × BinderMeta))
      (res : Expr)

/-- **The flat field derivation** (see the module docstring).  `hi` is the
end of the holes: members at `nP … hiAt 0 - 1`, the classes' after. -/
inductive FieldD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (cls : List ClassInfo)
    (hi : Nat) : ClassJ → Prop where
  /-- the reduct mentions no member and no hole -/
  | const {dep kb : Nat} {e w : Expr}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP hi = false) :
      FieldD ops env ctx cls hi
        (.field dep kb e .ordinary (if e.nestOcc ctx.names ctx.nP hi then w else e))
  /-- a `Π` with a hole-free domain and a walked body -/
  | pi {dep kb : Nat} {e a b : Expr} {bm : BinderMeta} {k : ClassField} {nb : Expr}
      (hw : ops.whnf env dep e = .ok (.forallE a b bm))
      (hocc : (Expr.forallE a b bm).nestOcc ctx.names ctx.nP hi = true)
      (ha : a.nestOcc ctx.names ctx.nP hi = false)
      (hb : FieldD ops env ctx cls hi (.field (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) k nb)) :
      FieldD ops env ctx cls hi (.field dep kb e k (.forallE a (nb.abstract1 dep) bm))
  /-- a member hole at the block's parameters, then hole-free indices, full
  arity; the member's class `c` -/
  | memberHole {dep kb : Nat} {e w : Expr} {i : Nat} {ty : Expr} {c : Nat} {ci : ClassInfo}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP hi = true)
      (hfn : w.getAppFn = .fvar i ty) (hlo : ctx.nP ≤ i) (hhi : i < ctx.hiAt 0)
      (hc : cls[c]? = some ci) (hmem : ci.member = some (i - ctx.nP))
      (hpar : w.getAppArgs.take ctx.nP = ctx.params)
      (hlen : (w.getAppArgs.drop ctx.nP).length = ci.nIdx)
      (hfree : ∀ x ∈ w.getAppArgs.drop ctx.nP, x.nestOcc ctx.names ctx.nP hi = false) :
      FieldD ops env ctx cls hi (.field dep kb e (.recursive c kb) w)
  /-- a class hole at hole-free indices, full arity; its class `c` -/
  | classHole {dep kb : Nat} {e w : Expr} {i : Nat} {ty hty : Expr} {c : Nat} {ci : ClassInfo}
      (hw : ops.whnf env dep e = .ok w)
      (hocc : w.nestOcc ctx.names ctx.nP hi = true)
      (hfn : w.getAppFn = .fvar i ty) (hout : ¬(ctx.nP ≤ i ∧ i < ctx.hiAt 0))
      (hc : cls[c]? = some ci) (hhole : ci.hole = some (.fvar i hty))
      (hlen : w.getAppArgs.length = ci.nIdx)
      (hfree : ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP hi = false) :
      FieldD ops env ctx cls hi (.field dep kb e (.recursive c kb) w)
  | teleNil {base j : Nat} {cur : Expr} :
      FieldD ops env ctx cls hi (.tele base 0 j cur [] [] cur)
  /-- one field of a telescope, then the rest opened at its variable -/
  | teleCons {base nF j : Nat} {a b : Expr} {bm : BinderMeta} {k : ClassField} {nd : Expr}
      {ks : List ClassField} {nds : List (Expr × BinderMeta)} {res : Expr}
      (ha : FieldD ops env ctx cls hi (.field (base + j) 0 a k nd))
      (hb : FieldD ops env ctx cls hi
        (.tele base nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) ks nds res)) :
      FieldD ops env ctx cls hi (.tele base (nF + 1) j (.forallE a b bm) (k :: ks) ((nd, bm) :: nds) res)

/-- `classOfHole`, read: a member hole's class is that member's, a class
hole's the class holding it. -/
theorem classOfHole_spec {cls : List ClassInfo} {i c : Nat} (h : classOfHole ctx cls i = some c) :
    ∃ ci, cls[c]? = some ci ∧
      ((ctx.nP ≤ i ∧ i < ctx.hiAt 0) ∧ ci.member = some (i - ctx.nP) ∨
        ¬(ctx.nP ≤ i ∧ i < ctx.hiAt 0) ∧ ∃ hty, ci.hole = some (.fvar i hty)) := by
  unfold classOfHole at h
  split at h
  · rename_i hr
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    refine ⟨cls[c], List.getElem?_eq_getElem hlt, Or.inl ⟨by simpa using hr, ?_⟩⟩
    simpa using hp
  · rename_i hr
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    refine ⟨cls[c], List.getElem?_eq_getElem hlt, Or.inr ⟨by simpa using hr, ?_⟩⟩
    revert hp
    split
    · rename_i h' hty hh; intro hp; exact ⟨hty, by rw [hh]; simp at hp; rw [hp]⟩
    · intro hp; exact absurd hp (by simp)

/-- **Check 3 at one field, inverted**: a successful walk (any fuel) is a
derivation. -/
theorem classPos_deriv {cls : List ClassInfo} {hi : Nat} :
    ∀ {fuel dep kb : Nat} {e : Expr} {k : ClassField} {nf : Expr},
      classPos ops env ctx cls hi fuel dep kb e = .ok (k, nf) →
      FieldD ops env ctx cls hi (.field dep kb e k nf)
  | 0, _, _, _, _, _, h => nomatch h
  | fuel + 1, dep, kb, e, k, nf, h => by
    unfold classPos at h
    obtain ⟨w, hw, h⟩ := exceptBind_ok h
    split at h
    · rename_i hocc
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .const hw (by simpa using hocc)
    rename_i hocc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hocc
    split at h
    · rename_i a b bm
      split at h
      · exact nomatch h
      rename_i ha
      obtain ⟨⟨k', nb⟩, hb, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .pi hw hocc (by simpa using ha) (classPos_deriv hb)
    · split at h
      · rename_i i ty c hfn hc
        simp only [hfn] at hc
        obtain ⟨ci, hci, hsp⟩ := classOfHole_spec hc
        dsimp only at h
        split at h
        · rename_i ix hix
          split at h
          · rename_i hok
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hok
            have hcd : cls.getD c default = ci := by simp [List.getD_eq_getElem?_getD, hci]
            rw [hcd] at hok
            rcases hsp with ⟨hr, hmem⟩ | ⟨hr, hty, hhole⟩
            · rw [show (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true by
                simp [hr.1, hr.2]] at hix
              simp only [↓reduceIte] at hix
              split at hix
              · rename_i hpar
                simp only [Option.some.injEq] at hix
                subst hix
                exact .memberHole hw hocc hfn hr.1 hr.2 hci hmem (by simpa using hpar) hok.1 hok.2
              · exact nomatch hix
            · rw [show (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = false by
                simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega] at hix
              simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hix
              subst hix
              exact .classHole hw hocc hfn hr hci hhole hok.1 hok.2
          · exact nomatch h
        · exact nomatch h
      · exact nomatch h

/-- **Check 3 at a telescope, inverted.** -/
theorem classFields_deriv {cls : List ClassInfo} {hi fuel : Nat} {base : Nat} :
    ∀ {nF j : Nat} {cur : Expr} {ks : List ClassField} {nds : List (Expr × BinderMeta)}
      {res : Expr},
      classFields (fun d e => classPos ops env ctx cls hi fuel d 0 e) base nF j cur
        = .ok (ks, nds, res) →
      FieldD ops env ctx cls hi (.tele base nF j cur ks nds res)
  | 0, j, cur, ks, nds, res, h => by
    simp only [classFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .teleNil
  | nF + 1, j, cur, ks, nds, res, h => by
    unfold classFields at h
    split at h
    · rename_i a b bm
      obtain ⟨⟨k, nd⟩, hk, h⟩ := exceptBind_ok h
      obtain ⟨⟨ks', nds', res'⟩, hr, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .teleCons (classPos_deriv hk) (classFields_deriv hr)
    · exact nomatch h

/-! ## Checks 3 and 4 at one constructor -/

/-- The constructor's result is headed by its class's OWN hole: a
member's hole, or a container class's. -/
@[expose] def ClassResOk (ctx : NestCtx) (c : ClassInfo) (cur : Expr) : Prop :=
  (∃ t ty, c.member = some t ∧ cur.getAppFn = .fvar (ctx.nP + t) ty) ∨
    (c.member = none ∧ ∃ h hty ty, c.hole = some (.fvar h hty) ∧ cur.getAppFn = .fvar h ty)

/-- **One constructor's walk** (check 3), at its walked telescope `nds` and
result `cur`: every field derived, U4, the result the class's own hole
with hole-free indices, and at a member's constructor U2 (the field
universes at the holes), M3 on the walked form and M2′. -/
structure ClassCtorWalk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (cls : List ClassInfo) (hi : Nat) (c : ClassInfo) (cv : ConstantVal)
    (nF : Nat) (crest : Expr) (ks : List ClassField) (nds : List (Expr × BinderMeta))
    (cur : Expr) : Prop where
  tele : FieldD ops env ctx cls hi (.tele hi nF 0 crest ks nds cur)
  u4 : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
    structUsedLater (closeTelescope nds hi cur) 0 i) = false
  res : ClassResOk ctx c cur
  resIdx : (cur.getAppArgs.drop (if c.member.isSome then ctx.nP else 0)).all
    (fun x => !x.nestOcc ctx.names ctx.nP hi) = true
  member : c.member.isSome = true →
    (∃ xq, openPisAtFvars nF (closeTelescope nds hi cur) hi = some xq ∧
      ∃ r, checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
        ctx.sort hi xq.1 [] nF = .ok r) ∧
    (closeTelescope nds hi cur).holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true ∧
    (nestAbstract ctx holes cv.type).nestOcc ctx.names 0 0 = false

/-- **Checks 3 and 4 at one constructor, as run**: the abstracted crest
typed at the holes' context (check 4), its walk (check 3), and the
output — the constructor, its field count, the walked kinds (R4) and the
walked telescope read back (R5). -/
structure ClassCtorRun (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (cls : List ClassInfo) (hi : Nat) (c : ClassInfo) (cv : ConstantVal)
    (nF : Nat) (crest : Expr) (x : ClassCtor) : Prop where
  nodup : Name.nodup cv.levelParams = true
  typed : ∃ ty s, ops.inferType env hi crest = .ok ty ∧ ops.ensureSort env hi ty = .ok s
  walk : ∃ nds cur, ClassCtorWalk ops env ctx holes cls hi c cv nF crest x.kinds nds cur ∧
    x.tyN = classReadBack ctx cls (closeTelescope nds hi cur)
  cv : x.cv = cv
  nF : x.nF = nF

/-- **`classCtor`, inverted.** -/
theorem classCtor_run {holes : List Expr} {cls : List ClassInfo} {hi : Nat} {c : ClassInfo}
    {cv : ConstantVal} {nF : Nat} {crest : Expr} {x : ClassCtor}
    (h : classCtor ops env ctx holes cls hi c cv nF crest = .ok x) :
    ClassCtorRun ops env ctx holes cls hi c cv nF crest x := by
  unfold classCtor at h
  simp only [bind, Except.bind] at h
  split at h
  case isFalse => close_throw h
  rename_i hnd
  split at h
  · close_throw h
  rename_i ty hty
  split at h
  · close_throw h
  rename_i s hs
  split at h
  · close_throw h
  rename_i r hf
  obtain ⟨ks, nds, cur⟩ := r
  simp only at h
  split at h
  case isTrue => close_throw h
  rename_i hu4
  split at h
  case h_2 => simp at h
  rename_i i ty0 h0 hfn hown
  have hres : i = h0 → ClassResOk ctx c cur := by
    rintro rfl
    rcases hm : c.member with _ | t
    · rcases hh : c.hole with _ | hv
      · simp [hm, hh] at hown
      · cases hv <;> simp [hm, hh] at hown
        subst hown
        exact Or.inr ⟨hm, _, _, ty0, hh, hfn⟩
    · simp only [hm, Option.some.injEq] at hown
      exact Or.inl ⟨t, ty0, hm, by rw [hfn, hown]⟩
  have hu4' : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
      structUsedLater (closeTelescope nds hi cur) 0 i) = false := by simpa using hu4
  have hfd := classFields_deriv hf
  split at h
  · rename_i hm
    split at h
    case isFalse => close_throw h
    rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hih, hidx⟩ := hcond
    split at h
    · close_throw h
    rename_i xq hxq
    split at h
    · close_throw h
    rename_i r hr
    split at h
    case isFalse => close_throw h
    rename_i hha
    split at h
    · close_throw h
    rename_i u hnm
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨hnd, ⟨ty, s, hty, hs⟩, ⟨nds, cur, ⟨hfd, hu4', hres hih, by simpa [hm] using hidx,
      fun _ => ?_⟩, rfl⟩, rfl, rfl⟩
    refine ⟨⟨xq, unwrapOr_ok hxq, r, hr⟩, hha, ?_⟩
    unfold nestNoMemberConst at hnm
    split at hnm
    · close_throw hnm
    · rename_i hn; simpa using hn
  · rename_i hm
    split at h
    case isFalse => close_throw h
    rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hih, hidx⟩ := hcond
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hnd, ⟨ty, s, hty, hs⟩, ⟨nds, cur, ⟨hfd, hu4', hres hih, by simpa [hm] using hidx,
      fun h' => absurd h' hm⟩, rfl⟩, rfl, rfl⟩

/-- **Checks 3 and 4 at a class's constructors, inverted** (pairwise with
the crests, up to the shorter list). -/
theorem classCtors_run {holes : List Expr} {cls : List ClassInfo} {hi : Nat} {c : ClassInfo} :
    ∀ {cs : List (ConstantVal × Nat)} {crests : List Expr} {xs : List ClassCtor},
      classCtors ops env ctx holes cls hi c cs crests = .ok xs →
      xs.length = min cs.length crests.length ∧
      ∀ (j : Nat) (x : ClassCtor), xs[j]? = some x → ∃ cv nF crest,
        cs[j]? = some (cv, nF) ∧ crests[j]? = some crest ∧
        ClassCtorRun ops env ctx holes cls hi c cv nF crest x
  | (cv, nF) :: cs, crest :: crests, xs, h => by
    unfold classCtors at h
    obtain ⟨x, hx, h⟩ := exceptBind_ok h
    obtain ⟨xs', hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := classCtors_run hxs
    refine ⟨by simp [hl, Nat.succ_min_succ], fun j y hy => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨cv, nF, crest, rfl, rfl, classCtor_run hx⟩
    | succ j => simpa using hall j y (by simpa using hy)
  | [], _, xs, h => by
    simp only [classCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨by simp, fun _ _ h => by simp at h⟩
  | _ :: _, [], xs, h => by
    simp only [classCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨by simp, fun _ _ h => by simp at h⟩

/-- **Checks 3 and 4 at every class, inverted.** -/
theorem classAllCtors_run {holes : List Expr} {cls : List ClassInfo} {hi : Nat} :
    ∀ {cs : List ClassInfo} {crests : List (List Expr)} {xss : List (List ClassCtor)},
      classAllCtors ops env ctx holes cls hi cs crests = .ok xss →
      xss.length = min cs.length crests.length ∧
      ∀ (i : Nat) (xs : List ClassCtor), xss[i]? = some xs → ∃ c crs,
        cs[i]? = some c ∧ crests[i]? = some crs ∧
        classCtors ops env ctx holes cls hi c c.ctors crs = .ok xs
  | c :: cs, crs :: crests, xss, h => by
    unfold classAllCtors at h
    obtain ⟨x, hx, h⟩ := exceptBind_ok h
    obtain ⟨xs', hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := classAllCtors_run hxs
    refine ⟨by simp [hl, Nat.succ_min_succ], fun j y hy => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨c, crs, rfl, rfl, hx⟩
    | succ j => simpa using hall j y (by simpa using hy)
  | [], _, xs, h => by
    simp only [classAllCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨by simp, fun _ _ h => by simp at h⟩
  | _ :: _, [], xs, h => by
    simp only [classAllCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨by simp, fun _ _ h => by simp at h⟩

/-! ## Check 1: the classes -/

/-- **Check 1 at one class, as run** (`classInfo`): one constructor per
arm.  `a` is the number of container classes before it; its hole is
`fvar (hiAt 0 + a)`. -/
inductive ClassKeyOk (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (a : Nat) (key : ClassKey) : ClassInfo → Prop where
  /-- a MEMBER: exactly the member at the block's levels and parameters -/
  | member {ds : List Expr} {t : Nat}
      (hsc : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.nP)
      (hann : key.ds.mapM (fun d => ops.annotate env ctx.nP (classCanon ctx.params d)) = .ok ds)
      (hlp : (Expr.mkAppN (.const key.ind key.lvls) ds).allLevelParamsDefined ctx.lps = true)
      (ht : ctx.names.findIdx? (· == key.ind) = some t)
      (hlv : key.lvls = ctx.lps.map .param) (hds : ds = ctx.params) :
      ClassKeyOk ops env ctx holes ctorsAs a key
        { key := ⟨key.ind, key.lvls, ctx.params⟩, dsA := ctx.params,
          dsE := ctx.params.map Expr.eraseFVarTys, member := some t, nPc := ctx.nP,
          nIdx := ctx.nIdxs.getD t 0, ctors := ctorsAs.getD t [], hole := none }
  /-- a CONTAINER instance: a stored inductive (not `Quot`) at all its
  parameters, which mention some member, every member at the block's
  levels (M2′) and applied to the parameters (M3); its instantiated type
  (`nestInstType`: level count, N2 = R2, N3 = R3); K.52; the hole -/
  | container {ds : List Expr} {nPc nIdx : Nat} {ctors : List (ConstantVal × Nat)}
      {fty hty : Expr}
      (hsc : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.nP)
      (hann : key.ds.mapM (fun d => ops.annotate env ctx.nP (classCanon ctx.params d)) = .ok ds)
      (hlp : (Expr.mkAppN (.const key.ind key.lvls) ds).allLevelParamsDefined ctx.lps = true)
      (ht : ctx.names.findIdx? (· == key.ind) = none)
      (hq : key.ind ≠ quotName)
      (hC : nestContainer ctx key.ind = some (nPc, ctors))
      (hlen : ds.length = nPc)
      (hocc : ds.any (·.nestOcc ctx.names 0 0) = true)
      (hM2 : (ds.map (nestAbstract ctx holes)).any (·.nestOcc ctx.names 0 0) = false)
      (hM3 : (ds.map (nestAbstract ctx holes)).all
        (·.holesApplied ctx.names ctx.nP (ctx.hiAt 0)) = true)
      (hnI : nestInstType (m := CheckM) ctx (ctx.hiAt 0)
        ⟨key.ind, key.lvls, ds.map (nestAbstract ctx holes)⟩ = .ok (nIdx, fty))
      (hK52 : ∃ ty, ops.inferType env (ctx.hiAt 0)
        (Expr.mkAppN (.const key.ind key.lvls) (ds.map (nestAbstract ctx holes))) = .ok ty)
      (hhty : instPisWith (ds.map (nestAbstract ctx holes)) fty = some hty) :
      ClassKeyOk ops env ctx holes ctorsAs a key
        { key := ⟨key.ind, key.lvls, ds⟩, dsA := ds.map (nestAbstract ctx holes),
          dsE := (ds.map (nestAbstract ctx holes)).map Expr.eraseFVarTys, member := none,
          nPc := nPc, nIdx := nIdx, ctors := ctors, hole := some (.fvar (ctx.hiAt 0 + a) hty) }

/-- **`classInfo`, inverted.** -/
theorem classInfo_run {holes : List Expr} {ctorsAs : List (List (ConstantVal × Nat))} {a : Nat}
    {key : ClassKey} {ci : ClassInfo}
    (h : classInfo ops env ctx holes ctorsAs a key = .ok ci) :
    ClassKeyOk ops env ctx holes ctorsAs a key ci := by
  unfold classInfo at h
  extract_lets hiM at h
  obtain ⟨hsc, h⟩ := unless_jp_ok h
  have hsc' : ∀ x ∈ key.ds, x.bvarB = 0 ∧ x.fvarB ≤ ctx.nP := by
    intro x hx
    have := List.all_eq_true.mp hsc x hx
    simpa using this
  obtain ⟨ds, hann, h⟩ := exceptBind_ok h
  obtain ⟨hlp, h⟩ := unless_jp_ok h
  split at h
  · rename_i t ht
    obtain ⟨hmem, h⟩ := unless_jp_ok h
    simp only [Bool.and_eq_true, beq_iff_eq] at hmem
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .member hsc' hann hlp ht hmem.1 hmem.2
  · rename_i ht
    obtain ⟨hq, h⟩ := when_jp_ok h
    split at h
    case h_2 => close_throw h
    rename_i nPc ctors hC
    obtain ⟨hlen, h⟩ := unless_jp_ok h
    obtain ⟨hocc, h⟩ := unless_jp_ok h
    extract_lets dsA at h
    obtain ⟨hM2, h⟩ := when_jp_ok h
    obtain ⟨hM3, h⟩ := unless_jp_ok h
    obtain ⟨⟨nIdx, fty⟩, hnI, h⟩ := exceptBind_ok h
    obtain ⟨ty, hK, h⟩ := exceptBind_ok h
    obtain ⟨hty, hhty, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .container hsc' hann hlp ht (by simpa using hq) hC (by simpa using hlen) hocc hM2 hM3 hnI
      ⟨ty, hK⟩ (unwrapOr_ok hhty)

/-- **R2**: a container class's index telescope (its inductive's, at the
member-abstracted parameters) mentions no member and no member hole. -/
theorem ClassKeyOk.idxFree {holes : List Expr} {ctorsAs : List (List (ConstantVal × Nat))}
    {a : Nat} {key : ClassKey} {ci : ClassInfo}
    (h : ClassKeyOk ops env ctx holes ctorsAs a key ci) (hc : ci.member = none) :
    ∃ cvC caps ty s, ctx.find? key.ind = some (.indInfo cvC caps) ∧
      instPisWith ci.dsA (cvC.type.instantiateLevelParams cvC.levelParams key.lvls) = some ty ∧
      ty.piBinders.2 = .sort s ∧
      (ty.piBinders.1.any fun b => b.1.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = false ∧
      ci.nIdx = ty.piBinders.1.length ∧
      Level.isEquiv s ctx.sort = some true ∧
      key.lvls.length = cvC.levelParams.length := by
  cases h with
  | member => exact nomatch hc
  | container _ _ _ _ _ _ _ _ _ _ hnI =>
    obtain ⟨cvC, caps, hf, -, -, ty, s, hty, hs, hocc, hn, hsort⟩ := nestInstType_inv hnI
    obtain ⟨cvC', caps', hf', hl⟩ := nestInstType_lvls hnI
    rw [hf] at hf'
    cases hf'
    exact ⟨cvC, caps, ty, s, hf, hty, hs, hocc, hn, hsort, hl⟩

/-- **Check 1 at every class, as run**: the hole counter `a` counts the
container classes before. -/
inductive ClassInfosD (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) : Nat → List ClassKey → List ClassInfo → Prop where
  | nil {a : Nat} : ClassInfosD ops env ctx holes ctorsAs a [] []
  | cons {a : Nat} {k : ClassKey} {ks : List ClassKey} {c : ClassInfo} {cs : List ClassInfo}
      (hk : ClassKeyOk ops env ctx holes ctorsAs a k c)
      (hr : ClassInfosD ops env ctx holes ctorsAs (if c.member.isSome then a else a + 1) ks cs) :
      ClassInfosD ops env ctx holes ctorsAs a (k :: ks) (c :: cs)

theorem classInfos_run {holes : List Expr} {ctorsAs : List (List (ConstantVal × Nat))} :
    ∀ {a : Nat} {ks : List ClassKey} {cs : List ClassInfo},
      classInfos ops env ctx holes ctorsAs a ks = .ok cs → ClassInfosD ops env ctx holes ctorsAs a ks cs
  | _, [], cs, h => by
    simp only [classInfos, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a, k :: ks, cs, h => by
    unfold classInfos at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    obtain ⟨rest, hr, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .cons (classInfo_run hc) (classInfos_run hr)

/-- Every class, at its position: check 1 at the number of container
classes before it. -/
theorem ClassInfosD.getElem {holes : List Expr} {ctorsAs : List (List (ConstantVal × Nat))} :
    ∀ {a : Nat} {ks : List ClassKey} {cs : List ClassInfo},
      ClassInfosD ops env ctx holes ctorsAs a ks cs →
      ks.length = cs.length ∧ ∀ (i : Nat) (c : ClassInfo), cs[i]? = some c → ∃ k, ks[i]? = some k ∧
        ClassKeyOk ops env ctx holes ctorsAs (a + ((cs.take i).filter (·.member.isNone)).length) k c
  | _, _, _, .nil => ⟨rfl, fun _ _ h => by simp at h⟩
  | a, k :: ks, c :: cs, .cons hk hr => by
    obtain ⟨hl, hall⟩ := hr.getElem
    refine ⟨by simp [hl], fun i c' hc' => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
      subst hc'
      exact ⟨k, rfl, by simpa using hk⟩
    | succ i =>
      obtain ⟨k', hk', h'⟩ := hall i c' (by simpa using hc')
      refine ⟨k', by simpa using hk', ?_⟩
      have : (if c.member.isSome then a else a + 1) +
          ((cs.take i).filter (·.member.isNone)).length =
          a + (((c :: cs).take (i + 1)).filter (·.member.isNone)).length := by
        cases hm : c.member <;> simp [hm] <;> omega
      rw [← this]; exact h'

/-! ## R6: the keys typed with their cyclic inner classes abstracted -/

/-- A class's CYCLIC inner classes: the container classes whose
inductive is younger (`age`) than its own. -/
@[expose] def classCyc (age : Name → Nat) (cls : List ClassInfo) (c : ClassInfo) : List ClassInfo :=
  cls.filter fun d => d.member.isNone && age c.key.ind < age d.key.ind

/-- **R6, inverted**: every container class whose key names a cyclic
inner class is typed at the holes' context with those abstracted. -/
theorem classKeysCyclic_run {age : Name → Nat} {cls : List ClassInfo} {hi : Nat} :
    ∀ {cs : List ClassInfo}, classKeysCyclic ops env age cls hi cs = .ok () →
      ∀ c ∈ cs, c.member = none → c.dsA.map (classAbs (classCyc age cls c)) ≠ c.dsA →
        ∃ ty, ops.inferType env hi (Expr.mkAppN (.const c.key.ind c.key.lvls)
          (c.dsA.map (classAbs (classCyc age cls c)))) = .ok ty
  | [], _ => fun _ h => nomatch h
  | c :: cs, h => by
    unfold classKeysCyclic at h
    dsimp only at h
    have key : classKeysCyclic ops env age cls hi cs = .ok () ∧
        (c.member = none → c.dsA.map (classAbs (classCyc age cls c)) ≠ c.dsA →
          ∃ ty, ops.inferType env hi (Expr.mkAppN (.const c.key.ind c.key.lvls)
            (c.dsA.map (classAbs (classCyc age cls c)))) = .ok ty) := by
      split at h
      · split at h
        · obtain ⟨u, hu, h⟩ := exceptBind_ok h
          refine ⟨h, fun _ _ => ?_⟩
          simp only [discard, Functor.discard, Functor.mapConst, Except.map, Function.comp_apply]
            at hu
          split at hu
          · exact nomatch hu
          · rename_i ty hty; exact ⟨ty, hty⟩
        · rename_i hne
          exact ⟨h, fun _ hne' => absurd (by simpa [classCyc] using hne) hne'⟩
      · rename_i hm
        exact ⟨h, fun hm' => absurd (by simp [hm']) hm⟩
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact key.2
    · exact classKeysCyclic_run key.1 c' hc'

/-! ## The per-component defeq tier -/

/-- **Parameters per component**: equal up to the free variables'
annotations, or both inferred and `isDefEq` at depth `d`. -/
@[expose] def ClassParamDefEq (ops : CheckerOps CheckM) (env : Env) (d : Nat) (a b : Expr) : Prop :=
  a.eraseFVarTys = b.eraseFVarTys ∨
    ((∃ t, ops.inferType env d a = .ok t) ∧ (∃ t, ops.inferType env d b = .ok t) ∧
      ops.isDefEq env d a b = .ok true)

/-- **`classParamsDefEq`, inverted**: pairwise `ClassParamDefEq`. -/
theorem classParamsDefEq_true {d : Nat} :
    ∀ {as bs : List Expr}, classParamsDefEq ops env d as bs = .ok true →
      as.length = bs.length ∧ ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        ClassParamDefEq ops env d a b
  | [], [], _ => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | [], _ :: _, h => by simp [classParamsDefEq, pure, Except.pure] at h
  | _ :: _, [], h => by simp [classParamsDefEq, pure, Except.pure] at h
  | a :: as, b :: bs, h => by
    unfold classParamsDefEq at h
    have key : ClassParamDefEq ops env d a b ∧ classParamsDefEq ops env d as bs = .ok true := by
      split at h
      · rename_i he; exact ⟨Or.inl (by simpa using he), h⟩
      · obtain ⟨t1, h1, h⟩ := exceptBind_ok h
        obtain ⟨t2, h2, h⟩ := exceptBind_ok h
        obtain ⟨b0, hb, h⟩ := exceptBind_ok h
        cases b0
        · simp [pure, Except.pure] at h
        · exact ⟨Or.inr ⟨⟨t1, h1⟩, ⟨t2, h2⟩, hb⟩, by simpa using h⟩
    obtain ⟨hl, hall⟩ := classParamsDefEq_true key.2
    refine ⟨by simp [hl], fun i a' b' ha hb => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha hb; exact key.1
    | succ i => exact hall i a' b' (by simpa using ha) (by simpa using hb)

/-- **An alias, as found**: some container class with the alias's
inductive, parameter count and hole, at equivalent levels, whose
hole-form parameters the occurrence's (the alias's, up to annotations)
match per component. -/
@[expose] def ClassAliasOk (ops : CheckerOps CheckM) (env : Env) (hi : Nat) (cls : List ClassInfo)
    (al : ClassAlias) : Prop :=
  ∃ ci ∈ cls, ∃ ps : List Expr, ci.key.ind = al.ind ∧ ci.nPc = al.nPc ∧ ci.hole = some al.hole ∧
    Level.isEquivList al.lvls ci.key.lvls = some true ∧ al.ps = ps.map Expr.eraseFVarTys ∧
    classParamsDefEq ops env hi ps (ci.holeForm cls) = .ok true

/-- **`classAliases`, inverted.** -/
theorem classAliases_run {hi : Nat} {cls : List ClassInfo} :
    ∀ {es : List Expr} {al : List ClassAlias}, classAliases ops env hi cls es = .ok al →
      ∀ a ∈ al, ClassAliasOk ops env hi cls a
  | [], al, h => by
    simp only [classAliases, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ h; exact nomatch h
  | e :: es, al, h => by
    unfold classAliases at h
    obtain ⟨rest, hr, h⟩ := exceptBind_ok h
    have ih := classAliases_run hr
    split at h
    · rename_i I us hfn
      dsimp only at h
      obtain ⟨found, hloop, h⟩ := exceptBind_ok h
      have hP := except_forIn_inv (fun f : Option ClassAlias => ∀ a, f = some a →
          ClassAliasOk ops env hi cls a) (by intro a h; simp at h) (fun c hc s s' hs hst => by
        split at hst
        · rename_i hcond
          obtain ⟨b0, hb, hst⟩ := exceptBind_ok hst
          split at hst
          · rename_i hb0
            simp only [pure, Except.pure, Except.ok.injEq] at hst
            subst hst
            intro a ha
            simp only [ForInStep.value, Option.some.injEq] at ha
            subst ha
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isSome_iff_exists]
              at hcond
            obtain ⟨⟨⟨⟨-, hI⟩, -⟩, hv, hhv⟩, hlv⟩ := hcond
            refine ⟨c, hc, _, hI, rfl, ?_, hlv, rfl, by rw [hb, hb0]⟩
            simp [hhv]
          · simp only [pure, Except.pure, Except.ok.injEq] at hst
            subst hst; exact hs
        · simp only [pure, Except.pure, Except.ok.injEq] at hst
          subst hst; exact hs) hloop
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro a ha
      cases found with
      | none => exact ih a ha
      | some a0 =>
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hP _ rfl
        · exact ih a ha
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ih

/-- **The candidates the defeq tier sees satisfy the candidate guard.** -/
theorem classCandsGo_mem {isCand : Expr → Bool} :
    ∀ (e : Expr) (acc : Std.HashSet Expr × List Expr) (x : Expr),
      x ∈ (classCandsGo isCand acc e).2 → x ∈ acc.2 ∨ isCand x = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc x hx
    unfold classCandsGo at hx
    split at hx
    · exact Or.inl hx
    · rcases iha _ x hx with hx | hx
      · rcases ihf _ x hx with hx | hx
        · dsimp only at hx
          split at hx
          · rename_i hc
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inr hc
            · exact Or.inl hx
          · exact Or.inl hx
        · exact Or.inr hx
      · exact Or.inr hx
  | lam t b _ iht ihb =>
    intro acc x hx
    unfold classCandsGo at hx
    split at hx
    · exact Or.inl hx
    · rcases ihb _ x hx with hx | hx
      · have := iht _ x hx; exact this
      · exact Or.inr hx
  | forallE t b _ iht ihb =>
    intro acc x hx
    unfold classCandsGo at hx
    split at hx
    · exact Or.inl hx
    · rcases ihb _ x hx with hx | hx
      · have := iht _ x hx; exact this
      · exact Or.inr hx
  | letE t v b iht ihv ihb =>
    intro acc x hx
    unfold classCandsGo at hx
    split at hx
    · exact Or.inl hx
    · rcases ihb _ x hx with hx | hx
      · rcases ihv _ x hx with hx | hx
        · have := iht _ x hx; exact this
        · exact Or.inr hx
      · exact Or.inr hx
  | proj _ _ y ih =>
    intro acc x hx
    unfold classCandsGo at hx
    split at hx
    · exact Or.inl hx
    · have := ih _ x hx; exact this
  | _ => intro acc x hx; unfold classCandsGo at hx; exact Or.inl hx

theorem classCands_foldl_mem {isCand : Expr → Bool} :
    ∀ (L : List (List Expr)) (acc : Std.HashSet Expr × List Expr) (x : Expr),
      x ∈ (L.foldl (fun acc cs => cs.foldl (classCandsGo isCand) acc) acc).2 →
        x ∈ acc.2 ∨ isCand x = true := by
  have inner : ∀ (cs : List Expr) (acc : Std.HashSet Expr × List Expr) (x : Expr),
      x ∈ (cs.foldl (classCandsGo isCand) acc).2 → x ∈ acc.2 ∨ isCand x = true := by
    intro cs
    induction cs with
    | nil => intro acc x hx; exact Or.inl hx
    | cons e cs ih =>
      intro acc x hx
      rcases ih _ x hx with hx | hx
      · exact classCandsGo_mem e acc x hx
      · exact Or.inr hx
  intro L
  induction L with
  | nil => intro acc x hx; exact Or.inl hx
  | cons cs L ih =>
    intro acc x hx
    rcases ih _ x hx with hx | hx
    · exact inner cs acc x hx
    · exact Or.inr hx

/-- **An alias comes from a candidate**: its inductive the candidate's
head, its parameters the candidate's first `nPc` arguments, erased. -/
@[expose] def ClassAliasFrom (es : List Expr) (a : ClassAlias) : Prop :=
  ∃ e ∈ es, ∃ us, e.getAppFn = .const a.ind us ∧ a.nPc ≤ e.getAppArgs.length ∧
    a.ps = (e.getAppArgs.take a.nPc).map Expr.eraseFVarTys

theorem classAliases_from {hi : Nat} {cls : List ClassInfo} :
    ∀ {es : List Expr} {al : List ClassAlias}, classAliases ops env hi cls es = .ok al →
      ∀ a ∈ al, ClassAliasFrom es a
  | [], al, h => by
    simp only [classAliases, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro _ h; exact nomatch h
  | e :: es, al, h => by
    unfold classAliases at h
    obtain ⟨rest, hr, h⟩ := exceptBind_ok h
    have ih : ∀ a ∈ rest, ClassAliasFrom (e :: es) a := fun a ha => by
      obtain ⟨e', he', hrest⟩ := classAliases_from hr a ha
      exact ⟨e', List.mem_cons_of_mem _ he', hrest⟩
    split at h
    · rename_i I us hfn
      dsimp only at h
      obtain ⟨found, hloop, h⟩ := exceptBind_ok h
      have hP := except_forIn_inv (fun f : Option ClassAlias => ∀ a, f = some a →
          ClassAliasFrom (e :: es) a) (by intro a h; simp at h) (fun c hc s s' hs hst => by
        split at hst
        · rename_i hcond
          obtain ⟨b0, hb, hst⟩ := exceptBind_ok hst
          split at hst
          · simp only [pure, Except.pure, Except.ok.injEq] at hst
            subst hst
            intro a ha
            simp only [ForInStep.value, Option.some.injEq] at ha
            subst ha
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            exact ⟨e, List.mem_cons_self, us, hfn, hcond.1.1.2, rfl⟩
          · simp only [pure, Except.pure, Except.ok.injEq] at hst
            subst hst; exact hs
        · simp only [pure, Except.pure, Except.ok.injEq] at hst
          subst hst; exact hs) hloop
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro a ha
      cases found with
      | none => exact ih a ha
      | some a0 =>
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hP _ rfl
        · exact ih a ha
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ih

/-- **Two container classes identified**, in the order compared: one
inductive, equivalent levels, syntactically the same (`ClassInfo.same`) or
per component in hole form. -/
@[expose] def ClassSameOk (ops : CheckerOps CheckM) (env : Env) (hi : Nat) (cls : List ClassInfo)
    (i j : Nat) : Prop :=
  (cls.getD i default).member = none ∧ (cls.getD j default).member = none ∧
    (cls.getD i default).key.ind = (cls.getD j default).key.ind ∧
    Level.isEquivList (cls.getD i default).key.lvls (cls.getD j default).key.lvls = some true ∧
    ((cls.getD i default).same (cls.getD j default) = true ∨
      classParamsDefEq ops env hi ((cls.getD i default).holeForm cls)
        ((cls.getD j default).holeForm cls) = .ok true)

/-- **`classSamePairs`, inverted**: every recorded pair identified, in one
order or the other. -/
theorem classSamePairs_run {hi : Nat} {cls : List ClassInfo} {out : List (Nat × Nat)}
    (h : classSamePairs ops env hi cls = .ok out) :
    ∀ p ∈ out, ClassSameOk ops env hi cls p.1 p.2 ∨ ClassSameOk ops env hi cls p.2 p.1 := by
  unfold classSamePairs at h
  dsimp only at h
  obtain ⟨r, hloop, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  let P : List (Nat × Nat) → Prop := fun o =>
    ∀ p ∈ o, ClassSameOk ops env hi cls p.1 p.2 ∨ ClassSameOk ops env hi cls p.2 p.1
  refine except_forIn_inv (P := P) (by intro p hp; exact nomatch hp) (fun i _ s s' hs hst => ?_) hloop
  obtain ⟨r', hin, hst⟩ := exceptBind_ok hst
  simp only [pure, Except.pure, Except.ok.injEq] at hst
  subst hst
  refine except_forIn_inv (P := P) hs (fun j _ s s' hs hst => ?_) hin
  split at hst
  · rename_i hcond
    obtain ⟨b0, hb, hst⟩ := exceptBind_ok hst
    split at hst
    · rename_i hor
      simp only [pure, Except.pure, Except.ok.injEq] at hst
      subst hst
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, beq_iff_eq]
        at hcond
      obtain ⟨⟨⟨⟨-, hm1⟩, hm2⟩, hI⟩, hlv⟩ := hcond
      have hQ : ClassSameOk ops env hi cls i j := by
        refine ⟨hm1, hm2, hI, hlv, ?_⟩
        rcases Bool.or_eq_true_iff.mp hor with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (h1 ▸ hb)
      intro p hp
      simp only [ForInStep.value, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact Or.inl hQ
      · exact Or.inr hQ
      · exact hs p hp
    · simp only [pure, Except.pure, Except.ok.injEq] at hst
      subst hst; exact hs
  · simp only [pure, Except.pure, Except.ok.injEq] at hst
    subst hst; exact hs

/-! ## Check 5: the walk against the inductive hypotheses -/

/-- **`classMinorSlot`, inverted**: the slot is a minor premise of class
`c` for constructor `C`, with inductive hypotheses `ihs`. -/
theorem classMinorSlot_run {rd : ClassRead} {c : Nat} {C : Name} {s : Nat}
    {ihs : List (Nat × Nat)} (h : classMinorSlot (m := CheckM) rd c C = .ok (s, ihs)) :
    rd.slots[s]? = some (.minor c C ihs) := by
  unfold classMinorSlot at h
  dsimp only at h
  split at h
  · rename_i x hx
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hm : (s, ihs) ∈ [(s, ihs)] := List.mem_singleton_self _
    rw [← hx] at hm
    obtain ⟨s', -, hs'⟩ := List.mem_filterMap.mp hm
    split at hs'
    · rename_i c' C' ihs' heq
      split at hs'
      · rename_i hcc
        simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        simp only [Bool.and_eq_true, beq_iff_eq] at hcc
        obtain ⟨rfl, rfl⟩ := hcc
        exact heq
      · exact nomatch hs'
    · exact nomatch hs'
  · close_throw h

/-- One field's inductive hypothesis against its walk: an ordinary field
has none; a recursive one exactly one, at a class the same as the one it
lands at, and the generator's kind names the ih's class. -/
@[expose] def ClassIhAgree (sameIdx : Nat → Nat → Bool) (ihs : List (Nat × Nat)) (i : Nat)
    (k k' : ClassField) : Prop :=
  (k = .ordinary ∧ k' = .ordinary ∧ ihs.filter (·.1 == i) = []) ∨
    ∃ c tele i' t, k = .recursive c tele ∧ ihs.filter (·.1 == i) = [(i', t)] ∧
      sameIdx c t = true ∧ k' = .recursive t tele

/-- **`classIhsAgree`, inverted.** -/
theorem classIhsAgree_run {sameIdx : Nat → Nat → Bool} {ctor : Name} {ihs : List (Nat × Nat)} :
    ∀ {i : Nat} {ks ks' : List ClassField},
      classIhsAgree (m := CheckM) sameIdx ctor ihs i ks = .ok ks' →
      ks'.length = ks.length ∧ ∀ (l : Nat) (k : ClassField), ks[l]? = some k →
        ∃ k', ks'[l]? = some k' ∧ ClassIhAgree sameIdx ihs (i + l) k k'
  | _, [], ks', h => by
    simp only [classIhsAgree, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | i, k :: ks, ks', h => by
    unfold classIhsAgree at h
    dsimp only at h
    have key : ∃ k' ks'', ClassIhAgree sameIdx ihs i k k' ∧
        classIhsAgree (m := CheckM) sameIdx ctor ihs (i + 1) ks = .ok ks'' ∧ ks' = k' :: ks'' := by
      split at h
      · rename_i hf
        obtain ⟨k0, hk0, h⟩ := exceptBind_ok h
        obtain ⟨ks'', hks, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at hk0 h
        subst hk0
        exact ⟨_, ks'', Or.inl ⟨rfl, rfl, hf⟩, hks, h.symm⟩
      · rename_i c tele i' t hf
        split at h
        · rename_i hs
          obtain ⟨k0, hk0, h⟩ := exceptBind_ok h
          obtain ⟨ks'', hks, h⟩ := exceptBind_ok h
          simp only [pure, Except.pure, Except.ok.injEq] at hk0 h
          subst hk0
          exact ⟨_, ks'', Or.inr ⟨c, tele, i', t, rfl, hf, hs, rfl⟩, hks, h.symm⟩
        · close_throw h
      · close_throw h
    obtain ⟨k', ks'', hagree, hks, rfl⟩ := key
    obtain ⟨hl, hall⟩ := classIhsAgree_run hks
    refine ⟨by simp [hl], fun l k0 hk0 => ?_⟩
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk0
      subst hk0
      exact ⟨k', rfl, by simpa using hagree⟩
    | succ l =>
      obtain ⟨k1, h1, h2⟩ := hall l k0 (by simpa using hk0)
      exact ⟨k1, by simpa using h1, by rw [show i + (l + 1) = i + 1 + l by omega]; exact h2⟩

/-! ## The whole check -/

/-- The class check's context: the canonical parameters `params`, the
members' holes after them. -/
@[expose] def classCtxOf (p : BlockParts) (fe₁ : FEnv) (env₁ : Env) (params : List Expr) : NestCtx :=
  ⟨p.toBlockShape.memberNames, p.toBlockShape.lps, p.toBlockShape.nP, p.toBlockShape.nIdxs, params,
    p.toBlockShape.resSort, fe₁.find?, env₁.consts⟩

/-- The end of the holes: the members', then one per container class. -/
@[expose] def classHi (ctx : NestCtx) (cls : List ClassInfo) : Nat :=
  ctx.hiAt 0 + (cls.filter (·.member.isNone)).length

/-- The crests after the defeq tier's second abstraction. -/
@[expose] def classAliasAbs (al : List ClassAlias) (e : Expr) : Expr :=
  (classAbsGo (aliasOcc? al) none {} e).1

/-- The installation counter the class check reads as an inductive's AGE. -/
@[expose] def classAge (fe₁ : FEnv) : Name → Nat := fun I => ((fe₁.idx[I]?).map (·.1)).getD 0

/-- An inductive's recorded block (`IndCaps.all`). -/
@[expose] def classMates (fe₁ : FEnv) : Name → List Name := fun I => match fe₁.find? I with
  | some (.indInfo _ caps) => caps.all
  | _ => []

/-- The crests after the defeq tier's second abstraction, each class's at
the aliases it may use (`classAliasesFor`). -/
@[expose] def classCrestsAl (fe₁ : FEnv) (cls : List ClassInfo) (al : List ClassAlias)
    (crests0 : List (List Expr)) : List (List Expr) :=
  (cls.zip crests0).map fun (c, cs) =>
    cs.map (classAliasAbs (classAliasesFor (classAge fe₁) (classMates fe₁) c al))

/-- The identification check 5 uses. -/
@[expose] def classSameIdx (cls : List ClassInfo) (pairs : List (Nat × Nat)) (i j : Nat) : Bool :=
  i == j || (cls.getD i default).same (cls.getD j default) || pairs.contains (i, j)

/-- A class's constructor instantiated (before the class abstraction): a
member's at the canonical parameters with the members abstracted, a
container's at the class's levels and member-abstracted parameters. -/
@[expose] def classCrestInst (ctx : NestCtx) (holes : List Expr) (c : ClassInfo) (cv : ConstantVal) :
    Option Expr :=
  match c.member with
  | some _ => instPisWith ctx.params (nestAbstract ctx holes cv.type)
  | none => instPisWith c.dsA (cv.type.instantiateLevelParams cv.levelParams c.key.lvls)

theorem classCrest_run {holes : List Expr} {cls : List ClassInfo} {c : ClassInfo} {cv : ConstantVal}
    {e : Expr} (h : classCrest (m := CheckM) ctx holes cls c cv = .ok e) :
    ∃ e0, classCrestInst ctx holes c cv = some e0 ∧ e = classAbs cls e0 := by
  unfold classCrest at h
  obtain ⟨e0, h0, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨e0, unwrapOr_ok h0, h.symm⟩

/-- **The class check, as run** (see the module docstring): the pre-pass's
reading, the context, the classes (check 1) and R6, the crests and the
defeq tier, reachability, checks 3/4 (`walked`), check 5 (`ctors`, the
output), the elimination guard, and check 6's two runs. -/
structure ClassRun (ops : CheckerOps CheckM) (fe₁ : FEnv) (env₁ : Env) (fe : FEnv) (p : BlockParts)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) (ctors : List (List ClassCtor)) : Type where
  rd : ClassRead
  pq : List Expr × Expr
  holes : List Expr
  cls : List ClassInfo
  crests0 : List (List Expr)
  al : List ClassAlias
  pairs : List (Nat × Nat)
  walked : List (List ClassCtor)
  formerTys : List Expr
  pre : List (Expr × BinderMeta)
  cvRis : List ConstantVal
  pins : targetRecPins (m := CheckM) p.toBlockShape block = .ok ()
  hrd : classRead p.toBlockShape.nP (fun I =>
      if p.toBlockShape.memberNames.contains I then p.toBlockShape.nP else
        match fe₁.find? I with
        | some (.indInfo _ caps) => caps.nparams
        | _ => 0) p.toBlockShape.recs = some rd
  hpq : ∃ cvTa0, cvTas.head? = some cvTa0 ∧ openPisAtFvars p.toBlockShape.nP cvTa0.type 0 = some pq
  hholes : nestHoles (classCtxOf p fe₁ env₁ pq.1) = some holes
  /-- check 1 -/
  hcls : ClassInfosD ops env₁ (classCtxOf p fe₁ env₁ pq.1) holes ctorsAs 0 rd.classes cls
  hone : (List.range p.toBlockShape.k).all
    (fun t => (cls.filter (·.member == some t)).length == 1) = true
  /-- every container class's block mates at its instantiation are classes -/
  hmates : classMatesOk cls (classMates fe₁) = true
  /-- R6 -/
  r6 : ∀ c ∈ cls, c.member = none →
    c.dsA.map (classAbs (classCyc (classAge fe₁) cls c)) ≠ c.dsA →
    ∃ ty, ops.inferType env₁ (classHi (classCtxOf p fe₁ env₁ pq.1) cls)
      (Expr.mkAppN (.const c.key.ind c.key.lvls)
        (c.dsA.map (classAbs (classCyc (classAge fe₁) cls c)))) = .ok ty
  /-- the crests, instantiated and syntactically abstracted -/
  hcrests : cls.mapM (fun c => c.ctors.mapM fun x =>
    classCrest (m := CheckM) (classCtxOf p fe₁ env₁ pq.1) holes cls c x.1) = .ok crests0
  /-- the defeq tier -/
  hal : ∀ a ∈ al, ClassAliasOk ops env₁ (classHi (classCtxOf p fe₁ env₁ pq.1) cls) cls a
  /-- the defeq tier's candidates, and the candidate guard -/
  cands : List Expr
  hcand : ∀ e ∈ cands, ∃ I us nPc, e.getAppFn = .const I us ∧
    (cls.filterMap fun c => if c.member.isNone then some (c.key.ind, c.nPc) else none).lookup I
      = some nPc ∧ nPc ≤ e.getAppArgs.length ∧
    ∀ x ∈ e.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ classHi (classCtxOf p fe₁ env₁ pq.1) cls
  halFrom : ∀ a ∈ al, ClassAliasFrom cands a
  hpairs : ∀ q ∈ pairs, ClassSameOk ops env₁ (classHi (classCtxOf p fe₁ env₁ pq.1) cls) cls q.1 q.2 ∨
    ClassSameOk ops env₁ (classHi (classCtxOf p fe₁ env₁ pq.1) cls) cls q.2 q.1
  /-- reachability -/
  reached : (List.range cls.length).all (classReached
    (classCrestsAl fe₁ cls al crests0) cls (classMates fe₁)
    (classSameIdx cls pairs) (cls.length + 1)
    ((List.range cls.length).filter fun c => (cls.getD c default).member.isSome)).contains = true
  /-- checks 3 and 4 -/
  hwalk : classAllCtors ops env₁ (classCtxOf p fe₁ env₁ pq.1) holes cls
    (classHi (classCtxOf p fe₁ env₁ pq.1) cls) cls (classCrestsAl fe₁ cls al crests0)
      = .ok walked
  /-- check 5 -/
  h5 : (List.range cls.length).mapM (fun c => (walked.getD c []).mapM fun x => do
    let (_, ihs) ← classMinorSlot (m := CheckM) rd c x.cv.name
    let ks ← classIhsAgree (m := CheckM) (classSameIdx cls pairs) x.cv.name ihs 0 x.kinds
    pure { x with kinds := ks }) = .ok ctors
  hminors : ((rd.slots.filter fun | .minor .. => true | _ => false).length ==
    (ctors.map List.length).sum) = true
  /-- the elimination guard -/
  elim : (p.toBlockShape.large &&
    !blockLargeElimAllowed p.toBlockShape (cls.any (·.member.isNone))) = false
  /-- check 6: the family generated, every recursor's type and rules -/
  hformer : cls.mapM (fun c => match c.member with
    | some t => pure ((cvTas.getD t default).type)
    | none => match fe₁.find? c.key.ind with
      | some (.indInfo cv _) => pure (cv.type.instantiateLevelParams cv.levelParams c.key.lvls)
      | _ => throw (.internal "class check: class former vanished")) = (.ok formerTys : CheckM _)
  hpre : ClassGen.prefixBinders ⟨p.toBlockShape.nP, pq.1, cls, formerTys, rd.slots, ctors,
    structElimLevel p.toBlockShape.elim p.toBlockShape.large, []⟩ = some pre
  htys : classRecTysOk ops fe ⟨p.toBlockShape.nP, pq.1, cls, formerTys, rd.slots, ctors,
    structElimLevel p.toBlockShape.elim p.toBlockShape.large, pre⟩ p.toBlockShape.k
    p.toBlockShape.recs (targetRecRules block) rd.recCls = .ok cvRis
  hrules : classRecsRulesOk ops StructWalkers.plain fe
    (consBlockRecsBareF p.toBlockShape 0
      ((cvRis.zip rd.recCls).map fun (cv, c) => (cv, (cls.getD c default).nIdx)) fe)
    ⟨p.toBlockShape.nP, pq.1, cls, formerTys, rd.slots, ctors,
      structElimLevel p.toBlockShape.elim p.toBlockShape.large, pre⟩
    (fun t => ((List.range p.toBlockShape.recs.length).find? fun r => rd.recCls.getD r 0 == t).map
      fun r => (p.toBlockShape.recs.getD r default).cvR.name)
    (Level.zeronessOf (structElimLevel p.toBlockShape.elim p.toBlockShape.large))
    p.toBlockShape.recs cvRis rd.recCls = .ok out

/-- **The class check, inverted** — the ONE unfolding of `classRecCheck`
(at the pure install's shadow operations `ShadowOps.ofOps ops`; the
model's `ShadowOps.fueled mode F` is one). -/
theorem classRecCheck_run {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {ctors : List (List ClassCtor)}
    (h : classRecCheck (ShadowOps.ofOps ops) fe₁ env₁ fe p block cvTas ctorsAs = .ok (out, ctors)) :
    Nonempty (ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors) := by
  unfold classRecCheck at h
  simp only [ShadowOps.ofOps] at h
  obtain ⟨u0, hpins, h⟩ := exceptBind_ok h
  obtain ⟨rd, hrd, h⟩ := exceptBind_ok h
  obtain ⟨cvTa0, hcv, h⟩ := exceptBind_ok h
  obtain ⟨pq, hpq, h⟩ := exceptBind_ok h
  obtain ⟨holes, hholes, h⟩ := exceptBind_ok h
  obtain ⟨u1, -, h⟩ := exceptBind_ok h
  obtain ⟨cls, hcls, h⟩ := exceptBind_ok h
  obtain ⟨hone, h⟩ := unless_jp_ok h
  obtain ⟨hmates, h⟩ := unless_jp_ok h
  obtain ⟨u2, hr6, h⟩ := exceptBind_ok h
  obtain ⟨crests0, hcr, h⟩ := exceptBind_ok h
  obtain ⟨al, hal, h⟩ := exceptBind_ok h
  obtain ⟨pairs, hpairs, h⟩ := exceptBind_ok h
  split at h
  case isFalse => close_throw h
  rename_i hreach
  obtain ⟨walked, hwalk, h⟩ := exceptBind_ok h
  obtain ⟨u3, -, h⟩ := exceptBind_ok h
  obtain ⟨ctors', h5, h⟩ := exceptBind_ok h
  split at h
  case isFalse => close_throw h
  rename_i hmin
  split at h
  case isTrue => close_throw h
  rename_i hel
  obtain ⟨formerTys, hformer, h⟩ := exceptBind_ok h
  obtain ⟨pre, hpre, h⟩ := exceptBind_ok h
  obtain ⟨cvRis, htys, h⟩ := exceptBind_ok h
  obtain ⟨u4, -, h⟩ := exceptBind_ok h
  obtain ⟨out', hout, h⟩ := exceptBind_ok h
  obtain ⟨u5, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  cases u0
  refine ⟨⟨rd, pq, holes, cls, crests0, al, pairs, walked, formerTys, pre, cvRis, hpins,
    unwrapOr_ok hrd, ⟨cvTa0, unwrapOr_ok hcv, unwrapOr_ok hpq⟩, unwrapOr_ok hholes,
    classInfos_run hcls, hone, hmates, classKeysCyclic_run hr6, hcr, classAliases_run hal,
    _, fun e he => ?_, classAliases_from hal, classSamePairs_run hpairs, hreach, hwalk, h5, hmin,
    by simpa using hel, hformer, unwrapOr_ok hpre, htys, hout⟩⟩
  rcases classCands_foldl_mem _ _ e he with hx | hx
  · exact nomatch hx
  · revert hx
    split
    · rename_i I us hfn
      split
      · rename_i nPc hl
        intro hx
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
        exact ⟨I, us, nPc, hfn, hl, hx.1, fun x hx' => (hx.2 x hx').1⟩
      · intro hx; exact nomatch hx
    · intro hx; exact nomatch hx

/-- **One class's constructor, through the whole run** (checks 3–5): its
crest instantiated (`e0`) and abstracted — syntactic tier, then the defeq
tier — typed and walked (`ClassCtorRun`, the walk's output `x`), and the
check's output `x'`: `x` with every recursive field re-pointed at its
inductive hypothesis's class (`ClassIhAgree`, at the class's minor slot). -/
theorem ClassRun.ctor {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {ctors : List (List ClassCtor)}
    (R : ClassRun ops fe₁ env₁ fe p block cvTas ctorsAs out ctors)
    {c : Nat} {ci : ClassInfo} {j : Nat} {cv : ConstantVal} {nF : Nat}
    (hc : R.cls[c]? = some ci) (hj : ci.ctors[j]? = some (cv, nF)) :
    ∃ e0 xs x xs' x', classCrestInst (classCtxOf p fe₁ env₁ R.pq.1) R.holes ci cv = some e0 ∧
      R.walked[c]? = some xs ∧ xs[j]? = some x ∧
      ClassCtorRun ops env₁ (classCtxOf p fe₁ env₁ R.pq.1) R.holes R.cls
        (classHi (classCtxOf p fe₁ env₁ R.pq.1) R.cls) ci cv nF
        (classAliasAbs (classAliasesFor (classAge fe₁) (classMates fe₁) ci R.al)
          (classAbs R.cls e0)) x ∧
      ctors[c]? = some xs' ∧ xs'[j]? = some x' ∧
      x'.cv = x.cv ∧ x'.nF = x.nF ∧ x'.tyN = x.tyN ∧
      ∃ (s : Nat) (ihs : List (Nat × Nat)), R.rd.slots[s]? = some (ClassSlot.minor c cv.name ihs) ∧ x'.kinds.length = x.kinds.length ∧
        ∀ (l : Nat) (k : ClassField), x.kinds[l]? = some k →
          ∃ k', x'.kinds[l]? = some k' ∧ ClassIhAgree (classSameIdx R.cls R.pairs) ihs l k k' := by
  -- the crest
  obtain ⟨hl0, hcr⟩ := except_mapM_ok R.hcrests
  obtain ⟨crs, hcrs, hcrsRun⟩ := hcr c ci hc
  obtain ⟨hlc, hce⟩ := except_mapM_ok hcrsRun
  obtain ⟨e, he, heRun⟩ := hce j (cv, nF) hj
  obtain ⟨e0, he0, rfl⟩ := classCrest_run heRun
  -- the walk
  obtain ⟨hlw, hw⟩ := classAllCtors_run R.hwalk
  have hcl : c < R.cls.length := (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨xs, hxs⟩ : ∃ xs, R.walked[c]? = some xs :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlw]; simp [classCrestsAl, hl0, hcl])⟩
  obtain ⟨ci', crs', hci', hcrs', hxsRun⟩ := hw c xs hxs
  rw [hc] at hci'; cases hci'
  have hz : (R.cls.zip R.crests0)[c]? = some (ci, crs) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hcrs⟩
  simp only [classCrestsAl, List.getElem?_map, hz, Option.map_some, Option.some.injEq] at hcrs'
  subst hcrs'
  obtain ⟨hlx, hx⟩ := classCtors_run hxsRun
  have hjl : j < ci.ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨x, hxj⟩ : ∃ x, xs[j]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlx]; simp [hlc, hjl])⟩
  obtain ⟨cv', nF', crest', hcv', hcrest', hrun⟩ := hx j x hxj
  rw [hj] at hcv'; cases hcv'
  simp only [List.getElem?_map, he, Option.map_some, Option.some.injEq] at hcrest'
  subst hcrest'
  -- check 5
  obtain ⟨hl5, h5⟩ := except_mapM_ok R.h5
  obtain ⟨xs', hxs', hxsRun'⟩ := h5 c c (by simp [hcl])
  obtain ⟨hl5', h5'⟩ := except_mapM_ok hxsRun'
  have hgd : R.walked.getD c [] = xs := by simp [List.getD_eq_getElem?_getD, hxs]
  rw [hgd] at h5'
  obtain ⟨x', hx', hxRun⟩ := h5' j x hxj
  obtain ⟨⟨s, ihs⟩, hs, hxRun⟩ := exceptBind_ok hxRun
  obtain ⟨ks, hks, hxRun⟩ := exceptBind_ok hxRun
  simp only [pure, Except.pure, Except.ok.injEq] at hxRun
  subst hxRun
  obtain ⟨hlk, hk⟩ := classIhsAgree_run hks
  refine ⟨e0, xs, x, xs', _, he0, hxs, hxj, hrun, hxs', hx', rfl, rfl, rfl, s, ihs, ?_, hlk,
    fun l k hk' => by simpa using hk l k hk'⟩
  rw [← hrun.cv]; exact classMinorSlot_run hs

end ConLeche
