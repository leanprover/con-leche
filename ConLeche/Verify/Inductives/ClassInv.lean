module

public import ConLeche.Kernel.Inductives.ClassCheck
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv

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

end ConLeche
