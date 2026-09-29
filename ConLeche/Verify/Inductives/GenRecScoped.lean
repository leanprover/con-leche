module

public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.NestNfScope
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.CheckerF
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Cached.GenRecC

public section

/-!
# The generated stage's generator inputs are scoped (`ClassGenScoped`)

`genScoped_of_run`: the generated recursor stage's run (`GenRecRun`)
builds its generator `R.g` from inputs scoped the way `ClassGenScoped`
asks — what `recStage_of_gen` and the family premise take as their
hypothesis `hg`.  Field by field, each from the run's own binds:

* `params` — the canonical parameters are the first former's opened
  telescope (`blockNestCtx`): a closed former opened at `0` gives
  `fvar i` typed over the earlier ones;
* `ds` — a class's parameters: a member's are the canonical parameters,
  an outside class's are its key's (the pre-pass's reading off the RAW
  stream recursor types, moved to the canonical parameters and kept below
  them by `classKeyOf`, then annotated: `genRun_keys_scoped`) under
  `targetMajorOf`'s guard (no loose bound variable, free variables below
  `nP`);
* `former` — a member's former is a (closed) stream former, an outside
  class's the stored inductive's type at levels (`EnvWF`);
* `tyN` — the datum entry of the positivity check's table, whose entries
  are scoped over the parameters (`NfStScoped`, `Verify/Inductives/NestNfScope.lean`),
  from the positivity stage's state through the seeds;
* `tyD` — a stored constructor's type (closed: a stream constructor's or a
  stored one's at levels) instantiated at the class's parameters;
* `order` — the pre-pass reads a minor premise's class and its inductive
  hypotheses' classes as ordinals of the motives read BEFORE it
  (`classOfMotiveVar` over `classReadSlots`' `motPos`), and the generator's
  recursive kinds are exactly those hypotheses' classes (`classFieldsOf`);
* `pre` — the prefix is computed with `pre := []`, which `prefixBinders`
  does not read.

The caller's hypotheses: the two environments well formed, the stream's
formers and constructors closed, one former per member, and the
positivity stage's final state scoped (`checkBlockPositivity_nfScoped`).
-/

namespace ConLeche

open Expr

/-! ## Small list facts -/

theorem except_mapM_getElem? {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      l'.length = l.length ∧ ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, l'[i]? = some b ∧ f a = .ok b
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ _ h => nomatch h⟩
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := except_mapM_getElem? hbs
    refine ⟨by simp [hl], fun i a' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : a = a' := by simpa using hi
      exact ⟨b, rfl, hb⟩
    | succ i => simpa using hall i a' (by simpa using hi)

/-- `targetMajorNfs` keeps entries of its table only. -/
theorem targetMajorNfs_sub {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys pfvs : List Expr} {us : List Level} {ds : List Expr}
    {ctors : List (ConstantVal × Nat)} :
    ∀ {tbl nfs : List NestCtorNf},
      targetMajorNfs ops env p formerTys pfvs us ds ctors tbl = .ok nfs → ∀ e ∈ nfs, e ∈ tbl
  | [], nfs, h => by
    simp only [targetMajorNfs, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro e he; exact nomatch he
  | e₀ :: tbl, nfs, h => by
    unfold targetMajorNfs at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    have ih := targetMajorNfs_sub hrest
    intro e he
    split at h
    · obtain ⟨b, -, h⟩ := exceptBind_ok h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih e he)
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact List.mem_cons_of_mem _ (ih e he)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact List.mem_cons_of_mem _ (ih e he)


/-! ## The pre-pass: a minor premise after the motives it names -/

/-- The prefix positions of the motives among `slots` (`ClassRead.motiveSlot`'s list). -/
@[expose] def ClassRead.motPosOf (slots : List ClassSlot) : List Nat :=
  (List.range slots.length).filter fun s =>
    match slots[s]? with | some (.motive _) => true | _ => false

theorem ClassRead.motiveSlot_eq (slots : List ClassSlot) (c : Nat) :
    ClassRead.motiveSlot ⟨slots, []⟩ c = (ClassRead.motPosOf slots)[c]? := rfl

theorem ClassRead.motPosOf_append (A B : List ClassSlot) :
    ClassRead.motPosOf (A ++ B) =
      ClassRead.motPosOf A ++ (ClassRead.motPosOf B).map (A.length + ·) := by
  unfold ClassRead.motPosOf
  rw [List.length_append, List.range_add, List.filter_append, List.filter_map]
  congr 1
  · apply List.filter_congr
    intro s hs
    rw [List.mem_range] at hs
    rw [List.getElem?_append_left hs]
  · congr 1
    apply List.filter_congr
    intro s _
    simp only [Function.comp_apply]
    rw [List.getElem?_append_right (by omega)]
    simp

theorem ClassRead.motPosOf_lt {slots : List ClassSlot} {v : Nat}
    (h : v ∈ ClassRead.motPosOf slots) : v < slots.length := by
  unfold ClassRead.motPosOf at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- A motive ordinal below the motives of the first `s` slots has its
motive before slot `s`. -/
theorem ClassRead.motiveSlot_of_lt {slots : List ClassSlot} {s c : Nat}
    (h : c < (ClassRead.motPosOf (slots.take s)).length) :
    ∃ s', s' < s ∧ ClassRead.motiveSlot ⟨slots, []⟩ c = some s' := by
  have hsp : slots = slots.take s ++ slots.drop s := (List.take_append_drop s slots).symm
  rw [ClassRead.motiveSlot_eq, hsp, ClassRead.motPosOf_append, List.getElem?_append_left h,
    List.getElem?_eq_getElem h]
  refine ⟨_, ?_, rfl⟩
  have := ClassRead.motPosOf_lt (List.getElem_mem h)
  simp only [List.length_take] at this
  omega

theorem classOfMotiveVar_lt {nP : Nat} {motPos : List Nat} {p c : Nat}
    (h : classOfMotiveVar nP motPos p = some c) : c < motPos.length := by
  unfold classOfMotiveVar at h
  split at h
  · exact (List.findIdx?_eq_some_iff_getElem.mp h).1
  · exact nomatch h

/-- **A minor premise's reading names motives read before it**: its class
and every inductive hypothesis's class are ordinals into `motPos`. -/
theorem classReadMinor_cls {np : Nat} {motPos : List Nat} {d : Nat} {dom : Expr} {c : Nat}
    {C : Name} {ihs : List (Nat × Nat)}
    (h : classReadMinor np motPos d dom = some (.minor c C ihs)) :
    c < motPos.length ∧ ∀ q ∈ ihs, q.2 < motPos.length := by
  unfold classReadMinor at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨c', hc', x, -, h⟩ := h
    split at h
    · simp only [Option.pure_def, Option.some.injEq, ClassSlot.minor.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      refine ⟨classOfMotiveVar_lt hc', fun q hq => ?_⟩
      obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hq
      split at hj
      · split at hj
        · rename_i t ht
          split at hj
          · split at hj
            · split at hj
              · simp only [Option.some.injEq] at hj
                subst hj
                exact classOfMotiveVar_lt ht
              · exact nomatch hj
            · exact nomatch hj
          · exact nomatch hj
        · exact nomatch hj
      · exact nomatch hj
    · exact nomatch h
  · exact nomatch h

theorem ClassRead.motPosOf_snoc_minor (pre : List ClassSlot) (c : Nat) (C : Name)
    (ihs : List (Nat × Nat)) :
    ClassRead.motPosOf (pre ++ [.minor c C ihs]) = ClassRead.motPosOf pre := by
  rw [ClassRead.motPosOf_append]; simp [ClassRead.motPosOf]

theorem ClassRead.motPosOf_snoc_motive (pre : List ClassSlot) (k : ClassKey) :
    ClassRead.motPosOf (pre ++ [.motive k]) = ClassRead.motPosOf pre ++ [pre.length] := by
  rw [ClassRead.motPosOf_append]; simp [ClassRead.motPosOf]

/-- **The slots the pre-pass reads**: every minor premise's class and
inductive hypotheses' classes are motives of the slots before it. -/
theorem classReadSlots_order (nPc : Name → Nat) (np : Nat) :
    ∀ (n : Nat) (pre : List ClassSlot) (body : Expr) (rest : List ClassSlot),
      classReadSlots nPc np n (ClassRead.motPosOf pre) (np + pre.length) body = some rest →
      ∀ (j c : Nat) (C : Name) (ihs : List (Nat × Nat)), rest[j]? = some (.minor c C ihs) →
        c < (ClassRead.motPosOf (pre ++ rest.take j)).length ∧
        ∀ q ∈ ihs, q.2 < (ClassRead.motPosOf (pre ++ rest.take j)).length
  | 0, pre, body, rest, h => by
    simp only [classReadSlots, Option.some.injEq] at h
    subst h
    intro j c C ihs hj
    exact nomatch hj
  | n + 1, pre, .forallE dom body bm, rest, h => by
    have fin : ∀ (slot : ClassSlot) (rest' : List ClassSlot),
        (∀ c C ihs, slot = .minor c C ihs →
          classReadMinor np (ClassRead.motPosOf pre) (np + pre.length) dom = some slot) →
        classReadSlots nPc np n (ClassRead.motPosOf (pre ++ [slot])) (np + pre.length + 1)
          (body.instantiate1 (.fvar (np + pre.length) dom)) = some rest' →
        ∀ (j c : Nat) (C : Name) (ihs : List (Nat × Nat)),
          (slot :: rest')[j]? = some (.minor c C ihs) →
          c < (ClassRead.motPosOf (pre ++ (slot :: rest').take j)).length ∧
          ∀ q ∈ ihs, q.2 < (ClassRead.motPosOf (pre ++ (slot :: rest').take j)).length := by
      intro slot rest' hmin hrest j c C ihs hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simpa using classReadMinor_cls (hmin _ _ _ rfl)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [show np + pre.length + 1 = np + (pre ++ [slot]).length by simp; omega] at hrest
        have := classReadSlots_order nPc np n (pre ++ [slot]) _ rest' hrest j c C ihs hj
        simpa [List.take_succ_cons, List.append_assoc] using this
    unfold classReadSlots at h
    dsimp only at h
    split at h
    · cases hl : dom.piBinders.fst.getLast? with
      | none => simp [hl] at h
      | some md =>
        obtain ⟨mdom, mb⟩ := md
        simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · simp only [Option.pure_def, Option.bind_some, Option.bind_eq_some_iff] at h
          obtain ⟨rest', hrest', h⟩ := h
          obtain rfl := Option.some.inj h
          refine fin _ rest' (fun _ _ _ h => nomatch h) ?_
          rw [ClassRead.motPosOf_snoc_motive]
          simpa using hrest'
        · simp at h
    · cases hm : classReadMinor np (ClassRead.motPosOf pre) (np + pre.length) dom with
      | none => simp [hm] at h
      | some slot =>
        simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨rest', hrest', h⟩ := h
        obtain rfl := Option.some.inj h
        obtain ⟨c, C, ihs, rfl⟩ := Cached.classReadMinor_minor hm
        refine fin _ rest' (fun _ _ _ _ => hm) ?_
        rw [ClassRead.motPosOf_snoc_minor]
        simpa using hrest'
  | _ + 1, _, .bvar _, _, h | _ + 1, _, .fvar .., _, h
  | _ + 1, _, .sort _, _, h | _ + 1, _, .const .., _, h
  | _ + 1, _, .app .., _, h | _ + 1, _, .lam .., _, h
  | _ + 1, _, .letE .., _, h | _ + 1, _, .lit _, _, h
  | _ + 1, _, .proj .., _, h => by simp [classReadSlots] at h

/-- **The pre-pass's layout**: every minor premise comes after the
motives of its class and of its inductive hypotheses' classes. -/
theorem classRead_order {nP : Nat} {nPc : Name → Nat} {recs : List RecShape} {rd : ClassRead}
    (h : classRead nP nPc recs = some rd) :
    ∀ (s c : Nat) (C : Name) (ihs : List (Nat × Nat)), rd.slots[s]? = some (.minor c C ihs) →
      (∃ s', s' < s ∧ ClassRead.motiveSlot ⟨rd.slots, []⟩ c = some s') ∧
      ∀ q ∈ ihs, ∃ s', s' < s ∧ ClassRead.motiveSlot ⟨rd.slots, []⟩ q.2 = some s' := by
  unfold classRead at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rc0, -, ⟨pf, body⟩, -, slots, hslots, recCls, -, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  intro s c C ihs hs
  have hslots' : classReadSlots nPc nP (rc0.rP - nP) (ClassRead.motPosOf [])
      (nP + ([] : List ClassSlot).length) body = some slots := by
    simpa [ClassRead.motPosOf] using hslots
  obtain ⟨hc, hq⟩ := classReadSlots_order nPc nP _ [] body slots hslots' s c C ihs hs
  simp only [List.nil_append] at hc hq
  exact ⟨ClassRead.motiveSlot_of_lt hc, fun q hq' => ClassRead.motiveSlot_of_lt (hq q hq')⟩

/-- The one minor premise slot of a class's constructor. -/
theorem classMinorSlot_unique {rd : ClassRead} {c : Nat} {C : Name} {s' : Nat}
    {ihs' : List (Nat × Nat)} (h : classMinorSlot (m := CheckM) rd c C = .ok (s', ihs')) :
    ∀ s ihs, rd.slots[s]? = some (.minor c C ihs) → s = s' ∧ ihs = ihs' := by
  intro s ihs hs
  simp only [classMinorSlot] at h
  split at h
  · rename_i x hx
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hmem : (s, ihs) ∈ [(s', ihs')] := by
      rw [← hx]
      refine List.mem_filterMap.mpr ⟨s, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hs).1, ?_⟩
      simp [hs]
    simpa using hmem
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The generator's recursive kinds are the minor premise's inductive
hypotheses' classes. -/
theorem classFieldsOf_rec {p : BlockShape} {ctor : Name} {ihs : List (Nat × Nat)} :
    ∀ (i : Nat) (fvs : List Expr) (ks : List ClassField),
      classFieldsOf (m := CheckM) p ctor ihs i fvs = .ok ks →
      ∀ t tele, ClassField.recursive t tele ∈ ks → ∃ f, (f, t) ∈ ihs
  | i, [], ks, h => by
    simp only [classFieldsOf, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro t tele ht; exact nomatch ht
  | i, f :: fs, ks, h => by
    unfold classFieldsOf at h
    dsimp only at h
    intro t tele ht
    have tail : ∀ k' : ClassField, (classFieldsOf (m := CheckM) p ctor ihs (i + 1) fs >>=
        fun ks' => pure (k' :: ks')) = Except.ok ks → ClassField.recursive t tele ∈ ks →
        k' = .recursive t tele ∨ ∃ f, (f, t) ∈ ihs := by
      intro k' hk hmem
      obtain ⟨ks', hks', hk⟩ := exceptBind_ok hk
      simp only [pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      rcases List.mem_cons.mp hmem with h' | h'
      · exact .inl h'.symm
      · exact .inr (classFieldsOf_rec (i + 1) fs ks' hks' t tele h')
    split at h
    · obtain ⟨k', hk', h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hk'
      subst hk'
      rcases tail _ h ht with h' | h'
      · exact nomatch h'
      · exact h'
    · rename_i a t' _ hf
      obtain ⟨k', hk', h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hk'
      subst hk'
      rcases tail _ h ht with h' | h'
      · simp only [ClassField.recursive.injEq] at h'
        obtain ⟨rfl, -⟩ := h'
        have : (a, t') ∈ ihs.filter (·.1 == i) := by rw [hf]; exact List.mem_cons_self
        exact ⟨a, (List.mem_filter.mp this).1⟩
      · exact h'
    · obtain ⟨k', hk', h⟩ := exceptBind_ok h
      simp [throw, throwThe, MonadExceptOf.throw] at hk'

/-! ## The run's pieces -/

section Run

variable {mode : CheckMode} {F : Nat} {env₁ envC : Env} {p : BlockShape} {nestedBit : Bool}
  {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The run's walk context: the first former opened, the environment's
lookups. -/
theorem genRun_ctx
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out) :
    ∃ cvTa0 rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (R.ctx.params, rest) ∧
      R.ctx = p.nestCtx R.ctx.params env₁.find? env₁.consts ∧ nestHoles R.ctx = some R.holes := by
  obtain ⟨cvTa0, fvsP, rest, h0, hop, hctx, hh⟩ := blockNestCtx_inv R.hctx
  rw [mkFEnv_find?_fun] at hctx
  refine ⟨cvTa0, rest, h0, ?_, ?_, hh⟩
  · rw [hctx]; exact hop
  · rw [hctx]; rfl

/-- **The canonical parameters**: `fvar i`, typed over the earlier ones. -/
theorem genRun_params
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) :
    R.ctx.params.length = p.nP ∧
      ∀ (i : Nat) (x : Expr), R.ctx.params[i]? = some x → ∃ ty, x = .fvar i ty ∧ ScB i ty := by
  obtain ⟨cvTa0, rest, h0, hop, -, -⟩ := genRun_ctx R
  obtain ⟨hl, hfvs, -⟩ := ScB.openPis hop (hT cvTa0 (List.mem_of_mem_head? h0))
  exact ⟨hl, fun i x hx => by simpa using hfvs i x hx⟩

theorem genRun_params_scb
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) : ∀ x ∈ R.ctx.params, ScB p.nP x := by
  obtain ⟨hl, hP⟩ := genRun_params R hT
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hxe, hty⟩ := hP i _ (List.getElem?_eq_getElem hi)
  rw [hxe]
  exact ScB.fvar (by omega) hty

/-- **The run's class keys are scoped** over the canonical parameters:
each parameter moved to them, kept below them by the guard, then
annotated (`classKeyOf`). -/
theorem genRun_keys_scoped
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) :
    ∀ key ∈ R.keys, ∀ x ∈ key.ds, WScoped p.nP x := by
  have hpar := genRun_params_scb R hT
  obtain ⟨hlP, -⟩ := genRun_params R hT
  intro key hk x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hk
  have hl := mapM_ok_length R.hkeys
  have hil : i < R.rd.classes.length := by
    rw [← hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨key', hkey', hrun⟩ := mapM_ok_getElem? R.hkeys i _ (List.getElem?_eq_getElem hil)
  rw [hi] at hkey'
  obtain rfl := Option.some.inj hkey'
  obtain ⟨-, -, hg, hann⟩ := classKeyOf_run hrun
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  have hlj := mapM_ok_length hann
  have hjl : j < (classKeyCanon R.ctx.params R.rd.classes[i]).ds.length := by
    rw [← hlj]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨x', hx', hax⟩ := mapM_ok_getElem? hann j _ (List.getElem?_eq_getElem hjl)
  rw [hj] at hx'
  obtain rfl := Option.some.inj hx'
  have hmem := List.getElem_mem hjl
  have hyg := hg _ hmem
  have hyw : WScoped p.nP (classKeyCanon R.ctx.params R.rd.classes[i]).ds[j] := by
    generalize hy : (classKeyCanon R.ctx.params R.rd.classes[i]).ds[j] = y at hmem hyg
    simp only [classKeyCanon, List.mem_map] at hmem
    obtain ⟨y0, -, rfl⟩ := hmem
    exact replaceFVars_WScoped_of_below (fun i r hr => (hpar r (List.mem_of_getElem? hr)).1)
      (fun i hi => by simp [hlP, hi]) y0 (Expr.fvarB_le hyg.2)
  exact annotateCore_WScoped _ _ hax hyw

/-- **Every class checked as a major**, scoped: its parameters scoped over
the canonical parameters (an outside class's below them), its
constructors closed, a member's index a member. -/
theorem genRun_Ms₀
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henvC : EnvWF envC) (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type) :
    ∀ M ∈ R.Ms₀, (∀ x ∈ M.ds, ScB p.nP x) ∧ (M.member = none → ∀ x ∈ M.ds, x.fvarB ≤ p.nP) ∧
      (∀ cA ∈ M.ctors, ScB 0 (targetCtorAt M cA.1)) ∧
      (∀ t, M.member = some t → t < p.memberNames.length) ∧
      (M.member = none → ∃ cv caps, envC.find? M.ind = some (.indInfo cv caps)) := by
  have hpar := genRun_params_scb R hT
  obtain ⟨hlen, hall⟩ := R.majors
  have hkeys := genRun_keys_scoped R hT
  intro M hM
  obtain ⟨i, hi, hMi⟩ := List.getElem_of_mem hM
  have hik : i < R.keys.length := by omega
  obtain ⟨M', hM', ⟨C⟩⟩ := hall i _ (List.getElem?_eq_getElem hik)
  rw [List.getElem?_eq_getElem hi, hMi] at hM'
  obtain rfl := Option.some.inj hM'
  have hkey : R.keys[i] ∈ R.keys := List.getElem_mem _
  generalize R.keys[i] = key at hkey C
  cases C.major with
  | member I t ms ctorsA hfn ht hms hctors hpar' nfs =>
    dsimp only
    refine ⟨fun x hx => hpar x (List.mem_of_mem_take hx), fun h => by simp at h,
      fun cA hcA => hct ctorsA (List.mem_of_getElem? hctors) cA hcA, fun t' ht' => ?_,
      fun h => by simp at h⟩
    obtain rfl : t = t' := Option.some.inj ht'
    exact (List.findIdx?_eq_some_iff_getElem.mp ht).1
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
    dsimp only
    refine ⟨fun x hx => ?_, fun _ x hx => (hdsSc x hx).2, fun cA hcA => ?_, fun _ h => by simp at h,
      fun _ => ?_⟩
    · have hxa := List.mem_of_mem_take hx
      rw [Expr.getAppArgs_mkAppN] at hxa
      simp only [Expr.getAppArgs, List.nil_append] at hxa
      have hw := hkeys key hkey x hxa
      exact ⟨WScoped.of_fvarsBelow hw (Expr.fvarB_le (hdsSc _ hx).2),
        Expr.bvarB_le (by rw [(hdsSc _ hx).1]; exact Nat.le_refl 0)⟩
    · have hc : NestCtxOk (⟨[], [], 0, [], [], .zero, (mkFEnv envC).find?,
          (mkFEnv envC).env.consts⟩ : NestCtx) ∧
          NestCtxB (⟨[], [], 0, [], [], .zero, (mkFEnv envC).find?,
            (mkFEnv envC).env.consts⟩ : NestCtx) := by
        rw [mkFEnv_find?_fun, mkFEnv_env]
        exact ⟨⟨fun ci hci => (henvC ci hci).1,
            fun _ ci hf => (henvC ci (List.mem_of_find?_eq_some hf)).1⟩,
          ⟨fun ci hci => (henvC ci hci).2.2.2.1,
            fun _ ci hf => (henvC ci (List.mem_of_find?_eq_some hf)).2.2.2.1⟩⟩
      have h0 := nestContainer_scb hc.1 hc.2 hctors cA hcA
      simp only [targetCtorAt]
      refine ScB.of_closed ?_ ?_ 0
      · rw [Expr.hasFvar_instantiateLevelParams]; exact (ScB.closed h0).1
      · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact h0.2
    · unfold targetCtorsOf nestContainer at hctors
      dsimp only at hctors
      split at hctors
      · rename_i cv caps hf
        rw [mkFEnv_find?_fun] at hf
        exact ⟨cv, caps, hf⟩
      · exact nomatch hctors

/-- **Every class with its table entries**: the class checked as a major,
its entries among the table's. -/
theorem genRun_Ms
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out) :
    R.Ms.length = R.Ms₀.length ∧ ∀ (c : Nat) (M : TargetMajor), R.Ms[c]? = some M →
      ∃ M₀, R.Ms₀[c]? = some M₀ ∧ M = { M₀ with nfs := M.nfs } ∧
        ∀ e ∈ M.nfs, e ∈ R.st.ctorNfs.toList := by
  obtain ⟨hlen, hall⟩ := classesNfs_run R.hMs
  refine ⟨hlen, fun c M hM => ?_⟩
  have hc : c < R.Ms₀.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hM).1
  obtain ⟨nfs, hMs, hnfs⟩ := hall c _ (List.getElem?_eq_getElem hc)
  rw [hM] at hMs
  obtain rfl := Option.some.inj hMs
  exact ⟨_, List.getElem?_eq_getElem hc, rfl, targetMajorNfs_sub hnfs⟩

/-- **The positivity check's table after the seeds is scoped** over the
parameters: every entry the generated stage reads a datum off
(`ClassCtor.tyN`) — lane B2's fact. -/
theorem genRun_tbl_scoped
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henv₁ : EnvWF env₁) (henvC : EnvWF envC) (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type) (hpos : NfStScoped p.nP pos) :
    ∀ e ∈ R.st.ctorNfs.toList, ScB p.nP e.ty := by
  obtain ⟨cvTa0, rest, h0, hop, hctx, hh⟩ := genRun_ctx R
  obtain ⟨hlP, -⟩ := genRun_params R hT
  have hMs₀ := genRun_Ms₀ R henvC hT hct
  have hcb : NestCtxOk R.ctx ∧ NestCtxB R.ctx := by
    rw [hctx]; exact nestCtx_ok_of_envWF henv₁ p R.ctx.params
  have hnP : R.ctx.nP = p.nP := by rw [hctx]; rfl
  have hparH : ∀ x ∈ R.ctx.params, ScB (R.ctx.hiAt 0) x := by
    intro x hx
    have := genRun_params_scb R hT x hx
    exact this.mono (by rw [← hnP]; simp [NestCtx.hiAt])
  have hholes := nestHoles_ok hcb.1 hh
  have hseeds : ∀ s ∈ classSeeds R.ctx R.holes R.Ms₀, ∀ x ∈ s.1.ds, ScB (R.ctx.hiAt 0) x := by
    intro s hs x hx
    obtain ⟨M, hM, hMn, rfl⟩ := Cached.mem_classSeeds hs
    obtain ⟨hds, hfb, -⟩ := hMs₀ M hM
    refine ⟨(nestSeedOf_ds hh (by rw [hlP, hnP]) (fun y hy => Expr.fvarB_le (by
        rw [hnP]; exact hfb hMn y hy)) x hx).2 (fun y hy => (hholes y hy).1)
        (fun y hy => (hparH y hy).1), ?_⟩
    refine nestSeedOf_closed hh (fun a ha => ?_) (fun y hy => (hds y hy).2) x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hxe, -⟩ := (genRun_params R hT).2 i _ (List.getElem?_eq_getElem hi)
    exact ⟨i, ty, hxe⟩
  have hst := nestSeeds_nfScoped hcb.1 hcb.2 (fun d e w hw he => whnf_WScoped henv₁ F hw he)
    (fun d e w hw he => whnf_looseBVars henv₁ F hw he) _ pos R.st R.hst hseeds
    (by rw [hnP]; exact hpos)
  rw [hnP] at hst
  exact hst.2

/-- A generated constructor of class `c`, as its run. -/
theorem genRun_ctor
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    {c : Nat} {x : ClassCtor} (hx : x ∈ R.ctors.getD c []) :
    ∃ M cA, R.Ms[c]? = some M ∧ cA ∈ M.ctors ∧
      Nonempty (ClassCtorRun mode F (mkFEnv envC).env p (cvTas.map (·.type)) R.rd R.Ms c cA x) := by
  obtain ⟨hlen, hall⟩ := classesCtors_run R.hctors
  by_cases hc : c < R.Ms.length
  · obtain ⟨xs, hxs, hrun⟩ := hall c _ (List.getElem?_eq_getElem hc)
    rw [List.getD_eq_getElem?_getD, hxs, Option.getD_some] at hx
    rw [Nat.zero_add] at hrun
    obtain ⟨hl, hall'⟩ := classCtorsOf_run hrun
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨x', hx', hR⟩ := hall' j _ (List.getElem?_eq_getElem (show j < R.Ms[c].ctors.length by
      omega))
    rw [List.getElem?_eq_getElem hj] at hx'
    obtain rfl := Option.some.inj hx'
    exact ⟨_, _, List.getElem?_eq_getElem hc, List.getElem_mem _, hR⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hx
    exact nomatch hx

/-- A class of the run (checked, with its table entries), at its index:
the scoping facts of the major it was checked as. -/
theorem genRun_cls
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henvC : EnvWF envC) (hT : ∀ cv ∈ cvTas, ScB 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type) {c : Nat} {M : TargetMajor}
    (hM : R.Ms[c]? = some M) :
    (∀ x ∈ M.ds, ScB p.nP x) ∧ (∀ cA ∈ M.ctors, ScB 0 (targetCtorAt M cA.1)) ∧
      (∀ t, M.member = some t → t < p.memberNames.length) ∧
      (M.member = none → ∃ cv caps, envC.find? M.ind = some (.indInfo cv caps)) ∧
      ∀ e ∈ M.nfs, e ∈ R.st.ctorNfs.toList := by
  obtain ⟨-, hall⟩ := genRun_Ms R
  obtain ⟨M₀, hM₀, hMe, hsub⟩ := hall c M hM
  obtain ⟨hds, -, hctA, hmem, hout⟩ := genRun_Ms₀ R henvC hT hct M₀ (List.mem_of_getElem? hM₀)
  rw [hMe]
  exact ⟨hds, hctA, hmem, hout, by rw [← hMe]; exact hsub⟩

/-- **The generated stage's generator inputs are scoped** (`ClassGenScoped`,
see the module docstring) — the hypothesis `hg` of `recStage_of_gen` and
of the family premise, from the run and:

* `henv₁`/`henvC`: the formers' and the constructors' environments well
  formed (`EnvWF`, the install's invariant);
* `hT`/`hct`: the stream's formers and constructors closed (checked
  constants, `checkConstantVal_typeWF`);
* `hTlen`: a former per member (the formers' pass);
* `hpos`: the positivity stage's final state scoped
  (`checkBlockPositivity_nfScoped`). -/
theorem genScoped_of_run
    (R : GenRecRun mode F (mkFEnv env₁) env₁ (mkFEnv envC) p nestedBit pos cvTas block ctorsAs out)
    (henv₁ : EnvWF env₁) (henvC : EnvWF envC)
    (hT : ∀ cv ∈ cvTas, ScB 0 cv.type) (hTlen : p.memberNames.length ≤ cvTas.length)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, ScB 0 c.1.type)
    (hpos : NfStScoped p.nP pos) :
    ClassGenScoped R.g := by
  obtain ⟨hlP, hP⟩ := genRun_params R hT
  have htbl := genRun_tbl_scoped R henv₁ henvC hT hct hpos
  have hcls := fun {c} {M} (hM : R.Ms[c]? = some M) => genRun_cls R henvC hT hct hM
  refine ⟨hlP, hP, ?ds, ?former, ?tyN, ?tyD, ?order, ?pre⟩
  case ds =>
    intro c e he
    show ScB p.nP e
    change e ∈ (R.Ms.getD c default).ds at he
    rw [List.getD_eq_getElem?_getD] at he
    cases hM : R.Ms[c]? with
    | none => rw [hM] at he; exact nomatch he
    | some M => rw [hM] at he; exact (hcls hM).1 e he
  case former =>
    intro c hc
    change c < R.Ms.length at hc
    change ScB 0 (R.formerTysC.getD c default)
    obtain ⟨hlF, hallF⟩ := except_mapM_getElem? R.hformer
    obtain ⟨b, hb, hrun⟩ := hallF c _ (List.getElem?_eq_getElem hc)
    rw [List.getD_eq_getElem?_getD, hb, Option.getD_some]
    obtain ⟨-, -, hmem, hout, -⟩ := hcls (List.getElem?_eq_getElem hc)
    unfold classFormerTy at hrun
    split at hrun
    · rename_i t ht
      simp only [pure, Except.pure, Except.ok.injEq] at hrun
      subst hrun
      have htl : t < cvTas.length := Nat.lt_of_lt_of_le (hmem t ht) hTlen
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
      exact hT _ (List.getElem_mem htl)
    · rename_i hn
      split at hrun
      · rename_i cv caps hf
        simp only [pure, Except.pure, Except.ok.injEq] at hrun
        subst hrun
        rw [mkFEnv_find?_fun] at hf
        have hw := henvC _ (List.mem_of_find?_eq_some hf)
        refine ScB.of_closed ?_ ?_ 0
        · rw [Expr.hasFvar_instantiateLevelParams]; exact hw.1
        · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hw.2.2.2.1
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  case tyN =>
    intro c x hx
    change ScB p.nP x.tyN
    obtain ⟨M, cA, hM, -, ⟨Q⟩⟩ := genRun_ctor R hx
    have hty : x.tyN = Q.e0.ty := congrArg ClassCtor.tyN Q.hx
    rw [hty]
    have he0 : Q.e0 ∈ Q.E := List.mem_of_mem_head? Q.he0
    rw [Q.hE, List.getD_eq_getElem?_getD, hM, Option.getD_some] at he0
    exact htbl _ ((hcls hM).2.2.2.2 _ (List.mem_filter.mp he0).1)
  case tyD =>
    intro c x hx
    change ScB p.nP x.tyD
    obtain ⟨M, cA, hM, hcA, ⟨Q⟩⟩ := genRun_ctor R hx
    have hD := Q.hD
    rw [List.getD_eq_getElem?_getD, hM, Option.getD_some] at hD
    obtain ⟨hds, hctA, -⟩ := hcls hM
    exact ScB.of_instPisWith hD ((hctA cA hcA).mono (Nat.zero_le _)) hds
  case order =>
    intro s c C ihs hs
    change R.rd.slots[s]? = some (.minor c C ihs) at hs
    obtain ⟨hc, hq⟩ := classRead_order R.hrd s c C ihs hs
    refine ⟨hc, fun x hx hxC t tele ht => ?_⟩
    obtain ⟨M, cA, -, -, ⟨Q⟩⟩ := genRun_ctor R hx
    have hcv : x.cv = cA.1 := congrArg ClassCtor.cv Q.hx
    have hkinds := Q.hkinds
    have hslot := Q.hslot
    rw [← hcv, hxC] at hslot hkinds
    obtain ⟨-, rfl⟩ := classMinorSlot_unique hslot s ihs hs
    obtain ⟨f, hf⟩ := classFieldsOf_rec 0 Q.fvs x.kinds hkinds t tele ht
    exact hq (f, t) hf
  case pre =>
    exact R.hpre

end Run

end ConLeche
