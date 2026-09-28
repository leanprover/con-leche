module

public import ConLeche.Model.Inductives.ClassStage

public section

/-!
# The stage coherence, LOCAL form (P2d, DESIGN CLASSCHECK / P2D3)

`StageCoh` (`ClassSubst.lean` §7) reads a class outside the stage holes
`F` as its key in HOLE FORM — every class inside the key abstracted, so
the coherent value of a class depends on the coherent values of the
classes inside its key, recursively.  A class fact's valuation is built
the other way round: a coherent class's hole holds its container's
carrier at its key read with only the STAGE classes abstracted
(`classKeyF`) — a function of the stage holes alone, no recursion over
keys.  This file is the reading at such valuations (`StageCohF`):

* `classAbsF_read_rel` — the restriction to `F` reads two related
  spellings (`eqUpToLevels`) alike, wherever classes the same up to
  spelling carry one stage value;
* `classAbs_read_stageF` — the class abstraction reads as its
  restriction to `F` at every locally coherent valuation (P1, the head
  obligation discharged by `classAbsF_read_rel` at the key).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo classOcc? classAbs)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- A class's key with only the classes `F` keeps abstracted. -/
@[expose] def classKeyF (cls : List ClassInfo) (F : Expr → Bool) (c : ClassInfo) : Expr :=
  Expr.mkAppN (.const c.key.ind c.key.lvls) (c.dsA.map (classAbsF cls F))

/-- Classes in `F` the same up to spelling carry one value. -/
@[expose] def SameF (V : Type w) [SetTheory V] (cls : List ClassInfo) (F : Expr → Bool) (H : Nat)
    (τ : Nat → V) : Prop :=
  ∀ c ∈ cls, ∀ c' ∈ cls, ∀ i ty i' ty', c.hole = some (.fvar i ty) →
    c'.hole = some (.fvar i' ty') → F (.fvar i ty) = true → SameKey c c' →
    τ (H - 1 - i) = τ (H - 1 - i')

/-- **The local stage coherence**: a class outside `F` reads as its key
with only the classes in `F` abstracted; classes in `F` the same up to
spelling carry one value. -/
@[expose] def StageCohF (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (F : Expr → Bool) (H : Nat)
    (τ : Nat → V) : Prop :=
  (∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → F (.fvar i ty) = false → ∀ a,
      denoteMeta acval env φ H (classKeyF cls F c) = some a → τ (H - 1 - i) = interp V τ a) ∧
  SameF V cls F H τ

/-- The `F`-keys are frame-scoped, closed, and read. -/
@[expose] def KeysFOk (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (cls : List ClassInfo) (F : Expr → Bool) (H : Nat) : Prop :=
  ∀ c ∈ cls, c.hole.isSome → F (c.hole.getD default) = false →
    Expr.fvarsBelow H (classKeyF cls F c) ∧ (classKeyF cls F c).looseBVarsBounded 0 = true ∧
    (denoteMeta acval env φ H (classKeyF cls F c)).isSome

theorem optAgree_mono' {Good Good' : (Nat → V) → Prop} (hG : ∀ τ, Good τ → Good' τ) {d : Nat}
    {o2 o1 : Option AnnotTerm} (h : OptAgree (ValAgree V Good' d) o2 o1) :
    OptAgree (ValAgree V Good d) o2 o1 := by
  cases o2 <;> cases o1 <;> simp_all [OptAgree]
  intro vals τ hvl hτ
  exact h vals τ hvl (hG τ hτ)

set_option maxHeartbeats 8000000 in
/-- **The restriction reads related spellings alike**: for `p`, `q` the
same up to levels, the abstractions restricted to `F` read alike at every
valuation giving the classes of `F` one value per class up to spelling —
with the `some` mode's version. -/
theorem classAbsF_read_rel {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    {F : Expr → Bool} (hF : FClosed cls F) :
    ∀ (N : Nat) (q p : Expr), sizeOf q < N → Expr.eqUpToLevels p q = true →
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (SameF V cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0))) ∧
      (∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) → F h = true →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (SameF V cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) (some (h, n)) p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q).instantiateList
              as1 0))) := by
  intro N
  induction N with
  | zero => intro q p hN; omega
  | succ N ihN =>
  intro q p hN hpq
  have hsome : ∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) →
      F h = true → ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V (SameF V cls F H) d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (occRestrict (classOcc? cls) F) (some (h, n)) p).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q).instantiateList
            as1 0)) := by
    intro h n h' hp hq hFh d as2 as1 h2 h1
    obtain ⟨h'', hq', c, hc, c', hc', hch, hch', hsk, -, -, -⟩ := classOcc_both hwf hpq hp
    rw [hq] at hq'
    obtain rfl : h' = h'' := by simp at hq'; exact hq'
    obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c hc h hch
    obtain ⟨i', ty', rfl, hi'⟩ := hwf.hole c' hc' h' hch'
    rcases n with _ | n
    · simp only [classAbsSpec, Expr.instantiateList, denoteMeta_fvar, OptAgree]
      intro vals τ hvl hτ
      rw [interp_hole_read hi vals τ hvl, interp_hole_read hi' vals τ hvl]
      exact hτ c hc c' hc' i ty i' ty' hch hch' hFh hsk
    · obtain ⟨pf, pa, rfl, hpf⟩ := classOcc_app hwf hp
      obtain ⟨qf, qa, rfl, hqf⟩ := classOcc_app hwf hq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      have hsf := (ihN qf pf (by simp at hN; omega) hpq.1).2 _ n _ hpf hqf hFh d as2 as1 h2 h1
      have hsa := (ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1
      simp only [classAbsSpec, Expr.instantiateList, denoteMeta_app]
      exact optAgree_app hsf hsa
  refine ⟨fun d as2 as1 h2 h1 => ?_, hsome⟩
  cases q with
  | app qf qa =>
    cases p with
    | app pf pa =>
      have hpq0 := hpq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      have hdesc : OptAgree (ValAgree V (SameF V cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((Expr.app (classAbsSpec (occRestrict (classOcc? cls) F) none pf)
              (classAbsSpec (occRestrict (classOcc? cls) F) none pa)).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((Expr.app (classAbsSpec (occRestrict (classOcc? cls) F) none qf)
              (classAbsSpec (occRestrict (classOcc? cls) F) none qa)).instantiateList as1 0)) := by
        simp only [Expr.instantiateList, denoteMeta_app]
        exact optAgree_app ((ihN qf pf (by simp at hN; omega) hpq.1).1 d as2 as1 h2 h1)
          ((ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1)
      cases hp : classOcc? cls (.app pf pa) with
      | none =>
        have hq : classOcc? cls (.app qf qa) = none := classOcc_none_of hwf hpq0 hp
        have hR : occRestrict (classOcc? cls) F (.app qf qa) = none := occRestrict_eq_none hq
        have hR' : occRestrict (classOcc? cls) F (.app pf pa) = none := occRestrict_eq_none hp
        simp only [classAbsSpec, hR, hR']
        exact hdesc
      | some r =>
        obtain ⟨h, n⟩ := r
        obtain ⟨h', hq, c, hc, c', hc', hch, hch', hsk, -, -, -⟩ := classOcc_both hwf hpq0 hp
        have hFF : F h = F h' := hF c hc c' hc' _ _ hch hch' hsk
        cases hFh : F h with
        | true =>
          have hR' : occRestrict (classOcc? cls) F (.app pf pa) = some (h, n) :=
            occRestrict_eq_some_of hp hFh
          have hR : occRestrict (classOcc? cls) F (.app qf qa) = some (h', n) :=
            occRestrict_eq_some_of hq (hFF ▸ hFh)
          have hs := hsome h n h' hp hq hFh d as2 as1 h2 h1
          have hL : classAbsSpec (occRestrict (classOcc? cls) F) none (.app pf pa)
              = classAbsSpec (occRestrict (classOcc? cls) F) (some (h, n)) (.app pf pa) := by
            rcases n with _ | n <;> simp [classAbsSpec, hR']
          have hL' : classAbsSpec (occRestrict (classOcc? cls) F) none (.app qf qa)
              = classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) (.app qf qa) := by
            rcases n with _ | n <;> simp [classAbsSpec, hR]
          rw [hL, hL']
          exact hs
        | false =>
          have hR' : occRestrict (classOcc? cls) F (.app pf pa) = none :=
            occRestrict_eq_none_of hp hFh
          have hR : occRestrict (classOcc? cls) F (.app qf qa) = none :=
            occRestrict_eq_none_of hq (hFF ▸ hFh)
          simp only [classAbsSpec, hR, hR']
          exact hdesc
    | _ => simp [Expr.eqUpToLevels] at hpq
  | lam qt qb qm | forallE qt qb qm =>
    cases p <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hpq
    rename_i pt pb pm
    obtain ⟨⟨rfl, hT⟩, hB⟩ := hpq
    have hTa := (ihN qt pt (by simp at hN; omega) hT).1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList]
    first
    | rw [denoteMeta_lam, denoteMeta_lam]
    | rw [denoteMeta_forallE, denoteMeta_forallE]
    revert hTa
    cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none pt).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB' := (ihN qb pb (by simp at hN; omega) hB).1 (d + 1) _ _
      (h2.cons ((classAbsSpec (occRestrict (classOcc? cls) F) none pt).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB'
    revert hB'
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none pb).instantiateList
          (Expr.fvar (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none pt).instantiateList as2 0)
            :: as2) 0)
      <;> cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qb).instantiateList
          (Expr.fvar (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
            :: as1) 0)
      <;> simp [OptAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2
        = interp V (cons x (consList vals τ)) b1 := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    first
    | (simp only [interp_lam, hA vals τ hvl hτ]; exact lamR_congr fun x _ => hbx x)
    | (simp only [interp_pi, hA vals τ hvl hτ]; exact piR_congr fun x _ => hbx x)
  | proj sn si qx =>
    cases p <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hpq
    rename_i ps pi px
    obtain ⟨⟨hs, hi⟩, hX⟩ := hpq
    subst hs hi
    have hXa := (ihN qx px (by simp at hN; omega) hX).1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList, denoteMeta_proj]
    revert hXa
    cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none px).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qx).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? ps pi with
    | some entry =>
      intro vals τ hvl hτ
      exact interp_projAV_congr _ (he vals τ hvl hτ)
    | none =>
      rcases pi with _ | _ | pi
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · simp [AnnotTerm.projPair?]
  | letE qt qv qb =>
    cases p <;> simp only [Expr.eqUpToLevels, reduceCtorEq] at hpq
    simp only [classAbsSpec, Expr.instantiateList]
    rw [denoteMeta, denoteMeta]
    trivial
  | _ =>
    have hsem := Expr.semEq_of_eqUpToLevels hpq
    rw [classAbsSpec_none_atom _ (by intro f a h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t b m h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t b m h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t v b h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro s i x h; subst h; simp [Expr.eqUpToLevels] at hpq),
      classAbsSpec_none_atom _ (by intro f a h; cases h) (by intro t b m h; cases h)
        (by intro t b m h; cases h) (by intro t v b h; cases h) (by intro s i x h; cases h),
      denoteMeta_semEq (semEq_instantiateList_loc h2 h1 _ _ 0 hsem)]
    exact optAgree_refl' (V := V) _

end ConLeche.Model
