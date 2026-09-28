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

theorem sameF_of_stageCohF {cls : List ClassInfo} {F : Expr → Bool} {H : Nat} {τ : Nat → V}
    (h : StageCohF V acval env φ cls F H τ) : SameF V cls F H τ := h.2

set_option maxHeartbeats 8000000 in
/-- **P1 at locally coherent values**: for related spellings `p`, `q`,
the class abstraction of `p` and the `F`-restricted abstraction of `q`
read alike at every locally coherent valuation — every class outside `F`
read as its key with the classes of `F` abstracted (`StageCohF`).  With
the `some` mode's version. -/
theorem classAbs_read_stageF_both
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {F : Expr → Bool}
    (hkf : KeysFOk acval env φ cls F H) (hF : FClosed cls F) :
    ∀ (N : Nat) (q p : Expr), sizeOf q < N → Expr.eqUpToLevels p q = true →
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCohF V acval env φ cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (classOcc? cls) none p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0))) ∧
      (∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCohF V acval env φ cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (classOcc? cls) (some (h, n)) p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h' then classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q
              else classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList
                as1 0))) := by
  intro N
  induction N with
  | zero => intro q p hN; omega
  | succ N ihN =>
  intro q p hN hpq
  have hsome : ∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) →
      ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V (StageCohF V acval env φ cls F H) d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (classOcc? cls) (some (h, n)) p).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((if F h' then classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q
            else classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0)) := by
    intro h n h' hp hq d as2 as1 h2 h1
    obtain ⟨h'', hq', c, hc, c', hc', hch, hch', hsk, hmp, hmq, hnq⟩ := classOcc_both hwf hpq hp
    rw [hq] at hq'
    obtain rfl : h' = h'' := by simp at hq'; exact hq'
    have hchs : c.hole.isSome := by rw [hch]; rfl
    obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c hc h hch
    obtain ⟨i', ty', rfl, hi'⟩ := hwf.hole c' hc' h' hch'
    have hFF : F (.fvar i ty) = F (.fvar i' ty') := hF c hc c' hc' _ _ hch hch' hsk
    rcases n with _ | n
    · -- a head part
      simp only [classAbsSpec]
      cases hFq : F (.fvar i' ty') with
      | true =>
        simp only [if_true, Expr.instantiateList, denoteMeta_fvar, OptAgree]
        intro vals τ hvl hτ
        rw [interp_hole_read hi vals τ hvl, interp_hole_read hi' vals τ hvl]
        exact hτ.2 c hc c' hc' i ty i' ty' hch hch' (hFF.trans hFq) hsk
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have hFp : F (.fvar i ty) = false := hFF.trans hFq
        obtain ⟨us', hfn, hlv, hle, hps⟩ := hmq
        have hlen : q.getAppArgs.length = c.nPc := by omega
        have hqe : q = Expr.mkAppN (.const c.key.ind us') q.getAppArgs := by
          rw [← hfn]; exact (Expr.mkAppN_getAppFn_getAppArgs q).symm
        have hdesc : classAbsSpec (occRestrict (classOcc? cls) F) none q
            = Expr.mkAppN (.const c.key.ind us')
                (q.getAppArgs.map (classAbsSpec (occRestrict (classOcc? cls) F) none)) := by
          conv => lhs; rw [hqe]
          rw [classAbsSpec_spine _ q.getAppArgs (.const c.key.ind us') (fun j hj1 hj => ?_)]
          · simp [classAbsSpec]
          · rcases Nat.lt_or_ge j q.getAppArgs.length with hjl | hjl
            · apply occRestrict_eq_none
              apply classOcc_short hwf hc hchs (us := us')
              · rw [Expr.getAppFn_mkAppN']; rfl
              · rw [Expr.getAppArgs_mkAppN']
                simp only [Expr.getAppArgs, List.nil_append, List.length_take]
                omega
            · have hj' : j = q.getAppArgs.length := by omega
              rw [hj', List.take_length, ← hqe]
              exact occRestrict_eq_none_of hq hFq
        rw [hdesc]
        have hK := hkf c hc hchs (by rw [hch]; exact hFp)
        rw [show (Expr.fvar i ty).instantiateList as2 0 = .fvar i ty from by
          simp [Expr.instantiateList]]
        refine optAgree_trans (hole_agree_lift (V := V) (Good := StageCohF V acval env φ cls F H)
          (d := d) (as1 := as2) hacl hi ty hK.1 hK.2.1
          (Expr.SemEq.refl _) hK.2.2
          (fun τ (hτ : StageCohF V acval env φ cls F H τ) a ha => hτ.1 c hc i ty hch hFp a ha)) ?_
        unfold classKeyF
        rw [Expr.instantiateList_mkAppN', Expr.instantiateList_mkAppN']
        have hdl : c.dsA.length = c.nPc := hwf.len c hc hchs
        have hqa : q.getAppArgs.take c.nPc = q.getAppArgs := List.take_of_length_le (by omega)
        rw [hqa] at hps
        apply optAgree_mkAppN
        · simp only [List.length_map]
          omega
        · simp only [Expr.instantiateList]
          rw [denoteMeta_semEq (show Expr.SemEq (.const c.key.ind c.key.lvls)
            (.const c.key.ind us') from ⟨rfl, (Level.evalEqList_of_canon hlv.symm).1,
              (Level.evalEqList_of_canon hlv.symm).2⟩)]
          exact optAgree_refl' (V := V) _
        · intro k a2 a1 ha2 ha1
          simp only [List.getElem?_map, Option.map_eq_some_iff] at ha2 ha1
          obtain ⟨b2, hb2, rfl⟩ := ha2
          obtain ⟨x2', hx2', rfl⟩ := ha1
          obtain ⟨x2, hx2, rfl⟩ := hx2'
          obtain ⟨y2, hy2, rfl⟩ := hb2
          have hR : Expr.eqUpToLevels y2 x2 = true := Expr.eqUpToLevels_symm (hps.2 k x2 y2 hx2 hy2)
          have hrel := (classAbsF_read_rel (V := V) (acval := acval) (env := env) (φ := φ) hwf hF
            (sizeOf x2 + 1) x2 y2 (by omega) hR).1 d as2 as1 h2 h1
          unfold classAbsF
          exact optAgree_mono' (fun τ hτ => sameF_of_stageCohF hτ) hrel
    · -- one more index argument
      obtain ⟨pf, pa, rfl, hpf⟩ := classOcc_app hwf hp
      obtain ⟨qf, qa, rfl, hqf⟩ := classOcc_app hwf hq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      have hsf := (ihN qf pf (by simp at hN; omega) hpq.1).2 _ n _ hpf hqf d as2 as1
        h2 h1
      have hsa := (ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1
      cases hFq : F (.fvar i' ty') with
      | true =>
        simp only [hFq, if_true] at hsf ⊢
        simp only [classAbsSpec, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app hsf hsa
      | false =>
        simp only [hFq, Bool.false_eq_true, if_false] at hsf ⊢
        have hR : occRestrict (classOcc? cls) F (.app qf qa) = none := occRestrict_eq_none_of hq hFq
        simp only [classAbsSpec, hR, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app hsf hsa
  refine ⟨fun d as2 as1 h2 h1 => ?_, hsome⟩
  cases q with
  | app qf qa =>
    cases p with
    | app pf pa =>
      have hpq0 := hpq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      cases hp : classOcc? cls (.app pf pa) with
      | none =>
        have hq : classOcc? cls (.app qf qa) = none := classOcc_none_of hwf hpq0 hp
        have hR : occRestrict (classOcc? cls) F (.app qf qa) = none := occRestrict_eq_none hq
        simp only [classAbsSpec, hp, hR, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app ((ihN qf pf (by simp at hN; omega) hpq.1).1 d as2 as1 h2 h1)
          ((ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1)
      | some r =>
        obtain ⟨h, n⟩ := r
        obtain ⟨h', hq, -⟩ := classOcc_both hwf hpq0 hp
        have hs := hsome h n h' hp hq d as2 as1 h2 h1
        have hL : classAbsSpec (classOcc? cls) none (.app pf pa)
            = classAbsSpec (classOcc? cls) (some (h, n)) (.app pf pa) := by
          rcases n with _ | n <;> simp [classAbsSpec, hp]
        rw [hL]
        cases hF' : F h' with
        | true =>
          have hR : occRestrict (classOcc? cls) F (.app qf qa) = some (h', n) :=
            occRestrict_eq_some_of hq hF'
          have hL' : classAbsSpec (occRestrict (classOcc? cls) F) none (.app qf qa)
              = classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) (.app qf qa) := by
            rcases n with _ | n <;> simp [classAbsSpec, hR]
          rw [hL']
          simpa [hF'] using hs
        | false => simpa [hF'] using hs
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
        ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB' := (ihN qb pb (by simp at hN; omega) hB).1 (d + 1) _ _
      (h2.cons ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB'
    revert hB'
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (classOcc? cls) none pb).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0)
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
    cases denoteMeta acval env φ (H + d) ((classAbsSpec (classOcc? cls) none px).instantiateList as2 0)
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

/-- **P1 at locally coherent values**: the class abstraction reads as its
restriction to the holes `F`. -/
theorem classAbs_read_stageF
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {F : Expr → Bool}
    (hkf : KeysFOk acval env φ cls F H) (hF : FClosed cls F) (e : Expr)
    {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (StageCohF V acval env φ cls F H) d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) := by
  rw [classAbs_eq_spec]
  exact (classAbs_read_stageF_both hacl hwf hkf hF (sizeOf e + 1) e e (by omega)
    (Expr.eqUpToLevels_refl e)).1 d as2 as1 h2 h1

section Alias

open ConLeche (ClassAlias aliasOcc? classAbsGo)

/-- **The defeq tier reads as its input at locally coherent values**, when
it keeps no stage hole: an alias hole reads its target's `F`-key, which
its target's hole-form key reads as (`classAbs_read_stageF`), which the
replaced occurrence reads as (`AliasKeySem`). -/
theorem aliasAbs_read_stageF
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {al : List ClassAlias} {H : Nat} (hwfc : ClassOccWF cls H)
    (hwf : AliasWF al H) (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (hhk : HoleKeysOk acval env φ cls H) {F : Expr → Bool} (hkf : KeysFOk acval env φ cls F H)
    (hFc : FClosed cls F) (hF : ∀ a ∈ al, F a.hole = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V acval env φ cls F H τ)
    (hsem : AliasKeySem V acval env φ cls al H Good)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} e).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hnone : occRestrict (aliasOcc? al) F = fun _ => none := by
    funext x
    unfold occRestrict
    split
    · rename_i h n hx
      obtain ⟨a, ha, rfl, -⟩ := aliasOcc_spec hx
      simp [hF a ha]
    · rfl
  have h := aliasAbs_read_hole (V := V) (acval := acval) (env := env) (φ := φ) hwf (F := F)
    (Good := Good) (fun x h hx _ d' as2' as1' _ _ => ?_) e h2 h1
  · rwa [hnone, classAbsSpec_none] at h
  · rw [hnone, classAbsSpec_none]
    obtain ⟨a, ha, rfl, us, hfn, hle, hn, hlv, hps⟩ := aliasOcc_spec hx
    obtain ⟨i, ty, hi, hiH⟩ := hwf.hole a ha
    obtain ⟨ci, hci, hch, hkey⟩ := hsem a ha
    have hsem' : Expr.SemEq x (aliasKey a) := by
      have hlen : x.getAppArgs.length = a.nPc := by omega
      have hx' : x = Expr.mkAppN (.const a.ind us) (x.getAppArgs.take a.nPc) := by
        rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs]
      rw [hx']
      unfold aliasKey
      have hlvl := Level.evalEqList_of_isEquivList hlv
      have hps' : (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys
          = a.ps.map Expr.eraseFVarTys := by
        rw [hps, ← hps, List.map_map]
        apply List.map_congr_left
        intro p _
        exact (Expr.eraseFVarTys_idem p).symm
      obtain ⟨hl, hpw⟩ := semEq_of_map_erase hps'
      exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl hpw
    rw [hi]
    refine hole_agree_lift hacl hiH ty (hwf.keyScoped a ha).1 (hwf.keyScoped a ha).2 hsem'
      (hden a ha) (fun τ hτ r hr => ?_)
    have hchs : ci.hole.isSome := by rw [hch]; rfl
    have hFci : F (ci.hole.getD default) = false := by rw [hch]; exact hF a ha
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (hhk ci hci hchs).2.2
    obtain ⟨rF, hrF⟩ := Option.isSome_iff_exists.mp (hkf ci hci hchs hFci).2.2
    have hτF := hG τ hτ
    -- the hole-form key reads as the `F`-key at a locally coherent valuation
    have hkk : interp V τ r' = interp V τ rF := by
      have hag : OptAgree (ValAgree V (StageCohF V acval env φ cls F H) 0)
          (denoteMeta acval env φ H (holeKey cls ci)) (denoteMeta acval env φ H (classKeyF cls F ci)) := by
        unfold holeKey classKeyF ConLeche.ClassInfo.holeForm
        apply optAgree_mkAppN _ _ (by simp) (optAgree_refl' (V := V) _)
        intro k a2 a1 ha2 ha1
        simp only [List.getElem?_map, Option.map_eq_some_iff] at ha2 ha1
        obtain ⟨b2, hb2, rfl⟩ := ha2
        obtain ⟨b1, hb1, rfl⟩ := ha1
        obtain rfl : b1 = b2 := Option.some.inj (hb1.symm.trans hb2)
        have := classAbs_read_stageF (V := V) hacl hwfc hkf hFc b1 (LocList.nil H) (LocList.nil H)
        simpa [Expr.instantiateList_nil] using this
      rw [hr', hrF] at hag
      have := hag [] τ rfl hτF
      simpa [consList_nil] using this
    rw [hi] at hch
    rw [hτF.1 ci hci i ty hch (by rw [← hi]; exact hF a ha) rF hrF, ← hkk,
      hkey τ hτ r r' hr hr']

/-- **A crest's whole abstraction, read at locally coherent values**: the
syntactic tier, then a defeq tier keeping no stage hole, reads as the
syntactic tier restricted to the stage holes `F`. -/
theorem crestAbs_read_stageF
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) (hhk : HoleKeysOk acval env φ cls H)
    {F : Expr → Bool} (hkf : KeysFOk acval env φ cls F H) (hFc : FClosed cls F)
    {al : List ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, F a.hole = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V acval env φ cls F H τ)
    (hsem : AliasKeySem V acval env φ cls al H Good)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} (classAbs cls e)).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) :=
  optAgree_trans (aliasAbs_read_stageF hacl hwf hawf hden hhk hkf hFc hF hG hsem (classAbs cls e) h2 h1)
    (optAgree_mono' hG (classAbs_read_stageF hacl hwf hkf hFc e h1 h1))

end Alias

end ConLeche.Model
