module

public import ConLeche.Model.Inductives.ClassStageF

public section

/-!
# P1 between two restrictions (P2d, DESIGN CLASSCHECK / P2D4)

`classAbs_read_stageF` compares the FULL class abstraction with its
restriction to the stage holes `F`.  A coherent class `d`, read by a
container class `c`, is read with `c`'s stage classes abstracted (`c`'s
view) where `d`'s own fact abstracts `d`'s stage classes: two
RESTRICTIONS `F ⊆ F1`.  They read alike at every valuation holding every
class of `F1` outside `F` at its key with the classes of `F` abstracted
(`StageCohFR`), and the classes of `F` the same up to spelling at one
value — the P1 induction with the left recogniser restricted too
(`classAbsF_read_restrict`).
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

/-- **Coherence between two restrictions**: a class kept by `F1` but not
by `F` reads as its key with the classes of `F` abstracted; classes of
`F` the same up to spelling carry one value. -/
@[expose] def StageCohFR (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (F1 F : Expr → Bool) (H : Nat)
    (τ : Nat → V) : Prop :=
  (∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → F1 (.fvar i ty) = true →
      F (.fvar i ty) = false → ∀ a,
      denoteMeta acval env φ H (classKeyF cls F c) = some a → τ (H - 1 - i) = interp V τ a) ∧
  SameF V cls F H τ

set_option maxHeartbeats 8000000 in
/-- **P1 between two restrictions**, at related spellings `p`, `q`: the
`F1`-restricted abstraction of `p` and the `F`-restricted abstraction of
`q` read alike at every valuation coherent between them
(`StageCohFR`).  With the `some` mode's version. -/
theorem classAbsF_read_restrict_both
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {F F1 : Expr → Bool}
    (hkf : KeysFOk acval env φ cls F H) (hF : FClosed cls F) (hF1 : FClosed cls F1)
    (hsub : ∀ h, F h = true → F1 h = true) :
    ∀ (N : Nat) (q p : Expr), sizeOf q < N → Expr.eqUpToLevels p q = true →
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCohFR V acval env φ cls F1 F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F1) none p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0))) ∧
      (∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) → F1 h = true →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCohFR V acval env φ cls F1 F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F1) (some (h, n)) p).instantiateList as2 0))
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
      F1 h = true →
      ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V (StageCohFR V acval env φ cls F1 F H) d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (occRestrict (classOcc? cls) F1) (some (h, n)) p).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((if F h' then classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q
            else classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0)) := by
    intro h n h' hp hq hF1h d as2 as1 h2 h1
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
        refine optAgree_trans (hole_agree_lift (V := V) (Good := StageCohFR V acval env φ cls F1 F H)
          (d := d) (as1 := as2) hacl hi ty hK.1 hK.2.1
          (Expr.SemEq.refl _) hK.2.2
          (fun τ (hτ : StageCohFR V acval env φ cls F1 F H τ) a ha => hτ.1 c hc i ty hch hF1h hFp a ha)) ?_
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
          exact optAgree_mono' (fun τ hτ => hτ.2) hrel
    · -- one more index argument
      obtain ⟨pf, pa, rfl, hpf⟩ := classOcc_app hwf hp
      obtain ⟨qf, qa, rfl, hqf⟩ := classOcc_app hwf hq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      have hsf := (ihN qf pf (by simp at hN; omega) hpq.1).2 _ n _ hpf hqf hF1h d as2 as1
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
        have hR1 : occRestrict (classOcc? cls) F1 (.app pf pa) = none := occRestrict_eq_none hp
        simp only [classAbsSpec, hR1, hR, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app ((ihN qf pf (by simp at hN; omega) hpq.1).1 d as2 as1 h2 h1)
          ((ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1)
      | some r =>
        obtain ⟨h, n⟩ := r
        obtain ⟨h', hq, c, hc, c', hc', hch, hch', hsk, -⟩ := classOcc_both hwf hpq0 hp
        cases hF1h : F1 h with
        | false =>
          have hF1' : F1 h' = false := by rw [← hF1 c hc c' hc' _ _ hch hch' hsk]; exact hF1h
          have hFh' : F h' = false := by
            cases hx : F h' with
            | false => rfl
            | true => rw [hsub h' hx] at hF1'; exact absurd hF1' (by simp)
          have hR1 : occRestrict (classOcc? cls) F1 (.app pf pa) = none :=
            occRestrict_eq_none_of hp hF1h
          have hR : occRestrict (classOcc? cls) F (.app qf qa) = none :=
            occRestrict_eq_none_of hq hFh'
          simp only [classAbsSpec, hR1, hR, Expr.instantiateList, denoteMeta_app]
          exact optAgree_app ((ihN qf pf (by simp at hN; omega) hpq.1).1 d as2 as1 h2 h1)
            ((ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1)
        | true =>
        have hs := hsome h n h' hp hq hF1h d as2 as1 h2 h1
        have hR1 : occRestrict (classOcc? cls) F1 (.app pf pa) = some (h, n) :=
          occRestrict_eq_some_of hp hF1h
        have hL : classAbsSpec (occRestrict (classOcc? cls) F1) none (.app pf pa)
            = classAbsSpec (occRestrict (classOcc? cls) F1) (some (h, n)) (.app pf pa) := by
          rcases n with _ | n <;> simp [classAbsSpec, hR1]
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
        ((classAbsSpec (occRestrict (classOcc? cls) F1) none pt).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB' := (ihN qb pb (by simp at hN; omega) hB).1 (d + 1) _ _
      (h2.cons ((classAbsSpec (occRestrict (classOcc? cls) F1) none pt).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB'
    revert hB'
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict (classOcc? cls) F1) none pb).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec (occRestrict (classOcc? cls) F1) none pt).instantiateList as2 0)
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
    cases denoteMeta acval env φ (H + d) ((classAbsSpec (occRestrict (classOcc? cls) F1) none px).instantiateList as2 0)
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

/-- **P1 between two restrictions** (see the module docstring). -/
theorem classAbsF_read_restrict
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {F F1 : Expr → Bool}
    (hkf : KeysFOk acval env φ cls F H) (hF : FClosed cls F) (hF1 : FClosed cls F1)
    (hsub : ∀ h, F h = true → F1 h = true) (e : Expr)
    {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (StageCohFR V acval env φ cls F1 F H) d)
      (denoteMeta acval env φ (H + d) ((classAbsF cls F1 e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) := by
  unfold classAbsF
  exact (classAbsF_read_restrict_both hacl hwf hkf hF hF1 hsub (sizeOf e + 1) e e (by omega)
    (Expr.eqUpToLevels_refl e)).1 d as2 as1 h2 h1

end ConLeche.Model
