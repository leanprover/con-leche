module

import ConLeche.Model.Inductives.FixRuleKit
public import ConLeche.Model.Inductives.MutualRecLaw
public section

/-!
# The mutual rule's right-hand side is graded (task #278, M2.2c′)

`ConLeche/Model/Inductives/FixRuleOk.lean`'s `fixRuleOk` at `k`
motives: rule `J`'s right-hand side — the λ-tower over the parameters,
the `k` motives, the `n` minors and constructor `J`'s fields, with the
core `mutualRuleCoreAV` — is `WellDenotedV` at every frame.

The one piece that does NOT transfer from the fixpoint route is the
inductive hypothesis' own facts (`ihAppAVK_facts` below): the ih of a
field targeting member `t` fires member `t`'s recursor leaf and lands
in an ih domain whose motive is member `t`'s, so the membership is read
off THAT member's stored recursor type (`mutualConcAV k n nIdx t`,
whose head is the motive `k - 1 - t` binders up), not off the single
motive of the fixpoint route's conclusion.

Everything else is the fixpoint route's shape at a `k`-motive frame:
the block split of a rule spine (`mutualBlock_split`), the minor's
space and its fold (`interp_minorAVAtRM`, `minorSpI_fold`), the ih
tower's fold (`ihSpL_spine`) and the λ-tower's two walks
(`mkLamsC_wellDenoted`/`mkLamsC_validV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

/-! `frameIdx` is spelled `Semantics.frameIdx` throughout: the plain
name resolves to `FixRecRead`'s frame lemma. -/

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The `k`-motive prefix and conclusion -/

theorem recPrefixBvarsMK_wellDenoted {nP k n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsMK nP k n nF m) : WellDenoted V σ a := by
  unfold recPrefixBvarsMK at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
  · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial

theorem recPrefixBvarsMK_validV {nP k n nF m : Nat} {σ : Nat → V} {a : AnnotTerm}
    (ha : a ∈ recPrefixBvarsMK nP k n nF m) : AnnotValid V σ a := by
  unfold recPrefixBvarsMK at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
  · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial

/-- **Member `mm`'s recursor conclusion, read at a walk frame**: motive
`mm` (the `k` motives sit `n` minors, the index values and the major
below) at the index values and the major (`recConcAV_at` with `k`
motives). -/
theorem mutualConcAV_at {k n nIdx mm : Nat} {ρp : Nat → V} {Ms ms vals : List V} {f : V}
    (hlenK : Ms.length = k) (hlenM : ms.length = n) (hlenV : vals.length = nIdx) (hmm : mm < k) :
    interp V (cons f (consList vals (consList ms (consList Ms ρp)))) (mutualConcAV k n nIdx mm)
      = SetTheory.app (vals.foldl SetTheory.app (Ms.getD mm pt)) f := by
  have hfr : RecFrameS 1 (consList vals (consList ms (consList Ms ρp)))
      (cons f (consList vals (consList ms (consList Ms ρp)))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  unfold mutualConcAV
  rw [interp_app, interp_mkAppN,
    ← List.foldl_map (f := interp V (cons f (consList vals (consList ms (consList Ms ρp)))))
      (g := SetTheory.app),
    map_idxVarsAV_interp hfr, interp_bvar, interp_bvar, cons_zero]
  have hM : cons f (consList vals (consList ms (consList Ms ρp))) (1 + nIdx + n + k - 1 - mm)
      = Ms.getD mm pt := by
    rw [show 1 + nIdx + n + k - 1 - mm = ((n + k - 1 - mm) + vals.length) + 1 from by omega,
      cons_succ, consList_apply_add,
      show n + k - 1 - mm = ms.length + Ms.length - 1 - mm from by omega]
    exact consList_motive_apply (by omega)
  have hI : Semantics.frameIdx nIdx (consList vals (consList ms (consList Ms ρp))) = vals := by
    rw [← hlenV]; exact Semantics.frameIdx_consList' _ _
  rw [hM, hI]

/-! ## One inductive hypothesis at a `k`-motive frame -/

set_option maxHeartbeats 1600000 in
/-- **An inductive hypothesis' facts** at a mutual rule's leaf frame
(the `k`-motive twin of `ihAppAV_facts`): for recursive field `i` of
the rule's constructor, targeting member `tgt`, whose recursor leaf is
`R`, the λ-tower over the field's telescope of `R` at the block
`(p⃗, M⃗, S⃗)`, the field's index values and the field applied to the
telescope's values is graded, bit-valid, and lies in the ih domain —
the nested product over the telescope of **member `tgt`'s** motive at
those index values and that application.

The premises are member `tgt`'s recursor typing (its leaf is graded and
inhabits the reading of its stored type `mkPisAV rds (mutualConcAV k n
nIdxT tgt)`) and, at every spine fitting the field's telescope, the
index expressions' facts, the field's application chain and the spine
fit of `(p⃗, M⃗, S⃗, e⃗_i(a⃗), f_i a⃗)` against that stored type's binder
data. -/
theorem ihAppAVK_facts {ℓ wB b nP k n nF i nIdxT tgt : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {ρ : Nat → V} {as₁ Ms ms as₂ : List V}
    (hlenP : as₁.length = nP) (hlenK : Ms.length = k) (hlenM : ms.length = n)
    (hlenF : as₂.length = nF) (hi : i < nF) (htgt : tgt < k)
    {R : AnnotTerm} (hRcl : Term.bvarsBelow 0 R.erase) (hRok : ∀ σ : Nat → V, WellDenotedV V σ R)
    {rds : List (Nat × Nat × AnnotTerm)} (hrdsZ : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0))
    (hconc0 : ℓ = 0 → ∀ as' : List V, SpineFit ρ (rds.map (·.2.2)) as' →
      interp V (consList as' ρ) (mutualConcAV k n nIdxT tgt) ∈ˢ (univZero : V))
    (hRmem : interp V ρ R ∈ˢ interp V ρ (mkPisAV rds (mutualConcAV k n nIdxT tgt)))
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} (hEisLen : Eis.length = nIdxT)
    (hTOk : FieldsOkB wB (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)))
    (hTV : FieldsValid (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)))
    (hleaves : ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)) bs →
      (∀ E ∈ Eis, WellDenoted V (consList bs (consList (as₂.take i) (consList as₁ ρ))) E) ∧
      (∀ E ∈ Eis, AnnotValid V (consList bs (consList (as₂.take i) (consList as₁ ρ))) E) ∧
      AppChainOk (as₂.getD i pt) bs ∧
      SpineFit ρ (rds.map (·.2.2))
        (as₁ ++ Ms ++ ms ++
          Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))) ++
          [bs.foldl SetTheory.app (as₂.getD i pt)])) :
    WellDenoted V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
        (ihAppAVK R nP k n nF i (rebit b tl) Eis) ∧
      AnnotValid V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
        (ihAppAVK R nP k n nF i (rebit b tl) Eis) ∧
      interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
          (ihAppAVK R nP k n nF i (rebit b tl) Eis)
        ∈ˢ piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)))
          (fun as => SetTheory.app
            ((Eis.map (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
              SetTheory.app (Ms.getD tgt pt))
            (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
  have hk : 0 < k := by omega
  obtain ⟨M0, Mrest, rfl⟩ : ∃ M0 Mrest, Ms = M0 :: Mrest := by
    cases Ms with
    | nil => rw [List.length_nil] at hlenK; omega
    | cons M0 Mrest => exact ⟨M0, Mrest, rfl⟩
  have hlenK' : Mrest.length + 1 = k := by rw [List.length_cons] at hlenK; omega
  have hms : (Mrest ++ ms).length + 1 = n + k := by
    rw [List.length_append, hlenM]; omega
  -- **per telescope spine**: the body's grading, value and validity
  have hbody : ∀ bs : List V,
      SpineFit (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)) bs →
      WellDenoted V
          (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))))
          (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF bs.length ++
            Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)])) ∧
        interp V
            (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))))
            (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF bs.length ++
              Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
              [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)]))
          ∈ˢ SetTheory.app
            ((Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).foldl
              SetTheory.app ((M0 :: Mrest).getD tgt pt))
            (bs.foldl SetTheory.app (as₂.getD i pt)) ∧
        (ℓ = 0 → SetTheory.app
            ((Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).foldl
              SetTheory.app ((M0 :: Mrest).getD tgt pt))
            (bs.foldl SetTheory.app (as₂.getD i pt)) ∈ˢ (univZero : V)) ∧
        AnnotValid V
          (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))))
          (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF bs.length ++
            Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)])) := by
    intro bs hsp
    obtain ⟨hEok, hEV, hchainF, hfit⟩ := hleaves bs hsp
    have hchain := appChainOk_of_mkPisAV' hrdsZ hconc0 hRmem hfit
    have hval := mkPisAV_fold_mem hrdsZ hconc0 hRmem hfit
    -- the conclusion at the spine: member `tgt`'s motive at the values
    have hfrC : consList (as₁ ++ (M0 :: Mrest) ++ ms ++
          Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))) ++
          [bs.foldl SetTheory.app (as₂.getD i pt)]) ρ
        = cons (bs.foldl SetTheory.app (as₂.getD i pt))
            (consList (Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))))
              (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))) := by
      rw [consList_append, consList_append, consList_append, consList_append, consList_cons,
        consList_nil]
    rw [hfrC, mutualConcAV_at hlenK hlenM (by rw [List.length_map, hEisLen]) htgt] at hval
    have hconcZ : ℓ = 0 → SetTheory.app
        ((Eis.map (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ))))).foldl
          SetTheory.app ((M0 :: Mrest).getD tgt pt))
        (bs.foldl SetTheory.app (as₂.getD i pt)) ∈ˢ (univZero : V) := by
      intro h0
      have := hconc0 h0 _ hfit
      rw [hfrC, mutualConcAV_at hlenK hlenM (by rw [List.length_map, hEisLen]) htgt] at this
      exact this
    -- the argument readings
    have hargs := ihAppAVK_args_interp (ρ := ρ) (fs := as₂) (bs := bs) hlenP hlenK hk hlenM hlenF
      hi Eis
    rw [Semantics.frameIdx_consList'] at hargs
    have hRi : interp V
        (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))) R
        = interp V ρ R := interp_closed (V := V) hRcl _ ρ
    have hvars : (teleVarsAV bs.length).map (interp V
        (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))))) = bs :=
      map_fieldBvars_interp rfl _
    have hfld : interp V
        (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ)))))
        (AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length))
        = bs.foldl SetTheory.app (as₂.getD i pt) := by
      rw [interp_mkAppN, interp_bvar, consList_apply_add, consList_apply_lt' as₂ _ (by omega),
        show as₂.length - 1 - (nF - 1 - i) = i from by omega,
        ← List.foldl_map (f := interp V
            (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))))
          (g := SetTheory.app) (l := teleVarsAV bs.length), hvars]
    have hargsOk : ∀ a ∈ recPrefixBvarsMK nP k n nF bs.length ++
        Eis.map (ihIdxAtM nF (n + k) i 0 bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + bs.length)) (teleVarsAV bs.length)],
        WellDenoted V
          (consList bs (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))) a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact recPrefixBvarsMK_wellDenoted ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          have hiff := WellDenoted_ihIdxAtM (o := n + k) (ρp := consList as₁ ρ) (M := M0)
            (ms := Mrest ++ ms) hms (fs := as₂) (ihs := []) hlenF rfl (Nat.le_of_lt hi) bs E
          rw [consList_nil, ← consList_motives_cons] at hiff
          exact hiff.mpr (hEok E hE)
      · rw [List.mem_singleton] at ha; subst ha
        refine (mkAppN_wellDenoted_of_chain (f := .bvar (nF - 1 - i + bs.length))
          (args := teleVarsAV bs.length) trivial (fun a ha => ?_) ?_).1
        · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
        · rw [interp_bvar, consList_apply_add, consList_apply_lt' as₂ _ (by omega),
            show as₂.length - 1 - (nF - 1 - i) = i from by omega, hvars]
          exact hchainF
    obtain ⟨hok, hv⟩ := mkAppN_wellDenoted_of_chain (hRok _).1 hargsOk
      (by rw [hargs, hRi]; exact hchain)
    refine ⟨hok, by rw [hv, hargs, hRi]; exact hval, hconcZ, ?_⟩
    refine mkAppN_validV (hRok _).2 fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact recPrefixBvarsMK_validV ha
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        have hiff := AnnotValid_ihIdxAtM (o := n + k) (ρp := consList as₁ ρ) (M := M0)
          (ms := Mrest ++ ms) hms (fs := as₂) (ihs := []) hlenF rfl (Nat.le_of_lt hi) bs E
        rw [consList_nil, ← consList_motives_cons] at hiff
        exact hiff.mpr (hEV E hE)
    · rw [List.mem_singleton] at ha; subst ha
      refine mkAppN_validV trivial fun a ha => ?_
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial
  -- **the tower**: the moved telescope's walk and the leaf facts
  have hdom_eq : (ihTeleAtR nF (n + k) i 0 (rebit b tl)).map (·.2.2)
      = (ihTeleAtR nF (n + k) i 0 tl).map (·.2.2) := by
    rw [ihTeleAtR, ihTeleAtR, ihTeleAtGo_rebit, rebit_map_dom]
  have hspIff : ∀ bs : List V,
      SpineFit (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))
          ((ihTeleAtR nF (n + k) i 0 (rebit b tl)).map (·.2.2)) bs ↔
        SpineFit (consList (as₂.take i) (consList as₁ ρ)) (tl.map (·.2.2)) bs := by
    intro bs
    have h := spineFit_ihTeleAtGo (o := n + k) (ρp := consList as₁ ρ) (M := M0)
      (ms := Mrest ++ ms) hms (fs := as₂) (ihs := []) hlenF rfl (Nat.le_of_lt hi) tl [] bs
    simp only [List.length_nil, consList] at h
    rw [← consList_motives_cons] at h
    rw [hdom_eq]
    exact h
  have hwalk : DomsWalk (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))
      (ihTeleAtR nF (n + k) i 0 (rebit b tl)) := by
    refine domsWalk_of_fieldsOkB (w := wB) ?_
    have h := fieldsOkB_ihTeleAtGo (o := n + k) (ρp := consList as₁ ρ) (M := M0)
      (ms := Mrest ++ ms) hms (fs := as₂) (ihs := []) hlenF rfl (Nat.le_of_lt hi) tl [] hTOk
    simp only [List.length_nil, consList] at h
    rw [← consList_motives_cons] at h
    rw [hdom_eq]
    exact h
  have hz : ∀ d ∈ ihTeleAtR nF (n + k) i 0 (rebit b tl), (ℓ = 0 ↔ d.2.1 = 0) := by
    intro d hd
    rw [ihTeleAtR, ihTeleAtGo_rebit] at hd
    rw [mem_rebit hd]; exact hbz
  have hunder : UnderTowerOk ℓ
      (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))
      (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF (rebit b tl).length ++
        Eis.map (ihIdxAtM nF (n + k) i 0 (rebit b tl).length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + (rebit b tl).length))
          (teleVarsAV (rebit b tl).length)]))
      (AnnotTerm.mkAppN (.bvar (nF + (n + k) - 1 + 0 + (rebit b tl).length - tgt))
        (Eis.map (ihIdxAtM nF (n + k) i 0 (rebit b tl).length) ++
          [AnnotTerm.mkAppN (.bvar (nF - 1 - i + 0 + (rebit b tl).length))
            (teleVarsAV (rebit b tl).length)]))
      (ihTeleAtR nF (n + k) i 0 (rebit b tl)) := by
    refine underTowerOk_of_walk hwalk fun bs hsp => ?_
    have hsp' := (hspIff bs).mp hsp
    have hlen : bs.length = (rebit b tl).length := by
      rw [hsp'.length_eq, List.length_map, rebit_length]
    obtain ⟨hok, hmem, h0, -⟩ := hbody bs hsp'
    have hT := interp_ihDomBodyM (mot := tgt) (o := n + k) (l := 0) (ρp := consList as₁ ρ)
      (Ms := M0 :: Mrest) (ms := ms) (by rw [List.length_cons]; omega)
      (by rw [List.length_cons]; omega) (fs := as₂) (ihs := []) hlenF rfl hi bs Eis
    rw [consList_nil] at hT
    rw [← hlen, hT]
    exact ⟨hok, hmem, h0⟩
  refine ⟨mkLamsAV_bits_wellDenoted hz hunder, ?_, ?_⟩
  · refine mkLamsAV_bits_validV (underTowerValid_of ?_ fun bs hsp => ?_)
    · intro q d hq bs hsp
      have hv := fieldsValid_ihTeleAtGo (o := n + k) (ρp := consList as₁ ρ) (M := M0)
        (ms := Mrest ++ ms) hms (fs := as₂) (ihs := []) hlenF rfl (Nat.le_of_lt hi) tl [] hTV
      simp only [List.length_nil, consList] at hv
      rw [← consList_motives_cons] at hv
      have hv' : FieldsValid (consList as₂ (consList ms (consList (M0 :: Mrest) (consList as₁ ρ))))
          ((ihTeleAtR nF (n + k) i 0 (rebit b tl)).map (·.2.2)) := by
        rw [hdom_eq]; exact hv
      have h := fieldsValid_getD hv' (j := q)
        (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hq).1)
        (bs := bs) (by rw [← List.map_take]; exact hsp)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hq] at h
      exact h
    · have hsp' := (hspIff bs).mp hsp
      have hlen : bs.length = (rebit b tl).length := by
        rw [hsp'.length_eq, List.length_map, rebit_length]
      rw [← hlen]
      exact (hbody bs hsp').2.2.2
  · have hdom := interp_ihDomAVM (ℓ := ℓ) (mot := tgt) (o := n + k) (l := 0)
      (ρp := consList as₁ ρ) (Ms := M0 :: Mrest) (ms := ms) (by rw [List.length_cons]; omega)
      (by rw [List.length_cons]; omega) (fs := as₂) (ihs := []) hlenF rfl hi
      (tl := rebit b tl) (fun d hd => by rw [mem_rebit hd]; exact hbz.symm) Eis
    rw [consList_nil, rebit_map_dom] at hdom
    rw [← hdom]
    unfold ihDomAVM ihAppAVK
    exact mkLamsAV_bits_mem hz hunder

end ConLeche.Model
