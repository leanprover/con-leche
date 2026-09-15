module

import ConLeche.Model.Inductives.FixLeafOk
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

/-! ## The block split of a mutual rule spine -/

omit [SetTheory V] in
/-- The block frame's shift: the `k` motives and the `n` minors sit
between the rule's leaf frame and the parameter frame. -/
theorem shiftE_blockMinors {k n : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hlenK : Ms.length = k) (hlenM : ms.length = n) :
    shiftE (k + n) 0 (consList ms (consList Ms ρp)) = ρp := by
  rw [← consList_append, show k + n = (Ms ++ ms).length from by rw [List.length_append]; omega,
    shiftE_consList]

/-- **The block split** of a spine fitting a mutual recursor's binder
data below the indices: the parameters, the `k` motives, the `n` minors
(in their ih-extended readings, each over its constructor's own member
motive and its fields' target motives). -/
theorem mutualBlock_split {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {nP n ℓ wB b k : Nat} {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
    {ipsOf : Nat → List (Nat × Nat × AnnotTerm)}
    {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {cds : List CtorDatumR} (hn : cds.length = n)
    {mems : Nat → Nat} {tgts : Nat → Nat → Nat}
    {Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hminor : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ Ms : List V, Ms.length = k →
      ∀ q cd, cds[q]? = some cd → ∀ ms : List V, ms.length = q →
        interp V (consList ms (consList Ms ρp))
            (minorAVAtRM (mems q) (tgts q) m cd.1 ψ nP cd.2.1 b (k + q) cd.2.2.1 cd.2.2.2.1
              cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI [] wB ρp (Ms.getD (mems q) pt) (Ess.getD q []) q fs)
              (ihDomsIM ℓ ρp (fun i => Ms.getD (tgts q i) pt) rss tlss Eiss
                (fun r => (Fss.getD r []).length) q fs))
            (Fss.getD q []) ρp [])
    (ρb : Nat → V) (as : List V)
    (hsp : SpineFit ρb ((rebit b pps ++
        motivesDataGo Lof nIdxOf ipsOf ψ nP elimL b k 0 ++
        fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)) as) :
    ∃ (ps Ms ms : List V),
      as = (ps ++ Ms) ++ ms ∧ ps.length = nP ∧ Ms.length = k ∧ ms.length = n ∧
      Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) ∧
      -- the MOTIVE block's own fit (task #278 M2.5f): the `k` motives
      -- are not arbitrary sets of the right number — `hzeroC`/`hzeroD`
      -- read their spaces
      SpineFit (consList ps ρb)
        ((motivesDataGo Lof nIdxOf ipsOf ψ nP elimL b k 0).map (·.2.2)) Ms ∧
      (∀ q, q < n → ms.getD q pt ∈ˢ minorSpI ℓ
        (fun fs => ihSpL ℓ
          (concI [] wB (consList ps ρb) (Ms.getD (mems q) pt) (Ess.getD q []) q fs)
          (ihDomsIM ℓ (consList ps ρb) (fun i => Ms.getD (tgts q i) pt) rss tlss Eiss
            (fun r => (Fss.getD r []).length) q fs))
        (Fss.getD q []) (consList ps ρb) []) := by
  have hlenMD : (fixMinorsDataM mems tgts m ψ nP b cds k).length = n := by
    rw [fixMinorsDataM_length, hn]
  rw [List.map_append, List.map_append, rebit_map_dom] at hsp
  obtain ⟨c₁, ms, rfl, hsp₂, hspM⟩ := spineFit_append_inv hsp
  obtain ⟨ps, Ms, rfl, hspP, hspMot⟩ := spineFit_append_inv hsp₂
  have hlenPs : ps.length = nP := by rw [hspP.length_eq, List.length_map, hlenP]
  have hlenMs : Ms.length = k := by
    rw [hspMot.length_eq, List.length_map, motivesDataGo_length]
  have hlenms : ms.length = n := by rw [hspM.length_eq, List.length_map, hlenMD]
  have hρp : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρb) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρb) hspP
    rwa [List.append_nil] at this
  have hframe : consList (ps ++ Ms) ρb = consList Ms (consList ps ρb) := consList_append _ _ _
  rw [hframe] at hspM
  refine ⟨ps, Ms, ms, rfl, hlenPs, hlenMs, hlenms, hρp, hspMot, ?_⟩
  intro q hq
  obtain ⟨cd, hcd⟩ : ∃ cd, cds[q]? = some cd := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hmem := FixKI.spineFit_getD_mem' hspM (l := q) (by rw [List.length_map, hlenMD]; exact hq)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, fixMinorsDataM_getElem?, hcd,
    Option.map_some, Option.getD_some] at hmem
  have hread := hminor (consList ps ρb) hρp Ms hlenMs q cd hcd (ms.take q)
    (by rw [List.length_take, hlenms]; omega)
  rw [hread] at hmem
  exact hmem

/-! ## The mutual rule's right-hand side -/

set_option maxHeartbeats 6400000 in
/-- **The mutual rule's right-hand side is `WellDenotedV`** at every
frame: the λ-tower over rule `J`'s binder data — the parameters, the
`k` motives, the `n` minors and constructor `J`'s field data — with
minor `J` at the fields and the inductive hypotheses as its body. -/
theorem mutualRuleOk {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {nP n k nF ℓ wB b : Nat} (hbz : ℓ = 0 ↔ b = 0)
    (hb : pwBit ψ (Level.zeronessOf elimL) = b)
    {Ls : List AnnotTerm} (hLs : Ls.length = k)
    {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} (hn : cds.length = n)
    {mems : Nat → Nat} {tgts : Nat → Nat → Nat}
    {Fss Ess : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {j : Nat} {C : Name} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdxJ : List Nat} {EissJ : List (List AnnotTerm)} {tlsJ : List (List (Nat × Nat × AnnotTerm))}
    (hcd : cds[j]? = some (C, nF, ds, Es, recIdxJ, EissJ, tlsJ))
    (hlenDs : ds.length = nP + nF) (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hEsj : Ess[j]? = some Es) (hrecIdx : recIdxJ = recIdx (rss.getD j []) nF)
    (hEissJ : Eiss.getD j [] = EissJ) (htlsJ : tlss.getD j [] = tlsJ)
    (hleafC : m.acval C ψ = sumMkAV [] 0 wB j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hclC : Term.bvarsBelow 0 (m.acval C ψ).erase)
    (hiff : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp ↔
      Sat V (((ds.take nP).map (·.2.2)).reverse) ρp)
    (hmems : mems j < k) (htgts : ∀ i ∈ recIdx (rss.getD j []) nF, tgts j i < k)
    (hEisLen : ∀ i ∈ recIdx (rss.getD j []) nF,
      ((Eiss.getD j []).getD i []).length = nIdxs.getD (tgts j i) 0)
    {mm : Nat}
    (hstore : ∀ σ : Nat → V, WellDenotedV V σ
      (mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm)
        (mutualConcAV k n (nIdxs.getD mm 0) mm)))
    {Rof : Nat → AnnotTerm} (hRcl : ∀ t, Term.bvarsBelow 0 (Rof t).erase)
    (hRok : ∀ (t : Nat) (σ : Nat → V), WellDenotedV V σ (Rof t))
    (hRmem : ∀ t, t < k → ∀ σ : Nat → V, interp V σ (Rof t) ∈ˢ interp V σ
      (mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts t)
        (mutualConcAV k n (nIdxs.getD t 0) t)))
    (hRconc0 : ℓ = 0 → ∀ t, t < k → ∀ (σ : Nat → V) (as : List V),
      SpineFit σ
        ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts t).map (·.2.2)) as →
      interp V (consList as σ) (mutualConcAV k n (nIdxs.getD t 0) t) ∈ˢ (univZero : V))
    (hminor : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ Ms : List V, Ms.length = k →
      ∀ q cd, cds[q]? = some cd → ∀ ms : List V, ms.length = q →
        interp V (consList ms (consList Ms ρp))
            (minorAVAtRM (mems q) (tgts q) m cd.1 ψ nP cd.2.1 b (k + q) cd.2.2.1 cd.2.2.2.1
              cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI ℓ (fun fs => ihSpL ℓ (concI [] wB ρp (Ms.getD (mems q) pt) (Ess.getD q []) q fs)
              (ihDomsIM ℓ ρp (fun i => Ms.getD (tgts q i) pt) rss tlss Eiss
                (fun r => (Fss.getD r []).length) q fs))
            (Fss.getD q []) ρp [])
    (hfields : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      SumFieldsOkB wB ρp Fss ∧ FieldsOkB wB ρp ((ds.drop nP).map (·.2.2)) ∧
      FieldsValid ρp ((ds.drop nP).map (·.2.2)))
    (hteles : ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ as₂ : List V, SpineFit ρp ((ds.drop nP).map (·.2.2)) as₂ →
      ∀ i ∈ recIdx (rss.getD j []) nF,
        FieldsOkB wB (consList (as₂.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) ∧
        FieldsValid (consList (as₂.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V,
          SpineFit (consList (as₂.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs →
          (∀ E ∈ (Eiss.getD j []).getD i [],
            WellDenoted V (consList bs (consList (as₂.take i) ρp)) E) ∧
          (∀ E ∈ (Eiss.getD j []).getD i [],
            AnnotValid V (consList bs (consList (as₂.take i) ρp)) E) ∧
          AppChainOk (as₂.getD i pt) bs)
    -- **the ih's spine** (task #278 M2.5f): the block prefix must be a
    -- FITTING spine, not merely one of the right lengths — `SpineFit`
    -- is membership-based, so lengths alone make the conclusion false
    -- at garbage parameters or motives
    (hih : ∀ (ρ : Nat → V) (as₁ Ms ms as₂ : List V),
      as₁.length = nP → Ms.length = k →
      SpineFit ρ (((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).take
        (nP + k + n)).map (·.2.2)) ((as₁ ++ Ms) ++ ms) →
      SpineFit (consList as₁ ρ) ((ds.drop nP).map (·.2.2)) as₂ →
      ∀ i ∈ recIdx (rss.getD j []) nF,
      ∀ bs : List V, SpineFit (consList (as₂.take i) (consList as₁ ρ))
          (((tlss.getD j []).getD i []).map (·.2.2)) bs →
        SpineFit ρ
          ((mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts (tgts j i)).map (·.2.2))
          (as₁ ++ Ms ++ ms ++
            ((Eiss.getD j []).getD i []).map
              (interp V (consList bs (consList (as₂.take i) (consList as₁ ρ)))) ++
            [bs.foldl SetTheory.app (as₂.getD i pt)]))
    -- **the `Prop` regime's two universe facts** (task #278 M2.5f): at
    -- a MOTIVE SPINE, not at arbitrary sets of the right number — the
    -- motives' spaces are what puts the conclusion and the ih domains
    -- in the truth values (`piTele_app_univZero`)
    (hzeroC : ℓ = 0 → ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ Ms : List V, SpineFit ρp ((motivesDataGo (fun t => Ls.getD t default)
          (fun t => nIdxs.getD t 0) (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)) Ms →
        ∀ acc : List V, concI [] wB ρp (Ms.getD (mems j) pt) Es j acc ∈ˢ (univZero : V))
    (hzeroD : ℓ = 0 → ∀ ρp : Nat → V, Sat V ((pps.map (·.2.2)).reverse) ρp →
      ∀ Ms : List V, SpineFit ρp ((motivesDataGo (fun t => Ls.getD t default)
          (fun t => nIdxs.getD t 0) (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)) Ms →
        ∀ (as₂ : List V) (A : V),
        A ∈ ihDomsIM ℓ ρp (fun i => Ms.getD (tgts j i) pt) rss tlss Eiss
          (fun r => (Fss.getD r []).length) j as₂ → A ∈ˢ (univZero : V)) :
    ∀ ρ : Nat → V, WellDenotedV V ρ
      (mkLamsAV (mutualRuleDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts ds)
        (mutualRuleCoreAV b Rof (tgts j) nP k n nF j recIdxJ tlsJ EissJ)) := by
  intro ρ
  subst hrecIdx
  subst hEissJ
  subst htlsJ
  have hjn : j < n := by rw [← hn]; exact (List.getElem?_eq_some_iff.mp hcd).1
  have hlenFs' : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hFsD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hEsD : Ess.getD j [] = Es := by rw [List.getD_eq_getElem?_getD, hEsj]; rfl
  have har : (Fss.getD j []).length = nF := by rw [hFsD, hlenFs']
  have hlenMD : (fixMinorsDataM mems tgts m ψ nP b cds k).length = n := by
    rw [fixMinorsDataM_length, hn]
  -- the binder data: the block prefix `X` and the lifted fields `D`
  generalize hX : rebit b pps ++
      motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0)
        (fun t => ipss.getD t []) ψ nP elimL b k 0 ++
      fixMinorsDataM mems tgts m ψ nP b cds k = X
  generalize hD : rebit b (liftDoms (k + n) 0 (ds.drop nP)) = D
  have hlenX : X.length = nP + k + n := by
    rw [← hX]
    simp only [List.length_append, rebit_length, hlenP, motivesDataGo_length, hlenMD]
  have hlenD : D.length = nF := by
    rw [← hD, rebit_length, liftDoms_length]; simp [hlenDs]
  have hDdoms : D.map (·.2.2) = (liftDoms (k + n) 0 (ds.drop nP)).map (·.2.2) := by
    rw [← hD, rebit_map_dom]
  have hbits : ∀ d ∈ X ++ D, d.2.1 = b := by
    intro d hd
    rw [← hX, ← hD] at hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact mem_rebit hd
    · exact mem_motivesDataGo hd
    · exact mem_fixMinorsDataM hd
    · exact mem_rebit hd
  have hlds : mutualRuleDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts ds
      = (X ++ D).map fun d => (b, d.2.2) := by
    unfold mutualRuleDataAV
    rw [hb, hLs, hn, hX, hD]
    exact List.map_congr_left fun d hd => by rw [hbits d hd]
  have hzXD : ∀ d ∈ X ++ D, (b = 0 ↔ d.2.1 = 0) := fun d hd => by rw [hbits d hd]
  -- the stored recursor type's binder data and its block prefix
  have hrdsE : mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm
      = X ++ rebit b (liftDoms (k + n) 0 (ipss.getD mm [])) ++
        [(0, b, majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) k n)] := by
    unfold mutualRecDataAV
    rw [hb, hLs, hn, hX]
  have hprefix :
      (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).take (nP + k + n) = X := by
    have hlenXD : (X ++ rebit b (liftDoms (k + n) 0 (ipss.getD mm []))).length
        = nP + k + n + (ipss.getD mm []).length := by
      rw [List.length_append, hlenX, rebit_length, liftDoms_length]
    rw [hrdsE,
      List.take_append_of_le_length (by omega :
        nP + k + n ≤ (X ++ rebit b (liftDoms (k + n) 0 (ipss.getD mm []))).length),
      List.take_append_of_le_length (by omega : nP + k + n ≤ X.length),
      List.take_of_length_le (by omega : X.length ≤ nP + k + n)]
  have hFOk := (WellDenoted_mkPisAV_inv (hstore ρ).1).1
  have hFV := (AnnotValid_mkPisAV_inv (hstore ρ).2).1
  have hwalkX : DomsWalk ρ X := by
    have h := domsWalk_take (nP + k + n) (domsWalk_of_fieldsOkB hFOk)
    rwa [hprefix] at h
  rw [hlds]
  show WellDenotedV V ρ (mkLamsC b (X ++ D)
    (mutualRuleCoreAV b Rof (tgts j) nP k n nF j (recIdx (rss.getD j []) nF) (tlss.getD j [])
      (Eiss.getD j [])))
  -- the conclusion, spelled at the rule's leaf frame
  generalize hTC : AnnotTerm.mkAppN (.bvar (nF + (k + n) - 1 - mems j))
      ((Es.map fun E => E.liftN (k + n) nF) ++
        [AnnotTerm.mkAppN (m.acval C ψ)
          (paramBvarsAt nP (nP + (k + n) + nF) ++ fieldBvars nF)]) = TC
  -- **the leaf facts** at every fitting spine of the rule's binder data
  have hleaf : ∀ as : List V, SpineFit ρ ((X ++ D).map (·.2.2)) as →
      WellDenoted V (consList as ρ)
        (mutualRuleCoreAV b Rof (tgts j) nP k n nF j (recIdx (rss.getD j []) nF) (tlss.getD j [])
          (Eiss.getD j [])) ∧
      interp V (consList as ρ)
          (mutualRuleCoreAV b Rof (tgts j) nP k n nF j (recIdx (rss.getD j []) nF) (tlss.getD j [])
            (Eiss.getD j []))
        ∈ˢ interp V (consList as ρ) TC ∧
      (b = 0 → interp V (consList as ρ) TC ∈ˢ (univZero : V)) ∧
      AnnotValid V (consList as ρ)
        (mutualRuleCoreAV b Rof (tgts j) nP k n nF j (recIdx (rss.getD j []) nF) (tlss.getD j [])
          (Eiss.getD j [])) := by
    intro as hsp
    rw [List.map_append] at hsp
    obtain ⟨block, as₂, rfl, hspB, hspD⟩ := spineFit_append_inv hsp
    rw [← hX] at hspB
    obtain ⟨as₁, Ms, ms, rfl, hlen₁, hlenMs, hlenm, hρp, hspMot, hms⟩ :=
      mutualBlock_split hlenP hn hminor ρ _ hspB
    have hframe : consList ((as₁ ++ Ms) ++ ms) ρ = consList ms (consList Ms (consList as₁ ρ)) := by
      rw [consList_append, consList_append]
    rw [hframe] at hspD
    rw [hDdoms, spineFit_liftDoms, shiftE_blockMinors hlenMs hlenm] at hspD
    have hlen₂ : as₂.length = nF := by rw [hspD.length_eq, hlenFs']
    rw [consList_append, hframe]
    obtain ⟨hokB, -, -⟩ := hfields _ hρp
    have hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) (consList as₁ ρ) := (hiff _).mp hρp
    -- the conclusion's value
    have hTv : interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ)))) TC
        = concI [] wB (consList as₁ ρ) (Ms.getD (mems j) pt) Es j as₂ := by
      rw [← hTC]
      exact interp_minorConcAVM (o := k + n) (by omega) (by omega) hlenDs hleafC hclC hFsj hokB
        hsatC hspD
    -- the minor at the fields
    have hmj := hms j hjn
    have hc0 : ℓ = 0 → ∀ acc : List V,
        ihSpL ℓ (concI [] wB (consList as₁ ρ) (Ms.getD (mems j) pt) (Ess.getD j []) j acc)
          (ihDomsIM ℓ (consList as₁ ρ) (fun i => Ms.getD (tgts j i) pt) rss tlss Eiss
            (fun r => (Fss.getD r []).length) j acc) ∈ˢ (univZero : V) := by
      intro h0 acc
      refine ihSpL_zero_univZero h0 ?_ _
      rw [hEsD]
      exact hzeroC h0 _ hρp Ms hspMot acc
    have hchainM := minorSpI_appChainOk hc0 hmj (by rw [hFsD]; exact hspD)
    have hfoldM := minorSpI_fold hc0 hmj (by rw [hFsD]; exact hspD)
    rw [List.nil_append] at hfoldM
    have hbv : interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
        (.bvar (nF + n - 1 - j)) = ms.getD j pt := by
      rw [interp_bvar, show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega,
        consList_apply_add, consList_apply_lt' ms _ (by omega),
        show ms.length - 1 - (n - 1 - j) = j from by omega]
    have hfb : (fieldBvars nF).map
        (interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))) = as₂ := by
      show ((List.range nF).map fun q => AnnotTerm.bvar (nF - 1 - q)).map
        (interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))) = as₂
      exact map_fieldBvars_interp hlen₂ _
    obtain ⟨hokF, hvF⟩ := mkAppN_wellDenoted_of_chain (f := .bvar (nF + n - 1 - j))
      (args := fieldBvars nF) (σ := consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
      trivial (fun a ha => by obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; trivial)
      (by rw [hbv, hfb]; exact hchainM)
    rw [hbv, hfb] at hvF
    -- the inductive hypotheses
    have hihF : ∀ i ∈ recIdx (rss.getD j []) nF,
        WellDenoted V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
          (ihAppAVK (Rof (tgts j i)) nP k n nF i (rebit b ((tlss.getD j []).getD i []))
            ((Eiss.getD j []).getD i [])) ∧
        AnnotValid V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
          (ihAppAVK (Rof (tgts j i)) nP k n nF i (rebit b ((tlss.getD j []).getD i []))
            ((Eiss.getD j []).getD i [])) ∧
        interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
            (ihAppAVK (Rof (tgts j i)) nP k n nF i (rebit b ((tlss.getD j []).getD i []))
              ((Eiss.getD j []).getD i []))
          ∈ˢ piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ))
              (((tlss.getD j []).getD i []).map (·.2.2)))
            (fun as => SetTheory.app
              ((((Eiss.getD j []).getD i []).map
                (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
                  SetTheory.app (Ms.getD (tgts j i) pt))
              (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
      intro i hi
      obtain ⟨hTOk, hTV, hleaves⟩ := hteles _ hρp as₂ hspD i hi
      refine ihAppAVK_facts hbz hlen₁ hlenMs hlenm hlen₂ (mem_recIdx.mp hi).1 (htgts i hi)
        (hRcl _) (hRok _) ?_ ?_ (hRmem _ (htgts i hi) ρ) (hEisLen i hi) hTOk hTV ?_
      · intro d hd; rw [mem_mutualRecDataAV hd, hb]; exact hbz
      · intro h0 as' hsp'; exact hRconc0 h0 _ (htgts i hi) ρ as' hsp'
      · intro bs hbs
        obtain ⟨hEok, hEV, hchainF⟩ := hleaves bs hbs
        exact ⟨hEok, hEV, hchainF,
          hih ρ as₁ Ms ms as₂ hlen₁ hlenMs (by rw [hprefix, ← hX]; exact hspB) hspD i hi bs hbs⟩
    -- the ih tower's fold
    have hAs : ihDomsIM ℓ (consList as₁ ρ) (fun i => Ms.getD (tgts j i) pt) rss tlss Eiss
          (fun r => (Fss.getD r []).length) j as₂
        = (recIdx (rss.getD j []) nF).map fun i =>
            piTele ℓ (teleOfFields (consList (as₂.take i) (consList as₁ ρ))
                (((tlss.getD j []).getD i []).map (·.2.2)))
              (fun as => SetTheory.app
                ((((Eiss.getD j []).getD i []).map
                  (interp V (consList as (consList (as₂.take i) (consList as₁ ρ))))).foldl
                    SetTheory.app (Ms.getD (tgts j i) pt))
                (as.foldl SetTheory.app (as₂.getD i pt))) [] := by
      unfold ihDomsIM
      simp only [har]
    have hsp_ih := ihSpL_spine (V := V) (ℓ := ℓ)
      (C := concI [] wB (consList as₁ ρ) (Ms.getD (mems j) pt) (Ess.getD j []) j as₂)
      (As := ihDomsIM ℓ (consList as₁ ρ) (fun i => Ms.getD (tgts j i) pt) rss tlss Eiss
        (fun r => (Fss.getD r []).length) j as₂)
      (args := (recIdx (rss.getD j []) nF).map fun i =>
        ihAppAVK (Rof (tgts j i)) nP k n nF i (rebit b ((tlss.getD j []).getD i []))
          ((Eiss.getD j []).getD i []))
      (f := AnnotTerm.mkAppN (.bvar (nF + n - 1 - j)) (fieldBvars nF))
      (σ := consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
      (fun h0 => by rw [hEsD]; exact hzeroC h0 _ hρp Ms hspMot as₂)
      hokF (by rw [hvF]; exact hfoldM)
      (by rw [hAs, List.length_map, List.length_map])
      (by
        intro l hl
        rw [hAs, List.length_map] at hl
        obtain ⟨i, hi⟩ : ∃ i, (recIdx (rss.getD j []) nF)[l]? = some i :=
          ⟨_, List.getElem?_eq_getElem hl⟩
        have hmem : i ∈ recIdx (rss.getD j []) nF := List.mem_of_getElem? hi
        have hgd1 : ∀ (f : Nat → AnnotTerm) (xs : List Nat) (d : AnnotTerm),
            xs[l]? = some i → (xs.map f).getD l d = f i := by
          intro f xs d hx
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
        have hgd2 : ∀ (f : Nat → V) (xs : List Nat) (d : V),
            xs[l]? = some i → (xs.map f).getD l d = f i := by
          intro f xs d hx
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
        rw [hAs, hgd1 _ _ _ hi, hgd2 _ _ _ hi]
        exact ⟨(hihF i hmem).1, (hihF i hmem).2.2⟩)
      (fun h0 A hA => hzeroD h0 _ hρp Ms hspMot as₂ A hA)
    rw [← AnnotTerm.mkAppN_append] at hsp_ih
    refine ⟨hsp_ih.1, ?_, ?_, ?_⟩
    · rw [hTv, ← hEsD]; exact hsp_ih.2
    · intro hb0
      rw [hTv]
      exact hzeroC (hbz.mpr hb0) _ hρp Ms hspMot as₂
    · unfold mutualRuleCoreAV
      refine mkAppN_validV trivial fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
        trivial
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        exact (hihF i hi).2.1
  -- **the tower**: the domain walk
  have hwalk : DomsWalk ρ (X ++ D) := by
    refine domsWalk_append hwalkX ?_
    intro as hsp
    rw [← hX] at hsp
    obtain ⟨as₁, Ms, ms, rfl, hlen₁, hlenMs, hlenm, hρp, -, -⟩ :=
      mutualBlock_split hlenP hn hminor ρ _ hsp
    rw [← hD]
    refine domsWalk_rebit b (domsWalk_liftDoms (w := wB) _ 0 _ ?_)
    rw [consList_append, consList_append, shiftE_blockMinors hlenMs hlenm]
    exact (hfields _ hρp).2.1
  refine ⟨mkLamsC_wellDenoted (T := TC) hzXD (underTowerOk_of_walk (C := TC) hwalk fun as hsp => ?_),
    mkLamsC_validV ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hleaf as hsp
    exact ⟨h1, h2, h3⟩
  · -- the validity walk
    refine underTowerValid_of ?_ fun as hsp => (hleaf as hsp).2.2.2
    intro q d hq as hsp
    rcases Nat.lt_or_ge q X.length with hqX | hqX
    · -- a block entry: the stored recursor type's binder datum
      have hqR : (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm)[q]? = some d := by
        rw [List.getElem?_append_left hqX] at hq
        rw [← hprefix, List.getElem?_take_of_lt (by omega)] at hq
        exact hq
      have htake : (X ++ D).take q
          = (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm).take q := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hqX), ← hprefix, List.take_take,
          show min q (nP + k + n) = q from by omega]
      rw [htake] at hsp
      have h := fieldsValid_getD hFV (j := q)
        (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hqR).1)
        (bs := as) (by rw [← List.map_take]; exact hsp)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hqR] at h
      exact h
    · -- a field entry, lifted under the block
      rw [List.getElem?_append_right hqX] at hq
      have hqD : q - X.length < D.length := (List.getElem?_eq_some_iff.mp hq).1
      rw [← hD, show rebit b (liftDoms (k + n) 0 (ds.drop nP))
          = (liftDoms (k + n) 0 (ds.drop nP)).map (fun d => (d.1, b, d.2.2)) from rfl,
        List.getElem?_map, liftDoms_getElem?] at hq
      obtain ⟨r, hr⟩ : ∃ r, (ds.drop nP)[q - X.length]? = some r :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hD, rebit_length, liftDoms_length] at hqD; exact hqD)⟩
      rw [hr] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      show AnnotValid V (consList as ρ) (r.2.2.liftN (k + n) (0 + (q - X.length)))
      rw [List.take_append, List.take_of_length_le (by omega : X.length ≤ q)] at hsp
      rw [List.map_append] at hsp
      obtain ⟨block, as₂, rfl, hspB, hspD⟩ := spineFit_append_inv hsp
      rw [← hX] at hspB
      obtain ⟨as₁, Ms, ms, rfl, hlen₁, hlenMs, hlenm, hρp, -, -⟩ :=
        mutualBlock_split hlenP hn hminor ρ _ hspB
      have hframe : consList ((as₁ ++ Ms) ++ ms) ρ
          = consList ms (consList Ms (consList as₁ ρ)) := by
        rw [consList_append, consList_append]
      rw [hframe] at hspD
      rw [← hD, show rebit b (liftDoms (k + n) 0 (ds.drop nP))
          = (liftDoms (k + n) 0 (ds.drop nP)).map (fun d => (d.1, b, d.2.2)) from rfl,
        ← List.map_take, liftDoms_take, List.map_map] at hspD
      have hDmap : ((liftDoms (k + n) 0 ((ds.drop nP).take (q - X.length))).map
          ((fun d : Nat × Nat × AnnotTerm => d.2.2) ∘ fun d => (d.1, b, d.2.2)))
          = (liftDoms (k + n) 0 ((ds.drop nP).take (q - X.length))).map (·.2.2) := rfl
      rw [hDmap, spineFit_liftDoms, shiftE_blockMinors hlenMs hlenm] at hspD
      have hlenDrop : (ds.drop nP).length = nF := by simp [hlenDs]
      have hqD' : q - X.length < nF := by rw [hlenD] at hqD; exact hqD
      have hlen₂ : as₂.length = q - X.length := by
        rw [hspD.length_eq, List.length_map, List.length_take]
        omega
      rw [consList_append, hframe, AnnotValid_liftN, Nat.zero_add, ← hlen₂, shiftE_consList_len,
        shiftE_blockMinors hlenMs hlenm]
      have hvFs : FieldsValid (consList as₁ ρ) ((ds.drop nP).map (·.2.2)) := (hfields _ hρp).2.2
      have h := fieldsValid_getD hvFs (j := q - X.length) (by rw [hlenFs']; exact hqD')
        (bs := as₂) (by rw [← List.map_take]; exact hspD)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr] at h
      simpa using h

end ConLeche.Model
