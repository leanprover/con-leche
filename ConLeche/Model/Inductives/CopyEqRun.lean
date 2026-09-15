module

public import ConLeche.Model.Inductives.PsiRun
public import ConLeche.SetTheory.Derive.BekicUnit
import ConLeche.Model.IndRepToolkit
import ConLeche.Model.Inductives.CopyPins
import ConLeche.Model.Inductives.CopyCtorWalk
public section

/-!
# The set-equality consumer: a copy's carrier IS the container's at the pin (task #279 M-F)

The run-level consumer of DESIGN §M.59 (a), stated first.  For every
pin `j` of a nested run, the auxiliary block's copy member `k₀ + j` —
its leaf in the scratch model `mpAux` — applied to fitting parameters
and indices is the CONTAINER's leaf applied to the pin's readings and
the same indices (`CopyLeafEq`): an equality of SETS, replacing the
bijection ψ of §M.4.  It follows from Bekić at one component
(`bekic_component'`, `ConLeche/SetTheory/Derive/BekicUnit.lean`), the
two `leaf` clauses (the aux member's, the container's), and ONE named
fact, the **section agreement** `SectionAgree`: the copy's section of
the aux block's functor at the fixed point's other components is the
container's functor at the pin's readings, along a bijection of the
index sets.  Its discharge is where the syntactic content lives
(K.10/K.12's copy identities at the level of `ChainFit`) and where the
injections must agree — see §M.59 (b) for why the latter is FALSE at
today's block-position tags and what would make it true.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ElimState BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

namespace IndRepData

variable (d : IndRepData V)

/-- **Member `t`'s index component** of the block's index set at a
parameter frame: the tuples of the member's own fitting index spines. -/
@[expose] noncomputable def copyIdxS (ψ : Name → Nat) (t : Nat) (ρp : Nat → V) : V :=
  sep (d.idx ψ ρp) (fun s => ∃ is, SpineFit ρp (d.IdsM t ψ) is ∧ s = d.tup ψ t is)

/-- The other components. -/
@[expose] noncomputable def copyIdxC (ψ : Name → Nat) (t : Nat) (ρp : Nat → V) : V :=
  sep (d.idx ψ ρp) (fun s => ¬ s ∈ˢ d.copyIdxS ψ t ρp)

theorem copyIdxS_subset {ψ : Name → Nat} {t : Nat} {ρp : Nat → V} :
    d.copyIdxS ψ t ρp ⊆ˢ d.idx ψ ρp :=
  sep_subset

/-- **The section agreement — the operator identity at a pin (NAMED,
DESIGN §M.59 (c))**: at every block parameter frame `ρp = as ∷ ρ`,
with the pin's readings `v := ⟦DsA⟧ρp` and the container's frame
`ρp' = v ∷ ρp`, there is a bijection `f/g` between the container's index
set at `ρp'` and the copy's index component (`copyIdxS`) sending the
container's tuple of an index spine to the copy's, along which the
copy's section of the block's functor `Φ` — at the simultaneous least
fixed point's OTHER components — is the container's functor `Φ_J` at
the pin's readings.  Its fibres are SETS OF VALUES: the agreement
includes the injections (§M.59 (b)). -/
@[expose] def SectionAgree (ψ : Name → Nat) (k₀ j : Nat) (c : CopyData V) : Prop :=
  ∀ (ρ : Nat → V) (as : List V), SpineFit ρ (d.params ψ) as →
    ∃ f g : V → V,
      (∀ i, i ∈ˢ c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ)) →
        f i ∈ˢ d.copyIdxS ψ (k₀ + j) (consList as ρ)) ∧
      (∀ s, s ∈ˢ d.copyIdxS ψ (k₀ + j) (consList as ρ) →
        g s ∈ˢ c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ))) ∧
      (∀ i, i ∈ˢ c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ)) →
        g (f i) = i) ∧
      (∀ s, s ∈ˢ d.copyIdxS ψ (k₀ + j) (consList as ρ) → f (g s) = s) ∧
      (∀ is, SpineFit (consList as ρ) (d.IdsM (k₀ + j) ψ) is →
        f (c.dJ.tup c.ψ' c.mm is) = d.tup ψ (k₀ + j) is) ∧
      ∀ Y, Y ∈ˢ famSpace (d.w ψ) (d.copyIdxS ψ (k₀ + j) (consList as ρ)) →
        ∀ i, i ∈ˢ c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ)) →
          app (app (d.Φ ψ (consList as ρ))
              (famJoin (d.copyIdxS ψ (k₀ + j) (consList as ρ)) (d.copyIdxC ψ (k₀ + j) (consList as ρ)) Y
                (famRestr (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ)))
                  (d.copyIdxC ψ (k₀ + j) (consList as ρ))))) (f i)
            = app (app (c.dJ.Φ c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ)))
                (famPull f Y
                  (c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ))))) i

/-- **The copy's carrier is the container's at the pin** — the
set-equality form of the identification (the successor of ψ, DESIGN
§M.59 (a)): the copy member `k₀ + j`'s leaf at fitting parameters `as`
and indices `is` is the container's leaf at the pin's readings and the
same indices. -/
@[expose] def CopyLeafEq (m : EnvModel V env) (ψ : Name → Nat) (k₀ j : Nat) (c : CopyData V) : Prop :=
  ∀ (ρ : Nat → V) (as is : List V), SpineFit ρ (d.params ψ) as →
    SpineFit (consList as ρ) (d.IdsM (k₀ + j) ψ) is →
    (as ++ is).foldl app (interp V ρ (m.acval (d.memberName (k₀ + j)) ψ))
      = (c.DsA.map (interp V (consList as ρ)) ++ is).foldl app
          (interp V (consList as ρ) (m.acval (c.dJ.memberName c.mm) c.ψ'))

end IndRepData

/-- **The equality from the agreement, at the datum**: Bekić at the
copy's component plus the two `leaf` clauses. -/
theorem copyLeafEq_of_sectionAgree {m : EnvModel V env} {d : IndRepData V} {ψ : Name → Nat}
    {k₀ j : Nat} {c : CopyData V} {s : Level} (hs : ∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ)
    {cvTA cvRA : ConstantVal} {mIA rPA : Nat} {rulesA : List RecRule}
    (hrepA : IndRep m (d.memberName (k₀ + j)) cvTA cvRA mIA rPA rulesA
      { d with resSort := s } (k₀ + j))
    {cvTJ cvRJ : ConstantVal} {mIJ rPJ : Nat} {rulesJ : List RecRule}
    (hrepJ : IndRep m (c.dJ.memberName c.mm) cvTJ cvRJ mIJ rPJ rulesJ c.dJ c.mm)
    (hok : CopyData.Ok m d ψ k₀ j c) (hsa : d.SectionAgree ψ k₀ j c) :
    d.CopyLeafEq m ψ k₀ j c := by
  intro ρ as is hsp his
  have hsat : Sat V (d.params ψ).reverse (consList as ρ) := d.satOfSpine hsp
  -- the pin's readings fit the container's parameters (at the block frame)
  have hvfitM := d.pinFit_of_leafShape (L := m.acval (c.dJ.memberName c.mm) c.ψ') rfl
    hok.ff hok.ls hok.pin hsat
  have hlen0 : (c.dJ.ppsM 0 c.ψ').length = c.dJ.nP + c.dJ.nIdxAt 0 := by
    obtain ⟨cv0, caps0, hf0⟩ := hrepJ.membersFound 0 (Nat.lt_of_lt_of_le
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hrepJ.memReal) hrepJ.kRealLe)
    exact (hrepJ.formersRead 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hrepJ.memReal) cv0 caps0 hf0).len c.ψ'
  have hvfit : SpineFit (consList as ρ) (c.dJ.params c.ψ') (c.DsA.map (interp V (consList as ρ))) := by
    refine spineFit_of_satIff ?_ (fun ρ' h => (hok.pIffM ρ').mpr h) hvfitM
    unfold IndRepData.params
    rw [List.length_map, List.length_take, List.length_map, List.length_take, hlen0, hok.ff.1,
      Nat.min_eq_left (Nat.le_add_right _ _), Nat.min_eq_left (Nat.le_add_right _ _)]
  have hsat' : Sat V (c.dJ.params c.ψ').reverse
      (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ)) :=
    c.dJ.satOfSpine hvfit
  have his' : SpineFit (consList (c.DsA.map (interp V (consList as ρ))) (consList as ρ))
      (c.dJ.IdsM c.mm c.ψ') is :=
    (hok.idx.idxIff _ hsat is).mp his
  -- the two leaves
  have hleafA := hrepA.leaf ψ ρ as is hsp his
  have hleafJ := hrepJ.leaf c.ψ' (consList as ρ) _ is hvfit his'
  have hwA : IndRepData.w { d with resSort := s } ψ = d.w ψ := hs ψ
  have hidxA : IndRepData.idx { d with resSort := s } ψ (consList as ρ) = d.idx ψ (consList as ρ) := rfl
  have hΦA : IndRepData.Φ { d with resSort := s } = d.Φ := rfl
  have htupA : IndRepData.tup { d with resSort := s } = d.tup := rfl
  rw [hwA, hidxA, hΦA, htupA] at hleafA
  have hwJ : c.dJ.w c.ψ' = d.w ψ := hok.idx.sort
  rw [hwJ] at hleafJ
  rw [hleafA, hleafJ]
  -- the functors' laws
  have hfunA := hrepA.functor ψ (consList as ρ) hsat
  rw [hwA, hidxA, hΦA] at hfunA
  obtain ⟨-, hmonoA, hmapsA, hclA⟩ := hfunA
  have hfunJ := hrepJ.functor c.ψ' _ hsat'
  rw [hwJ] at hfunJ
  obtain ⟨-, hmonoJ, hmapsJ, hclJ⟩ := hfunJ
  -- the agreement's bijection
  obtain ⟨f, g, hf, hg, hgf, hfg, htup, hagree⟩ := hsa ρ as hsp
  have htupJ := hrepJ.tupMem c.ψ' _ hsat' is his'
  have key := bekic_component' (d.copyIdxS_subset) hmonoA hmapsA hclA hmonoJ hmapsJ hclJ f g hf hg hgf hfg
    hagree (c.dJ.tup c.ψ' c.mm is) htupJ
  rw [htup is his] at key
  exact key

/-- **The run-level consumer** (DESIGN §M.59 (a)): from a nested run,
under the containers' representation, for every pin `j` the section
agreement (NAMED) yields the copy's carrier equality with the
container's at the pin, in the scratch model `mpAux` — the copy
member's leaf and the container's leaf both read there (the latter
agrees with the pre-block model's by `AuxBlockAgree`). -/
theorem copyLeafEq_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (params : List Expr)
      (pbs : List (Expr × BinderMeta)),
      ConLeche.auxBlock p st = some b ∧ st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        AuxBlockAgree F mp mpAux b true d ∧
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V,
            (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
            ∀ j, j < st.pins.length →
              d.SectionAgree ψ p.k j (cd j) →                     -- NAMED: the operator identity
              d.CopyLeafEq mpAux.base2 ψ p.k j (cd j)) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, -, -, hlenSt, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, mpAux, d, hreps, -, hag, hpins⟩ := pinFacts_of_run hμ mp hE h
  refine ⟨st, b, envAux, params, pbs, hb, hlenSt, mpAux, d, hreps, hag, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  refine ⟨cd, hcd, ?_⟩
  intro j hj hsa
  obtain ⟨⟨pf, hbm, _⟩, _⟩ := hcd j hj
  -- the aux member's representation
  obtain ⟨-, hkb, -, -, -, -, -, hmem⟩ := hreps
  have hjk : p.k + j < b.k := by
    rw [ConLeche.auxBlock_k hb, hlenSt]; omega
  obtain ⟨s, cvTA, cvRA, capsA, mIA, rPA, rulesA, -, -, -, hs, hrepA⟩ := hmem (p.k + j) hjk
  -- the container member's representation and the copy's data
  obtain ⟨cvTJ, cvRJ, mIJ, rPJ, rulesJ, hrepJ⟩ := pf.repAll (cd j).mm pf.mm
  have hok : CopyData.Ok mpAux.base2 d ψ p.k j (cd j) := by
    have := pf.grp (cd j).mm pf.mm
    rw [hbm] at this
    exact this
  exact copyLeafEq_of_sectionAgree hs hrepA hrepJ hok hsa

end ConLeche.Model
