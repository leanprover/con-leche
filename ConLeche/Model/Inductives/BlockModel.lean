module

public import ConLeche.Model.Inductives.BlockRep
public section

/-!
# The block's representation, from the stages' semantic outputs (task #315 M3)

`blockModelAt_of_stages`: every clause of `BlockRep.lean`'s
`BlockModelAt` at the fixpoint route's data — the operator is
`blockPhi`, the injections the tagged tuples of the member-LOCAL sum
route, the members' leaves `blockTyAV`.

The one bridge the record needs and the tower files do not have is
between the two spellings of "a spine fits constructor `j`'s entries":
the operator's is a `SpineFit` along the X-chain (`chainXBIGo`, at the
frame carrying the index tuple and the family tuple), the record's is
`FitsFrom` at the parameter frame with the recursive entries named as
SETS (`slotSet` at the target component).  They are the same relation
(`fitsFrom_iff_spineFit_chainXBIGo`): the X-chain's recursive entry
denotes that slot (`xEntryB_rec`) and its ordinary entry is the
domain's own reading two frames up (`xEntryB_ord`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The representation -/

/-- **The block's representation, from the stages' outputs.**  Every
clause of `BlockModelAt` at the fixpoint route's data: the operator's
fibre is the hole fit (`hfib` — the datum's operator is the hole
operator, lane HOLE2), it maps the tuple space into itself, is monotone
(positivity's) and has a closed tuple; at the least tuple the hole fit
is the stored fit (`hcarrier`, the override law); the injections are
the member-LOCAL sum route's tagged tuples (`hinj`), the members' leaves
the block operator at chains agreeing with `d.Φ` (`hleaf`, `hChs` — the
hole chains), the constructors' `sumMkAV` (`hctorLeaf`).  The remaining
hypotheses are the stages' own facts: the data's lengths, the
parameter-telescope interchanges the members and the constructors were
checked to agree on (`hparams`, `hparamsC` — `blockParamsIff` and
`ctorFramesGen` at the run) and the constructors' result index fit
(`hresFit`, the constructors' typing: their result applications were
inferred at the opened telescope). -/
theorem blockModelAt_of_stages {env : Env} (mo : EnvModel V env) {names : List Name}
    {d : BlockData V}
    -- what the representation IS
    (hnames : d.memberNames = names)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    -- the data's shape
    (hlenC : ∀ (ψ : Name → Nat) (c : Nat), (d.Fss c ψ).length = (d.ctorsM c).length)
    (hN0 : 0 < d.N)
    (hlenPps : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    -- the operator, at every parameter frame
    (hidxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ))
    (hfib : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
      ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
        x ∈ˢ app (d.Φ ψ ρp X c) t ↔ ∃ j fs, d.toLfp.HFits ψ ρp X t c j fs ∧ x = d.inj ψ c j fs)
    (hmaps : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      MapsTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp))
    (hmono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp))
    (hfitsMono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X Y, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) Y →
      TupleLe d.N (d.idx ψ ρp) X Y → ∀ c, c < d.N → ∀ (t : V) (j : Nat) (fs : List V),
        d.toLfp.HFits ψ ρp X t c j fs → d.toLfp.HFits ψ ρp Y t c j fs)
    (hclosed : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∃ L, IsClosedTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp) L)
    (hcarrier : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.N → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ (j : Nat) (fs : List V),
        d.toLfp.HFits ψ ρp (lfpTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) t c j fs ↔
          d.StoredFit ψ ρp t c j fs)
    -- the members' leaves — the block operator at chains `Chs` graded at
    -- every parameter frame and agreeing with `d.Φ` on the tuple space (lane
    -- HOLE2: the hole chains, whose operator IS `d.Φ`) — and the members'
    -- parameter agreement
    (Chs : (Name → Nat) → Nat → List (List AnnotTerm))
    (hleaf : ∀ mm, mm < d.k → ∀ ψ : Name → Nat, mo.acval (d.memberName mm) ψ
      = blockTyG d.N (d.w ψ) (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (Chs ψ) (d.ppsM mm ψ) mm)
    (hChs : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      BlockChainsOkG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (Chs ψ) ∧
      ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
        blockPhiG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (Chs ψ) X c
          = d.Φ ψ ρp X c)
    (hparams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρ)
    -- the constructors' leaves and their parameter frames
    (hctorLeaf : ∀ c, c < d.N → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → ∀ ψ : Name → Nat, mo.acval cA.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP).map (·.2.2))
            (uChains (d.Fss c ψ)))
    (hFssD : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2))
    (hdsLen : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.dsF c j ψ).length = d.nP + ((d.Fss c ψ).getD j []).length)
    (hparamsC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.dsF c j ψ).take d.nP).map (·.2.2)).reverse ρ)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
      ∀ c, c < d.N → SumFieldsOkB (d.w ψ) ρ (uChains (d.Fss c ψ)))
    -- the constructors' RESULT index readings fit the component's telescope
    (hresFit : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
      ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ fs : List V, SpineFit ρ ((d.Fss c ψ).getD j []) fs →
      SpineFit ρ (d.IdsM c ψ) (((d.Ess c ψ).getD j []).map (interp V (consList fs ρ)))) :
    BlockModelAt mo names d := by
  have hlenParams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (((d.ppsM c ψ).take d.nP).map (·.2.2)).length = d.nP := by
    intro ψ c hc
    rw [List.length_map, List.length_take, hlenPps ψ c hc]
    omega
  have hlenParamsD : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP :=
    fun ψ => hlenParams ψ 0 hN0
  -- the parameter spine at ANY component's own telescope
  have hspP : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ (d.params ψ) as → SpineFit ρ (((d.ppsM c ψ).take d.nP).map (·.2.2)) as := by
    intro ψ c hc ρ as hsp
    exact (spineFit_iff_of_sat_iff (by rw [hlenParamsD, hlenParams ψ c hc]) (hparams ψ c hc) ρ as
      (by rw [hsp.length_eq, hlenParamsD])).mp hsp
  have hspPC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ (d.params ψ) as → SpineFit ρ (((d.dsF c j ψ).take d.nP).map (·.2.2)) as := by
    intro ψ c j hc hj ρ as hsp
    have hl : (((d.dsF c j ψ).take d.nP).map (·.2.2)).length = d.nP := by
      rw [List.length_map, List.length_take, hdsLen ψ c j hj]
      omega
    exact (spineFit_iff_of_sat_iff (by rw [hlenParamsD, hl]) (hparamsC ψ c j hc hj) ρ as
      (by rw [hsp.length_eq, hlenParamsD])).mp hsp
  refine ⟨hnames, hidxOk, fun ψ ρp hρ => ⟨hmono ψ ρp hρ, hmaps ψ ρp hρ, hclosed ψ ρp hρ⟩,
    hfib, hfitsMono, ?_, ?_, hresFit, hcarrier, ?_, ?_⟩
  · -- leaf
    intro mm hmm ψ ρ as is hsa hsi
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := d.satOfSpine hsa
    have hlenI : is.length = (d.IdsM mm ψ).length := hsi.length_eq
    have hsp : SpineFit ρ ((d.ppsM mm ψ).map (·.2.2)) (as ++ is) := by
      have hsplit : (d.ppsM mm ψ).map (·.2.2)
          = ((d.ppsM mm ψ).take d.nP).map (·.2.2) ++ d.IdsM mm ψ := by
        show _ = _ ++ ((d.ppsM mm ψ).drop d.nP).map (·.2.2)
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact SpineFit.append
        (hspP ψ mm (Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _)) ρ as hsa) hsi
    have hsh : shiftE (d.IdsM mm ψ).length 0 (consList (as ++ is) ρ) = consList as ρ := by
      rw [consList_append, ← hlenI]
      have := shiftE_consList_add (V := V) is 0 (consList as ρ)
      rwa [shiftE_zero_zero] at this
    have hfr : ConLeche.Semantics.frameIdx (d.IdsM mm ψ).length (consList (as ++ is) ρ) = is :=
      ConLeche.Semantics.frameIdx_of (d.IdsM mm ψ).length hlenI ρ
    have hbase : BlockBaseG d.N (d.w ψ) (consList (as ++ is) ρ) (fun c => d.uM c ψ)
        (fun c => d.IdsM c ψ) (Chs ψ) mm := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hsh]; exact hidxOk ψ _ hsat
      · rw [hsh]; exact (hChs ψ (consList as ρ) hsat).1
      · rw [hsh, hfr]; exact hsi
    rw [hleaf mm hmm ψ,
      blockTyG_fold (show mm < d.N from Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _))
        hsp hbase, hsh, hfr]
    congr 1
    exact lfpTuple_congr (fun _ _ => rfl)
      (fun X hX m hm => (hChs ψ (consList as ρ) hsat).2 X hX m hm)
      (Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _))
  · -- ctor
    intro c hc j cA hj ψ ρ as fs hsa hsf
    have hjl : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := d.satOfSpine hsa
    rw [hctorLeaf c hc j cA hj ψ, hinj]
    by_cases hw : d.w ψ = 0
    · rw [if_pos hw, hw, sumMkAV_zero, foldl_app_pt]
    · rw [if_neg hw]
      have h2 : SpineFit (consList as ρ) (((d.dsF c j ψ).drop d.nP).map (·.2.2)) fs := by
        rw [← hFssD ψ c j hjl]; exact hsf
      have hjF : j < (d.Fss c ψ).length := by rw [hlenC]; exact hjl
      have h3 : (uChains (d.Fss c ψ))[j]?
          = some (((d.dsF c j ψ).drop d.nP).map (·.2.2) ++ [idxEqAV []]) := by
        rw [uChains_getElem?, List.getElem?_eq_getElem hjF]
        show some _ = some _
        rw [show (d.Fss c ψ)[j] = (d.Fss c ψ).getD j [] from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjF, Option.getD_some],
          hFssD ψ c j hjl]
      have h4 := sumMkAV_fold (V := V) (w := d.w ψ) (j := j)
        (pds := (d.dsF c j ψ).take d.nP) (fds := (d.dsF c j ψ).drop d.nP)
        (Fss := uChains (d.Fss c ψ)) (ρ := ρ) (as := as) (bs := fs)
        hw (hspPC ψ c j hc hjl ρ as hsa) h2 (hFssOk ψ (consList as ρ) hsat c hc) h3
      rw [List.take_append_drop] at h4
      exact h4
  · -- mkZero
    intro ψ hw c j fs
    rw [hinj, if_pos hw]
  · -- mkInj
    intro ψ hw c hc j fs j' fs' hj hj' hlen hlen' heq
    rw [hinj, hinj, if_neg hw, if_neg hw] at heq
    obtain ⟨rfl, hT⟩ := inj_inj heq
    refine ⟨rfl, ?_⟩
    have hll : (fs ++ [pt]).length = (fs' ++ [pt]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [hlen, hlen']
    have := mkTower_inj hll hT
    exact List.append_cancel_right this

end ConLeche.Model
