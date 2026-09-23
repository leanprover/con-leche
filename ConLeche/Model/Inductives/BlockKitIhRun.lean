module

public import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.BlockRecRegimes
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Rules.InferSoundKit

public section

/-!
# The kit arms' `ih` values — `ihv` pinned, `hihChain` and `hihF` (lane RM55, sub-lane IH)

`BlockWfOwed` / `BlockSqOwed` (`BlockRecPreHpre.lean`) quantify the
arm's `ih` values `ihv` existentially.  They are pinned here
(`blockKitIhv`): per key the λ-tower over the rule frame's MOVED field
telescope whose body is the recursion graph at the PREDECESSOR the
guarded call names — `blockRecIhvAt` at exactly the per-key data the
pinned `ih` TERMS `blockRuleIhsRunAV` use, so `blockRecIhvAt_eq`
relates the two verbatim.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockRuleFrame)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The per-key data, and `ihv` pinned -/

section Pin

variable (pp : ConLeche.BlockParts)
  (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
  (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ψ : Name → Nat)

/-- The `ih` call's MOVED field telescope at key field `i` (the rule
frame's). -/
@[expose] def blockKitTlA (c j : Nat) : Nat → List (Nat × Nat × AnnotTerm) := fun i =>
  ihTeleAtR (blockRuleFrameAt pp rs c j).nF (pp.toBlockShape.rulePrefixAt c - pp.nP) i 0
    (rebit (pwBit ψ (blockRuleFrameAt pp rs c j).pw) (blockRuleTlAV pp rs acval envC ψ c j i))

/-- The `ih` call's index readings, moved with the telescope. -/
@[expose] def blockKitEisA (c j : Nat) : Nat → List AnnotTerm := fun i =>
  (blockRuleEisAV pp rs acval envC ψ c j i).map
    (ihIdxAtM (blockRuleFrameAt pp rs c j).nF (pp.toBlockShape.rulePrefixAt c - pp.nP) i 0
      (ConLeche.structFieldTeleOf (blockRuleCtorOf rs c j).1.type (blockRuleFrameAt pp rs c j).nP
        (blockRuleFrameAt pp rs c j).nF i).length)

/-- The `ih` call's applied field: field `i` along the telescope's own
variables. -/
@[expose] def blockKitFapA (c j : Nat) : Nat → AnnotTerm := fun i =>
  AnnotTerm.mkAppN
    (.bvar ((blockRuleFrameAt pp rs c j).nF - 1 - i + 0
      + (ConLeche.structFieldTeleOf (blockRuleCtorOf rs c j).1.type (blockRuleFrameAt pp rs c j).nP
          (blockRuleFrameAt pp rs c j).nF i).length))
    (teleVarsAV (ConLeche.structFieldTeleOf (blockRuleCtorOf rs c j).1.type
      (blockRuleFrameAt pp rs c j).nP (blockRuleFrameAt pp rs c j).nF i).length)

/-- **The pinned `ih` terms ARE `blockRecIhsAt` at the per-key data.** -/
theorem blockRuleIhsRunAV_eq_ihsAt (c j : Nat) :
    blockRuleIhsRunAV pp rs acval envC ψ c j
      = blockRecIhsAt (Level.eval ψ (ConLeche.structElimLevel pp.elim pp.large)) rs.length
          (pp.toBlockShape.rulePrefixAt c) (blockRuleFrameAt pp rs c j).nF
          (blockRuleFrameAt pp rs c j).ihKeys (blockKitTlA pp rs acval envC ψ c j)
          (blockKitEisA pp rs acval envC ψ c j) (blockKitFapA pp rs c j) := rfl

/-- **`ihv`, PINNED**: per key, the λ-tower over the moved telescope of
the graph `g` at the predecessor the call names. -/
@[expose] noncomputable def blockKitIhv (ℓ : Nat) (d : BlockData V) (ρ : Nat → V) :
    List V → Nat → Nat → List V → V → List V := fun xs c j fs g =>
  blockRecIhvAt ℓ (fun c' is => d.tup ψ (pp.toBlockShape.recTgtAt c') is)
    (consList (xs ++ fs) ρ) (blockRuleFrameAt pp rs c j).ihKeys
    (blockKitTlA pp rs acval envC ψ c j) (blockKitEisA pp rs acval envC ψ c j)
    (blockKitFapA pp rs c j) g

/-- **The pinned `ihv` has the frame's `nR` entries** — the length
`blockRecCa_value` asks of the `ih` block. -/
theorem blockKitIhv_length (ℓ : Nat) (d : BlockData V) (ρ : Nat → V) (xs : List V) (c j : Nat)
    (fs : List V) (g : V) :
    (blockKitIhv pp rs acval envC ψ ℓ d ρ xs c j fs g).length
      = (blockRuleFrameAt pp rs c j).nR := by
  simp only [blockKitIhv, blockRecIhvAt_length]
  rfl

end Pin

/-! ## 2. The graph at a predecessor IS the candidate's fold — at the
kit family's DATA fields

`blockRecIhCall` (`BlockRecPreRun.lean` §30) at `kitCandOf`/`kitGraphOf`:
it reads no law of the kit — the candidate's fold is `lamTowerA_fold`,
the graph's value at a predecessor is `app_graph` — so it holds at the
data fields alone, with no kit (whose typing obligations would include
the very rows produced here). -/

theorem kitCandOf_fold_graph {ℓ K : Nat} {rP : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {Is Cr : List V → Nat → V}
    {tupOf : Nat → List V → V} {pr B : List V → V → V} {st : List V → V → V → V}
    (hℓ : ℓ ≠ 0) {c' : Nat} {xs is : List V} {x u : V} (hxl : xs.length = rP c')
    (hsp : SpineFit ρ ((rds c').map (·.2.2)) (xs ++ (is ++ [x])))
    (hpred : (tagged c' (tupOf c' is) x : V) ∈ˢ pr xs u) :
    app (kitGraphOf ℓ K Is Cr pr B st xs u) (tagged c' (tupOf c' is) x)
      = (xs ++ (is ++ [x])).foldl SetTheory.app (kitCandOf ℓ K rP rds ρ Is Cr tupOf pr B st c') := by
  rw [kitCandOf, lamTowerA_fold hℓ hsp]
  simp only [List.nil_append]
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split, kitGraphOf, app_graph hpred]
  rfl

/-! ## 3. Depth along a telescope -/

/-- A member of a nested product folded along a fitting tuple is the
member itself or ∈-below it. -/
theorem piTele_fold_tc {v : Nat} (hv : v ≠ 0) {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {f : V} {as : List V},
      f ∈ˢ piTele v T B acc → FitsS T as →
      as.foldl SetTheory.app f = f ∨ as.foldl SetTheory.app f ∈ˢ ConLeche.SetTheory.tc f
  | _, .nil, _, _, [], _, _ => Or.inl rfl
  | _, .nil, _, _, _ :: _, _, hfit => hfit.elim
  | _, .cons _ _, _, _, [], _, hfit => hfit.elim
  | _, .cons A T, acc, f, a :: as, hf, hfit => by
    have hfa : SetTheory.app f a ∈ˢ ConLeche.SetTheory.tc f := by
      have hf' : f ∈ˢ piSet A (fun a => piTele v (T a) B (acc ++ [a])) := by
        have := hf
        simp only [piTele] at this
        rwa [piR_pos hv] at this
      exact app_mem_tc hf' hfit.1
    rw [List.foldl_cons]
    rcases piTele_fold_tc hv (T := T a) (acc := acc ++ [a]) (f := SetTheory.app f a) (as := as)
      (app_mem_piR_pos hv hf hfit.1) hfit.2 with h | h
    · right; rw [h]; exact hfa
    · right; exact tc_trans h hfa

/-! ## 4. ONE `ih` key, with its conclusion's PEEL

`blockRuleIhKey_run` (`BlockRuleGrading.lean`) states what the grading
and the typed tuple's fit read about an `ih` opener.  The kit's `hihF`
needs one more fact, the peel `BlockRuleConclAt` of the callee's
conclusion `CihR` — its VALUE (`blockRecCa_value`), since the ih value
there is the recursion GRAPH, not a member of the callee's type — and
`hihChain`/`hihF` both need the call's spine fitting the callee's
binder data at the rule's MOVED readings.  The key lemma computes both
(`hcon`, `hfitB`) as internal steps; this is its prelude restated with
those two exported (DUPLICATION to fold: exporting `hcon` and the
moved fit from `blockRuleIhKey_run` deletes this lemma's body). -/

section Key

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **ONE `ih` key, with its conclusion's peel and the call's fit.** -/
theorem blockKitIhKey_run
    (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    (ψ : Name → Nat) {q : Nat} (hq : q < (blockRuleFrameAt p rs j i).nR) :
    ∃ (fi c' : Nat) (CihR : AnnotTerm),
      (blockRuleFrameAt p rs j i).ihKeys[q]? = some (fi, c') ∧ c' < rs.length ∧ fi < cA.2 ∧
      p.toBlockShape.rulePrefixAt c' = p.toBlockShape.rulePrefixAt j ∧
      ((d.rss (p.toBlockShape.recTgtAt j)).getD i []).getD fi false = true ∧
      d.tgts (p.toBlockShape.recTgtAt j) i fi = p.toBlockShape.recTgtAt c' ∧
      (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default
        = (mkPisAV (blockKitTlA p rs mpC.base2.acval envC ψ j i fi) CihR).liftN q 0 ∧
      BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') cA.2
        (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length
        (blockRecTyAV mpC.base2.acval envC rs ψ c')
        (blockKitEisA p rs mpC.base2.acval envC ψ j i fi) (blockKitFapA p rs j i fi) CihR ∧
      DomsBelow (p.toBlockShape.rulePrefixAt j + cA.2)
        (blockKitTlA p rs mpC.base2.acval envC ψ j i fi) ∧
      (∀ e ∈ blockKitEisA p rs mpC.base2.acval envC ψ j i fi,
        Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2
          + (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length) e.erase) ∧
      Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2
          + (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length)
        (blockKitFapA p rs j i fi).erase ∧
      ∀ (σ : Nat → V) (xs fs : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j) xs →
        SpineFit (consList xs σ) (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i)
          fs →
        ∀ bs : List V, SpineFit (consList (xs ++ fs) σ)
          ((blockKitTlA p rs mpC.base2.acval envC ψ j i fi).map (·.2.2)) bs →
        SpineFit (consList (fs.take fi) (consList (xs.take p.nP) σ))
            ((((d.tlss (p.toBlockShape.recTgtAt j) ψ).getD i []).getD fi []).map (·.2.2)) bs ∧
          SpineFit σ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
            (xs ++ (blockKitEisA p rs mpC.base2.acval envC ψ j i fi
                ++ [blockKitFapA p rs j i fi]).map
              (interp V (consList bs (consList (xs ++ fs) σ)))) ∧
          interp V (consList bs (consList (xs ++ fs) σ)) (blockKitFapA p rs j i fi)
            = bs.foldl SetTheory.app (fs.getD fi pt) := by
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hjR : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  -- the rule's right-hand side (the kinds cover the constructors)
  have hir : i < r.2.2.2.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hir)⟩
  -- the member, the constructor and its record
  obtain ⟨ms, hms, hctA, hlenms⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : p.toBlockShape.recTgtAt j
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  have hmmN : p.toBlockShape.recTgtAt j
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
    Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hctM : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j) = r.2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j))[i]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcf : BlockCtorFacts mpC.base2
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) p.lps
      (p.toBlockShape.recTgtAt j) i cA := ⟨hfindC, hlpsC, hcd⟩
  have hcdP := hcd
  rw [show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP
    from rfl] at hcdP
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hcbC : ConstsBound envC cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨_, cvTa, _, _, _, _, _, -, hcvTa, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ cvTa hcvTa
  have hframes := (hS.frames _ hmemk i cA hcj).1 ψ
  have ho : p.toBlockShape.rulePrefixAt j = p.nP + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    omega
  have hFE := blockRuleFdomsAV_liftDoms h hr hcA hrhs hcore hmemk hcj hnP rfl ho ψ
  -- the `ih` openers: the frame, the tower, its opening and the fused readings
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, -, -, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) hct
  obtain ⟨rbs, ty, concl, -, -, hpis, hopen, -, -, -⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt j) i
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt j) i,
          (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xrestF
            (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  have hcfv : blockRuleCtorFvs p rs j i
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt j) i
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt j) i := by
    rw [blockRuleCtorFvs, hct, hop0]; rfl
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hks : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ksF
      (p.toBlockShape.recTgtAt j) i = (blockRuleKsOf p j i).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨hihfv, hL2, -, -, -, -, -, -, -, -, -⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  have hrow1 : ConLeche.openPisAtFvars ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF) cA.1.type 0
      = some (blockRuleCtorFvs p rs j i,
          ((ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0).map (·.2)).getD default) := by
    rw [hfrP, hfrF, hcfv, hop0]; rfl
  have hrow2 : (cA.1.type.stripPis ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF)).isSome = true := by
    rw [hfrP, hfrF]; exact hstripC
  have hrow3 : ∀ q, (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q).length
      = (ConLeche.structFieldTeleOf cA.1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF q).length := by
    intro q
    simp only [blockRuleTlAV, hct, hfrP, hfrF, List.length_map, List.length_range]
  have hkeys : (blockRuleFrameAt p rs j i).ihKeys
      = ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
        ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
        (blockRuleKsOf p j i) := rfl
  -- a key's field reads, at the block's rows too
  have hfldM : ∀ q c' : Nat, (q, c') ∈ (blockRuleFrameAt p rs j i).ihKeys →
      q < cA.2 ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) ∧
        blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
          = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD q [] ∧
        blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
          = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
              (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
    intro q c' hm
    rw [hkeys] at hm
    obtain ⟨hqF, hk⟩ := mem_blockIhKeys_kind hm
    have hF := blockFieldReadAt_of (ψ := ψ) hcdP hop0 (show q < cA.2 by omega)
      (by rw [hks]; exact hk)
    obtain ⟨e1, e2⟩ := fieldReadAt_eq hF
    have eT : blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
        = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
      rw [e1]; simp only [blockRuleTlAV, hct, hcfv]
    have eE : blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
        = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
            (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
      rw [e2]; simp only [blockRuleEisAV, hct, hcfv]
    refine ⟨by omega, ?_, eT, eE⟩
    rw [hfrP, hfrF, hcfv, eT, eE]
    exact hF
  -- the callees' stored types
  have hrecTyM : ∀ c' : Nat,
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, -, hb, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
      exact ⟨hf, hb, _, hread⟩
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      exact ⟨rfl, rfl, AnnotTerm.sort (Level.eval ψ Level.zero), by simp [denoteMeta]⟩
  have hrow8 : FvarList ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse := by
    rw [hfrR, hfrF, List.reverse_append]; exact hL2
  have hpisF : ConLeche.blockIhPis (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).rP
      (blockRuleFrameAt p rs j i).nF (blockRuleFrameAt p rs j i).pw
      (fun c' => (rs.map (·.1.type)).getD c' (.sort .zero)) (blockRuleFrameAt p rs j i).teleOf
      (blockRuleFrameAt p rs j i).idxOf (blockRuleFrameAt p rs j i).ihKeys 0
      (blockRuleResidAt p rs j i) = some (blockRuleIhTeleAt p rs j i) := by
    rw [hfrP, hfrR, hfrF]; exact hpis
  have hopenF : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).ihKeys.length
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := by
    rw [hfrR, hfrF]; exact hopen
  have hopDom := blockIhOpenerDom_run (mT := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt j - p.nP)
    (by rw [hfrR, hfrP]) (by rw [hfrP, hfrR]; omega) hrow1 hCf hCb hrow2
    (by rw [hfrP, hfrF]; exact htele) (by rw [hfrP, hfrF]; exact hidxF) hrow3
    (fun q c' _ hk => ⟨by rw [hfrF]; exact (hfldM q c' (List.mem_of_getElem? hk)).1,
      (hfldM q c' (List.mem_of_getElem? hk)).2.1⟩)
    (fun _ c' _ _ => hrecTyM c') hpisF hihfv hrow8 hopenF
  have hlenFvsIh : (blockRuleFvsIhAt p rs j i).length = (blockRuleFrameAt p rs j i).nR :=
    openPisAtFvars_length _ hopen
  have hexI : ∀ (l : Nat) (x : Expr), (blockRuleFvsIhAt p rs j i)[l]? = some x →
      ∃ A, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + l)
        (Expr.fvarTypeD x) = some A := by
    intro l x hx
    have hl : l < (blockRuleFrameAt p rs j i).ihKeys.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenFvsIh] at this
      exact this
    obtain ⟨_, _, -, -, hread⟩ := hopDom ((blockRuleFrameAt p rs j i).ihKeys[l]).1
      ((blockRuleFrameAt p rs j i).ihKeys[l]).2 l x (List.getElem?_eq_getElem hl) hx
    rw [hfrR, hfrF] at hread
    exact ⟨_, hread⟩
  have hIdomE : blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i
      = readOpenedDoms mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2)
          (blockRuleFvsIhAt p rs j i) := by
    rw [blockRuleIhdomsAV, hct]
  -- the key
  have hqK : q < (blockRuleFrameAt p rs j i).ihKeys.length := hq
  obtain ⟨fi, c', hkeyE⟩ : ∃ fi c', (blockRuleFrameAt p rs j i).ihKeys[q]? = some (fi, c') :=
    ⟨_, _, List.getElem?_eq_getElem hqK⟩
  obtain ⟨x, hx⟩ : ∃ x, (blockRuleFvsIhAt p rs j i)[q]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenFvsIh]; exact hq)⟩
  obtain ⟨TVa, CihR, hTVa, hpeel, hread⟩ := hopDom fi c' q x hkeyE hx
  have hmemKey : (fi, c') ∈ (blockRuleFrameAt p rs j i).ihKeys := List.mem_of_getElem? hkeyE
  obtain ⟨hfiC, -, eT, eE⟩ := hfldM fi c' hmemKey
  -- the key's block facts
  obtain ⟨-, hlenR, -⟩ := checkBlockRecK_recNames h
  have hrecTgtsLen : p.recTgts.length = rs.length := by
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).length = _
    rw [List.length_map, List.length_range, hlenR]
  have hrecTgts : ∀ e, e < rs.length → p.recTgts.getD e rs.length = p.toBlockShape.recTgtAt e := by
    intro e he
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).getD e rs.length = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hFssLen : (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt j) ψ).getD i []).length = cA.2 := by
    have hFssD : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
        (p.toBlockShape.recTgtAt j) ψ).getD i []
        = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
          (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    show p.nP + cA.2 - p.nP = cA.2
    omega
  have hkey' : (ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
      ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
      (blockRuleKsOf p j i)).getD q (0, 0) = (fi, c') := by
    rw [← hkeys, List.getD_eq_getElem?_getD, hkeyE]; rfl
  obtain ⟨hc'K, hfiF, hrss, htgtc', hrPs, hkind⟩ :=
    blockIhKey_block_facts (d := blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
      (ψ := ψ) (K := rs.length) (mem := p.toBlockShape.recTgtAt) hcj hks hksLen hFssLen
      (fun _ => rfl) hrecTgtsLen hrecTgts hkey' (by rw [← hkeys]; exact hqK)
  have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
  have hrPc' : p.toBlockShape.rulePrefixAt c' = p.toBlockShape.rulePrefixAt j := by
    rw [← hrPs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  -- the opener's domain IS the moved telescope over the call's conclusion
  have hIget : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default
      = (mkPisAV (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []))) CihR).liftN q 0 := by
    have hr1 := readOpenedDoms_reads hexI q x hx
    rw [← hIdomE] at hr1
    rw [hfrR, hfrF] at hread
    have heq := Option.some.inj (hr1.symm.trans hread)
    rw [heq, eT]

  -- the spelled per-key data, at the block's rows
  have hFr : (blockRuleFrameAt p rs j i).nF = cA.2 := hfrF
  have hTlA : blockKitTlA p rs mpC.base2.acval envC ψ j i fi
      = ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi [])) := by
    rw [blockKitTlA, hFr, eT]
  have hm : (ConLeche.structFieldTeleOf (blockRuleCtorOf rs j i).1.type
        (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF fi).length
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hct, ← hrow3 fi, eT]
  have hEisA : blockKitEisA p rs mpC.base2.acval envC ψ j i fi
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) := by
    rw [blockKitEisA, hm, hFr, eE]
  have hFapA : blockKitFapA p rs j i fi
      = AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) := by
    rw [blockKitFapA, hm, hFr, Nat.add_zero]
  have hTlLen : (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hTlA, ihTeleAtR_length, rebit_length]
  have htlE : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ := by
    rw [BlockData.tlss, BlockData.cds, tlssOfR_fixCtorDataList_getD hcj]
  have hEisE : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Eiss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ := by
    rw [BlockData.Eiss, BlockData.cds, eissOfR_fixCtorDataList_getD hcj]
  -- the callee's type, its binder data and its conclusion
  obtain ⟨-, -, -, hreadT, hTyE, hrdsLen, -, -, -, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr' ψ
  have hTVaE : TVa = blockRecTyAV mpC.base2.acval envC rs ψ c' := by
    have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
    rw [hg] at hTVa
    exact Option.some.inj (hTVa.symm.trans hreadT)
  have hcon : BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') cA.2
      (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length
      (blockRecTyAV mpC.base2.acval envC rs ψ c')
      (blockKitEisA p rs mpC.base2.acval envC ψ j i fi) (blockKitFapA p rs j i fi) CihR := by
    rw [hTlLen, hEisA, hFapA, ← hTVaE, hrPc']
    rw [hfrR, hfrF, eT, eE, Nat.add_zero] at hpeel
    exact hpeel
  -- the bounds
  have hTlB : DomsBelow (p.nP + fi)
      (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []) := hcdP.tssBelow ψ fi
  have hDB : DomsBelow (p.toBlockShape.rulePrefixAt j + cA.2)
      (blockKitTlA p rs mpC.base2.acval envC ψ j i fi) := by
    have hD := ihTeleAtGo_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt j - p.nP)
      (i := fi) (l := 0) (K := p.nP + fi) (k := 0)
      (tl := rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
        (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []))
      (by rw [Nat.add_zero]; exact domsBelow_rebit hTlB)
    rw [show p.nP + fi + (cA.2 - fi + 0) + (p.toBlockShape.rulePrefixAt j - p.nP) + 0
      = p.toBlockShape.rulePrefixAt j + cA.2 from by omega] at hD
    rw [hTlA]; exact hD
  have hEB : ∀ e ∈ blockKitEisA p rs mpC.base2.acval envC ψ j i fi,
      Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2
        + (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length) e.erase := by
    intro e he
    rw [hEisA] at he
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
    have hEb := ihIdxAtM_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt j - p.nP) (i := fi)
      (l := 0) (m := (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) (hcdP.eissBelow ψ fi E hE)
    rw [hTlLen]
    rw [show p.nP + fi + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
        ppsOf).tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length + (cA.2 - fi + 0)
        + (p.toBlockShape.rulePrefixAt j - p.nP)
      = p.toBlockShape.rulePrefixAt j + cA.2 + (((blockDataOf V p.toBlockShape env₀ ctorsAs
        p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length
      from by omega] at hEb
    exact hEb
  have hFB : Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2
      + (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length)
      (blockKitFapA p rs j i fi).erase := by
    rw [hFapA, hTlLen, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · show _ < _
      omega
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      have := List.mem_range.mp hk
      show _ < _
      omega
  refine ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgtc', by rw [hIget, hTlA], hcon, hDB,
    hEB, hFB, ?_⟩
  intro σ xs fs hxs hfs bs hbsM
  -- the frame's lengths and the prefix's split
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).length
      = p.toBlockShape.rulePrefixAt j := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt j := by rw [hxs.length_eq, hpl]
  have hlenps : (xs.take p.nP).length = p.nP := by rw [List.length_take, hxlen]; omega
  have hms : (xs.drop p.nP).length = p.toBlockShape.rulePrefixAt j - p.nP := by
    rw [List.length_drop, hxlen]
  have hshift : shiftE (p.toBlockShape.rulePrefixAt j - p.nP) 0 (consList xs σ)
      = consList (xs.take p.nP) σ := by
    have hregroup : consList xs σ = consList (xs.drop p.nP) (consList (xs.take p.nP) σ) := by
      rw [← consList_append, List.take_append_drop]
    rw [hregroup, ← hms]
    exact shiftE_consList _ _
  have hfsB0 : SpineFit (consList (xs.take p.nP) σ)
      ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
        (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2)) fs := by
    rw [← hshift]
    rw [hFE] at hfs
    exact (spineFit_liftDoms (V := V) _).mp hfs
  have hFssD : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
        (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hfsB : SpineFit (consList (xs.take p.nP) σ)
      (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
        (p.toBlockShape.recTgtAt j) ψ).getD i []) fs := by
    rw [hFssD]; exact hfsB0
  have hfsl : fs.length = cA.2 := by rw [hfsB.length_eq, hFssLen]
  -- the parameters: the block's, and the constructor's own
  have hps : SpineFit σ
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).params ψ)
      (xs.take p.nP) := by
    have ht := spineFit_take hxs (i := p.nP) (by rw [hpl]; exact hnP)
    have hte : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).take p.nP
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ j).map (·.2.2)).take
          p.nP := by
      rw [blockRulePdomsAV, List.map_take, List.take_take, Nat.min_eq_left hnP]
    rw [hte] at ht
    exact (blockRecParams_run hμ mpC h hmr hr ψ σ _).mp ht
  have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.len ψ) hframes (spineFit_take_any hxs p.nP)
  -- the callee's prefix is the rule's
  have hprefR : SpineFit σ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c')) xs := by
    rw [← List.map_take]
    exact blockRecHpref_run hμ mpC h ψ hr hr' hxs
  have htgts : ∀ l, l < cA.2 →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tgts
        (p.toBlockShape.recTgtAt j) i l
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := by
    intro l _
    rw [← hN.2.2.2]
    exact hN.2.1 _ i l
  have hxl : xs.length = (xs.take p.nP).length + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    rw [hlenps, hxlen]; omega
  have htake : xs.take (xs.take p.nP).length = xs.take p.nP := by rw [hlenps]
  -- the moved telescope's fit is the block's own
  rw [hTlA] at hbsM
  have hbsC := spineFit_ihTeleAtR_rule (ρ := σ) (i := fi) hxl htake hfsl hbsM
  have hbl : bs.length
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hbsC.length_eq, List.length_map]
  obtain ⟨-, -, -, hfitB⟩ := blockIhCallFit_of hμ mpC h hmr hM hcj hcf hmmN htgts
    hfiC hkind hrss hr' htgtc' hprefR hps hpc hfsB (by rw [htlE]; exact hbsC)
  rw [hEisE] at hfitB
  have hes : ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)).map
        (interp V (consList bs (consList (xs ++ fs) σ)))
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ)))) := by
    rw [List.map_map]
    exact List.map_congr_left fun E _ => interp_ihIdxAtM_rule (i := fi) hxl htake hfsl hbl E
  have hmk := interp_fieldApp_rule (ρ := σ) (xs := xs) hfsl hfiC hbl
  refine ⟨by rw [htlE]; exact hbsC, ?_, by rw [hFapA]; exact hmk⟩
  rw [hEisA, hFapA, List.map_append, hes, List.map_cons, List.map_nil, hmk]
  exact hfitB

end Key

end ConLeche.Model
