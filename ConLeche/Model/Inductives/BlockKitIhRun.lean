module

import ConLeche.Model.Inductives.BlockRuleGrading
public import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.FixAssemblyKit

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
      Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + q)
        ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default).erase ∧
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
      (∀ x : Expr, (blockRuleFvsIhAt p rs j i)[q]? = some x →
        denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + q)
          (Expr.fvarTypeD x)
          = some ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default)) ∧
      blockRuleTlAV p rs mpC.base2.acval envC ψ j i fi
        = ((d.tlss (p.toBlockShape.recTgtAt j) ψ).getD i []).getD fi [] ∧
      blockRuleEisAV p rs mpC.base2.acval envC ψ j i fi
        = ((d.Eiss (p.toBlockShape.recTgtAt j) ψ).getD i []).getD fi [] ∧
      (ConLeche.structFieldTeleOf (blockRuleCtorOf rs j i).1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF fi).length
        = (((d.tlss (p.toBlockShape.recTgtAt j) ψ).getD i []).getD fi []).length ∧
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
            = bs.foldl SetTheory.app (fs.getD fi pt) ∧
          (blockKitEisA p rs mpC.base2.acval envC ψ j i fi).map
              (interp V (consList bs (consList (xs ++ fs) σ)))
            = (((d.Eiss (p.toBlockShape.recTgtAt j) ψ).getD i []).getD fi []).map
              (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ)))) := by
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
  have hIB : Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + q)
      ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default).erase := by
    obtain ⟨-, -, -, hlb, -, -, -, -, -, -, -, hWt, -⟩ :=
      blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
    have hr1 := readOpenedDoms_reads hexI q x hx
    rw [← hIdomE] at hr1
    have hW := openPisAtFvars_typeWScoped _ hopen hWt q x hx
    exact bvarsBelow_of_reading (m := mpC.base2) hW
      (hlb x (List.mem_append_right _ (List.mem_of_getElem? hx))) hr1
  refine ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgtc', by rw [hIget, hTlA], hIB, hcon, hDB,
    hEB, hFB, fun x' hx' => by
      have hr1 := readOpenedDoms_reads hexI q x' hx'
      rw [← hIdomE] at hr1
      exact hr1, by rw [htlE]; exact eT, by rw [hEisE]; exact eE, by rw [htlE]; exact hm, ?_⟩
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
  refine ⟨by rw [htlE]; exact hbsC, ?_, by rw [hFapA]; exact hmk,
    by rw [hEisA, hEisE]; exact hes⟩
  rw [hEisA, hFapA, List.map_append, hes, List.map_cons, List.map_nil, hmk]
  exact hfitB

/-- **Every `ih` opener's domain has a reading at its own depth** —
`blockRuleCerts_of_run`'s `hexI`, at the pinned openers. -/
theorem blockRuleIhReads_run
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
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[j]? = some cA)
    (ψ : Name → Nat) :
    ∀ (l : Nat) (x : Expr), (blockRuleFvsIhAt p rs c j)[l]? = some x →
      ∃ A, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + l)
        (Expr.fvarTypeD x) = some A := by
  intro l x hx
  have hir : j < r.2.2.2.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hir)⟩
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hl : l < (blockRuleFrameAt p rs c j).nR := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    rwa [openPisAtFvars_length _ hopen] at this
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hread, -⟩ :=
    blockKitIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hl
  exact ⟨_, hread x hx⟩

end Key

/-! ## 5. Congruence at FITTING spines; the `ih` values ARE the `ih` terms' readings -/

/-- **A λ-tower congruence at two frames, at FITTING spines** —
`lamTowerA_congr_below` with the body obligation only where the walk
goes: the tower is a graph over its domain. -/
theorem lamTowerA_congr_fit {m : Nat} {g₁ g₂ : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {N : Nat} {ρ₁ ρ₂ : Nat → V} {acc : List V},
      (∀ i, i < N → ρ₁ i = ρ₂ i) →
      (∀ l, l < ds.length → Term.bvarsBelow (N + l) ((ds.getD l default).2.2).erase) →
      (∀ bs : List V, SpineFit ρ₁ (ds.map (·.2.2)) bs →
        g₁ (acc ++ bs) (consList bs ρ₁) = g₂ (acc ++ bs) (consList bs ρ₂)) →
      lamTowerA m ρ₁ acc ds g₁ = lamTowerA m ρ₂ acc ds g₂
  | [], _, _, _, acc, _, _, hbody => by
    have h := hbody [] trivial
    simpa [lamTowerA] using h
  | dd :: ds, N, ρ₁, ρ₂, acc, hag, hb, hbody => by
    have hdom : interp V ρ₁ dd.2.2 = interp V ρ₂ dd.2.2 := by
      refine interp_congr_below (V := V) dd.2.2 N ρ₁ ρ₂ ?_ hag
      have h0 := hb 0 (by simp)
      simpa using h0
    show lamR m (interp V ρ₁ dd.2.2) (fun a => lamTowerA m (cons a ρ₁) (acc ++ [a]) ds g₁)
      = lamR m (interp V ρ₂ dd.2.2) (fun a => lamTowerA m (cons a ρ₂) (acc ++ [a]) ds g₂)
    rw [← hdom]
    refine lamR_congr fun a ha => ?_
    refine lamTowerA_congr_fit (N := N + 1) (fun i hi => ?_) (fun l hl => ?_) (fun bs hbs => ?_)
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have h := hb (l + 1) (by simpa using hl)
      rw [show N + 1 + l = N + (l + 1) from by omega]
      simpa using h
    · have h := hbody (a :: bs) ⟨ha, hbs⟩
      simpa [List.append_assoc] using h

/-- **`blockRecIhvAt_eq` with the call obligation at FITTING telescope
spines only** — the one `hcall` the run can pay: off the telescope the
recursion graph and the candidate are both junk, and not the same junk. -/
theorem blockRecIhvAt_eq_fit {ℓ K rP nF N : Nat} {a ρ : Nat → V} {xs fs : List V} {g : V}
    {tup : Nat → List V → V} {ihKeys : List (Nat × Nat)}
    {tlA : Nat → List (Nat × Nat × AnnotTerm)} {eisA : Nat → List AnnotTerm}
    {fapA : Nat → AnnotTerm}
    (hxl : xs.length = rP) (hfl : fs.length = nF) (hN : N = (xs ++ fs).length)
    (hkey : ∀ key ∈ ihKeys, key.2 < K)
    (htlB : ∀ key ∈ ihKeys, ∀ l, l < (tlA key.1).length →
      Term.bvarsBelow (N + l) (((tlA key.1).getD l default).2.2).erase)
    (hcall : ∀ key ∈ ihKeys, ∀ bs : List V,
      SpineFit (consList (xs ++ fs) ρ) ((tlA key.1).map (·.2.2)) bs →
      app g (tagged key.2
          (tup key.2 ((eisA key.1).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (fapA key.1)))
        = (xs ++ ((eisA key.1) ++ [fapA key.1]).map
            (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))))).foldl
              SetTheory.app (a key.2)) :
    blockRecIhvAt ℓ tup (consList (xs ++ fs) ρ) ihKeys tlA eisA fapA g
      = (blockRecIhsAt ℓ K rP nF ihKeys tlA eisA fapA).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ))) := by
  rw [blockRecIhvAt, blockRecIhsAt, List.map_map]
  refine List.map_congr_left fun key hkm => ?_
  show lamTowerA ℓ (consList (xs ++ fs) ρ) [] (tlA key.1) _
    = interp V (consList (xs ++ fs) (chainFrame K a ρ))
        (ihFunAV ℓ K key.2 rP nF (tlA key.1) (eisA key.1) (fapA key.1))
  rw [ihFunAV, interp_mkLamsC_A (acc := ([] : List V))]
  refine lamTowerA_congr_fit (N := N) (fun i hi => ?_) (htlB key hkm) (fun bs hbs => ?_)
  · exact consList_below_indep (xs ++ fs) ρ (chainFrame K a ρ) i (by rw [← hN]; exact hi)
  · have hbl : bs.length = (tlA key.1).length := by rw [hbs.length_eq, List.length_map]
    have hbody := interp_ihFunAV_body (V := V) (K := K) (c' := key.2) (tl := tlA key.1)
      (eis := eisA key.1) (fap := fapA key.1) (σ := chainFrame K a ρ)
      (chainFrame_apply (hkey key hkm) a ρ) hxl hfl hbl
    show app g _ = interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))) _
    rw [hbody, ← hcall key hkm bs hbs]

section ChainWf

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **REGIME WF's `hihChain`, PRODUCED** — `BlockWfOwed`'s row at the
pinned `ihv` (`blockKitIhv`) and `ihs` (`blockRuleIhsRunAV`), at the
checked elimination level: the graph-built `ih` values ARE the `ih`
terms' readings at the arm's chain frame.  Per key, the graph at the
call's argument is the candidate folded along the call's spine
(`kitCandOf_fold_graph`): the argument is a PREDECESSOR — in the
union by the callee's split (`blockWf_hsplit` at the call's fit,
`blockKitIhKey_run`), ∈-below by the recursive slot's nested product
(`piTele_fold_tc`, `mem_tc_inj_mkTower`). -/
theorem blockWfIhChain_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat) (ρ : Nat → V) (Rb0 : Nat → Nat → AnnotTerm)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : d.w ψ ≠ 0) :
    (∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs c j fs
            (blockWfGraph (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) rs.length d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ))
                  (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ)))) := by
  intro c hc j hj xs fs hxs hsp
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, hnF, hpre, hps, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxs hsp
  obtain ⟨hChain, hmkv⟩ :=
    blockWfCtorAt_run hμ h hkLen hcore hmr hM hN rfl hctM ψ rs.length _ ρ c hc j hj xs fs hxs hsp
  unfold blockWfCand at hmkv
  -- the fields at the base frame
  have hfsR : SpineFit (consList xs ρ)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) fs := by
    obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
    have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
    rw [blockRecFdomsK, ← hxs] at h2
    exact (spineFit_liftDomsK (K := rs.length) _ _ _).mp h2
  obtain ⟨-, -, hfrF, -⟩ := blockRuleFrameAt_rows (pp := p) (blockRuleCtorOf_eq hr hcA)
  have hNb : (xs ++ fs).length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hxs', hfsl]
  have hkeyAt : ∀ key ∈ (blockRuleFrameAt p rs c j).ihKeys, ∃ q,
      q < (blockRuleFrameAt p rs c j).nR ∧ (blockRuleFrameAt p rs c j).ihKeys[q]? = some key := by
    intro key hkm
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hkm
    exact ⟨q, hq, by rw [List.getElem?_eq_getElem hq, hqe]⟩
  rw [blockRuleIhsRunAV_eq_ihsAt]
  refine blockRecIhvAt_eq_fit (N := (xs ++ fs).length) hxs' (by rw [hfsl, hfrF]) rfl
    (fun key hkm => ?_) (fun key hkm => ?_) (fun key hkm => ?_)
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    exact hc'K
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, -, -, -, -, -, -, -, -, hDB, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro l hl
    rw [hNb]
    exact DomsBelow.getD_below l hDB hl
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, -, -, -, -, hEB, hFB, -, -, -, -,
      hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro bs hbs
    dsimp only at hbs ⊢
    obtain ⟨hbsC, hspC, hfap, -⟩ := hframe ρ xs fs hpre hfsR bs hbs
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length := by
      rw [hbs.length_eq, List.length_map]
    -- the chain readings of the call's arguments are the base ones
    have hchain : ∀ a : Nat → V, (blockKitEisA p rs mpC.base2.acval envC ψ c j fi
          ++ [blockKitFapA p rs c j fi]).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame rs.length a ρ))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ c j fi
          ++ [blockKitFapA p rs c j fi]).map (interp V (consList bs (consList (xs ++ fs) ρ))) := by
      intro a
      refine List.map_congr_left fun e he => (interp_leaf_chain rfl ?_).symm
      rw [hNb, hbl]
      rcases List.mem_append.mp he with he | he
      · exact hEB e he
      · rw [List.mem_singleton.mp he]; exact hFB
    rw [hchain]
    rw [List.map_append, List.map_singleton] at hspC ⊢
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    -- the call's argument is a predecessor
    unfold blockWfGraph blockWfCand
    refine (kitCandOf_fold_graph (tupOf := fun c is =>
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
        (p.toBlockShape.recTgtAt c) is) hℓ hxl' hspC ?_)
    rw [mem_tcPred, tagVal_tagged, tagVal_tagged, hmkv]
    refine ⟨?_, ?_⟩
    · have hsplit := blockWf_hsplit hM
        (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
        (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (fun c _ => by rw [blockRulePdomsAV, List.map_take])
        (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
        (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
      rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
      exact tagged_mem_unionSet hc'K hsplit.2.2.1 hsplit.2.2.2
    · rw [hfap]
      have hinj : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).inj ψ
          (p.toBlockShape.recTgtAt c) j fs
          = if (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).w ψ = 0
            then (pt : V) else inj j (mkTower (fs ++ [pt])) := rfl
      rw [hinj, if_neg hw]
      have hfiF : fi < (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
          (p.toBlockShape.recTgtAt c) ψ).getD j []).length := by rw [hnF]; exact hfiC
      have hat := (FitsFrom.at_pos hChain.1 fi hfiF).2
      rw [Nat.zero_add, if_pos hrss] at hat
      unfold BlockData.slotAt slotSet at hat
      have hfold := piTele_fold_tc hw hat (fitsS_teleOfFields.mpr hbsC)
      have hfmem : fs.getD fi pt ∈ fs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfsl]; exact hfiC)]
        exact List.getElem_mem _
      have htc := mem_tc_inj_mkTower j fs hfmem
      rcases hfold with h1 | h1
      · rw [h1]; exact htc
      · exact tc_trans h1 htc

end ChainWf

section IhFWf

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **REGIME WF's `hihF`, PRODUCED — at the NARROWED row** (`i ∈ d.idx …`,
the kit step's own `hi`, as `hspF` since RM53): the graph-built `ih`
values fit the pinned `ih` openers' domains (`blockRecIhdomsK`, whose
chain lift is the identity, `blockRuleCertsChain_eq`).  Per opener: the
tower over the moved telescope inhabits the Π-tower over the callee's
peeled conclusion `CihR` (`blockRecIhv_mem`), because `CihR` reads to
the motive at the call's argument (`blockRecCa_value` at the key's
peel, `blockRecMot_tagged`, `isOfW_tupW`) and that argument is a
predecessor (union by the callee's split, depth by the recursive
slot).  The witness `i ∈ d.idx …` pays the rule's field fit
(`blockKitSpF_run`), which the callee's split needs. -/
theorem blockWfIhF_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat) (ρ : Nat → V)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : d.w ψ ≠ 0) :
    (∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) ((p.toBlockShape.recTgtAt) c) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ tcPred (unionSet rs.length (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) (p.toBlockShape.recTgtAt) xs)
              (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt) xs))
            (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs
            ψ) (fun c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j) ((blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs c j fs g)) := by
  intro xs c hc hpar hpref j hj i fs hi hfit g hg
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  -- the rule's field fit, off the witness
  have hspF := blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ rs.length xs c hc
    hpar hpref j hj i fs hi hfit
  rw [blockRecFdomsK_eq_of_bounded hbnd hr hcA hrhs] at hspF
  obtain ⟨xs₁, fs₁, heq, h1, hfsR⟩ := spineFit_append_split hspF
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hpref.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hIlen : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  rw [(blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj rs.length).2.1]
  refine spineFit_of_getD (by rw [blockKitIhv_length, hIlen]) fun q hq => ?_
  rw [hIlen] at hq
  obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, hIget, -, hcon, -, -, -, -, -, -, -,
    hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
  -- the domain, past the `q` values already bound
  have htk : ((blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q).length
      = q := by
    rw [List.length_take, blockKitIhv_length]; omega
  rw [hIget]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q)
    (σ := consList (xs ++ fs) ρ)
    (mkPisAV (blockKitTlA p rs mpC.base2.acval envC ψ c j fi) CihR)
  rw [htk] at hcancel
  rw [hcancel]
  -- the value: the tower of the graph over the moved telescope
  have hval : (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).getD q pt
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
          (consList (xs ++ fs) ρ) [] (blockKitTlA p rs mpC.base2.acval envC ψ c j fi)
          (fun _ τ => app g (tagged c'
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
              (p.toBlockShape.recTgtAt c')
              ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map (interp V τ)))
            (interp V τ (blockKitFapA p rs c j fi)))) := by
    rw [blockKitIhv, blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, hkeyE]
    rfl
  rw [hval]
  obtain ⟨-, -, -, -, -, -, -, hpw⟩ := blockRuleFrameAt_rows (pp := p) hct
  refine blockRecIhv_mem (V := V) (c' := c')
    (tup := fun c'' is => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
      (p.toBlockShape.recTgtAt c'') is) hℓ (fun dd hdd => ?_) (fun bs hbs => ?_)
  · unfold blockKitTlA at hdd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hdd
    rw [he, mem_rebit hd', hpw]
    exact (pwBit_zeronessOf ψ _).symm
  · obtain ⟨hbsC, hspC, hfap, -⟩ := hframe ρ xs fs hpref hfsR bs hbs
    rw [List.map_append, List.map_singleton] at hspC
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    have hfsl : fs.length = cA.2 := by
      rw [hfsR.length_eq, blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length := by
      rw [hbs.length_eq, List.length_map]
    -- the callee's type and its split at the call's spine
    have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
    have hconclB := (checkBlockRecK_tyBounds hμ mpC h hr' ψ).2
    have hrdsL := hspC.length_eq
    rw [List.length_map, List.length_append, List.length_append, List.length_map,
      List.length_singleton, hxl'] at hrdsL
    have hCa := blockRecCa_value (V := V) (ρ := ρ) (xs := xs) (fs := fs) (ihvals := bs)
      (is := (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
        (interp V (consList bs (consList (xs ++ fs) ρ))))
      (maj := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
      hcon hTyE (by rw [← hrdsL]; omega) rfl hconclB hxl' hfsl hbl rfl rfl
    rw [hCa]
    have hsplitA := blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ) c' hc'K _
      hspC
    rw [prefOf_split hxl', idxOf_split hxl'] at hsplitA
    obtain ⟨-, -, hparS, hidxS, -⟩ := hsplitA
    have hmemk' := (blockRecMajor_run hμ mpC h hmr hr' ψ).2.1
    have hmN' : p.toBlockShape.recTgtAt c'
        < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
      Nat.lt_of_lt_of_le hmemk' (Nat.le_add_right _ _)
    have hIok := hM.idxOk ψ _ ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
      ppsOf).satOfSpine hparS) _ hmN'
    have hisOf := isOfW_tupW hIok hidxS
    rw [blockMembers_IdsM_length hmr hmemk' ψ] at hisOf
    have hmot := blockRecMot_tagged (V := V) (K := rs.length) hc'K
      (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (uOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
      (nIdxOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
        ppsOf).nIdxAt (p.recTgtAt c')) (ρ := ρ) (xs := xs)
      (i := (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
        (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
          (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (x := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
    have hisOf' : isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt (p.recTgtAt c'))
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
          (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ))) := hisOf
    rw [hisOf'] at hmot
    rw [← hmot]
    refine hg _ ?_
    -- the call's argument is a predecessor
    rw [mem_tcPred, tagVal_tagged, tagVal_tagged]
    refine ⟨?_, ?_⟩
    · have hsplit := blockWf_hsplit hM
        (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
        (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (fun c _ => by rw [blockRulePdomsAV, List.map_take])
        (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
        (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
      rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
      exact tagged_mem_unionSet hc'K hsplit.2.2.1 hsplit.2.2.2
    · rw [hfap]
      have hinj : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).inj ψ
          (p.toBlockShape.recTgtAt c) j fs
          = if (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).w ψ = 0
            then (pt : V) else inj j (mkTower (fs ++ [pt])) := rfl
      rw [hinj, if_neg hw]
      have hfiF : fi < (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
          (p.toBlockShape.recTgtAt c) ψ).getD j []).length := by
        rw [← hfit.1.length_eq, hfsl]; exact hfiC
      have hat := (FitsFrom.at_pos hfit.1 fi hfiF).2
      rw [Nat.zero_add, if_pos hrss] at hat
      unfold BlockData.slotAt slotSet at hat
      have hfold := piTele_fold_tc hw hat (fitsS_teleOfFields.mpr hbsC)
      have hfmem : fs.getD fi pt ∈ fs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hfsl]; exact hfiC)]
        exact List.getElem_mem _
      have htc := mem_tc_inj_mkTower j fs hfmem
      rcases hfold with h1 | h1
      · rw [h1]; exact htc
      · exact tc_trans h1 htc

end IhFWf

section SqGuard

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **The counting guard at regime SQ, from the run** (`ℓ ≠ 0 ∧ w = 0`):
one recursor, its member the block's first, at most one constructor,
large elimination — `blockRecCounting_run` at the checked level. -/
theorem blockSqGuard_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {env₀ : Env} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
      p.toBlockShape cvTas)
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).w ψ = 0) :
    rs.length = 1 ∧ p.toBlockShape.recTgtAt 0 = 0 ∧
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt 0)).length ≤ 1 ∧
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).large = true := by
  obtain ⟨us, uOf, helim, hmemU, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hℓeq := blockRecHeadLevel_run h helim hmemU hruns
  obtain ⟨hpos, hklen⟩ := blockRecLen_run h
  obtain ⟨-, -, hlarge, hk1, -, hnc⟩ :=
    blockRecCounting_run h helim hmemU hruns ψ (by rw [hℓeq ψ]; exact hℓ) hw
  have hmemk := (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hpos) ψ).2.1
  have hk1d : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k = 1 := hk1
  rw [hk1d] at hmemk
  exact ⟨by rw [hklen, hk1], by omega,
    Nat.le_trans (blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
      (ppsOf := ppsOf) h 0 hpos).2 hnc, hlarge⟩

end SqGuard

section Sq

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **REGIME SQ's `hihChain`, PRODUCED** — `BlockSqOwed`'s row at the
pinned `ihv`/`ihs`: as the WF arm's, with the predecessor map
`blockSqPred`, whose SOURCE spine at the rule's own element IS the
rule's fields (`blockSqSrcRule_run`), so the call's field and
telescope spine witness the membership.  The counting guard's facts
(`hK1`, `hmem0`, `hct1`, `hlarge`: `blockRecCounting_run`, in scope
at the seam's SQ branch) state the one-member block. -/
theorem blockSqIhChain_run
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
    (ψ : Name → Nat) (ρ : Nat → V)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : d.w ψ = 0)
    (Rb0 : Nat → Nat → AnnotTerm) :
    (∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs c j fs
            (blockSqGraph (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ))
                  (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 (blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ)) ρ))))
 := by
  intro c hc j hj xs fs hxs hsp
  obtain rfl : c = 0 := by omega
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨hK1, hmem0, hct1, hlarge⟩ := blockSqGuard_run hμ h hmr ψ hℓ hw
  have h0 : 0 < rs.length := by rw [hK1]; exact Nat.one_pos
  have hr : rs[0]? = some rs[0] := List.getElem?_eq_getElem h0
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, hnF, hpre, hps, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxs hsp
  obtain ⟨rfl, hsrcEq⟩ := blockSqSrcRule_run hμ h hkLen hS hcore hmr hM rfl hctM h0 hmem0 hct1
    hlarge ψ hw 1 _ ρ 0 Nat.one_pos j hj xs fs hxs hsp
  unfold blockSqCand at hsrcEq
  -- the fields at the base frame
  have hfsR : SpineFit (consList xs ρ)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ 0 0) fs := by
    obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
    have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
    rw [blockRecFdomsK, ← hxs] at h2
    exact (spineFit_liftDomsK (K := 1) _ _ _).mp h2
  obtain ⟨-, -, hfrF, -⟩ := blockRuleFrameAt_rows (pp := p) (blockRuleCtorOf_eq hr hcA)
  have hNb : (xs ++ fs).length = p.toBlockShape.rulePrefixAt 0 + cA.2 := by
    rw [List.length_append, hxs', hfsl]
  have hkeyAt : ∀ key ∈ (blockRuleFrameAt p rs 0 0).ihKeys, ∃ q,
      q < (blockRuleFrameAt p rs 0 0).nR ∧ (blockRuleFrameAt p rs 0 0).ihKeys[q]? = some key := by
    intro key hkm
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hkm
    exact ⟨q, hq, by rw [List.getElem?_eq_getElem hq, hqe]⟩
  rw [blockRuleIhsRunAV_eq_ihsAt, hK1]
  refine blockRecIhvAt_eq_fit (N := (xs ++ fs).length) hxs' (by rw [hfsl, hfrF]) rfl
    (fun key hkm => ?_) (fun key hkm => ?_) (fun key hkm => ?_)
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    rw [← hK1]; exact hc'K
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, -, -, -, -, -, -, -, -, hDB, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro l hl
    rw [hNb]
    exact DomsBelow.getD_below l hDB hl
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, -, -, -, -, hEB, hFB, -, -, -, -,
      hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro bs hbs
    dsimp only at hbs ⊢
    obtain ⟨hbsC, hspC, -, hesE⟩ := hframe ρ xs fs hpre hfsR bs hbs
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ 0 0 fi).length := by
      rw [hbs.length_eq, List.length_map]
    have hchain : ∀ a : Nat → V, (blockKitEisA p rs mpC.base2.acval envC ψ 0 0 fi
          ++ [blockKitFapA p rs 0 0 fi]).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame 1 a ρ))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ 0 0 fi
          ++ [blockKitFapA p rs 0 0 fi]).map (interp V (consList bs (consList (xs ++ fs) ρ))) := by
      intro a
      refine List.map_congr_left fun e he => (interp_leaf_chain rfl ?_).symm
      rw [hNb, hbl]
      rcases List.mem_append.mp he with he | he
      · exact hEB e he
      · rw [List.mem_singleton.mp he]; exact hFB
    rw [hchain]
    rw [List.map_append, List.map_singleton] at hspC ⊢
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    unfold blockSqGraph blockSqCand
    refine kitCandOf_fold_graph (tupOf := fun c is =>
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
        (p.toBlockShape.recTgtAt c) is) hℓ hxl' hspC ?_
    -- the call's argument is a predecessor of the SOURCE spine
    have hc'1 : c' < 1 := by rw [← hK1]; exact hc'K
    rw [blockSqPred, mem_sep]
    refine ⟨?_, fi, ?_, hrss, bs, ?_, ?_⟩
    · have hsplit := blockWf_hsplit hM
        (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
        (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (fun c _ => by rw [blockRulePdomsAV, List.map_take])
        (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
        (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
      rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
      exact tagged_mem_unionSet hc'1 hsplit.2.2.1 hsplit.2.2.2
    · rw [hnF]; exact hfiC
    · rw [blockSqSpine_tagged, hsrcEq]
      exact hbsC
    · rw [blockSqSpine_tagged, hsrcEq, tagIdx_tagged, ← htgt, hesE]
      rfl

end Sq

section IhFSq

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **REGIME SQ's `hihF`, PRODUCED — at the NARROWED row**: as the WF
arm's, with the predecessor map `blockSqPred`; the witness
`i ∈ d.idx …` pays both the rule's field fit (`blockKitSpF_run`) and
the subsingleton criterion at `i` (`blockChainFit_srcVals_zero`: the
fields ARE the source spine), which puts the call's argument in the
separated map. -/
theorem blockSqIhF_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat) (ρ : Nat → V)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : d.w ψ = 0) :
    (∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) ((p.toBlockShape.recTgtAt) c) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt) ((blockSqSrcs d ψ) 0)
              (unionSet 1 (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape
                rs ψ) (p.toBlockShape.recTgtAt) xs) (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt)
                xs))
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (blockRecIhdomsK 1 p mpC.base2.acval envC rs ψ c j) ((blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs c j fs g)) := by
  intro xs c hc hpar hpref j hj i fs hi hfit g hg
  have hc0 : c = 0 := by omega
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨hK1, hmem0, hct1, hlarge⟩ := blockSqGuard_run hμ h hmr ψ hℓ hw
  have hc : c < rs.length := by rw [hK1]; exact hc
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  -- the rule's field fit, off the witness
  have hspF := blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ 1 xs c hc
    hpar hpref j hj i fs hi hfit
  rw [blockRecFdomsK_eq_of_bounded hbnd hr hcA hrhs] at hspF
  obtain ⟨xs₁, fs₁, heq, h1, hfsR⟩ := spineFit_append_split hspF
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hpref.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  -- the subsingleton criterion: the fields ARE the source spine at `i`
  have hsrcI : fs = srcVals (isOfW
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt 0) ψ)
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt
        (p.toBlockShape.recTgtAt 0)) i)
      (blockSqSrcs (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ 0) := by
    subst hc0
    have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt 0))[j]? = some cA := by rw [hctM 0 _ hr]; exact hcA
    have hjl : j < ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt 0)).length := (List.getElem?_eq_some_iff.mp hcj).1
    obtain rfl : j = 0 := by omega
    have hmemk : p.toBlockShape.recTgtAt 0
        < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
      (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
    have hk0 : 0 < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk 0 cA hcj
    have hcf : BlockCtorFacts mpC.base2
        (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) p.lps
        (p.toBlockShape.recTgtAt 0) 0 cA := ⟨hfindC, hlpsC, blockCtorData_of_core hcore hcj⟩
    have hsrcs : blockSqSrcs (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ 0
        = srcList (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Ess
            (p.toBlockShape.recTgtAt 0) ψ).getD 0 [])
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
            (p.toBlockShape.recTgtAt 0) ψ).getD 0 []).length := by
      rw [hmem0]; rfl
    rw [hsrcs]
    obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
    refine blockChainFit_srcVals_zero hM hcj hcf hlarge hw
      (fun σ => ⟨fun hσ => ((hS.frames _ hmemk 0 cA hcj).1 ψ σ).mp
          (hS.paramsOf 0 hk0 ψ σ hσ _ hmemk),
        fun hσ => hS.paramsOf _ hmemk ψ σ (((hS.frames _ hmemk 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
      (blockMembers_IdsM_length hmr hmemk ψ)
      (by rw [List.length_take, hpref.length_eq, hpl]; exact Nat.min_eq_left hnP) hpar
      (fun l _ => by rw [← hN.2.2.2]; exact hN.2.1 _ 0 l)
      (Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)) hjl (lfpTuple_mem _ _ _ _)
      (TupleLe.refl _ _ _) hi hfit
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hIlen : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  rw [(blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj 1).2.1]
  refine spineFit_of_getD (by rw [blockKitIhv_length, hIlen]) fun q hq => ?_
  rw [hIlen] at hq
  obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, hIget, -, hcon, -, -, -, -, -, -, -,
    hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
  -- the domain, past the `q` values already bound
  have htk : ((blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q).length
      = q := by
    rw [List.length_take, blockKitIhv_length]; omega
  rw [hIget]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q)
    (σ := consList (xs ++ fs) ρ)
    (mkPisAV (blockKitTlA p rs mpC.base2.acval envC ψ c j fi) CihR)
  rw [htk] at hcancel
  rw [hcancel]
  -- the value: the tower of the graph over the moved telescope
  have hval : (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).getD q pt
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
          (consList (xs ++ fs) ρ) [] (blockKitTlA p rs mpC.base2.acval envC ψ c j fi)
          (fun _ τ => app g (tagged c'
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
              (p.toBlockShape.recTgtAt c')
              ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map (interp V τ)))
            (interp V τ (blockKitFapA p rs c j fi)))) := by
    rw [blockKitIhv, blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, hkeyE]
    rfl
  rw [hval]
  obtain ⟨-, -, -, -, -, -, -, hpw⟩ := blockRuleFrameAt_rows (pp := p) hct
  refine blockRecIhv_mem (V := V) (c' := c')
    (tup := fun c'' is => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
      (p.toBlockShape.recTgtAt c'') is) hℓ (fun dd hdd => ?_) (fun bs hbs => ?_)
  · unfold blockKitTlA at hdd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hdd
    rw [he, mem_rebit hd', hpw]
    exact (pwBit_zeronessOf ψ _).symm
  · obtain ⟨hbsC, hspC, -, hesE⟩ := hframe ρ xs fs hpref hfsR bs hbs
    rw [List.map_append, List.map_singleton] at hspC
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    have hfsl : fs.length = cA.2 := by
      rw [hfsR.length_eq, blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length := by
      rw [hbs.length_eq, List.length_map]
    -- the callee's type and its split at the call's spine
    have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
    have hconclB := (checkBlockRecK_tyBounds hμ mpC h hr' ψ).2
    have hrdsL := hspC.length_eq
    rw [List.length_map, List.length_append, List.length_append, List.length_map,
      List.length_singleton, hxl'] at hrdsL
    have hCa := blockRecCa_value (V := V) (ρ := ρ) (xs := xs) (fs := fs) (ihvals := bs)
      (is := (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
        (interp V (consList bs (consList (xs ++ fs) ρ))))
      (maj := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
      hcon hTyE (by rw [← hrdsL]; omega) rfl hconclB hxl' hfsl hbl rfl rfl
    rw [hCa]
    have hsplitA := blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ) c' hc'K _
      hspC
    rw [prefOf_split hxl', idxOf_split hxl'] at hsplitA
    obtain ⟨-, -, hparS, hidxS, -⟩ := hsplitA
    have hmemk' := (blockRecMajor_run hμ mpC h hmr hr' ψ).2.1
    have hmN' : p.toBlockShape.recTgtAt c'
        < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
      Nat.lt_of_lt_of_le hmemk' (Nat.le_add_right _ _)
    have hIok := hM.idxOk ψ _ ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
      ppsOf).satOfSpine hparS) _ hmN'
    have hisOf := isOfW_tupW hIok hidxS
    rw [blockMembers_IdsM_length hmr hmemk' ψ] at hisOf
    have hc'1 : c' < 1 := by rw [← hK1]; exact hc'K
    have hmot := blockRecMot_tagged (V := V) (K := 1) hc'1
      (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (uOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
      (nIdxOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
        ppsOf).nIdxAt (p.recTgtAt c')) (ρ := ρ) (xs := xs)
      (i := (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
        (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
          (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (x := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
    have hisOf' : isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt (p.recTgtAt c'))
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
          (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ))) := hisOf
    rw [hisOf'] at hmot
    rw [← hmot]
    refine hg _ ?_
    -- the call's argument is a predecessor of the SOURCE spine
    have hj0 : j = 0 := by
      have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c))[j]? = some cA := by rw [hctM c _ hr]; exact hcA
      have := (List.getElem?_eq_some_iff.mp hcj).1
      rw [hc0] at this
      omega
    subst hc0
    subst hj0
    rw [blockSqPred, mem_sep]
    refine ⟨?_, fi, ?_, hrss, bs, ?_, ?_⟩
    · have hsplit := blockWf_hsplit hM
        (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
        (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (fun c _ => by rw [blockRulePdomsAV, List.map_take])
        (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
        (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
      rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
      exact tagged_mem_unionSet hc'1 hsplit.2.2.1 hsplit.2.2.2
    · rw [← hfit.1.length_eq, hfsl]; exact hfiC
    · rw [blockSqSpine_tagged, ← hsrcI]
      exact hbsC
    · rw [blockSqSpine_tagged, ← hsrcI, tagIdx_tagged, htgt, hesE]
      obtain rfl : c' = 0 := by omega
      rw [hmem0]
      rfl

end IhFSq

end ConLeche.Model
