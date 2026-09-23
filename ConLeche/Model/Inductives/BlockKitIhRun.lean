module

import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreHpre
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The graph kit's `ih` values — `ihv` pinned, one key's readings

The graph kit's step (`BlockRecGraph.lean`) reads the rule's residue at
`ih` VALUES built from the recursion graph.  They are pinned here
(`blockKitIhv`): per key the λ-tower over the rule frame's MOVED field
telescope whose body is the graph at the call target the guarded call
names — `blockRecIhvAt` at exactly the per-key data the pinned `ih`
TERMS `blockRuleIhsRunAV` use, so the two are related verbatim
(`blockRecIhvAt_eq_fit`, §5).  §4 is one key's two readings (the
rule's and the block's), which both `ih` rows and the induction's link
consume; the last section is the counting guard's reading at `w = 0`.
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

/-! ## 4. ONE `ih` key, with its conclusion's PEEL

`blockRuleIhKey_run` (`BlockRuleGrading.lean`) states what the grading
and the typed tuple's fit read about an `ih` opener.  The kit's `hihF`
needs one more fact, the peel `BlockRuleConclAt` of the callee's
conclusion `CihR` — its VALUE (`blockRecCa_value`), since the ih value
there is the recursion GRAPH, not a member of the callee's type — and
`hihChain`/`hihF` both need the call's spine fitting the callee's
binder data at the rule's MOVED readings.  The key lemma exports both
(`hcon`, the moved fit); this lemma only restates them at the kit's
spelling (`blockKitTlA`/`blockKitEisA`/`blockKitFapA`) and adds the
moved telescope's bounds. -/

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
  obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, -, hIget, -, hTlB, hEisB, hrPc', hrss, htgtc', hIB,
    hreadQ, eT, eE, hm, htlE, hEisE, hcon, hcallF⟩ :=
    blockRuleIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hq
  -- the kit's spelling of the per-key data
  obtain ⟨-, -, hFr, -⟩ := blockRuleFrameAt_rows (pp := p) (blockRuleCtorOf_eq hr hcA)
  have hTlA : blockKitTlA p rs mpC.base2.acval envC ψ j i fi
      = ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
            ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi [])) := by
    rw [blockKitTlA, hFr, eT]
  have hEisA : blockKitEisA p rs mpC.base2.acval envC ψ j i fi
      = ((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) := by
    rw [blockKitEisA, hm, hFr, eE]
  have hFapA : blockKitFapA p rs j i fi
      = AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
          + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) := by
    rw [blockKitFapA, hm, hFr, Nat.add_zero]
  have hTlLen : (blockKitTlA p rs mpC.base2.acval envC ψ j i fi).length
      = ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hTlA, ihTeleAtR_length, rebit_length]
  -- the bounds, at the moved spelling
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hnP := TE.nP_le
  have hDB : DomsBelow (p.toBlockShape.rulePrefixAt j + cA.2)
      (blockKitTlA p rs mpC.base2.acval envC ψ j i fi) := by
    have hD := ihTeleAtGo_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt j - p.nP)
      (i := fi) (l := 0) (K := p.nP + fi) (k := 0)
      (tl := rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
        ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []))
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
      (l := 0) (m := ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) (hEisB E hE)
    rw [hTlLen]
    rw [show p.nP + fi + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length
        + (cA.2 - fi + 0) + (p.toBlockShape.rulePrefixAt j - p.nP)
      = p.toBlockShape.rulePrefixAt j + cA.2
        + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length from by omega] at hEb
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
  refine ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgtc', by rw [hIget, hTlA], hIB,
    by rw [hTlLen, hEisA, hFapA]; exact hcon, hDB, hEB, hFB, hreadQ,
    by rw [htlE]; exact eT, by rw [hEisE]; exact eE, by rw [htlE]; exact hm, ?_⟩
  intro σ xs fs hxs hfs bs hbsM
  obtain ⟨-, -, -, hconv, hcall⟩ := hcallF σ xs fs hxs hfs
  rw [hTlA] at hbsM
  have hbsC := hconv bs hbsM
  obtain ⟨-, -, -, hfitB, hmk, hes, -⟩ := hcall bs hbsC
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
    blockRuleIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hl
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

/-- **The `ih` value at a key IS the `ih` term's reading, with the call
obligation at FITTING telescope spines only** — the one `hcall` the run can pay: off the telescope the
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

section CountingGuard

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **The counting guard at `ℓ ≠ 0 ∧ w = 0`, from the run**: one
recursor, its member the block's first, at most one constructor, large
elimination — `blockRecCounting_run` at the checked level.  The graph
kit's `huniq` reads it at a `Prop` block with a large motive. -/
theorem blockCountingGuard_run (hμ : μ.verifiedChecks = true)
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
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  obtain ⟨hpos, hklen⟩ := blockRecLen_run h
  obtain ⟨-, -, hlarge, hk1, -, hnc⟩ :=
    blockRecCounting_run h hruns ψ hℓ hw
  have hmemk := (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hpos) ψ).2.1
  have hk1d : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k = 1 := hk1
  rw [hk1d] at hmemk
  exact ⟨by rw [hklen, hk1], by omega,
    Nat.le_trans (blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
      (ppsOf := ppsOf) h 0 hpos).2 hnc, hlarge⟩

end CountingGuard

end ConLeche.Model
