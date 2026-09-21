module

public import ConLeche.Model.Inductives.BlockRecRule
public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Semantics.Tower.BlockRecKitI
public import ConLeche.Semantics.Tower.BlockRecIndI
import ConLeche.SetModel.WfRec
public import ConLeche.SetTheory.Derive.TransClosure

public section

/-!
# The three regimes, wired to the block's representation (task #315, M5)

`blockRecStaged_of`'s `hrecP` is, through `blockRecAV_iota`
(`Semantics/Tower/BlockRecI.lean`), the family premise
`BlockRecPre`.  Its three fields are owed by three different tiers,
and this file is where they meet:

| field | who proves it |
|---|---|
| `hTy` | O-2 — the recursor's stored type reads to `mkPisAV rds concl` and the reading is a set of the family's level (`BlockRecRead.lean`) |
| `hEq` | the ι equations' grading, `hEq_iotaEqsAV_of` at the rule data |
| `hCand` | **the recursion theorem** — one of the three regimes |

and the regimes are:

* **WF** (`w ≠ 0 ∧ ℓ ≠ 0`) — `famCand_hCand` at a `WfRecKit` family:
  the recursion is over the tagged union of the classes' carriers,
  ∈-smaller elements are the predecessors, and the depth obligation is
  `blockData_mkDepth` below — the block's injections put a
  constructor's fields ∈-below the constructed value;
* **IND** (`ℓ = 0`) — `indCand_hCand`: the candidate is the point and
  the regime is the induction principle plus `ResidueOk` at every
  fitting spine;
* **SQ** (`w = 0 ∧ ℓ ≠ 0`) — `famCand_hCand` at the squash kit, whose
  step is the residue read at the SOURCE spine (`BlockRecSqI.lean`).

Nothing here re-proves a regime: each is a theorem of the semantics
tier, and what this file adds is the *dispatch* and the one fact about
the representation the WF regime needs that `BlockModelAt` does not
carry.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `mkDepth` — the WF regime's depth obligation, at the block's
representation

`BlockModelAt` carries `mkZero` and `mkInj` but no depth law, because
no earlier consumer needed one: the lfp route pins the predecessor set
by `mkInj`, and the ∈-recursion does not.  At the uniform tuple
encoding the law is one rewrite of `mem_tc_inj_mkTower`
(`SetModel/WfRec.lean`), off the SAME `hinj` hypothesis
`blockModelAt_of_stages` already takes. -/

/-- **The constructor's fields are ∈-below the constructed value.**
The WF regime's encoding-depth obligation at the block's injections. -/
theorem blockData_mkDepth {d : BlockData V}
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0) (c j : Nat) (fs : List V) {a : V} (ha : a ∈ fs) :
    a ∈ˢ ConLeche.SetTheory.tc (d.inj ψ c j fs) := by
  rw [hinj, if_neg hw]
  exact mem_tc_inj_mkTower j fs ha

/-- The reflexive field's half: the image of a graph field at an
argument is ∈-below the constructed value. -/
theorem blockData_mkDepth_app {d : BlockData V}
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0) (c j : Nat) (fs : List V) {g : V} (hg : g ∈ fs)
    {A x : V} {B : V → V} (hpi : g ∈ˢ piSet A B) (hx : x ∈ˢ A) :
    app g x ∈ˢ ConLeche.SetTheory.tc (d.inj ψ c j fs) := by
  rw [hinj, if_neg hw]
  exact app_field_mem_tc hg hpi hx

/-! ## `BlockRecPre`, assembled -/

section Pre

variable {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **The family premise, assembled** — the shape `blockRecAV_iota`
consumes, with its three fields in the form their owners prove them:
the types' reading (O-2), the ι equations' grading
(`hEq_iotaEqsAV_of`), and the recursion theorem (a regime). -/
theorem blockRecPre_of
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (hCand : ∃ cand : Nat → V, (∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K cand ρ) e) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ where
  hTy := hTy
  hEq := hEq_iotaEqsAV_of hwd
  hCand := hCand

end Pre

/-! ## The three regimes, as the dispatch reads them

Each is `blockRecPre_of` at the `hCand` its own tier proves.  The
regimes are DISJOINT and EXHAUSTIVE on the pair `(w, ℓ)`: `ℓ = 0` is
IND (every conclusion is a proposition — D-d makes it one bit for the
family), `ℓ ≠ 0 ∧ w ≠ 0` is WF, and `ℓ ≠ 0 ∧ w = 0` is SQ, where the
guard leaves a lone non-nested block with at most one constructor
under the subsingleton criterion. -/

section Regimes

variable {ℓ s K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **Regimes WF and SQ**: the candidate is the class kit's recursor,
and `ResidueOk` at the rule's own spine is the kit's step
(`famCand_hCand`'s `hst`). -/
theorem blockRecPre_kit
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)])))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st
          (tagged c
            (D.tupOf c ((es c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)))
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c ((es c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))
              (consList (xs ++ fs) (chainFrame K (famCand D) ρ))) (Rb c j)) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ :=
  blockRecPre_of hTy hwd (famCand_hCand D hℓ hTyE hbits hpl hrule hst)

/-- **Regime IND** (`ℓ = 0`): the candidate is the point, and the two
obligations are the induction principle and `ResidueOk` at `ℓ = 0` —
the residue's reading is a member of a truth value. -/
theorem blockRecPre_ind
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (hind : ∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c))
    (hres : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∃ T : V, T ∈ˢ (univZero : V) ∧
        interp V
            (consList
              ((ihs c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
              (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Rb c j) ∈ˢ T) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ :=
  blockRecPre_of hTy hwd (indCand_hCand hind hres)

/-- **`ResidueOk` IS regime IND's `hres`** at `ℓ = 0`: a residue that
is graded and lands in a truth value is what `indCand_hCand` asks
for. -/
theorem hres_of_residueOk {c j : Nat} {xs fs : List V} {T : V}
    (hT : T ∈ˢ (univZero : V))
    (h : ResidueOk V (Rb c j)
      ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
      (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) T) :
    ∃ T : V, T ∈ˢ (univZero : V) ∧
      interp V
          (consList
            ((ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Rb c j) ∈ˢ T :=
  ⟨T, hT, h.2⟩

end Regimes

end ConLeche.Model
