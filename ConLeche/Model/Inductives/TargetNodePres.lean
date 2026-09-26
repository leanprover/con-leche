module

public import ConLeche.Model.Inductives.TargetClassNodes
public import ConLeche.Model.Inductives.TargetNestKit
public import ConLeche.Model.Inductives.TargetRank

public section

/-!
# The node kit's core from a NODE PRESENTATION

`TgtNodeCore` (`TargetClassNodes.lean`) asks an induction over node
majors (`NestNodeInd`) together with a class→node relation along which
the recursor classes' data are the nodes' and the recursor's calls land
at related nodes.  This module builds that core from a PRESENTATION of
the nodes as recorded lfp clauses (`TgtNodePres`), whose fields are the
facts about the nodes one by one — the recursor-side plumbing (the
predecessor set, the kit, the transport of the class data) is done here,
once:

* the nodes: `nC` recorded clauses `Db b` at level assignments `ψb b`,
  TRUE frames `frb b`, depths `dp b`, admissible frames `Adm`
  (`lfpNestKit`'s data and its `hcl`/`hAdm`/`trans`/`top`: `trans` is
  positivity at the instantiation, `KeyPos` at a derived node, the
  clause's `fitsMono` at the block's own);
* the class tie, SEMANTIC: at a related pair `Rel c b` the class's
  clause, level assignment, frame and component are the node's
  (`tgtClsD`/`tgtClsψ`/`tgtClsFr`/`tgtClsM`), and the class's guard holds;
* the calls, at a related pair and a TRUE decoding, one callee node per
  call target (`hcall`): a node `b'` related to the callee's class at
  which the target lands, at EVERY admissible visit of the caller —
  its own group (`b' = b`, the target in the visit's hole tuple), an
  enclosing node (`G`), or a deeper node at an admissible frame
  (`NodeLands`, the kit's `calls` disjunction).

The predecessors of a node decoding are then DEFINED as the related
classes' call targets, each at its chosen callee node (`TgtNodePres.pred`),
and the kit is `lfpNestKit`.

`TgtNodePres.core` — the core.  `tgtClassInd_of_pres` — `TgtClassInd`
from presentations whose relation covers every GUARDED class (an
unguarded class has no major: its index set is empty).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

/-- **A call target lands at node `b'`** from node `b`'s decoding
`(m, t, j, fs)`: at every admissible visit `(G, ρ)` of `b` and every hole
tuple `Y` the fields fit at, the target `y` (component `m'`, index `t'`)
is in `Y` (`b' = b`, the own group), satisfies `G` (an enclosing node),
or lies in a deeper node's class at an admissible frame of it, the
caller's tuple added to the hypotheses. -/
@[expose] def NodeLands (nC : Nat) (Db : Nat → LfpDatum V) (ψb : Nat → Name → Nat)
    (frb : Nat → Nat → V) (dp : Nat → Nat)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop)
    (b m : Nat) (t : V) (j : Nat) (fs : List V) (b' m' : Nat) (t' y : V) : Prop :=
  ∀ G ρ, Adm b G ρ → ∀ Y,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
    (Db b).HFits (ψb b) ρ Y t m j fs →
    (b' = b ∧ y ∈ˢ app (Y m') t') ∨ G b' m' t' y ∨
      (dp b < dp b' ∧ b' < nC ∧ ∃ ρ', Adm b' (addOwn G b (Db b).N ((Db b).idx (ψb b) (frb b)) Y) ρ' ∧
        y ∈ˢ app ((lfpSClause (Db b') (ψb b') ((Db b').idx (ψb b') (frb b'))).carrier
          ρ' m') t')

section Pres

variable (μ : CheckMode) (F : Nat) (envC : Env)
  (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
  (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
  (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) (S : Nat → Prop)

/-- **A presentation of the recursor classes' nodes** at the prefix spine
`xs` (see the module docstring), its calls read only into the classes `S`. -/
structure TgtNodePres where
  nC : Nat
  Db : Nat → LfpDatum V
  ψb : Nat → Name → Nat
  frb : Nat → Nat → V
  dp : Nat → Nat
  Dd : Nat
  hD : ∀ b, b < nC → dp b < Dd
  Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop
  hcl : ∀ b, b < nC → LfpClause acval (Db b)
  hAdm : ∀ b, b < nC → ∀ G ρ, Adm b G ρ →
    Sat V ((Db b).params (ψb b)).reverse ρ ∧
      ∀ c, c < (Db b).N → (Db b).idx (ψb b) ρ c = (Db b).idx (ψb b) (frb b) c
  top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
      t ∈ˢ (Db b').idx (ψb b') (frb b') c →
      y ∈ˢ app ((Db b').carrier (ψb b') (frb b') c) t → G b' c t y) →
    Adm b G (frb b)
  /-- **the tie to the true frame** (positivity at the instantiation):
  at an admissible frame whose hypotheses hold of true elements, a spine
  fitting at holes below the true carrier fits at the true frame -/
  trans : ∀ b, b < nC → ∀ G,
    (∀ b' c t y, G b' c t y →
      y ∈ˢ app ((lfpSClause (Db b') (ψb b') ((Db b').idx (ψb b') (frb b'))).carrier
        (frb b') c) t) →
    ∀ ρ, Adm b G ρ → ∀ Y,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
    TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) Y ((Db b).carrier (ψb b) (frb b)) →
    ∀ t c j fs, c < (Db b).N → (Db b).HFits (ψb b) ρ Y t c j fs →
      (Db b).HFits (ψb b) (frb b) ((Db b).carrier (ψb b) (frb b)) t c j fs
  /-- the class → node relation -/
  Rel : Nat → Nat → Prop
  mOf : Nat → Nat → Nat
  hb : ∀ c b, c < (tgtRs out).length → Rel c b → b < nC
  hm : ∀ c b, c < (tgtRs out).length → Rel c b → mOf c b < (Db b).N
  /-- the class tie: at a related pair the class's data are the node's -/
  hDb : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsD d Dc out c = Db b
  hψb : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsψ cvc out ψ c = ψb b
  hfr : ∀ c b, c < (tgtRs out).length → Rel c b →
    tgtClsFr d acval envC p out ψ ρ xs c = frb b
  hmc : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsM mc p out c = mOf c b
  hG : ∀ c b, c < (tgtRs out).length → Rel c b → tgtClsG d acval envC p out ψ ρ xs c
  hnCt : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    (Db b).HFits (ψb b) (frb b) ((Db b).carrier (ψb b) (frb b)) t (mOf c b) j fs →
      j < blockRecNCt (tgtRs out) c
  /-- **the calls**: at a related pair and a true decoding, every call
  target that is a major of a class in `S` lands at a node related to
  its class -/
  hcall : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    t ∈ˢ (Db b).idx (ψb b) (frb b) (mOf c b) →
    (Db b).HFits (ψb b) (frb b) ((Db b).carrier (ψb b) (frb b)) t (mOf c b) j fs →
    ∀ c' t' y, c' < (tgtRs out).length → S c' →
      t' ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c' →
      y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c') t' →
      tgtCall μ F (mkFEnv envC) p formerTys out acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ
        xs c j fs (tagged c' t' y) →
      ∃ b', Rel c' b' ∧
        NodeLands nC Db ψb frb dp Adm b (mOf c b) t j fs b' (mOf c' b') t' y

end Pres

section Build

variable {μ : CheckMode} {F : Nat} {envC : Env}
  {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape} {formerTys : List Expr}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {S : Nat → Prop}

namespace TgtNodePres

variable (P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs S)

/-- The presentation's clause at node `b`. -/
@[expose] noncomputable def cl (b : Nat) : SClause V (Nat → V) :=
  lfpSClause (P.Db b) (P.ψb b) ((P.Db b).idx (P.ψb b) (P.frb b))

theorem cl_carrier (b : Nat) : (P.cl b).carrier (P.frb b) = (P.Db b).carrier (P.ψb b) (P.frb b) :=
  lfpSClause_carrier rfl

/-- The class tie, read at the class data. -/
theorem cls_eq {c b : Nat} (hc : c < (tgtRs out).length) (hR : P.Rel c b) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c
        = (P.Db b).idx (P.ψb b) (P.frb b) (P.mOf c b) ∧
      tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c
        = (P.Db b).carrier (P.ψb b) (P.frb b) (P.mOf c b) ∧
      tgtClsInj d Dc mc cvc p out ψ c = (P.Db b).inj (P.ψb b) (P.mOf c b) ∧
      (∀ t j fs, tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs c t j fs ↔
        (P.Db b).HFits (P.ψb b) (P.frb b) ((P.Db b).carrier (P.ψb b) (P.frb b)) t
          (P.mOf c b) j fs) := by
  classical
  have hD := P.hDb c b hc hR
  have hψ := P.hψb c b hc hR
  have hf := P.hfr c b hc hR
  have hm := P.hmc c b hc hR
  have hg := P.hG c b hc hR
  refine ⟨?_, ?_, ?_, fun t j fs => ?_⟩
  · simp only [tgtClsIs, if_pos hg, hD, hψ, hf, hm]
  · simp only [tgtClsCr, hD, hψ, hf, hm]
  · simp only [tgtClsInj, hD, hψ, hm]
  · simp only [tgtClsFit, hD, hψ, hf, hm]

/-- A preliminary kit (no predecessors): its majors `U` depend only on
the nodes. -/
@[expose] noncomputable def kit0 : NestKit V (Nat → V) :=
  lfpNestKit (acval := acval) P.nC P.Db P.ψb P.frb P.dp P.Dd P.hD P.Adm (fun _ => empty)
    P.hcl P.hAdm P.trans (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ u hu => absurd hu (not_mem_empty u))
    P.top

/-- **The predecessors of a node decoding**: the call targets of the
related classes' true decodings, each at its callee node. -/
@[expose] noncomputable def pred (e : NDec V) : V :=
  sep P.kit0.U fun u => ∃ c, c < (tgtRs out).length ∧ P.Rel c e.cls ∧ P.mOf c e.cls = e.c ∧
    e.t ∈ˢ (P.Db e.cls).idx (P.ψb e.cls) (P.frb e.cls) e.c ∧
    (P.Db e.cls).HFits (P.ψb e.cls) (P.frb e.cls) ((P.Db e.cls).carrier (P.ψb e.cls)
      (P.frb e.cls)) e.t e.c e.j e.fs ∧
    ∃ c' t' y b', c' < (tgtRs out).length ∧ S c' ∧ P.Rel c' b' ∧
      t' ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c' ∧
      y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c') t' ∧
      tgtCall μ F (mkFEnv envC) p formerTys out acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ
        xs c e.j e.fs (tagged c' t' y) ∧
      NodeLands P.nC P.Db P.ψb P.frb P.dp P.Adm e.cls e.c e.t e.j e.fs b' (P.mOf c' b') t' y ∧
      u = nenc b' (P.mOf c' b') t' y

/-- **The node kit**, its predecessors `pred`. -/
@[expose] noncomputable def kit : NestKit V (Nat → V) :=
  lfpNestKit (acval := acval) P.nC P.Db P.ψb P.frb P.dp P.Dd P.hD P.Adm P.pred P.hcl P.hAdm
    P.trans (fun b _ G ρ' hρ Y hY c t j fs _ _ hf u hu => by
      obtain ⟨-, c0, -, -, hm0, -, -, c', t', y, b', hc', -, hR', ht', hy', -, hL, rfl⟩ :=
        mem_sep.mp hu
      have hb' := P.hb c' b' hc' hR'
      obtain ⟨hIs', -⟩ := P.cls_eq hc' hR'
      refine ⟨b', P.mOf c' b', t', y, hb', P.hm c' b' hc' hR', by rw [← hIs']; exact ht', rfl, ?_⟩
      rcases hL G ρ' hρ Y hY hf with h | h | ⟨hlt, -, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hlt, h⟩))
    P.top

/-- **The core.** -/
@[expose] noncomputable def core : TgtNodeCore μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs S where
  K := P.kit.toNodeInd
  Rel := P.Rel
  mOf := P.mOf
  hb := P.hb
  hm := P.hm
  hIs := fun c b hc hR => (P.cls_eq hc hR).1
  hCr := fun c b hc hR => by
    rw [(P.cls_eq hc hR).2.1]
    exact (P.cl_carrier b).symm ▸ rfl
  hinj := fun c b hc hR j fs => by rw [(P.cls_eq hc hR).2.2.1]; rfl
  hnCt := fun c b hc hR t j fs hf => P.hnCt c b hc hR t j fs (by
    have := hf
    change (P.Db b).HFits (P.ψb b) (P.frb b) ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs
      at this
    rwa [P.cl_carrier] at this)
  hfit := fun c b hc hR t j fs hf => ((P.cls_eq hc hR).2.2.2 t j fs).mpr (by
    have := hf
    change (P.Db b).HFits (P.ψb b) (P.frb b) ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs
      at this
    rwa [P.cl_carrier] at this)
  hpredR := fun c b hc hR t j fs ht hf v hv => by
    obtain ⟨hvU, hcall, hSv⟩ := mem_graphPredG.mp hv
    obtain ⟨c', hc', t', ht', y, hy, rfl⟩ := mem_unionSet.mp hvU
    have hSc' := hSv c' t' y rfl
    have hf' : (P.Db b).HFits (P.ψb b) (P.frb b) ((P.Db b).carrier (P.ψb b) (P.frb b)) t
        (P.mOf c b) j fs := by
      have := hf
      change (P.Db b).HFits (P.ψb b) (P.frb b) ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs
        at this
      rwa [P.cl_carrier] at this
    have ht0 : t ∈ˢ (P.Db b).idx (P.ψb b) (P.frb b) (P.mOf c b) := ht
    obtain ⟨b', hR', hL⟩ := P.hcall c b hc hR t j fs ht0 hf' c' t' y hc' hSc' ht' hy hcall
    refine ⟨c', t', y, hc', rfl, b', hR', mem_sep.mpr ⟨?_, c, hc, hR, rfl, ht0, hf',
      c', t', y, b', hc', hSc', hR', ht', hy, hcall, hL, rfl⟩⟩
    obtain ⟨hIs', hCr', -⟩ := P.cls_eq hc' hR'
    refine P.kit0.nenc_mem_U (P.hb c' b' hc' hR') (P.hm c' b' hc' hR') ?_ ?_
    · show t' ∈ˢ (P.Db b').idx (P.ψb b') (P.frb b') (P.mOf c' b')
      rw [← hIs']; exact ht'
    · show y ∈ˢ app ((P.cl b').carrier (P.frb b') (P.mOf c' b')) t'
      rw [P.cl_carrier, ← hCr']; exact hy

end TgtNodePres

/-- **The empty presentation**: no node, no related class (for a prefix
spine at which no class is guarded). -/
@[expose] def TgtNodePres.empty :
    TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs S where
  nC := 0
  Db := Dc
  ψb := fun _ => ψ
  frb := fun _ => ρ
  dp := fun _ => 0
  Dd := 0
  hD := fun _ h => absurd h (Nat.not_lt_zero _)
  Adm := fun _ _ _ => False
  hcl := fun _ h => absurd h (Nat.not_lt_zero _)
  hAdm := fun _ h => absurd h (Nat.not_lt_zero _)
  top := fun _ h => absurd h (Nat.not_lt_zero _)
  trans := fun _ h => absurd h (Nat.not_lt_zero _)
  Rel := fun _ _ => False
  mOf := fun _ _ => 0
  hb := fun _ _ _ h => h.elim
  hm := fun _ _ _ h => h.elim
  hDb := fun _ _ _ h => h.elim
  hψb := fun _ _ _ h => h.elim
  hfr := fun _ _ _ h => h.elim
  hmc := fun _ _ _ h => h.elim
  hG := fun _ _ _ h => h.elim
  hnCt := fun _ _ _ h => h.elim
  hcall := fun _ _ _ h => h.elim

/-- **An unguarded class has no major.** -/
theorem tgtClsIs_unguarded {c : Nat} (hg : ¬ tgtClsG d acval envC p out ψ ρ xs c) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c = empty := by
  classical
  simp only [tgtClsIs, if_neg hg]

/-- **`TgtClassInd` from node presentations** whose relation covers every
GUARDED class at its prefix spine (every call read: `S` everything). -/
theorem tgtClassInd_of_pres
    (hP : ∀ xs : List V, ∃ P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs
        (fun _ => True),
      ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c → ∃ b, P.Rel c b) :
    TgtClassInd μ F envC acval p formerTys out d Dc mc cvc ψ ρ := by
  classical
  intro xs Q hstep u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  by_cases hg : tgtClsG d acval envC p out ψ ρ xs c
  · obtain ⟨P, hex⟩ := hP xs
    refine P.core.K.ind_recNodesOn (tgtRs out).length
      (fun c => tgtClsG d acval envC p out ψ ρ xs c) P.core.Rel P.core.mOf
      (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
      (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
      (graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
        (tgtCallS μ F (mkFEnv envC) p formerTys out
          acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ (fun _ => True)) xs)
      hex P.core.hb P.core.hm P.core.hIs P.core.hCr P.core.hinj P.core.hnCt P.core.hfit
      P.core.hpredR Q (fun u hu ⟨e, hdec, hpe⟩ => hstep u hu ⟨e, hdec, fun v hv => ?_⟩)
      c hc hg t ht x hx
    obtain ⟨hvU, hcall⟩ := mem_graphPredG.mp hv
    exact hpe v (mem_graphPredG.mpr ⟨hvU, hcall, fun _ _ _ _ => trivial⟩)
  · rw [tgtClsIs_unguarded hg] at ht
    exact absurd ht (not_mem_empty t)

/-- **Derivations along the calls into a layer, from node presentations**
(DERCORE's `Der`, `TargetRank.lean`): at a presentation reading the calls
into `S` only, every element of a class of `S` related to a node has a
derivation along the calls into `S`. -/
theorem tgtDer_of_pres (P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs S)
    (hcallK : ∀ c j fs c' t' y', tgtCall μ F (mkFEnv envC) p formerTys out acval envC ψ
      (tgtClsTup d Dc mc cvc p out ψ) ρ xs c j fs (tagged c' t' y') → c' < (tgtRs out).length)
    {c : Nat} (hc : c < (tgtRs out).length) (hSc : S c) (hrel : ∃ b, P.Rel c b)
    {t y : V} (ht : t ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c)
    (hy : y ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c) t) :
    Der (Is := tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
      (Cr := tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (injX := tgtClsInj d Dc mc cvc p out ψ)
      (nCt := blockRecNCt (tgtRs out)) (K := (tgtRs out).length)
      (fit := tgtClsFit d Dc mc cvc acval envC p out ψ ρ)
      (call := tgtCall μ F (mkFEnv envC) p formerTys out acval envC ψ
        (tgtClsTup d Dc mc cvc p out ψ) ρ) xs S (tagged c t y) := by
  classical
  refine P.core.K.ind_recNodesOn (tgtRs out).length (fun c' => c' = c) P.core.Rel P.core.mOf
    (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
    (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
    (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
    (graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
      (tgtCallS μ F (mkFEnv envC) p formerTys out
        acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ S) xs)
    (fun c' _ h => h ▸ hrel) P.core.hb P.core.hm P.core.hIs P.core.hCr P.core.hinj
    P.core.hnCt P.core.hfit P.core.hpredR
    (fun u => ∀ c' t' y', u = tagged c' t' y' → S c' →
      Der (Is := tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (Cr := tgtClsCr d Dc mc cvc acval envC p out ψ ρ)
        (injX := tgtClsInj d Dc mc cvc p out ψ)
        (nCt := blockRecNCt (tgtRs out)) (K := (tgtRs out).length)
        (fit := tgtClsFit d Dc mc cvc acval envC p out ψ ρ)
        (call := tgtCall μ F (mkFEnv envC) p formerTys out acval envC ψ
          (tgtClsTup d Dc mc cvc p out ψ) ρ) xs S u)
    (fun u _ ⟨e, hdec, hpe⟩ c' t' y' hu hSc' => ?_) c hc rfl t ht y hy c t y rfl hSc
  obtain ⟨hc1, hj1, i1, hi1, hf1, rfl⟩ := hdec
  obtain ⟨rfl, rfl, hyeq⟩ := tagged_inj hu
  subst hyeq
  have hymem : tgtClsInj d Dc mc cvc p out ψ e.1 e.2.1 e.2.2 ∈ˢ
      app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs e.1) i1 := by
    obtain ⟨c2, -, t2, -, x2, hx2, heq⟩ := mem_unionSet.mp ‹_›
    obtain ⟨rfl, rfl, rfl⟩ := tagged_inj heq
    exact hx2
  refine Der.mk hc1 hSc' hi1 hymem hj1 hf1 fun c'' t'' y'' hS'' ht'' hy'' hcall => ?_
  have hc'' : c'' < (tgtRs out).length := hcallK _ _ _ _ _ _ hcall
  refine hpe _ (mem_graphPredG.mpr ⟨tagged_mem_unionSet hc'' ht'' hy'', hcall, ?_⟩) c'' t'' y''
    rfl hS''
  intro c3 t3 y3 h3
  obtain ⟨rfl, -, -⟩ := tagged_inj h3
  exact hS''

end Build

/-! ## The tie -/

/-- **THE TIE** (`hex`): every GUARDED recursor class at the
prefix spine `xs` — outside majors included — is related to a node of
the presentation. -/
@[expose] def TgtNodeHex {μ : CheckMode} {F : Nat} {envC : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape} {formerTys : List Expr}
    {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {S : Nat → Prop}
    (P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs S) : Prop :=
  ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c → ∃ b, P.Rel c b

end ConLeche.Model
