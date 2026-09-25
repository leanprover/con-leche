module

public import ConLeche.Model.Inductives.TargetClassNodes
public import ConLeche.Model.Inductives.TargetNestKit
public import ConLeche.Model.Inductives.NestedRecStage

public section

/-!
# The node kit's core from a NODE PRESENTATION (lane NESTIND, session 17)

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
and the kit is `lfpNestKit`.  (Route B, `NestKitB`, is not usable here:
its `trans` without `TupleLe` fails at a `w = 0` node, where an
injection carries no fields.)

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
  (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)

/-- **A presentation of the recursor classes' nodes** at the prefix spine
`xs` (see the module docstring). -/
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
    Sat V ((Db b).params (ψb b)).reverse ρ ∧ (Db b).idx (ψb b) ρ = (Db b).idx (ψb b) (frb b)
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
  target that is a major lands at a node related to its class -/
  hcall : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    t ∈ˢ (Db b).idx (ψb b) (frb b) (mOf c b) →
    (Db b).HFits (ψb b) (frb b) ((Db b).carrier (ψb b) (frb b)) t (mOf c b) j fs →
    ∀ c' t' y, c' < (tgtRs out).length →
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
  {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}

namespace TgtNodePres

variable (P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs)

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
    ∃ c' t' y b', c' < (tgtRs out).length ∧ P.Rel c' b' ∧
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
      obtain ⟨-, c0, -, -, hm0, -, -, c', t', y, b', hc', hR', ht', hy', -, hL, rfl⟩ :=
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
@[expose] noncomputable def core : TgtNodeCore μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs where
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
    obtain ⟨hvU, hcall⟩ := mem_graphPredG.mp hv
    obtain ⟨c', hc', t', ht', y, hy, rfl⟩ := mem_unionSet.mp hvU
    have hf' : (P.Db b).HFits (P.ψb b) (P.frb b) ((P.Db b).carrier (P.ψb b) (P.frb b)) t
        (P.mOf c b) j fs := by
      have := hf
      change (P.Db b).HFits (P.ψb b) (P.frb b) ((P.cl b).carrier (P.frb b)) t (P.mOf c b) j fs
        at this
      rwa [P.cl_carrier] at this
    have ht0 : t ∈ˢ (P.Db b).idx (P.ψb b) (P.frb b) (P.mOf c b) := ht
    obtain ⟨b', hR', hL⟩ := P.hcall c b hc hR t j fs ht0 hf' c' t' y hc' ht' hy hcall
    refine ⟨c', t', y, hc', rfl, b', hR', mem_sep.mpr ⟨?_, c, hc, hR, rfl, ht0, hf',
      c', t', y, b', hc', hR', ht', hy, hcall, hL, rfl⟩⟩
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
    TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs where
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
GUARDED class at its prefix spine. -/
theorem tgtClassInd_of_pres
    (hP : ∀ xs : List V, ∃ P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs,
      ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c → ∃ b, P.Rel c b) :
    TgtClassInd μ F envC acval p formerTys out d Dc mc cvc ψ ρ := by
  classical
  intro xs Q hstep u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  by_cases hg : tgtClsG d acval envC p out ψ ρ xs c
  · obtain ⟨P, hex⟩ := hP xs
    exact P.core.K.ind_recNodesOn (tgtRs out).length
      (fun c => tgtClsG d acval envC p out ψ ρ xs c) P.core.Rel P.core.mOf
      (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
      (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
      (graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
        (tgtCall μ F (mkFEnv envC) p formerTys out
          acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs)
      hex P.core.hb P.core.hm P.core.hIs P.core.hCr P.core.hinj P.core.hnCt P.core.hfit
      P.core.hpredR Q hstep c hc hg t ht x hx
  · rw [tgtClsIs_unguarded hg] at ht
    exact absurd ht (not_mem_empty t)

end Build

/-! ## `NestedClassIndOwed` from the node presentations -/

/-- **THE TIE** (`hex`, ruling (i)): every GUARDED recursor class at the
prefix spine `xs` — outside majors included — is related to a node of
the presentation. -/
@[expose] def TgtNodeHex {μ : CheckMode} {F : Nat} {envC : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape} {formerTys : List Expr}
    {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    (P : TgtNodePres μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs) : Prop :=
  ∀ c, c < (tgtRs out).length → tgtClsG d acval envC p out ψ ρ xs c → ∃ b, P.Rel c b

/-- **OWED — a node presentation and its tie at every nested context and
prefix spine** (ruling (i)): the presentation (the nodes' clauses,
frames, `trans` and calls, and the class tie) is NESTIND's; the tie's
covering (`TgtNodeHex`: every guarded class, outside majors included, is
visited by a node of the block's positivity derivation) is what ruling
(i)'s walk supplies. -/
@[expose] def NestedClassNodesOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) (nodesR : List ConLeche.NestKey),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR →
    ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
        ∃ P : TgtNodePres μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type))
          out dR Dc mc cvc ψ ρ xs, TgtNodeHex P

/-- **`NestedClassIndOwed` from the node presentations.** -/
theorem nestedClassIndOwed_of_nodes {μ : CheckMode} {F : Nat} {block : List ConstantInfo}
    (h : NestedClassNodesOwed V μ F block) : NestedClassIndOwed V μ F block :=
  fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx Dc mc cvc hcls hsel ψ ρ =>
    tgtClassInd_of_pres
      (h envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx Dc mc cvc hcls hsel ψ ρ)

end ConLeche.Model
