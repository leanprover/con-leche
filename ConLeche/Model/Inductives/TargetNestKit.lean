module

public import ConLeche.SetModel.NestRec
public import ConLeche.Model.Inductives.ClauseKit
public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The nested recursor's classes as LFP CLAUSES

The recursor model at a nested block (`graphRecPre_core`,
`BlockRecGraph.lean`) is over the recursor's CLASSES: a member of the
block, or a container at an instantiation (an outside major).  Charter
item 5: "the model uses nothing from an inductive but its lfp clause" —
so every class is presented by ONE recorded clause (`LfpClause`,
`Model/Annot/BlockLfp.lean`) at a level assignment and a parameter
frame, and this module turns clauses into the set-level kit
`NestKit` (`SetModel/NestRec.lean`) whose induction the recursor's
classes read (`NestNodeInd.ind_recNodesOn`, `SetModel/NestRecCls.lean`).

* `lfpSClause D ψ Is` (`ClauseKit.lean`) — the clause of `D` at `ψ` as a class presentation
  over parameter frames, its index sets pinned at `Is` (the TRUE
  frame's: a container instance's index telescope is hole-free — the
  walk's N2 — so it reads alike at every frame the induction visits);
  `lfpSClause_okAt` — the kit's `ok`, from the clause's `functor` and
  `fibre`; `lfpSClause_carrier` — its carrier is the datum's.
* `lfpNestKit` — the kit over clause classes, `ok` proved; the three
  premises that read the RUN (`trans`: positivity at the instantiation,
  `calls`: the rule's calls, `top`: the true frames' parameter
  readings) are the kit's own.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V} {ψ : Name → Nat}
  {Is : Nat → V} {ρp : Nat → V}

/-! ## The kit over clause classes -/

/-- **The nested kit over clause classes**: class `b < nC` is the
clause of `Db b` at `ψb b`, visited at admissible parameter frames
(`Adm`, which must satisfy the telescope and read the TRUE frame's
index sets, `hAdm`); its true frame is `frb b`.  `ok` is the clause's
(`lfpSClause_okAt`); `trans`, `calls` and `top` are the run's. -/
@[expose] noncomputable def lfpNestKit (nC : Nat) (Db : Nat → LfpDatum V)
    (ψb : Nat → Name → Nat) (frb : Nat → Nat → V) (dp : Nat → Nat) (Dd : Nat)
    (hD : ∀ b, b < nC → dp b < Dd)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop)
    (pred : NDec V → V)
    (hcl : ∀ b, b < nC → LfpClause acval (Db b))
    (hAdm : ∀ b, b < nC → ∀ G ρ, Adm b G ρ →
      Sat V ((Db b).params (ψb b)).reverse ρ ∧
        ∀ c, c < (Db b).N → (Db b).idx (ψb b) ρ c = (Db b).idx (ψb b) (frb b) c)
    (trans : ∀ b, b < nC → ∀ G,
      (∀ b' c t y, G b' c t y →
        y ∈ˢ app ((lfpSClause (Db b') (ψb b') ((Db b').idx (ψb b') (frb b'))).carrier
          (frb b') c) t) →
      ∀ ρ, Adm b G ρ → ∀ Y,
      InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
      TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) Y ((Db b).carrier (ψb b) (frb b)) →
      ∀ t c j fs, c < (Db b).N → (Db b).HFits (ψb b) ρ Y t c j fs →
        (Db b).HFits (ψb b) (frb b) ((Db b).carrier (ψb b) (frb b)) t c j fs)
    (calls : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → ∀ Y,
      InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
      ∀ c t j fs, c < (Db b).N → t ∈ˢ (Db b).idx (ψb b) (frb b) c →
      (Db b).HFits (ψb b) ρ Y t c j fs →
      ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (Db b').N ∧
        t' ∈ˢ (Db b').idx (ψb b') (frb b') c' ∧ u = nenc b' c' t' y ∧
        ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
          (dp b < dp b' ∧ ∃ ρ', Adm b' (addOwn G b (Db b).N ((Db b).idx (ψb b) (frb b)) Y) ρ' ∧
            y ∈ˢ app ((lfpSClause (Db b') (ψb b') ((Db b').idx (ψb b') (frb b'))).carrier
              ρ' c') t')))
    (top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
        t ∈ˢ (Db b').idx (ψb b') (frb b') c →
        y ∈ˢ app ((Db b').carrier (ψb b') (frb b') c) t → G b' c t y) →
      Adm b G (frb b)) :
    NestKit V (Nat → V) where
  nC := nC
  cl := fun b => lfpSClause (Db b) (ψb b) ((Db b).idx (ψb b) (frb b))
  fr := frb
  dp := dp
  D := Dd
  hD := hD
  Adm := Adm
  pred := pred
  ok := fun b hb G ρ hρ =>
    lfpSClause_okAt (hcl b hb) (hAdm b hb G ρ hρ).1 (hAdm b hb G ρ hρ).2
  trans := fun b hb G hG ρ hρ Y hY hle t c j fs hc hf => by
    have hle' : TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) Y
        ((Db b).carrier (ψb b) (frb b)) := hle
    show (Db b).HFits (ψb b) (frb b)
      ((lfpSClause (Db b) (ψb b) ((Db b).idx (ψb b) (frb b))).carrier (frb b)) t c j fs
    rw [lfpSClause_carrier rfl]
    exact trans b hb G hG ρ hρ Y hY hle' t c j fs hc hf
  calls := fun b hb G ρ hρ Y hY c t j fs hc ht hf u hu =>
    calls b hb G ρ hρ Y hY c t j fs hc ht hf u hu
  top := fun b hb G hG => top b hb G fun b' c t y hb' hdp hc ht hy =>
    hG b' c t y hb' hdp hc ht (by rw [lfpSClause_carrier rfl]; exact hy)

end ConLeche.Model
