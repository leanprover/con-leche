module

public import ConLeche.SetModel.ClassKit
public import ConLeche.Model.Inductives.TargetNestKit
public import ConLeche.Model.Inductives.ClassRecKit

public section

/-!
# The induction over the majors at the CLASSES: the class kit, wired (P3c)

`graphRecPre_gen` (`ClassRecKit.lean`) builds the recursor model at the
GENERATED recursor family; three of its premises are not the generator's:
the induction over the majors (`hind`), the kit's uniqueness row
(`huniq`) and the conclusion's typing (`hconclTy`).  This module
produces them.

**`hind` — one node per class** (PROOFPLAN §4.2).  A `ClassPres` presents
the recursor classes at a prefix spine `xs` as recorded lfp clauses: node
`b` is the clause of `Db b` at the level assignment `ψb b` and the TRUE
frame `frb b` (a container's key frame, or the member block's parameter
frame), visited at the admissible frames `Adm b G ρ`.  Class `c` has
exactly ONE node `nd c` and is its component `mOf c` — a class group
(a mutual container at one key) shares its node, one component per class.
The presentation's fields are the class side's facts, each in the shape
PROOFPLAN §2.4–2.5 gives them:

* `hcl`/`hAdm` — the node's recorded clause, and admissible frames
  satisfying its parameter telescope with the true index sets (R2: the
  index telescope is member-free);
* `fitMono`/`hAdmLe` — T5's `classMono` at the FIT (the `hwalk` of
  `carrier_le_on_group'`): along a per-node frame order `Le b` a fit
  grows with the frame and the tuple, and an admissible frame whose
  hypotheses are true lies below the true frame.  Together they are the
  kit's `trans`;
* `top` — the true frame is admissible for the deeper true classes;
* the class tie (T3′ at the generated family: `hIs`/`hCr`/`hinj`/`hfit`)
  — the generated class's index set, carrier, injection and decoding fit
  are its node's at the true frame, component `mOf c`;
* `hcall` — a generated `ih`'s call lands (`ClassLands`): in the caller's
  own group (the hole tuple), in the enclosing hypotheses (a free hole),
  or in a DEEPER class at a frame admissible for some layer of `extN`
  (a class read true at the caller's stage — F13's member call).

`ClassPres.ind` is the graph route's `hind` (`ClassKit.toNodeInd`, then
`NestNodeInd.ind_recNodesOn` at `Rel c b ↔ b = nd c`).

**`huniq`** (`ClassPres.uniq`): at `ℓ = 0` the bound is a truth value
(from `hconclTy`); at a nonzero sort the clause's injection is injective
(`LfpClause.mkInj`); at a `Prop`-valued class with a large eliminator the
per-major LICENCE (check 5's large-elimination criterion: the fields are
a function of the index) makes the decoding unique.

**`hconclTy`** (`genConclTy_of`): the conclusion's typing at every
generated binder fit — a fact of the generated TYPE — read at the
graph's classes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 1. The class kit over clause classes -/

section Kit

variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- Node `b`'s clause: `Db b` at `ψb b`, its index sets pinned at the
true frame's. -/
@[expose] noncomputable def lfpCl (Db : Nat → LfpDatum V) (ψb : Nat → Name → Nat)
    (frb : Nat → Nat → V) (b : Nat) : SClause V (Nat → V) :=
  lfpSClause (Db b) (ψb b) ((Db b).idx (ψb b) (frb b))

/-- **The class kit over clause classes** (`lfpNestKit` with the third
call case over `extN`).  `ok` is the clause's (`lfpSClause_okAt`). -/
@[expose] noncomputable def lfpClassKit (nC : Nat) (Db : Nat → LfpDatum V)
    (ψb : Nat → Name → Nat) (frb : Nat → Nat → V) (dp : Nat → Nat) (Dd : Nat)
    (hD : ∀ b, b < nC → dp b < Dd)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop)
    (pred : NDec V → V)
    (hcl : ∀ b, b < nC → LfpClause acval (Db b))
    (hAdm : ∀ b, b < nC → ∀ G ρ, Adm b G ρ →
      Sat V ((Db b).params (ψb b)).reverse ρ ∧
        ∀ c, c < (Db b).N → (Db b).idx (ψb b) ρ c = (Db b).idx (ψb b) (frb b) c)
    (trans : ∀ b, b < nC → ∀ G,
      (∀ b' c t y, G b' c t y → y ∈ˢ app ((lfpCl Db ψb frb b').carrier (frb b') c) t) →
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
          (dp b < dp b' ∧ ∃ n ρ', Adm b' (extN nC (lfpCl Db ψb frb) dp Adm G b Y n) ρ' ∧
            y ∈ˢ app ((lfpCl Db ψb frb b').carrier ρ' c') t')))
    (top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
        t ∈ˢ (Db b').idx (ψb b') (frb b') c →
        y ∈ˢ app ((Db b').carrier (ψb b') (frb b') c) t → G b' c t y) →
      Adm b G (frb b)) :
    ClassKit V (Nat → V) where
  nC := nC
  cl := lfpCl Db ψb frb
  fr := frb
  dp := dp
  D := Dd
  hD := hD
  Adm := Adm
  pred := pred
  ok := fun b hb G ρ hρ =>
    lfpSClause_okAt (hcl b hb) (hAdm b hb G ρ hρ).1 (hAdm b hb G ρ hρ).2
  trans := fun b hb G hG ρ hρ Y hY hle t c j fs hc hf => by
    show (Db b).HFits (ψb b) (frb b) ((lfpCl Db ψb frb b).carrier (frb b)) t c j fs
    rw [lfpCl, lfpSClause_carrier rfl]
    exact trans b hb G hG ρ hρ Y hY hle t c j fs hc hf
  calls := calls
  top := top

end Kit

/-! ## 2. The presentation of the generated classes -/

/-- **A call target lands at node `b'`** from node `b`'s decoding
`(m, t, j, fs)`: at every admissible visit `(G, ρ)` of `b` and every hole
tuple `Y` the fields fit at, the target `y` (component `m'`, index `t'`)
is in `Y` (the own group), satisfies `G` (a free hole), or lies in a
DEEPER node's class at a frame admissible for some layer of `extN`. -/
@[expose] def ClassLands (nC : Nat) (Db : Nat → LfpDatum V) (ψb : Nat → Name → Nat)
    (frb : Nat → Nat → V) (dp : Nat → Nat)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop)
    (b m : Nat) (t : V) (j : Nat) (fs : List V) (b' m' : Nat) (t' y : V) : Prop :=
  ∀ G ρ, Adm b G ρ → ∀ Y,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
    (Db b).HFits (ψb b) ρ Y t m j fs →
    (b' = b ∧ y ∈ˢ app (Y m') t') ∨ G b' m' t' y ∨
      (dp b < dp b' ∧ b' < nC ∧ ∃ n ρ', Adm b' (extN nC (lfpCl Db ψb frb) dp Adm G b Y n) ρ' ∧
        y ∈ˢ app ((lfpCl Db ψb frb b').carrier ρ' m') t')

section Pres

variable (acval : Name → (Name → Nat) → AnnotTerm) (K : Nat) (nCt : Nat → Nat)
  (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V)
  (fit : List V → Nat → V → Nat → List V → Prop)
  (call : List V → Nat → Nat → List V → V → Prop) (xs : List V)

/-- **A presentation of the recursor classes, one node per class**, at
the prefix spine `xs` (see the module docstring). -/
structure ClassPres where
  nC : Nat
  Db : Nat → LfpDatum V
  ψb : Nat → Name → Nat
  frb : Nat → Nat → V
  dp : Nat → Nat
  Dd : Nat
  hD : ∀ b, b < nC → dp b < Dd
  Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop
  /-- the node's recorded clause -/
  hcl : ∀ b, b < nC → LfpClause acval (Db b)
  /-- admissible frames satisfy the parameter telescope and read the
  true index sets -/
  hAdm : ∀ b, b < nC → ∀ G ρ, Adm b G ρ →
    Sat V ((Db b).params (ψb b)).reverse ρ ∧
      ∀ c, c < (Db b).N → (Db b).idx (ψb b) ρ c = (Db b).idx (ψb b) (frb b) c
  /-- the true frame is admissible for the deeper true classes -/
  top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
      t ∈ˢ (Db b').idx (ψb b') (frb b') c →
      y ∈ˢ app ((Db b').carrier (ψb b') (frb b') c) t → G b' c t y) →
    Adm b G (frb b)
  /-- the node's frame order (T5: the free holes grow) -/
  Le : Nat → (Nat → V) → (Nat → V) → Prop
  /-- **`classMono` at the fit**: along the frame order and the tuple
  order, a fit grows -/
  fitMono : ∀ b, b < nC → ∀ ρ ρ', Le b ρ ρ' → ∀ X Y,
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) X →
    InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
    TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) X Y →
    ∀ c, c < (Db b).N → ∀ t j fs, (Db b).HFits (ψb b) ρ X t c j fs →
      (Db b).HFits (ψb b) ρ' Y t c j fs
  /-- an admissible frame whose hypotheses are true lies below the true
  frame -/
  hAdmLe : ∀ b, b < nC → ∀ G,
    (∀ b' c t y, G b' c t y → y ∈ˢ app ((Db b').carrier (ψb b') (frb b') c) t) →
    ∀ ρ, Adm b G ρ → Le b ρ (frb b)
  /-- the class's node and component; `Gd c`: the class has majors here -/
  nd : Nat → Nat
  mOf : Nat → Nat
  Gd : Nat → Prop
  hGd : ∀ c, c < K → ∀ t, t ∈ˢ Is xs c → Gd c
  hnd : ∀ c, c < K → Gd c → nd c < nC
  hm : ∀ c, c < K → Gd c → mOf c < (Db (nd c)).N
  /-- **the class tie** (T3′ at the generated family) -/
  hIs : ∀ c, c < K → Gd c → Is xs c = (Db (nd c)).idx (ψb (nd c)) (frb (nd c)) (mOf c)
  hCr : ∀ c, c < K → Gd c → Cr xs c = (Db (nd c)).carrier (ψb (nd c)) (frb (nd c)) (mOf c)
  hinj : ∀ c, c < K → Gd c → ∀ j fs, injX c j fs = (Db (nd c)).inj (ψb (nd c)) (mOf c) j fs
  hfit : ∀ c, c < K → Gd c → ∀ t j fs, t ∈ˢ Is xs c →
    (fit xs c t j fs ↔
      (Db (nd c)).HFits (ψb (nd c)) (frb (nd c)) ((Db (nd c)).carrier (ψb (nd c)) (frb (nd c)))
        t (mOf c) j fs)
  hnCt : ∀ c, c < K → Gd c → ∀ t j fs,
    (Db (nd c)).HFits (ψb (nd c)) (frb (nd c)) ((Db (nd c)).carrier (ψb (nd c)) (frb (nd c)))
      t (mOf c) j fs → j < nCt c
  /-- **the calls**: at a true decoding, every call target that is a
  major lands at its class's node -/
  hcall : ∀ c, c < K → Gd c → ∀ t j fs,
    t ∈ˢ (Db (nd c)).idx (ψb (nd c)) (frb (nd c)) (mOf c) →
    (Db (nd c)).HFits (ψb (nd c)) (frb (nd c)) ((Db (nd c)).carrier (ψb (nd c)) (frb (nd c)))
      t (mOf c) j fs →
    ∀ c' t' y, c' < K → t' ∈ˢ Is xs c' → y ∈ˢ app (Cr xs c') t' →
      call xs c j fs (tagged c' t' y) →
      ClassLands nC Db ψb frb dp Adm (nd c) (mOf c) t j fs (nd c') (mOf c') t' y

end Pres

namespace ClassPres

variable {acval : Name → (Name → Nat) → AnnotTerm} {K : Nat} {nCt : Nat → Nat}
  {Is Cr : List V → Nat → V} {injX : Nat → Nat → List V → V}
  {fit : List V → Nat → V → Nat → List V → Prop}
  {call : List V → Nat → Nat → List V → V → Prop} {xs : List V}
  (P : ClassPres acval K nCt Is Cr injX fit call xs)

/-- **The kit's `trans`**: `fitMono` from the admissible frame to the
true one. -/
theorem trans : ∀ b, b < P.nC → ∀ G,
    (∀ b' c t y, G b' c t y → y ∈ˢ app ((lfpCl P.Db P.ψb P.frb b').carrier (P.frb b') c) t) →
    ∀ ρ, P.Adm b G ρ → ∀ Y,
    InTupleSpace ((P.Db b).w (P.ψb b)) (P.Db b).N ((P.Db b).idx (P.ψb b) (P.frb b)) Y →
    TupleLe (P.Db b).N ((P.Db b).idx (P.ψb b) (P.frb b)) Y
      ((P.Db b).carrier (P.ψb b) (P.frb b)) →
    ∀ t c j fs, c < (P.Db b).N → (P.Db b).HFits (P.ψb b) ρ Y t c j fs →
      (P.Db b).HFits (P.ψb b) (P.frb b) ((P.Db b).carrier (P.ψb b) (P.frb b)) t c j fs := by
  intro b hb G hG ρ hρ Y hY hle t c j fs hc hf
  have hG' : ∀ b' c t y, G b' c t y →
      y ∈ˢ app ((P.Db b').carrier (P.ψb b') (P.frb b') c) t := fun b' c t y h => by
    have := hG b' c t y h
    rwa [lfpCl, lfpSClause_carrier rfl] at this
  exact P.fitMono b hb ρ (P.frb b) (P.hAdmLe b hb G hG' ρ hρ) Y _ hY
    (lfpTuple_mem _ _ _ _) hle c hc t j fs hf

/-- A preliminary kit (no predecessors): its majors `U` depend only on
the nodes. -/
@[expose] noncomputable def kit0 : ClassKit V (Nat → V) :=
  lfpClassKit (acval := acval) P.nC P.Db P.ψb P.frb P.dp P.Dd P.hD P.Adm (fun _ => empty)
    P.hcl P.hAdm P.trans
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ u hu => absurd hu (not_mem_empty u)) P.top

/-- **The predecessors of a node decoding**: the call targets of the
node's classes' true decodings, each at its callee's node. -/
@[expose] noncomputable def pred (e : NDec V) : V :=
  sep P.kit0.U fun u => ∃ c, c < K ∧ P.Gd c ∧ P.nd c = e.cls ∧ P.mOf c = e.c ∧
    e.t ∈ˢ (P.Db e.cls).idx (P.ψb e.cls) (P.frb e.cls) e.c ∧
    (P.Db e.cls).HFits (P.ψb e.cls) (P.frb e.cls) ((P.Db e.cls).carrier (P.ψb e.cls)
      (P.frb e.cls)) e.t e.c e.j e.fs ∧
    ∃ c' t' y, c' < K ∧ t' ∈ˢ Is xs c' ∧ y ∈ˢ app (Cr xs c') t' ∧
      call xs c e.j e.fs (tagged c' t' y) ∧
      ClassLands P.nC P.Db P.ψb P.frb P.dp P.Adm e.cls e.c e.t e.j e.fs (P.nd c') (P.mOf c') t' y ∧
      u = nenc (P.nd c') (P.mOf c') t' y

/-- **The class kit**, its predecessors `pred`. -/
@[expose] noncomputable def kit : ClassKit V (Nat → V) :=
  lfpClassKit (acval := acval) P.nC P.Db P.ψb P.frb P.dp P.Dd P.hD P.Adm P.pred P.hcl P.hAdm
    P.trans (fun b _ G ρ' hρ Y hY c t j fs _ _ hf u hu => by
      obtain ⟨-, c0, -, -, rfl, rfl, -, -, c', t', y, hc', ht', -, -, hL, rfl⟩ := mem_sep.mp hu
      have hg' := P.hGd c' hc' t' ht'
      refine ⟨P.nd c', P.mOf c', t', y, P.hnd c' hc' hg', P.hm c' hc' hg',
        by rw [← P.hIs c' hc' hg']; exact ht', rfl, ?_⟩
      rcases hL G ρ' hρ Y hY hf with h | h | ⟨hlt, -, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hlt, h⟩))
    P.top

theorem kit_carrier (b : Nat) :
    (lfpCl P.Db P.ψb P.frb b).carrier (P.frb b) = (P.Db b).carrier (P.ψb b) (P.frb b) :=
  lfpSClause_carrier rfl

omit P in
/-- **`hind`: the induction over the majors of the generated classes**,
from the class kit at one node per class. -/
theorem ind (P : ClassPres acval K nCt Is Cr injX fit call xs) : ∀ Q : V → Prop,
    (∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      (∃ e, graphDecG Is injX nCt K fit xs u e ∧
        ∀ v, v ∈ˢ graphPredG Is Cr K call xs e → Q v) → Q u) →
    ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → Q u := by
  intro Q hstep u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  have hg := P.hGd c hc t ht
  have hfitT : ∀ c b, c < K → (P.Gd c ∧ b = P.nd c) → ∀ t j fs,
      (P.kit.toNodeInd.cl b).Fits (P.kit.toNodeInd.fr b) (P.kit.toNodeInd.KT b) t (P.mOf c) j fs →
      (P.Db (P.nd c)).HFits (P.ψb (P.nd c)) (P.frb (P.nd c))
        ((P.Db (P.nd c)).carrier (P.ψb (P.nd c)) (P.frb (P.nd c))) t (P.mOf c) j fs := by
    rintro c b - ⟨-, rfl⟩ t j fs hf
    have := hf
    change (P.Db (P.nd c)).HFits (P.ψb (P.nd c)) (P.frb (P.nd c))
      ((lfpCl P.Db P.ψb P.frb (P.nd c)).carrier (P.frb (P.nd c))) t (P.mOf c) j fs at this
    rwa [P.kit_carrier] at this
  refine P.kit.toNodeInd.ind_recNodesOn K P.Gd (fun c b => P.Gd c ∧ b = P.nd c)
    (fun c _ => P.mOf c) nCt (Is xs) (Cr xs) injX (fun c t j fs => t ∈ˢ Is xs c → fit xs c t j fs)
    (graphPredG Is Cr K call xs)
    (fun c _ hg => ⟨P.nd c, hg, rfl⟩)
    (fun c b hc ⟨hg, hb⟩ => hb ▸ P.hnd c hc hg)
    (fun c b hc ⟨hg, hb⟩ => hb ▸ P.hm c hc hg)
    (fun c b hc ⟨hg, hb⟩ => hb ▸ P.hIs c hc hg)
    (fun c b hc ⟨hg, hb⟩ => by
      subst hb
      show Cr xs c = (lfpCl P.Db P.ψb P.frb (P.nd c)).carrier (P.frb (P.nd c)) (P.mOf c)
      rw [P.kit_carrier]; exact P.hCr c hc hg)
    (fun c b hc ⟨hg, hb⟩ j fs => hb ▸ P.hinj c hc hg j fs)
    (fun c b hc hR t j fs hf => P.hnCt c hc hR.1 t j fs (hfitT c b hc hR t j fs hf))
    (fun c b hc hR t j fs hf ht => (P.hfit c hc hR.1 t j fs ht).mpr (hfitT c b hc hR t j fs hf))
    ?_ Q ?_ c hc hg t ht x hx
  · -- the calls land at their callees' nodes, among the kit's predecessors
    rintro c b hc ⟨hg, rfl⟩ t j fs ht hf v hv
    have hf' := hfitT c _ hc ⟨hg, rfl⟩ t j fs hf
    have ht' : t ∈ˢ (P.Db (P.nd c)).idx (P.ψb (P.nd c)) (P.frb (P.nd c)) (P.mOf c) := ht
    obtain ⟨hvU, hcl⟩ := mem_graphPredG.mp hv
    obtain ⟨c', hc', t', ht'', y, hy, rfl⟩ := mem_unionSet.mp hvU
    have hg' := P.hGd c' hc' t' ht''
    have hL := P.hcall c hc hg t j fs ht' hf' c' t' y hc' ht'' hy hcl
    refine ⟨c', t', y, hc', rfl, P.nd c', ⟨hg', rfl⟩, mem_sep.mpr ⟨?_, c, hc, hg, rfl, rfl, ht',
      hf', c', t', y, hc', ht'', hy, hcl, hL, rfl⟩⟩
    refine P.kit0.nenc_mem_U (P.hnd c' hc' hg') (P.hm c' hc' hg') ?_ ?_
    · show t' ∈ˢ (P.Db (P.nd c')).idx (P.ψb (P.nd c')) (P.frb (P.nd c')) (P.mOf c')
      rw [← P.hIs c' hc' hg']; exact ht''
    · show y ∈ˢ app ((lfpCl P.Db P.ψb P.frb (P.nd c')).carrier (P.frb (P.nd c')) (P.mOf c')) t'
      rw [P.kit_carrier, ← P.hCr c' hc' hg']; exact hy
  · -- the step, read at the graph's decodings
    intro u hu ⟨e, ⟨he1, he2, i, hi, hfi, hu'⟩, hpe⟩
    exact hstep u hu ⟨e, ⟨he1, he2, i, hi, hfi hi, hu'⟩, hpe⟩

end ClassPres

end ConLeche.Model
