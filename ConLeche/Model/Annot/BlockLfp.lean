module

public import ConLeche.SetModel.UnionRec
public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Tower.FixLeafI
public section

/-!
# The LFP CLAUSE of an inductive block (lane ENVLFP)

The fact the maintainer wanted in the environment invariant from the
start: **a member's denotation `⟦I⟧ p⃗` is the least fixed point of its
block's right-hand-side operator, with holes for the recursive
fields.**  The recursor model's graph route (DESIGN, ruling of
2026-09-23) asks nothing else of an inductive: the recursor's
uniqueness is ONE induction over the majors, and that induction is a
corollary of this clause (`LfpClause.ind_tagged`, `LfpClause.kitInd`).

**Why a separate datum.**  The clause is recorded in `EnvModelM`
(`Model/Annot/EnvModelM.lean`), which sits BELOW the block
representation (`BlockData`/`BlockModelAt`,
`Model/Inductives/BlockRep.lean`) in the import order.  So the clause
is stated over `LfpDatum`, the part of a block's representation the
clause reads — its member names, widths, parameter and index
telescopes, the operator `Φ`, and the constructors' fit relation and
injections — and a uniform block's datum is `BlockData.toLfp d`
(`BlockRep.lean`), its fields literally `d`'s.  The OPERATOR is
therefore exactly the one `BlockModelAt` uses: `d.Φ`, which at the
fixpoint route's data is `blockPhi` by `rfl` (`BlockDatum.lean`); the
clause's `fibre` says what that operator IS, fibre by fibre
(injections of the spines fitting a constructor, a recursive field
read at the tuple's component) — the NARROW clause: a container's
instance is read ordinarily, it is not a component.

**The clause** (`LfpClause`), at every level assignment `ψ` and every
parameter frame `ρp` satisfying the parameter telescope (exactly the
quantification `BlockModelAt` has, which is what the install proves):

* `functor` — `Φ` is monotone, maps the tuple space into itself, and
  has a closed tuple: the three facts `lfpTuple`'s laws need
  (`lfpTuple_induction` takes the first and the third);
* `fibre` — component `c`'s fibre at `(X, t)` is the set of injections
  of the spines fitting one of `c`'s constructors at `(X, t)`;
* `leaf` — a member's former, at fitting parameters and its own
  indices, is the least pre-fixed tuple's component at the index
  tuple.

**Universe instantiation.**  `leaf` holds at EVERY level assignment
`ψ`.  A use `.const I us` under `φ` reads the leaf at
`Level.substFn φ lps us` (`EnvModelM.constType`'s crossing), which is
one such `ψ` — `LfpClause.leaf_inst` states that case explicitly.
The installer establishes the clause at every `ψ` because it checks
the block's parameters once, polymorphically, and the model reads the
member's leaf as a function of the assignment.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

/-- **The part of a block's representation the lfp clause reads** (see
the module docstring).  A uniform block's is `BlockData.toLfp`. -/
structure LfpDatum (V : Type w) where
  /-- the members' names, by position -/
  names : List Name
  /-- the number of MEMBERS -/
  k : Nat
  /-- the operator's WIDTH (members, then instance components) -/
  N : Nat
  /-- the result sort's value, per level assignment -/
  w : (Name → Nat) → Nat
  /-- the parameter telescope -/
  params : (Name → Nat) → List AnnotTerm
  /-- per component: its own index telescope -/
  ids : Nat → (Name → Nat) → List AnnotTerm
  /-- per component: its index-tuple sort -/
  u : Nat → (Name → Nat) → Nat
  /-- **the tuple operator**, at a level assignment and a parameter frame -/
  Φ : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- **a field spine fits** component `c`'s constructor `j` at the
  functor frame `(ρp, X, t)` (the block's `j < #ctors ∧ ChainFit`) -/
  fits : (Name → Nat) → (Nat → V) → (Nat → V) → V → Nat → Nat → List V → Prop
  /-- the constructor injections -/
  inj : (Name → Nat) → Nat → Nat → List V → V

namespace LfpDatum

variable {V : Type w} [SetTheory V] (D : LfpDatum V)

/-- Member `mm`'s name. -/
@[expose] def member (mm : Nat) : Name := D.names.getD mm .anonymous

/-- The tuple of index-tuple sets at a parameter frame. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun c => idxSet (D.u c ψ) ρp (D.ids c ψ)

/-- **The carrier**: the least pre-fixed tuple of the operator. -/
@[expose] noncomputable def carrier (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  lfpTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)

/-- **The majors**: the carrier's elements, tagged by component and
index tuple (`unionSet`, the recursor's union). -/
@[expose] noncomputable def majors (ψ : Name → Nat) (ρp : Nat → V) : V :=
  unionSet D.N (D.idx ψ ρp) (D.carrier ψ ρp)

end LfpDatum

variable {V : Type w} [SetTheory V]

/-- **The lfp clause** of the block `D`, over the leaf valuation
`acval` (see the module docstring). -/
structure LfpClause (acval : Name → (Name → Nat) → AnnotTerm) (D : LfpDatum V) : Prop where
  /-- the members come first among the components -/
  kN : D.k ≤ D.N
  /-- **`Φ` is a monotone tuple functor** with a closed tuple -/
  functor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) ∧
    MapsTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) ∧
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) L
  /-- **what `Φ` is**: component `c`'s fibre at `(X, t)` is the set of
  injections of the spines fitting one of `c`'s constructors -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
    ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
      x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs
  /-- **the leaf**: a member's former at fitting parameters and its own
  indices is the carrier's component at the index tuple -/
  leaf : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (D.params ψ) as → SpineFit (consList as ρ) (D.ids mm ψ) is →
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      = app (D.carrier ψ (consList as ρ) mm) (tupW (D.u mm ψ) is)

namespace LfpClause

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}

/-- **Transport**: the clause reads the leaf valuation only at the
members' names. -/
theorem congr (h : LfpClause acval D) {acval' : Name → (Name → Nat) → AnnotTerm}
    (hag : ∀ mm, mm < D.k → acval' (D.member mm) = acval (D.member mm)) :
    LfpClause acval' D where
  kN := h.kN
  functor := h.functor
  fibre := h.fibre
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    rw [hag mm hmm]; exact h.leaf mm hmm ψ ρ as is hsa hsi

/-- **The clause at a universe instantiation**: the leaf at the
assignment a use `.const (D.member mm) us` under `φ` reads —
`Level.substFn φ lps us` — is the carrier at that assignment. -/
theorem leaf_inst (h : LfpClause acval D) {mm : Nat} (hmm : mm < D.k) (φ : Name → Nat)
    (lps : List Name) (us : List Level) {ρ : Nat → V} {as is : List V}
    (hsa : SpineFit ρ (D.params (Level.substFn φ lps us)) as)
    (hsi : SpineFit (consList as ρ) (D.ids mm (Level.substFn φ lps us)) is) :
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) (Level.substFn φ lps us)))
      = app (D.carrier (Level.substFn φ lps us) (consList as ρ) mm)
          (tupW (D.u mm (Level.substFn φ lps us)) is) :=
  h.leaf mm hmm _ ρ as is hsa hsi

/-- **The carrier is a fixed point**, componentwise. -/
theorem carrier_eq (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) :
    D.Φ ψ ρp (D.carrier ψ ρp) c = D.carrier ψ ρp c := by
  obtain ⟨hmono, hmaps, hcl⟩ := h.functor ψ ρp hsat
  exact lfpTuple_eq hcl hmono hmaps hc

/-- **The carrier's case analysis**: an element of component `c`'s
carrier is the injection of a spine fitting one of `c`'s constructors
at the carrier. -/
theorem carrier_case (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) {t : V}
    (ht : t ∈ˢ D.idx ψ ρp c) {x : V} (hx : x ∈ˢ app (D.carrier ψ ρp c) t) :
    ∃ j fs, D.fits ψ ρp (D.carrier ψ ρp) t c j fs ∧ x = D.inj ψ c j fs := by
  rw [← h.carrier_eq hsat hc] at hx
  exact (h.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _) c hc t ht x).mp hx

/-- **The block's induction principle, per component**
(`lfpTuple_induction` read through `fibre`): a property that holds at
every injection of a spine fitting at the SEPARATED tuple — whose
recursive fields therefore already satisfy it — holds on the whole
carrier. -/
theorem ind (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) (P : Nat → V → V → Prop)
    (hstep : ∀ c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ j fs,
      D.fits ψ ρp (sepTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) P) t c j fs →
      P c t (D.inj ψ c j fs)) :
    ∀ c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x, x ∈ˢ app (D.carrier ψ ρp c) t → P c t x := by
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ ρp hsat
  refine lfpTuple_induction hcl hmono P fun c hc t ht x hx => ?_
  obtain ⟨j, fs, hfit, rfl⟩ :=
    (h.fibre ψ ρp hsat _ (sepTuple_mem _ _ _ _ P) c hc t ht x).mp hx
  exact hstep c hc t ht j fs hfit

/-- **The induction over the TAGGED majors** — the form the recursor's
union reads: a property of majors that holds at `tagged c t (inj …)`
whenever the spine fits at the separated tuple holds at every major. -/
theorem ind_tagged (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) (P : V → Prop)
    (hstep : ∀ c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ j fs,
      D.fits ψ ρp (sepTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) fun c t x => P (tagged c t x))
        t c j fs →
      P (tagged c t (D.inj ψ c j fs))) :
    ∀ u, u ∈ˢ D.majors ψ ρp → P u := by
  intro u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  exact h.ind hsat (fun c t x => P (tagged c t x)) hstep c hc t ht x hx

/-- **The shape of GRAPH-F's `GraphRecKit.ind`** (`SetModel/GraphRec.lean`
on `agent/uinds-GRAPHF`), verbatim: the induction principle of a set
of majors `U` for a decoding relation `Dec` and predecessor sets
`pred`. -/
@[expose] def KitInd (U : V) (Dec : V → V → Prop) (pred : V → V) : Prop :=
  ∀ P : V → Prop,
    (∀ u, u ∈ˢ U → (∃ d, Dec u d ∧ ∀ j, j ∈ˢ pred d → P j) → P u) → ∀ u, u ∈ˢ U → P u

/-- **The recursor kit's `ind`, from the lfp clause.**  Over the
block's majors, for ANY decoding relation and predecessor map whose
reading of a spine fitting at a separated tuple is a decoding with its
predecessors in the separation (`hlink` — the graph producer's
structural obligation: the decoding carries the fields' fit, the
predecessors are the recursive fields' tagged values), the kit's
induction principle holds.  Nothing but `lfpTuple_induction` and
`fibre` is used: no Bekić, no regularity. -/
theorem kitInd (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) (Dec : V → V → Prop) (pred : V → V)
    (hlink : ∀ (P : V → Prop) c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ j fs,
      D.fits ψ ρp (sepTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) fun c t x => P (tagged c t x))
        t c j fs →
      ∃ d, Dec (tagged c t (D.inj ψ c j fs)) d ∧ ∀ q, q ∈ˢ pred d → P q) :
    KitInd (D.majors ψ ρp) Dec pred := by
  intro P hP
  refine h.ind_tagged hsat P fun c hc t ht j fs hfit => ?_
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ ρp hsat
  -- the injection is a major: it is built from the separated tuple
  have hx : D.inj ψ c j fs ∈ˢ app (D.Φ ψ ρp
      (sepTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) fun c t x => P (tagged c t x)) c) t :=
    (h.fibre ψ ρp hsat _ (sepTuple_mem _ _ _ _ _) c hc t ht _).mpr ⟨j, fs, hfit, rfl⟩
  have hmem : D.inj ψ c j fs ∈ˢ app (D.carrier ψ ρp c) t := by
    refine lfpTuple_closed hcl hmono c hc t ht _ ?_
    exact hmono _ _ (sepTuple_mem _ _ _ _ _) (lfpTuple_mem _ _ _ _) (sepTuple_le _ _ _ _ _)
      c hc t ht _ hx
  exact hP _ (tagged_mem_unionSet hc ht hmem) (hlink P c hc t ht j fs hfit)

end LfpClause

end ConLeche.Model
