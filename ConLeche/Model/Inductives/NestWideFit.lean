module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.SetModel.NestWideAt

public section

/-!
# (W) for a nested block from its wide fits (lane NESTW, L7 step 3, the consumer)

The Model-tier record the producer (the inversion of the positivity walk)
must deliver for a nested block's datum `D` at a level assignment `ψ` and
a parameter frame `ρp`, and the theorem that it gives the hole operator
its closed tuple (`NestWideFits.closed`) through the set-level wide
presentation (`WideFits.toWideAt`, `SetModel/NestWideAt.lean`).

The record (`NestWideFits`) is stated at the HOLE FIT (`LfpDatum.HFits`):
* `n` wide keys — the walk's FRAME OCCURRENCES (NESTW F-W3) — each with
  its container GROUP (`NestGroup`: the container's recorded block `D`,
  its level assignment at the instantiation, its parameter frame read off
  the wide tuple, the frame's depth) and its component there;
* per wide constructor a FLAT field list (`FField`: hole-free, or a
  Π-tower over a member hole or a key hole) and a result index — member
  `c`'s constructor `j` is the block's with every nested occurrence a key
  hole; key `q`'s constructor `j` is its container's at the instantiation;
* the containers' clauses (`gcl`), the level (`gw`: "mutually inductive
  types must live in the same universe", `nestInstType`), the containers'
  parameter frames satisfied (`gsat`), N2 (`idx`: a key's index set does
  not depend on the wide tuple);
* U4 at every non-ordinary field (`munread`/`kunread`, F-W1: the kernel
  fact NESTKERN's U4 extension supplies);
* **the fits** (`mfit`, `kfit`): a spine fitting a member's constructor at
  the hole frame of the members fits its flat fields at the wide tuple,
  once the keys dominate their values; a spine fitting a container's
  constructor at the group's tuple read at the keys fits the key's flat
  fields, once the deeper keys dominate.

The member injections are the hole operator's (the tagged tower of the
fields and a trailing point, `LfpDatum.holeOp_fibre`); the keys' are the
containers' clauses' `inj` (F-W2).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (mkTower)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- **A key group at the instantiation** (a container frame's reached
group): the container's recorded block, its level assignment at the
instantiation, its parameter frame read off the wide tuple, and the
frame's depth in the walk. -/
structure NestGroup (V : Type w) [SetTheory V] where
  D : LfpDatum V
  ψ : Name → Nat
  ρ : (Nat → V) → Nat → V
  dep : Nat

/-- **The key groups** of the wide presentation: a key's group, its
component there, the group's index sets and operator at the parameter
frame read off the wide tuple. -/
@[expose] noncomputable def nestKeyGroups (grp cmp : Nat → Nat) (G : Nat → NestGroup V) :
    KeyGroups V where
  grp := grp
  cmp := cmp
  g := fun g => (G g).D.N
  IsG := fun g W => (G g).D.idx (G g).ψ ((G g).ρ W)
  Θ := fun g W => (G g).D.Φ (G g).ψ ((G g).ρ W)
  dep := fun g => (G g).dep

/-- **The wide presentation of a nested block, at the hole fit** (see
the module docstring). -/
structure NestWideFits (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) : Type w where
  /-- the number of wide keys (the walk's frame occurrences) -/
  n : Nat
  /-- key ↦ its group, its component there -/
  grp : Nat → Nat
  cmp : Nat → Nat
  /-- group ↦ the container's block at the instantiation -/
  G : Nat → NestGroup V
  /-- the keys' index sets -/
  kIs : Nat → V
  /-- the frame the flat fields read -/
  ρ₀ : Nat → V
  /-- member `c`'s constructor `j`: flat fields, result index -/
  mf : Nat → Nat → List (FField V)
  mi : Nat → Nat → (Nat → V) → V
  /-- key `q`'s constructor `j`: flat fields, result index -/
  kf : Nat → Nat → List (FField V)
  ki : Nat → Nat → (Nat → V) → V
  /-- the containers' lfp clauses -/
  gcl : ∀ q, q < n → ∃ acv, LfpClause acv (G (grp q)).D
  /-- the containers live in the block's universe -/
  gw : ∀ q, q < n → (G (grp q)).D.w (G (grp q)).ψ = D.w ψ
  /-- the containers' parameter frames are satisfied -/
  gsat : ∀ q, q < n → ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W →
    Sat V ((G (grp q)).D.params (G (grp q)).ψ).reverse ((G (grp q)).ρ W)
  cmp_lt : ∀ q, q < n → cmp q < (G (grp q)).D.N
  inj : ∀ q q', q < n → q' < n → grp q = grp q' → cmp q = cmp q' → q = q'
  /-- N2: a key's index set is its component's -/
  idx : ∀ q, q < n → ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W →
    (G (grp q)).D.idx (G (grp q)).ψ ((G (grp q)).ρ W) (cmp q) = kIs q
  mwf : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ f ∈ mf c j, f.WF (D.w ψ) (D.N + n)
  kwf : ∀ q, q < n → ∀ j, j < (G (grp q)).D.nctors (cmp q) → ∀ f ∈ kf q j,
    f.WF (D.w ψ) (D.N + n)
  /-- U4 at every non-ordinary field (F-W1) -/
  munread : ∀ c, c < D.N → ∀ j, j < D.nctors c → HoleUnread (mf c j) ρ₀ ρ₀
  kunread : ∀ q, q < n → ∀ j, j < (G (grp q)).D.nctors (cmp q) → HoleUnread (kf q j) ρ₀ ρ₀
  /-- **the members' fit** -/
  mfit : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → InTupleSpace (D.w ψ) n kIs Y →
    Dominated D.N n (catTup D.N (D.idx ψ ρp) kIs) ((nestKeyGroups grp cmp G).ev (D.w ψ))
      (catTup D.N X Y) →
    ∀ c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ j fs, D.HFits ψ ρp X t c j fs →
    FitsF (mf c j) ρ₀ (catTup D.N X Y) fs ∧ mi c j (fconsList fs ρ₀) = t
  /-- **the keys' fit**, at every tuple of the group agreeing with the
  wide tuple at the reached components -/
  kfit : ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W → ∀ q, q < n →
    (∀ q', q' < n → (G (grp q)).dep < (G (grp q')).dep →
      FamLe (kIs q') ((nestKeyGroups grp cmp G).ev (D.w ψ) q' W) (W (D.N + q'))) →
    ∀ Z, InTupleSpace (D.w ψ) (G (grp q)).D.N
        ((G (grp q)).D.idx (G (grp q)).ψ ((G (grp q)).ρ W)) Z →
      (∀ q', q' < n → grp q' = grp q → Z (cmp q') = W (D.N + q')) →
    ∀ t, t ∈ˢ kIs q → ∀ j fs,
      (G (grp q)).D.HFits (G (grp q)).ψ ((G (grp q)).ρ W) Z t (cmp q) j fs →
      FitsF (kf q j) ρ₀ W fs ∧ ki q j (fconsList fs ρ₀) = t

namespace NestWideFits

variable {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V}

/-- The member injection: the hole operator's tagged tower. -/
@[expose] noncomputable def mInj : Nat → Nat → List V → V := fun _ j fs =>
  ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [(pt : V)]))

theorem mInj_univ {w' : Nat} (hw : w' ≠ 0) (c j : Nat) {fs : List V}
    (h : ∀ y ∈ fs, y ∈ˢ (univ w' : V)) : mInj c j fs ∈ˢ (univ w' : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have := uinj_mem_univ_pos hw j (fs := fs ++ [(pt : V)]) fun y hy => by
    rcases List.mem_append.mp hy with hy | hy
    · exact h y hy
    · rw [List.mem_singleton.mp hy]
      exact hU.transitive (unitSet_mem_univ w') pt_mem_unitSet
  rwa [uinj_pos hw] at this

/-- **The set-level flat fits** of the record, given the hole operator's
fibre premises (`LfpDatum.holeOp_fibre`). -/
noncomputable def toWideFits (F : NestWideFits D ψ ρp) (hw : D.w ψ ≠ 0)
    (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (happ : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    WideFits (D.w ψ) D.N (D.idx ψ ρp) (D.holeOp ψ ρp) where
  n := F.n
  kIs := F.kIs
  ρ₀ := F.ρ₀
  P := nestKeyGroups F.grp F.cmp F.G
  mn := D.nctors
  mf := F.mf
  mi := F.mi
  mι := mInj
  kn := fun q => (F.G (F.grp q)).D.nctors (F.cmp q)
  kf := F.kf
  ki := F.ki
  kι := fun q j fs => (F.G (F.grp q)).D.inj (F.G (F.grp q)).ψ (F.cmp q) j fs
  mwf := F.mwf
  kwf := F.kwf
  munread := F.munread
  kunread := F.kunread
  mιU := fun c _ j _ h => mInj_univ hw c j h
  cmp_lt := F.cmp_lt
  inj := F.inj
  idx := F.idx
  functor := fun W hW q hq => by
    obtain ⟨acv, hcl⟩ := F.gcl q hq
    have h := hcl.functor _ _ (F.gsat q hq W hW)
    rw [F.gw q hq] at h
    exact h
  mfib := fun X Y hX hY hd c hc t ht x hx => by
    obtain ⟨j, fs, hf, rfl⟩ := (LfpDatum.holeOp_fibre hok hkN X (happ c hc) (hres c hc) ht x).mp hx
    obtain ⟨hmf, hmi⟩ := F.mfit X Y hX hY hd c hc t ht j fs hf
    exact ⟨j, hf.1, fs, hmf, hmi, by rw [if_neg hw]; rfl⟩
  kfib := fun W hW q hq hdeep t ht x hx => by
    obtain ⟨acv, hcl⟩ := F.gcl q hq
    let P := nestKeyGroups (V := V) F.grp F.cmp F.G
    have hidx : ∀ q', q' < F.n → P.IsG (P.grp q') W (P.cmp q') = catTup D.N (D.idx ψ ρp) F.kIs (D.N + q') :=
      fun q' hq' => (F.idx q' hq' W hW).trans (catTup_add _ _ q').symm
    have hfill := KeyGroups.fill_inTupleSpace (P := P) hW hidx (P.grp q)
    have hsat := F.gsat q hq W hW
    have htG : t ∈ˢ (F.G (F.grp q)).D.idx (F.G (F.grp q)).ψ ((F.G (F.grp q)).ρ W) (F.cmp q) := by
      rw [F.idx q hq W hW]; exact ht
    have hfill' : InTupleSpace ((F.G (F.grp q)).D.w (F.G (F.grp q)).ψ) (F.G (F.grp q)).D.N
        ((F.G (F.grp q)).D.idx (F.G (F.grp q)).ψ ((F.G (F.grp q)).ρ W))
        (P.fill (D.w ψ) D.N F.n (F.grp q) W) := by
      rw [F.gw q hq]; exact hfill
    obtain ⟨j, fs, hf, rfl⟩ := (hcl.fibre _ _ hsat _ hfill' (F.cmp q) (F.cmp_lt q hq) t htG x).mp hx
    have hagree : ∀ q', q' < F.n → F.grp q' = F.grp q →
        P.fill (D.w ψ) D.N F.n (F.grp q) W (F.cmp q') = W (D.N + q') := by
      intro q' hq' hg
      rw [← hg]
      exact KeyGroups.fill_reached (P := P) hq' F.inj W
    obtain ⟨hkf, hki⟩ := F.kfit W hW q hq hdeep _ hfill hagree t ht j fs hf
    exact ⟨j, hf.1, fs, hkf, hki, rfl⟩

/-- **(W) for a nested block's hole operator**, from its wide fits, at a
`Type`-valued parameter frame. -/
theorem closed (F : NestWideFits D ψ ρp) (hw : D.w ψ ≠ 0)
    (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (happ : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.holeOp ψ ρp) L :=
  (F.toWideFits hw hok hkN happ hres).closed hw

end NestWideFits

end ConLeche.Model
