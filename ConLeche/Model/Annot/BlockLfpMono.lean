module

public import ConLeche.Model.Annot.BlockLfp
public import ConLeche.Semantics.Inductives.HoleMono
public import ConLeche.SetModel.HoleClose

public section

/-!
# The lfp clause with HOLES: what positivity needs from it (lane POSPROOF)

Charter item 2: "every stored `I p⃗` is the least fixed point of its
right-hand-side operator: the interpretation of its constructor types
with holes at the block's members … Monotonicity is DERIVED FROM
POSITIVITY".  Today's `LfpClause` (`BlockLfp.lean`) records the operator
`Φ` and the fit relation `fits` as OPAQUE data: nothing says that `fits`
is the reading of the stored constructor types, so nothing ties `Φ`'s
dependence on the parameter frame to anything positivity can see.  This
module states the missing link as an interface and proves, against it,
the two facts positivity must deliver:

* **`HoleReading` / `ReadsHoles`** — THE INTERFACE HOLE2 MUST MAKE
  `LfpClause` DELIVER: the block's fit relation IS the telescope fit of
  its stored constructors' field readings with holes (`fields`, the
  member-abstracted constructor domains read by `denoteMeta`), at the
  hole frame (`frame`: the parameter frame with the tuple's components at
  the member holes), together with the result index readings
  (`resIdx`).  No field kinds, no slots.
* **The consumer** (`monoTuple_of_holes`): the operator is monotone
  (`LfpClause.functor`'s first conjunct, which HOLE2 must PROVE rather
  than record) as soon as every field reading is `MonoOn` the hole order
  — which is what the run of `nestPos` on the field delivers.
* **The container case** (`LfpClause.carrier_le_of_holes`,
  `LfpClause.leaf_le_of_holes`): a stored container's member, read at
  two parameter spines, grows as soon as its constructors' field
  readings are positive AT THE INSTANTIATION (the frames at the two
  spines, the container's own holes held at the same tuple) — plus the
  lfp's monotonicity in its operator (`lfpTuple_le_of_opLe`).  No
  premise "C is monotone in its parameter" (charter item 4): the
  comparison is of THIS instantiation's two frames, and the only
  container facts used are its clause's closure and monotonicity in its
  own holes.
* **D2** (`readsOnly_of_holes`): a member whose field readings do not
  mention another member's hole reads the tuple only at itself, so its
  component is the least family of its own operator
  (`lfpTuple_eq_lfpFam_of_indep`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The interface -/

/-- **The hole reading of a block's constructors** — the data HOLE2's
clause must be stated over (HOLEOP §4.3's `absF`): per level assignment,
component `c` and constructor `j`, the field readings with holes and the
result index readings, and the hole frame. -/
structure HoleReading (V : Type w) where
  /-- component `c`'s constructor count -/
  nctors : Nat → Nat
  /-- **the hole frame**: the parameter frame with the tuple's
  components at the member holes -/
  frame : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- component `c`'s constructor `j`'s field readings (members as holes) -/
  fields : (Name → Nat) → Nat → Nat → List AnnotTerm
  /-- component `c`'s constructor `j`'s result index readings, below the fields -/
  resIdx : (Name → Nat) → Nat → Nat → List AnnotTerm

namespace HoleReading

variable (H : HoleReading V)

/-- **The hole fit**: `fs` fits constructor `j` of component `c` at the
hole frame of `(ρp, X)`, with result index tuple `t`. -/
@[expose] def Fits (u : Nat → (Name → Nat) → Nat) (ψ : Name → Nat) (ρp X : Nat → V) (t : V)
    (c j : Nat) (fs : List V) : Prop :=
  j < H.nctors c ∧ SpineFit (H.frame ψ ρp X) (H.fields ψ c j) fs ∧
    tupW (u c ψ) ((H.resIdx ψ c j).map (interp V (consList fs (H.frame ψ ρp X)))) = t

/-- **Positivity of a constructor along a frame relation**: every field
positive under its predecessors, every result index hole-free below
them. -/
@[expose] def CtorPos (R : FrameRel V) (ψ : Name → Nat) (c j : Nat) : Prop :=
  TeleMonoOn R (H.fields ψ c j) ∧
    ∀ e ∈ H.resIdx ψ c j, ConstOn (R.underTele (H.fields ψ c j)) e

/-- **The hole fit grows along a frame relation** at which the
constructor is positive. -/
theorem fits_mono {u : Nat → (Name → Nat) → Nat} {R : FrameRel V} {ψ : Name → Nat}
    {c j : Nat} (hpos : H.CtorPos R ψ c j) {ρp ρp' X X' : Nat → V}
    (hR : R (H.frame ψ ρp X) (H.frame ψ ρp' X')) {t : V} {fs : List V}
    (h : H.Fits u ψ ρp X t c j fs) : H.Fits u ψ ρp' X' t c j fs := by
  obtain ⟨hj, hsp, hres⟩ := h
  refine ⟨hj, spineFit_mono _ hpos.1 hR hsp, ?_⟩
  rw [← hres]
  congr 1
  refine List.map_congr_left fun e he => ?_
  exact (hpos.2 e he _ _ (FrameRel.underTele_consList _ fs hR hsp)).symm

end HoleReading

/-- **THE CLAUSE'S MISSING LINK** (what HOLE2 must make `LfpClause`
deliver): the block's fit relation is the hole fit of its stored
constructors. -/
@[expose] def ReadsHoles (D : LfpDatum V) (H : HoleReading V) : Prop :=
  ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
    ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ (j : Nat) (fs : List V),
      D.fits ψ ρp X t c j fs ↔ H.Fits D.u ψ ρp X t c j fs

/-! ## The consumer: the operator is monotone, from the field readings -/

/-- **The block's operator is monotone** — `LfpClause.functor`'s first
conjunct, DERIVED: from the fibre law, the clause's link to the hole
reading, and positivity of every constructor along the hole order `R`
(the frames of two ordered tuples are `R`-related).  The positivity
premise is what `nestPos`'s run on each field delivers. -/
theorem monoTuple_of_holes {D : LfpDatum V} {H : HoleReading V} (hrd : ReadsHoles D H)
    {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (R : FrameRel V)
    (hR : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → TupleLe D.N (D.idx ψ ρp) X Y →
      R (H.frame ψ ρp X) (H.frame ψ ρp Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < H.nctors c → H.CtorPos R ψ c j) :
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) := by
  intro X Y hX hY hXY
  refine tupleLe_of_fibre (hfib X hX) (hfib Y hY) fun c hc t ht j fs hf => ?_
  have hf' := (hrd ψ ρp hs X hX c hc t ht j fs).mp hf
  exact (hrd ψ ρp hs Y hY c hc t ht j fs).mpr
    (H.fits_mono (hpos c hc j hf'.1) (hR X Y hX hY hXY) hf')

/-! ## The container case -/

namespace LfpClause

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}

/-- **A container's carrier grows between two parameter frames** at
which its constructors are positive: the operator at the smaller frame
lies below the operator at the larger one AT EVERY TUPLE (the
container's own holes held at the same tuple — the in-progress
instantiations are constants), so the larger least tuple is closed for
the smaller operator (`lfpTuple_le_of_opLe`).  The container facts used
are its clause's fibre law at both frames and its closure and
monotonicity in its own holes at the larger one; nothing about the
container's parameter (charter item 4).  The index sets are the same at
both frames (the instance's index telescope is hole-free: `nestPos`'s
(N2)). -/
theorem carrier_le_of_holes (h : LfpClause acval D) {H : HoleReading V}
    (hrd : ReadsHoles D H) {ψ : Name → Nat} {ρp ρp' : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (hs' : Sat V (D.params ψ).reverse ρp')
    (hidx : D.idx ψ ρp = D.idx ψ ρp') (R : FrameRel V)
    (hR : ∀ Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y →
      R (H.frame ψ ρp Y) (H.frame ψ ρp' Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < H.nctors c → H.CtorPos R ψ c j) :
    TupleLe D.N (D.idx ψ ρp) (D.carrier ψ ρp) (D.carrier ψ ρp') := by
  obtain ⟨hmono', -, hcl'⟩ := h.functor ψ ρp' hs'
  unfold LfpDatum.carrier
  rw [hidx] at hR ⊢
  refine lfpTuple_le_of_opLe hcl' hmono' ?_
  have hL := lfpTuple_mem (D.w ψ) D.N (D.idx ψ ρp') (D.Φ ψ ρp')
  have hfib := h.fibre ψ ρp hs _ (by rw [hidx]; exact hL)
  have hfib' := h.fibre ψ ρp' hs' _ hL
  rw [hidx] at hfib
  refine tupleLe_of_fibre hfib hfib' fun c hc t ht j fs hf => ?_
  have hf' := (hrd ψ ρp hs _ (by rw [hidx]; exact hL) c hc t (by rw [hidx]; exact ht) j fs).mp hf
  exact (hrd ψ ρp' hs' _ hL c hc t ht j fs).mpr (H.fits_mono (hpos c hc j hf'.1) (hR _ hL) hf')

/-- **A container's member, read at two parameter spines**, grows when
its carrier does (the leaf law at both spines; the member's leaf is a
closed reading). -/
theorem leaf_le_of_carrier_le (h : LfpClause acval D) {mm : Nat} (hmm : mm < D.k)
    {ψ : Name → Nat} {ρ ρ' : Nat → V} {as as' is : List V}
    (hsa : SpineFit ρ (D.params ψ) as) (hsa' : SpineFit ρ' (D.params ψ) as')
    (hsi : SpineFit (consList as ρ) (D.ids mm ψ) is)
    (hsi' : SpineFit (consList as' ρ') (D.ids mm ψ) is)
    (hle : TupleLe D.N (D.idx ψ (consList as ρ)) (D.carrier ψ (consList as ρ))
      (D.carrier ψ (consList as' ρ'))) :
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      ⊆ˢ (as' ++ is).foldl app (interp V ρ' (acval (D.member mm) ψ)) := by
  rw [h.leaf mm hmm ψ ρ as is hsa hsi, h.leaf mm hmm ψ ρ' as' is hsa' hsi']
  have hmN : mm < D.N := Nat.lt_of_lt_of_le hmm h.kN
  exact app_fam_mono (lfpTuple_mem _ _ _ _ mm hmN) (hle mm hmN) _

/-- **The container case, whole**: a stored container's member applied to
two parameter spines (the instantiation's readings at a smaller and a
larger frame) and the same indices grows, when its constructors are
positive at the instantiation's two hole frames. -/
theorem leaf_le_of_holes (h : LfpClause acval D) {H : HoleReading V}
    (hrd : ReadsHoles D H) {mm : Nat} (hmm : mm < D.k)
    {ψ : Name → Nat} {ρ ρ' : Nat → V} {as as' is : List V}
    (hsa : SpineFit ρ (D.params ψ) as) (hsa' : SpineFit ρ' (D.params ψ) as')
    (hsi : SpineFit (consList as ρ) (D.ids mm ψ) is)
    (hsi' : SpineFit (consList as' ρ') (D.ids mm ψ) is)
    (hs : Sat V (D.params ψ).reverse (consList as ρ))
    (hs' : Sat V (D.params ψ).reverse (consList as' ρ'))
    (hidx : D.idx ψ (consList as ρ) = D.idx ψ (consList as' ρ')) (R : FrameRel V)
    (hR : ∀ Y, InTupleSpace (D.w ψ) D.N (D.idx ψ (consList as ρ)) Y →
      R (H.frame ψ (consList as ρ) Y) (H.frame ψ (consList as' ρ') Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < H.nctors c → H.CtorPos R ψ c j) :
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      ⊆ˢ (as' ++ is).foldl app (interp V ρ' (acval (D.member mm) ψ)) :=
  h.leaf_le_of_carrier_le hmm hsa hsa' hsi hsi'
    (h.carrier_le_of_holes hrd hs hs' hidx R hR hpos)

end LfpClause

/-! ## D2: an unreached member -/

/-- **An unreached member reads the tuple only at itself**: when the hole
frames of two tuples agreeing at component `m` agree off the positions
`P`, and no field or result index reading of `m`'s constructors mentions
`P` (the run found no other member's hole in `m`'s fields), then `m`'s
component of the operator is the same at both tuples — so by
`lfpTuple_eq_lfpFam_of_indep` it is the least family of `m`'s own
operator, whatever the other members are. -/
theorem readsOnly_of_holes {D : LfpDatum V} {H : HoleReading V} (hrd : ReadsHoles D H)
    {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp) {m : Nat} (hm : m < D.N)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (hmaps : MapsTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)) (P : Nat → Prop)
    (hag : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → X m = Y m →
      AgreeOff P (H.frame ψ ρp X) (H.frame ψ ρp Y))
    (hfree : ∀ j, j < H.nctors m → NoBVarTele P (H.fields ψ m j) ∧
      ∀ e ∈ H.resIdx ψ m j, NoBVar (shiftPN (H.fields ψ m j).length P) e) :
    ReadsOnly (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) m := by
  -- one direction of the fit, at any two tuples agreeing at `m`
  have hdir : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → X m = Y m →
      ∀ t, t ∈ˢ D.idx ψ ρp m → ∀ j fs, D.fits ψ ρp X t m j fs → D.fits ψ ρp Y t m j fs := by
    intro X Y hX hY hXY t ht j fs hf
    obtain ⟨hj, hsp, hres⟩ := (hrd ψ ρp hs X hX m hm t ht j fs).mp hf
    have hagXY := hag X Y hX hY hXY
    refine (hrd ψ ρp hs Y hY m hm t ht j fs).mpr ⟨hj, spineFit_congr_noBVar _ (hfree j hj).1 hagXY hsp, ?_⟩
    rw [← hres]
    congr 1
    refine List.map_congr_left fun e he => ?_
    have hlen : fs.length = (H.fields ψ m j).length := hsp.length_eq
    refine (interp_congr_noBVar e ?_ (agreeOff_consList fs hagXY)).symm
    rw [hlen]; exact (hfree j hj).2 e he
  intro X Y hX hY hXY
  refine famSpace_ext (hmaps X hX m hm) (hmaps Y hY m hm) fun t ht => ?_
  apply SetTheory.ext
  intro x
  rw [hfib X hX m hm t ht x, hfib Y hY m hm t ht x]
  constructor
  · rintro ⟨j, fs, hf, rfl⟩; exact ⟨j, fs, hdir X Y hX hY hXY t ht j fs hf, rfl⟩
  · rintro ⟨j, fs, hf, rfl⟩; exact ⟨j, fs, hdir Y X hY hX hXY.symm t ht j fs hf, rfl⟩

end ConLeche.Model
