module

public import ConLeche.Model.Annot.BlockLfp
public import ConLeche.Semantics.Inductives.HoleMono
public import ConLeche.SetModel.HoleClose
import ConLeche.SetModel.HoleOp

public section

/-!
# The lfp clause with HOLES: what positivity needs from it (lane POSPROOF)

Charter item 2: "every stored `I p⃗` is the least fixed point of its
right-hand-side operator: the interpretation of its constructor types
with holes at the block's members … Monotonicity is DERIVED FROM
POSITIVITY".  The clause (`BlockLfp.lean`) carries the hole reading of
the stored constructors (`LfpDatum.fields`/`resIdx`, the hole frame
`LfpDatum.frame`) and the link `LfpClause.holes` (`ReadsHoles`: the
block's fit relation IS the telescope fit of those readings at the hole
frame — lane HOLE2).  This module proves, against it, the facts
positivity must deliver:

* **Positivity of a constructor** along a frame relation (`CtorPos`)
  and the hole fit's growth along it (`LfpDatum.hfits_mono`).
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

/-! ## The interface

The hole reading itself — the fields with holes (`LfpDatum.fields`), the
result index readings (`resIdx`), the hole frame (`LfpDatum.frame`), the
hole fit (`HFits`) and the link (`ReadsHoles`) — is part of the datum
and the clause (`Annot/BlockLfp.lean`, lane HOLE2).  What positivity adds
is the relation along which a constructor is positive. -/

namespace LfpDatum

variable (D : LfpDatum V)

/-- **Positivity of a constructor along a frame relation**: every field
positive under its predecessors, every result index hole-free below
them. -/
@[expose] def CtorPos (R : FrameRel V) (ψ : Name → Nat) (c j : Nat) : Prop :=
  TeleMonoOn R (D.fields ψ c j) ∧
    ∀ e ∈ D.resIdx ψ c j, ConstOn (R.underTele (D.fields ψ c j)) e

variable {D}

/-- **The hole fit grows along a frame relation** at which the
constructor is positive. -/
theorem hfits_mono {R : FrameRel V} {ψ : Name → Nat} {c j : Nat} (hpos : D.CtorPos R ψ c j)
    {ρp ρp' X X' : Nat → V} (hR : R (D.frame ψ ρp X) (D.frame ψ ρp' X')) {t : V} {fs : List V}
    (h : D.HFits ψ ρp X t c j fs) : D.HFits ψ ρp' X' t c j fs := by
  obtain ⟨hj, hsp, hres⟩ := h
  refine ⟨hj, spineFit_mono _ hpos.1 hR hsp, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hres l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  exact (hpos.2 e (List.mem_of_getElem? he) _ _ (FrameRel.underTele_consList _ fs hR hsp)).symm

end LfpDatum

/-! ## The consumer: the operator is monotone, from the field readings -/

/-- **The block's operator is monotone** — `LfpClause.functor`'s first
conjunct, DERIVED: from the fibre law, the clause's link to the hole
reading, and positivity of every constructor along the hole order `R`
(the frames of two ordered tuples are `R`-related).  The positivity
premise is what `nestPos`'s run on each field delivers. -/
theorem monoTuple_of_holes {D : LfpDatum V} (hrd : D.ReadsHoles)
    {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (R : FrameRel V)
    (hR : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → TupleLe D.N (D.idx ψ ρp) X Y →
      R (D.frame ψ ρp X) (D.frame ψ ρp Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.CtorPos R ψ c j) :
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) := by
  intro X Y hX hY hXY
  refine tupleLe_of_fibre (hfib X hX) (hfib Y hY) fun c hc t ht j fs hf => ?_
  have hf' := (hrd ψ ρp hs X hX c hc t ht j fs).mp hf
  exact (hrd ψ ρp hs Y hY c hc t ht j fs).mpr
    (LfpDatum.hfits_mono (hpos c hc j hf'.1) (hR X Y hX hY hXY) hf')

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
theorem carrier_le_of_holes (h : LfpClause acval D) {ψ : Name → Nat} {ρp ρp' : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (hs' : Sat V (D.params ψ).reverse ρp')
    (hidx : D.idx ψ ρp = D.idx ψ ρp') (R : FrameRel V)
    (hR : ∀ Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y →
      R (D.frame ψ ρp Y) (D.frame ψ ρp' Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.CtorPos R ψ c j) :
    TupleLe D.N (D.idx ψ ρp) (D.carrier ψ ρp) (D.carrier ψ ρp') := by
  have hrd := h.holes
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
  exact (hrd ψ ρp' hs' _ hL c hc t ht j fs).mpr
    (LfpDatum.hfits_mono (hpos c hc j hf'.1) (hR _ hL) hf')

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
theorem leaf_le_of_holes (h : LfpClause acval D) {mm : Nat} (hmm : mm < D.k)
    {ψ : Name → Nat} {ρ ρ' : Nat → V} {as as' is : List V}
    (hsa : SpineFit ρ (D.params ψ) as) (hsa' : SpineFit ρ' (D.params ψ) as')
    (hsi : SpineFit (consList as ρ) (D.ids mm ψ) is)
    (hsi' : SpineFit (consList as' ρ') (D.ids mm ψ) is)
    (hs : Sat V (D.params ψ).reverse (consList as ρ))
    (hs' : Sat V (D.params ψ).reverse (consList as' ρ'))
    (hidx : D.idx ψ (consList as ρ) = D.idx ψ (consList as' ρ')) (R : FrameRel V)
    (hR : ∀ Y, InTupleSpace (D.w ψ) D.N (D.idx ψ (consList as ρ)) Y →
      R (D.frame ψ (consList as ρ) Y) (D.frame ψ (consList as' ρ') Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.CtorPos R ψ c j) :
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      ⊆ˢ (as' ++ is).foldl app (interp V ρ' (acval (D.member mm) ψ)) :=
  h.leaf_le_of_carrier_le hmm hsa hsa' hsi hsi'
    (h.carrier_le_of_holes hs hs' hidx R hR hpos)

open Classical in
/-- **The container case at a frame's GROUP** (lane CONTSEM): a container
frame abstracts only the reached part `G` of its group, the other members
read concretely — at the SMALLER parameter frame they hold the smaller
carrier.  If every constructor of a member of `G` whose fields fit at the
smaller parameter frame, with the `G`-holes at the larger carrier and the
rest at the smaller one, fits at the larger parameter frame's carrier
(what the frame walk's positivity delivers), then the smaller carrier
lies below the larger on `G` (`lfpTuple_le_on`: induction, no Bekić). -/
theorem carrier_le_on_group (h : LfpClause acval D) {ψ : Name → Nat} {ρp ρp' : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (hs' : Sat V (D.params ψ).reverse ρp')
    (hidx : D.idx ψ ρp = D.idx ψ ρp') (G : Nat → Prop)
    (hwalk : ∀ g, g < D.N → G g → ∀ t, t ∈ˢ D.idx ψ ρp g → ∀ j fs,
      D.HFits ψ ρp (fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x) t g j fs →
      D.HFits ψ ρp' (D.carrier ψ ρp') t g j fs) :
    ∀ g, g < D.N → G g → FamLe (D.idx ψ ρp g) (D.carrier ψ ρp g) (D.carrier ψ ρp' g) := by
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ ρp hs
  have hL' : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) (D.carrier ψ ρp') := by
    rw [hidx]; exact lfpTuple_mem _ _ _ _
  refine lfpTuple_le_on hcl hmono G hL' fun g hg hG t ht x hx => ?_
  have hZ : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp)
      (fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x) := by
    intro m hm
    by_cases hGm : G m
    · simp only [if_pos hGm]; exact hL' m hm
    · simp only [if_neg hGm]; exact lfpTuple_mem _ _ _ _ m hm
  obtain ⟨j, fs, hf, rfl⟩ := (h.fibre_holes hs hZ hg ht x).mp hx
  have hf' := hwalk g hg hG t ht j fs hf
  rw [← h.carrier_eq hs' hg]
  exact (h.fibre_holes hs' (lfpTuple_mem _ _ _ _) hg (by rw [← hidx]; exact ht) _).mpr
    ⟨j, fs, hf', rfl⟩

end LfpClause

/-! ## D2: an unreached member -/

/-- **An unreached member reads the tuple only at itself**: when the hole
frames of two tuples agreeing at component `m` agree off the positions
`P`, and no field or result index reading of `m`'s constructors mentions
`P` (the run found no other member's hole in `m`'s fields), then `m`'s
component of the operator is the same at both tuples — so by
`lfpTuple_eq_lfpFam_of_indep` it is the least family of `m`'s own
operator, whatever the other members are. -/
theorem readsOnly_of_holes {D : LfpDatum V} (hrd : D.ReadsHoles)
    {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp) {m : Nat} (hm : m < D.N)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (hmaps : MapsTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)) (P : Nat → Prop)
    (hag : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → X m = Y m →
      AgreeOff P (D.frame ψ ρp X) (D.frame ψ ρp Y))
    (hfree : ∀ j, j < D.nctors m → NoBVarTele P (D.fields ψ m j) ∧
      ∀ e ∈ D.resIdx ψ m j, NoBVar (shiftPN (D.fields ψ m j).length P) e) :
    ReadsOnly (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) m := by
  -- one direction of the fit, at any two tuples agreeing at `m`
  have hdir : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → X m = Y m →
      ∀ t, t ∈ˢ D.idx ψ ρp m → ∀ j fs, D.fits ψ ρp X t m j fs → D.fits ψ ρp Y t m j fs := by
    intro X Y hX hY hXY t ht j fs hf
    obtain ⟨hj, hsp, hres⟩ := (hrd ψ ρp hs X hX m hm t ht j fs).mp hf
    have hagXY := hag X Y hX hY hXY
    refine (hrd ψ ρp hs Y hY m hm t ht j fs).mpr
      ⟨hj, spineFit_congr_noBVar _ (hfree j hj).1 hagXY hsp, fun l hl => ?_⟩
    obtain ⟨e, he, heq⟩ := hres l hl
    refine ⟨e, he, ?_⟩
    rw [← heq]
    have hlen : fs.length = (D.fields ψ m j).length := hsp.length_eq
    refine (interp_congr_noBVar e ?_ (agreeOff_consList fs hagXY)).symm
    rw [hlen]; exact (hfree j hj).2 e (List.mem_of_getElem? he)
  intro X Y hX hY hXY
  refine famSpace_ext (hmaps X hX m hm) (hmaps Y hY m hm) fun t ht => ?_
  apply SetTheory.ext
  intro x
  rw [hfib X hX m hm t ht x, hfib Y hY m hm t ht x]
  constructor
  · rintro ⟨j, fs, hf, rfl⟩; exact ⟨j, fs, hdir X Y hX hY hXY t ht j fs hf, rfl⟩
  · rintro ⟨j, fs, hf, rfl⟩; exact ⟨j, fs, hdir Y X hY hX hXY.symm t ht j fs hf, rfl⟩

end ConLeche.Model
