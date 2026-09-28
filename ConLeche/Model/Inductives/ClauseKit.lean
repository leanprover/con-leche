module

public import ConLeche.SetModel.NestRec
public import ConLeche.Model.Annot.BlockLfp

public section

/-!
# An lfp clause as a class presentation

`lfpSClause D ψ Is` — the recorded clause of `D` at `ψ` as a class
presentation (`SClause`, `SetModel/NestRec.lean`) over parameter frames,
its index sets pinned at `Is`; `lfpSClause_okAt` — the kit's `ok`, from
the clause's `functor` and `fibre`; `lfpSClause_carrier` — its carrier
is the datum's.  The class kit (`ClassInd.lean`) presents every class
this way; the old node kit (`lfpNestKit`, `TargetNestKit.lean`) too.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A clause as a class presentation -/

/-- **The lfp clause of `D` at `ψ` as a class presentation** over
parameter frames, its index sets pinned at `Is`. -/
@[expose] noncomputable def lfpSClause (D : LfpDatum V) (ψ : Name → Nat) (Is : Nat → V) :
    SClause V (Nat → V) where
  w := D.w ψ
  N := D.N
  Is := Is
  Φ := D.Φ ψ
  Fits := fun ρp X t c j fs => D.HFits ψ ρp X t c j fs
  inj := D.inj ψ

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V} {ψ : Name → Nat}
  {Is : Nat → V} {ρp : Nat → V}

/-- The class's carrier at a frame whose index sets are `Is` is the
datum's carrier there. -/
theorem lfpSClause_carrier (hIs : D.idx ψ ρp = Is) :
    (lfpSClause D ψ Is).carrier ρp = D.carrier ψ ρp := by
  subst hIs; rfl

/-- **The kit's `ok`, from the clause**: at a frame satisfying the
parameter telescope whose index sets are `Is`, the class is a clause —
monotone with a closed tuple (`functor`) and its fibre the fitting
constructors' injections (`fibre`). -/
theorem lfpSClause_okAt (h : LfpClause acval D) (hsat : Sat V (D.params ψ).reverse ρp)
    (hIs : ∀ c, c < D.N → D.idx ψ ρp c = Is c) : (lfpSClause D ψ Is).OkAt ρp := by
  obtain ⟨hmono, -, ⟨L, hL⟩⟩ := h.functor ψ ρp hsat
  have hsp : ∀ X, InTupleSpace (D.w ψ) D.N Is X ↔ InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X :=
    fun X => ⟨fun hX m hm => by rw [hIs m hm]; exact hX m hm,
      fun hX m hm => by rw [← hIs m hm]; exact hX m hm⟩
  have hle : ∀ X Y, TupleLe D.N Is X Y ↔ TupleLe D.N (D.idx ψ ρp) X Y :=
    fun X Y => ⟨fun hXY m hm => by rw [hIs m hm]; exact hXY m hm,
      fun hXY m hm => by rw [← hIs m hm]; exact hXY m hm⟩
  refine ⟨fun X Y hX hY hXY => (hle _ _).mpr (hmono X Y ((hsp X).mp hX) ((hsp Y).mp hY)
      ((hle X Y).mp hXY)), ⟨L, (hsp L).mpr hL.1, (hle _ _).mpr hL.2⟩,
    fun X hX c hc t ht x => ?_⟩
  have ht' : t ∈ˢ D.idx ψ ρp c := by rw [hIs c hc]; exact ht
  exact h.fibre ψ ρp hsat X ((hsp X).mp hX) c hc t ht' x


end ConLeche.Model
