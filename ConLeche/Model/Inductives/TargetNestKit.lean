module

public import ConLeche.SetModel.NestRec
public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The nested recursor's classes as LFP CLAUSES

The recursor model at a nested block (`graphRecPre_core`,
`BlockRecGraph.lean`) is over the recursor's CLASSES: a member of the
block, or a container at an instantiation (an outside major).  Charter
item 5: "the model uses nothing from an inductive but its lfp clause" —
so every class is presented by ONE recorded clause (`LfpClause`,
`Model/Env/BlockLfp.lean`) at a level assignment and a parameter
frame, and this module turns clauses into the set-level kit
`NestKit` (`SetModel/NestRec.lean`) whose induction the recursor's
classes read (`NestNodeInd.ind_recNodesOn`, `SetModel/NestRecCls.lean`).

* `lfpSClause D ψ Is` — the clause of `D` at `ψ` as a class presentation
  over parameter frames, its index sets pinned at `Is` (the TRUE
  frame's: a container instance's index telescope is hole-free — the
  walk's N2 — so it reads alike at every frame the induction visits);
  `lfpSClause_okAt` — the kit's `ok`, from the clause's `mono`/`closed` and
  `fibre`; `lfpSClause_carrier` — its carrier is the datum's.
* `lfpNestKit` — the kit over clause classes, `ok` proved; the three
  premises that read the RUN (`trans`: positivity at the instantiation,
  `calls`: the rule's calls, `top`: the true frames' parameter
  readings) are the kit's own.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetTheory

open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A clause as a class presentation -/

/-- **The lfp clause of `D` at `ψ` as a class presentation** over
finite parameter frames `Fin len → V` (with fixed tail `tail`), its index sets pinned at `Is`. -/
@[expose] noncomputable def lfpSClause (D : LfpDatum V) (ψ : Name → Nat) (Is : Nat → V)
    (len : Nat) (tail : Nat → V) :
    SClause V len where
  w := D.w ψ
  N := D.N
  Is := Is
  Φ := fun ρ => D.Φ ψ (prepend ρ tail)
  hΦ := fun ρ => D.hΦ ψ (prepend ρ tail)
  Fits := fun ρ X t c j fs => D.HFits ψ (prepend ρ tail) X t c j fs
  inj := D.inj ψ

variable {acval : Name → (Name → Nat) → Term} {D : LfpDatum V} {ψ : Name → Nat}
  {Is : Nat → V} {len : Nat} {tail : Nat → V} {ρp : Fin len → V}

/-- The class's carrier at a frame whose index sets are `Is` is the
datum's carrier there. -/
theorem lfpSClause_carrier (hIs : D.idx ψ (prepend ρp tail) = Is) :
    (lfpSClause D ψ Is len tail).carrier ρp = D.carrier ψ (prepend ρp tail) := by
  subst hIs; rfl

/-- **The kit's `ok`, from the clause**: at a frame satisfying the
parameter telescope whose index sets are `Is`, the class is a clause —
monotone (`LfpClause.mono`), mapping the tuple space into itself
(`LfpClause.maps`), with a closed tuple (`LfpClause.closed`) and its fibre the fitting
constructors' injections (`fibre`). -/
theorem lfpSClause_okAt (h : LfpClause acval D)
    (hsat : Sat V (D.params ψ).reverse (prepend ρp tail))
    (hIs : ∀ c, c < D.N → D.idx ψ (prepend ρp tail) c = Is c) :
    (lfpSClause D ψ Is len tail).OkAt ρp := by
  have hmono := h.mono hsat
  have hmaps := h.maps ψ (prepend ρp tail) hsat
  obtain ⟨L, hL⟩ := h.closed hsat
  have hsp : ∀ X, InTupleSpace (D.w ψ) D.N Is X ↔
      InTupleSpace (D.w ψ) D.N (D.idx ψ (prepend ρp tail)) X :=
    fun X => ⟨fun hX m hm => by rw [hIs m hm]; exact hX m hm,
      fun hX m hm => by rw [← hIs m hm]; exact hX m hm⟩
  have hle : ∀ X Y, TupleLe D.N Is X Y ↔ TupleLe D.N (D.idx ψ (prepend ρp tail)) X Y :=
    fun X Y => ⟨fun hXY m hm => by rw [hIs m hm]; exact hXY m hm,
      fun hXY m hm => by rw [← hIs m hm]; exact hXY m hm⟩
  refine ⟨fun X Y hX hY hXY => (hle _ _).mpr (hmono X Y ((hsp X).mp hX) ((hsp Y).mp hY)
      ((hle X Y).mp hXY)), fun X hX => (hsp _).mpr (hmaps X ((hsp X).mp hX)),
    ⟨L, (hsp L).mpr hL.1, (hle _ _).mpr hL.2⟩,
    fun X hX c hc t ht x => ?_⟩
  have ht' : t ∈ˢ D.idx ψ (prepend ρp tail) c := by rw [hIs c hc]; exact ht
  exact h.fibre ψ (prepend ρp tail) hsat X ((hsp X).mp hX) c hc t ht' x

/-! ## The kit over clause classes -/

/-- **A class's index sets, pinned**: its clause's at its true frame if it
is live, empty otherwise (a class whose true frame does not fit its block
has no element, and the clause tells nothing there). -/
@[expose] noncomputable def pinIdx (D : LfpDatum V) (ψ : Name → Nat) (fr : Nat → V)
    (live : Prop) : Nat → V :=
  open Classical in fun c => if live then D.idx ψ fr c else empty

theorem pinIdx_of {fr : Nat → V} {live : Prop} (h : live) : pinIdx D ψ fr live = D.idx ψ fr := by
  classical
  funext c; exact ite_eq_left h

theorem live_of_mem_pinIdx {fr : Nat → V} {live : Prop} {c : Nat} {t : V}
    (h : t ∈ˢ pinIdx D ψ fr live c) : live := by
  classical
  by_cases hl : live
  · exact hl
  · simp only [pinIdx, ite_eq_right hl] at h; exact absurd h (not_mem_empty t)

/-- **The nested kit over clause classes**: class `b < nC` is the
clause of `Db b` at `ψb b`, its index sets pinned at its TRUE frame `frb b`
where it is live (`pinIdx`); it is visited at admissible parameter frames
(`Adm`, only at a live class: they satisfy the telescope and read the true
frame's index sets, `hAdm`).  `ok` is the clause's (`lfpSClause_okAt`);
`trans`, `calls` and `top` are the run's. -/
@[expose] noncomputable def lfpNestKit (nC : Nat) (Db : Nat → LfpDatum V)
    (ψb : Nat → Name → Nat) (frLen : Nat → Nat) (tailb : Nat → Nat → V)
    (frb : (b : Nat) → Fin (frLen b) → V) (live : Nat → Prop) (dp : Nat → Nat) (Dd : Nat)
    (hD : ∀ b, b < nC → dp b < Dd)
    (Adm : (b : Nat) → V → (Fin (frLen b) → V) → Prop)
    (pred : NDec V → V)
    (hcl : ∀ b, b < nC → LfpClause acval (Db b))
    (hAdm : ∀ b, b < nC → ∀ (G : V) (ρ : Fin (frLen b) → V), Adm b G ρ → live b ∧
      Sat V ((Db b).params (ψb b)).reverse (prepend ρ (tailb b)) ∧
        ∀ c, c < (Db b).N →
          (Db b).idx (ψb b) (prepend ρ (tailb b)) c =
            (Db b).idx (ψb b) (prepend (frb b) (tailb b)) c)
    (trans : ∀ b, b < nC → ∀ G : V,
      (∀ b' c t y, nenc b' c t y ∈ˢ G →
        y ∈ˢ app ((lfpSClause (Db b') (ψb b')
          (pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b'))
          (frLen b') (tailb b')).carrier (frb b') c) t) →
      ∀ ρ, Adm b G ρ → ∀ Y,
      InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y →
      TupleLe (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y
        ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) →
      ∀ t c j fs, c < (Db b).N →
        (Db b).HFits (ψb b) (prepend ρ (tailb b)) Y t c j fs →
        (Db b).HFits (ψb b) (prepend (frb b) (tailb b))
          ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) t c j fs)
    (calls : ∀ b, b < nC → ∀ (G : V) ρ, Adm b G ρ → ∀ Y,
      InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y →
      ∀ c t j fs, c < (Db b).N → t ∈ˢ (Db b).idx (ψb b) (prepend (frb b) (tailb b)) c →
      (Db b).HFits (ψb b) (prepend ρ (tailb b)) Y t c j fs →
      ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (Db b').N ∧ live b' ∧
        t' ∈ˢ (Db b').idx (ψb b') (prepend (frb b') (tailb b')) c' ∧ u = nenc b' c' t' y ∧
        ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ nenc b' c' t' y ∈ˢ G ∨
          (dp b < dp b' ∧ ∃ ρ',
            Adm b' (addOwn G b (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y) ρ' ∧
            y ∈ˢ app ((lfpSClause (Db b') (ψb b')
              ((Db b').idx (ψb b') (prepend (frb b') (tailb b')))
              (frLen b') (tailb b')).carrier ρ' c') t')))
    (top : ∀ b, b < nC → live b → ∀ G : V,
      (∀ b' c t y, b' < nC → dp b' < dp b → c < (Db b').N →
        live b' → t ∈ˢ (Db b').idx (ψb b') (prepend (frb b') (tailb b')) c →
        y ∈ˢ app ((Db b').carrier (ψb b') (prepend (frb b') (tailb b')) c) t →
        nenc b' c t y ∈ˢ G) →
      Adm b G (frb b)) :
    NestKit V where
  nC := nC
  frLen := frLen
  cl := fun b => lfpSClause (Db b) (ψb b)
    (pinIdx (Db b) (ψb b) (prepend (frb b) (tailb b)) (live b)) (frLen b) (tailb b)
  fr := frb
  dp := dp
  D := Dd
  hD := hD
  Adm := Adm
  pred := pred
  ok := fun b hb G ρ hρ => by
    obtain ⟨hl, hsat, hidx⟩ := hAdm b hb G ρ hρ
    refine lfpSClause_okAt (hcl b hb) hsat fun c hc => ?_
    rw [pinIdx_of hl]; exact hidx c hc
  trans := fun b hb G hG ρ hρ Y hY hle t c j fs hc hf => by
    have hl := (hAdm b hb G ρ hρ).1
    show (Db b).HFits (ψb b) (prepend (frb b) (tailb b))
      ((lfpSClause (Db b) (ψb b) (pinIdx (Db b) (ψb b) (prepend (frb b) (tailb b)) (live b))
        (frLen b) (tailb b)).carrier (frb b)) t c j fs
    rw [pinIdx_of hl, lfpSClause_carrier rfl]
    have hY' : InTupleSpace ((Db b).w (ψb b)) (Db b).N
        ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y := by
      have := hY; simp only [lfpSClause] at this; rw [pinIdx_of hl] at this; exact this
    have hle' : TupleLe (Db b).N ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y
        ((Db b).carrier (ψb b) (prepend (frb b) (tailb b))) := by
      have := hle
      simp only [SClause.carrier, lfpSClause] at this
      rw [pinIdx_of hl] at this
      exact this
    exact trans b hb G hG ρ hρ Y hY' hle' t c j fs hc hf
  calls := fun b hb G ρ hρ Y hY c t j fs hc ht hf u hu => by
    have hl := (hAdm b hb G ρ hρ).1
    have hY' : InTupleSpace ((Db b).w (ψb b)) (Db b).N
        ((Db b).idx (ψb b) (prepend (frb b) (tailb b))) Y := by
      have := hY; simp only [lfpSClause] at this; rw [pinIdx_of hl] at this; exact this
    have ht' : t ∈ˢ (Db b).idx (ψb b) (prepend (frb b) (tailb b)) c := by
      have := ht; simp only [lfpSClause] at this; rw [pinIdx_of hl] at this; exact this
    obtain ⟨b', c', t', y, hb', hc', hl', ht'', rfl, hcase⟩ :=
      calls b hb G ρ hρ Y hY' c t j fs hc ht' hf u hu
    refine ⟨b', c', t', y, hb', hc', ?_, rfl, ?_⟩
    · show t' ∈ˢ pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b') c'
      rw [pinIdx_of hl']; exact ht''
    · show (b' = b ∧ _) ∨ nenc b' c' t' y ∈ˢ G ∨ (dp b < dp b' ∧ ∃ ρ', Adm b'
        (addOwn G b (Db b).N (pinIdx (Db b) (ψb b) (prepend (frb b) (tailb b)) (live b)) Y) ρ' ∧
        y ∈ˢ app ((lfpSClause (Db b') (ψb b')
          (pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b'))
          (frLen b') (tailb b')).carrier ρ' c') t')
      rw [pinIdx_of hl]
      rcases hcase with h | h | ⟨hlt, ρ', hρ', hy⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨hlt, ρ', hρ', ?_⟩)
        rw [pinIdx_of hl']; exact hy
  top := fun b hb hne G hG => by
    obtain ⟨c, -, t, ht⟩ := hne
    have hl : live b := live_of_mem_pinIdx ht
    refine top b hb hl G fun b' c t y hb' hdp hc hl' ht' hy => hG b' c t y hb' hdp hc ?_ ?_
    · show t ∈ˢ pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b') c
      rw [pinIdx_of hl']; exact ht'
    · show y ∈ˢ app ((lfpSClause (Db b') (ψb b')
        (pinIdx (Db b') (ψb b') (prepend (frb b') (tailb b')) (live b'))
        (frLen b') (tailb b')).carrier (frb b') c) t
      rw [pinIdx_of hl', lfpSClause_carrier rfl]; exact hy

end ConLeche.Model
