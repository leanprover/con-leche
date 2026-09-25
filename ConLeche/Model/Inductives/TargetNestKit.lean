module

public import ConLeche.SetModel.NestRecB
public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The nested recursor's classes as LFP CLAUSES (lane NESTIND, L5 (b)/(c))

The recursor model at a nested block (`graphRecPre_core`,
`BlockRecGraph.lean`) is over the recursor's CLASSES: a member of the
block, or a container at an instantiation (an outside major).  Charter
item 5: "the model uses nothing from an inductive but its lfp clause" —
so every class is presented by ONE recorded clause (`LfpClause`,
`Model/Annot/BlockLfp.lean`) at a level assignment and a parameter
frame, and this module turns clauses into the set-level kit
`NestKit` (`SetModel/NestRec.lean`) whose induction the recursor's
classes read (`NestKit.ind_recClasses`, `SetModel/NestRecCls.lean`).

* `lfpSClause D ψ Is` — the clause of `D` at `ψ` as a class presentation
  over parameter frames, its index sets pinned at `Is` (the TRUE
  frame's: a container instance's index telescope is hole-free — the
  walk's N2 — so it reads alike at every frame the induction visits);
  `lfpSClause_okAt` — the kit's `ok`, from the clause's `functor` and
  `fibre`; `lfpSClause_carrier` — its carrier is the datum's.
* `lfpNestKit` — the kit over clause classes, `ok` proved; the three
  premises that read the RUN (`trans`: positivity at the instantiation,
  `calls`: the rule's calls, `top`: the true frames' parameter
  readings) are the kit's own.
* `lfpCls_huniq` — the kit's `huniq` at `Type` from `mkInj` of every
  class's datum (`ℓ = 0` is `huniq_of_prop`, as for members).
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
    (hIs : D.idx ψ ρp = Is) : (lfpSClause D ψ Is).OkAt ρp := by
  subst hIs
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ ρp hsat
  exact ⟨hmono, hcl, fun X hX c hc t ht x => h.fibre ψ ρp hsat X hX c hc t ht x⟩

/-- **Route B's `trans` at a clause class** (`NestKitB.trans`, `w ≠ 0`): a
spine hole-fitting constructor `j` at ANY frame and tuple whose injection
lies in the carrier at the true frame `ρT` fits there: the true decoding
of the injection (the fixed point, then the fibre) has the same
constructor and fields (`mkInj`; the fit's lengths do not depend on the
frame).  No positivity. -/
theorem lfpSClause_transB (h : LfpClause acval D) (hw : D.w ψ ≠ 0)
    {ρT : Nat → V} (hsatT : Sat V (D.params ψ).reverse ρT)
    {ρ Y : Nat → V} {t : V} {c j : Nat} {fs : List V} (hc : c < D.N)
    (ht : t ∈ˢ D.idx ψ ρT c) (hf : D.HFits ψ ρ Y t c j fs)
    (hm : D.inj ψ c j fs ∈ˢ app (D.carrier ψ ρT c) t) :
    D.HFits ψ ρT (D.carrier ψ ρT) t c j fs := by
  obtain ⟨hmono, hmaps, hcl⟩ := h.functor ψ ρT hsatT
  have hfix := lfpTuple_fixed hcl hmono hmaps c hc t ht _ hm
  obtain ⟨j', fs', hf', he⟩ :=
    (h.fibre ψ ρT hsatT _ (lfpTuple_mem _ _ _ _) c hc t ht _).mp hfix
  obtain ⟨rfl, rfl⟩ := h.mkInj ψ hw c hc j fs j' fs' hf.1 hf'.1 hf.2.1.length_eq
    hf'.2.1.length_eq he
  exact hf'

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
        (Db b).idx (ψb b) ρ = (Db b).idx (ψb b) (frb b))
    (trans : ∀ b, b < nC → ∀ G,
      (∀ b' c t y, G b' c t y →
        y ∈ˢ app ((lfpSClause (Db b') (ψb b') ((Db b').idx (ψb b') (frb b'))).carrier
          (frb b') c) t) →
      ∀ ρ, Adm b G ρ → ∀ Y,
      InTupleSpace ((Db b).w (ψb b)) (Db b).N ((Db b).idx (ψb b) (frb b)) Y →
      TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) Y ((Db b).carrier (ψb b) (frb b)) →
      ∀ t c j fs, (Db b).HFits (ψb b) ρ Y t c j fs →
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
  trans := fun b hb G hG ρ hρ Y hY hle t c j fs hf => by
    have hle' : TupleLe (Db b).N ((Db b).idx (ψb b) (frb b)) Y
        ((Db b).carrier (ψb b) (frb b)) := hle
    show (Db b).HFits (ψb b) (frb b)
      ((lfpSClause (Db b) (ψb b) ((Db b).idx (ψb b) (frb b))).carrier (frb b)) t c j fs
    rw [lfpSClause_carrier rfl]
    exact trans b hb G hG ρ hρ Y hY hle' t c j fs hf
  calls := fun b hb G ρ hρ Y hY c t j fs hc ht hf u hu =>
    calls b hb G ρ hρ Y hY c t j fs hc ht hf u hu
  top := fun b hb G hG => top b hb G fun b' c t y hb' hdp hc ht hy =>
    hG b' c t y hb' hdp hc ht (by rw [lfpSClause_carrier rfl]; exact hy)

/-- **The Route B kit over clause classes** (`NestKitB`, `SetModel/NestRecB.lean`)
at `w ≠ 0` (every class at its level assignment): `ok` is the clause's,
`trans` is `lfpSClause_transB` (no positivity); `calls` and `top` are the
run's. -/
@[expose] noncomputable def lfpNestKitB (nC : Nat) (Db : Nat → LfpDatum V)
    (ψb : Nat → Name → Nat) (frb : Nat → Nat → V) (dp : Nat → Nat) (Dd : Nat)
    (hD : ∀ b, b < nC → dp b < Dd)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop)
    (pred : NDec V → V)
    (hcl : ∀ b, b < nC → LfpClause acval (Db b))
    (hw : ∀ b, b < nC → (Db b).w (ψb b) ≠ 0)
    (hAdm : ∀ b, b < nC → ∀ G ρ, Adm b G ρ →
      Sat V ((Db b).params (ψb b)).reverse ρ ∧
        (Db b).idx (ψb b) ρ = (Db b).idx (ψb b) (frb b))
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
    NestKitB V (Nat → V) where
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
  trans := fun b hb _ _ _ _ _ t c j fs hc ht hf hm => by
    have hT := hAdm b hb _ _ (top b hb (fun _ _ _ _ => True) fun _ _ _ _ _ _ _ _ _ => trivial)
    show (Db b).HFits (ψb b) (frb b)
      ((lfpSClause (Db b) (ψb b) ((Db b).idx (ψb b) (frb b))).carrier (frb b)) t c j fs
    rw [lfpSClause_carrier rfl]
    have hm' : (Db b).inj (ψb b) c j fs ∈ˢ app ((Db b).carrier (ψb b) (frb b) c) t := by
      have := hm
      simp only [lfpSClause_carrier rfl] at this
      exact this
    exact lfpSClause_transB (hcl b hb) (hw b hb) hT.1 hc ht hf hm'
  calls := fun b hb G ρ hρ Y hY c t j fs hc ht hf u hu =>
    calls b hb G ρ hρ Y hY c t j fs hc ht hf u hu
  top := fun b hb G hG => top b hb G fun b' c t y hb' hdp hc ht hy =>
    hG b' c t y hb' hdp hc ht (by rw [lfpSClause_carrier rfl]; exact hy)

/-- The kit's TRUE class `b` is the datum's carrier at the true frame. -/
theorem lfpNestKit_KT {nC : Nat} {Db : Nat → LfpDatum V} {ψb : Nat → Name → Nat}
    {frb : Nat → Nat → V} {dp : Nat → Nat} {Dd : Nat} {hD : ∀ b, b < nC → dp b < Dd}
    {Adm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop} {pred : NDec V → V}
    {hcl} {hAdm} {trans} {calls} {top} (b : Nat) :
    (lfpNestKit (acval := acval) nC Db ψb frb dp Dd hD Adm pred hcl hAdm trans calls top).KT b
      = (Db b).carrier (ψb b) (frb b) :=
  lfpSClause_carrier rfl

/-! ## `huniq` at `Type`, class by class -/

/-- **The kit's `huniq` at `Type`**, over clause classes: recursor
class `c` reads clause `Dc c` at `ψc c`, component `mc c`, frame
`fc xs c`; a decoding's fields fit that component's constructor at the
carrier (the hole fit); at a `Type`-valued class two decodings of one
major are equal by the clause's `mkInj`. -/
theorem lfpCls_huniq {K : Nat} {nCt : Nat → Nat} {Dc : Nat → LfpDatum V}
    {ψc : Nat → Name → Nat} {mc : Nat → Nat} {fc : List V → Nat → Nat → V}
    {Is : List V → Nat → V} {B : V → V} {xs : List V}
    (hcl : ∀ c, c < K → LfpClause acval (Dc c))
    (hw : ∀ c, c < K → (Dc c).w (ψc c) ≠ 0)
    (hmc : ∀ c, c < K → mc c < (Dc c).N) :
    ∀ u, u ∈ˢ unionSet K (Is xs) (fun c => (Dc c).carrier (ψc c) (fc xs c) (mc c)) →
      ∀ e e',
        graphDecG Is (fun c => (Dc c).inj (ψc c) (mc c)) nCt K
          (fun xs c i j fs => (Dc c).HFits (ψc c) (fc xs c)
            ((Dc c).carrier (ψc c) (fc xs c)) i (mc c) j fs) xs u e →
        graphDecG Is (fun c => (Dc c).inj (ψc c) (mc c)) nCt K
          (fun xs c i j fs => (Dc c).HFits (ψc c) (fc xs c)
            ((Dc c).carrier (ψc c) (fc xs c)) i (mc c) j fs) xs u e' →
      e = e' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' := by
  rintro u - ⟨c, j, fs⟩ ⟨c', j', fs'⟩ ⟨hc, -, i, -, hf, rfl⟩ ⟨-, -, i', -, hf', heq⟩
  obtain ⟨rfl, rfl, hinj⟩ := tagged_inj heq
  obtain ⟨hj, hsp, -⟩ := hf
  obtain ⟨hj', hsp', -⟩ := hf'
  obtain ⟨rfl, rfl⟩ := (hcl c hc).mkInj (ψc c) (hw c hc) (mc c) (hmc c hc) j fs j' fs' hj hj'
    hsp.length_eq hsp'.length_eq hinj
  exact Or.inl rfl

end ConLeche.Model
