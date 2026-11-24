module

public import ConLeche.SetModel.Ops
public import ConLeche.Term.Const
public import ConLeche.SetTheory.Derive.Quot
public import ConLeche.SetTheory.Derive.Choice
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TupleTower

@[expose] public section

/-!
# The built-in constants

`bval` and its value towers, over the value-read `piV`/`lamV`
(`SetModel/Ops.lean`).

## The reading

Every abstraction in a constant's tower is `lamV`, and every space a
binder ranges over is the value reading of the binder's spelled type
(`BConst.typeAV`): a `piV`, whose regime is read off its fibres.  So
over an empty domain a space is `{pt}` and an abstraction the point,
on both sides, and every constant is a member of its type by
`lamV_mem` down its binders.  Where a body's type is a truth value
(`psigmaMk` at `max u v = 0`) the body is the point outright.

## The law surface

Each constant's application law is `app_lamV` down its binders: no
premise beyond domain membership, at every level.

`Empty.rec` is the point: its inner abstraction is over `∅`.
`quotLiftR` is the quotient lift as an abstraction over the quotient
set.  The other `SetTheory` operators used here (`natrec`, `schoice`,
`quotSet`, `quotClass`, `qrep`, `sigmaSet`, `sfst`/`ssnd`, `lfpFamSet`,
`lfpTuple`) need no replacement; the least fixed points' families are
members of the value-read family space `lfpFamSpace` (`famOf`).
-/

namespace ConLeche.SetModel

open SetTheory
open ConLeche.Term (BConst lv quotCl)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat.succ` -/

/-- `Nat.succ : Nat → Nat`. -/
noncomputable def natSuccV : V := lamV omega natsucc

theorem natSuccV_app {n : V} (hn : n ∈ˢ (omega : V)) :
    app (natSuccV V) n = natsucc n := app_lamV hn

/-- A successor is not the point: it is a natural number. -/
theorem natsucc_ne_pt {n : V} (hn : n ∈ˢ (omega : V)) : natsucc n ≠ pt := fun h =>
  pt_not_mem_omega (h ▸ natsucc_mem hn)

/-- `Nat.succ`'s abstraction is the graph regime's. -/
theorem natSuccV_eq_lamR : natSuccV V = lamR 1 (omega : V) natsucc :=
  lamV_eq_pos Nat.one_ne_zero natzero_mem (natsucc_ne_pt V natzero_mem)

theorem natSuccV_mem : natSuccV V ∈ˢ piR 1 (omega : V) fun _ => omega := by
  rw [natSuccV_eq_lamR]; exact lamR_mem fun _ hx => natsucc_mem hx

theorem natSuccV_memV : natSuccV V ∈ˢ piV (omega : V) fun _ => omega :=
  lamV_mem (fun _ hx => natsucc_mem hx) fun _ _ => IsTy_omega

/-! ## `Nat.rec` -/

/-- `Nat → Sort u`, the motive space. -/
noncomputable def natMotiveSpace (u : Nat) : V := piV omega fun _ => univ u

/-- `(n : Nat) → M n → M (n+1)`, the minor-premise space. -/
noncomputable def natStepSpace (M : V) : V :=
  piV omega fun n => piV (app M n) fun _ => app M (natsucc n)

/-- `Nat.rec.{u}`. -/
noncomputable def natRecV (u : Nat) : V :=
  lamV (natMotiveSpace V u) fun M =>
    lamV (app M natzero) fun z =>
      lamV (natStepSpace V M) fun s =>
        lamV omega fun n => natrec z s n

theorem natMotive_apply {u : Nat} {M n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hn : n ∈ˢ (omega : V)) : app M n ∈ˢ (univ u : V) :=
  app_mem_piV hM hn

/-- The step premise, unpacked: two eliminations, no fibre premise. -/
theorem natStep_apply {M s : V} (hs : s ∈ˢ natStepSpace V M) :
    ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (natsucc k) :=
  fun k hk _ hih => by
    have h1 : app s k ∈ˢ piV (app M k) fun _ => app M (natsucc k) := app_mem_piV hs hk
    exact app_mem_piV h1 hih

theorem natRecV_mem_fibre {M z s n : V}
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V M)
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n :=
  natrec_mem hz (natStep_apply V hs) hn

/-- ι for `Nat.rec`: four βs, no premise but domain membership. -/
theorem natRecV_app {u : Nat} {M z s n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V M)
    (hn : n ∈ˢ (omega : V)) :
    app (app (app (app (natRecV V u) M) z) s) n = natrec z s n := by
  rw [natRecV, app_lamV hM, app_lamV hz, app_lamV hs, app_lamV hn]

/-- `Nat.rec` inhabits its type. -/
theorem natRecV_mem (u : Nat) :
    natRecV V u ∈ˢ piV (natMotiveSpace V u) fun M =>
      piV (app M natzero) fun _ =>
        piV (natStepSpace V M) fun _ =>
          piV omega fun n => app M n := by
  refine lamV_mem (fun M hM => lamV_mem (fun z hz => lamV_mem (fun s hs =>
    lamV_mem (fun n hn => natRecV_mem_fibre V hz hs hn)
      fun n hn => IsTy_of_mem_univ (natMotive_apply V hM hn))
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV

/-! ## The dependent pair `.psigma` -/

/-- `A → Sort v`, the fibre space, as the value reading has it: over an
empty `A` it is `{pt}` (task #342, L16). -/
noncomputable def psigmaFibreSpace (v : Nat) (A : V) : V :=
  piV A fun _ => univ v

theorem psigmaFibre_apply {v : Nat} {A B a : V} (hB : B ∈ˢ psigmaFibreSpace V v A)
    (ha : a ∈ˢ A) : app B a ∈ˢ (univ v : V) :=
  app_mem_piV hB ha

/-- Over an inhabited `A` the fibre space is the graph space. -/
theorem lamR_mem_psigmaFibreSpace {v : Nat} {A x : V} {F : V → V} (hx : x ∈ˢ A)
    (hF : ∀ y, y ∈ˢ A → F y ∈ˢ (univ v : V)) : lamR (v + 1) A F ∈ˢ psigmaFibreSpace V v A := by
  unfold psigmaFibreSpace
  rw [piV_univ_eq_pos (Nat.succ_ne_zero v) hx _ fun _ _ => ⟨v, rfl⟩]
  exact lamR_mem hF

/-- A family of types over `A` is in the fibre space. -/
theorem lamV_mem_psigmaFibreSpace {v : Nat} {A : V} {F : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ (univ v : V)) : lamV A F ∈ˢ psigmaFibreSpace V v A :=
  lamV_mem hF fun _ _ => IsTy_univ v

/-- The fibre space is inhabited: by the constant family `∅` (the
point over an empty domain). -/
theorem lamV_empty_mem_psigmaFibreSpace (v : Nat) (A : V) :
    lamV A (fun _ => (empty : V)) ∈ˢ psigmaFibreSpace V v A :=
  lamV_mem_psigmaFibreSpace V fun _ _ => empty_mem_univ v

/-- The dependent pair `.psigma.{u,v}` — a type former. -/
noncomputable def psigmaV (u v : Nat) : V :=
  lamV (univ u) fun A =>
    lamV (psigmaFibreSpace V v A) fun B =>
      sigmaSet (Nat.max u v) A fun x => app B x

theorem psigmaV_app {u v : Nat} {A B : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) :
    app (app (psigmaV V u v) A) B = sigmaSet (Nat.max u v) A fun x => app B x := by
  rw [psigmaV, app_lamV hA, app_lamV hB]

/-- The pair former inhabits its type. -/
theorem psigmaV_mem (u v : Nat) :
    psigmaV V u v ∈ˢ piV (univ u : V) fun A =>
      piV (psigmaFibreSpace V v A) fun _ => (univ (Nat.max u v) : V) :=
  lamV_mem (fun _ hA => lamV_mem (fun _ hB =>
      sigma_mem_univ hA fun _ hx => psigmaFibre_apply V hB hx)
    fun _ _ => IsTy_univ _) fun _ _ => IsTy_piV

/-- The pair former is the graph regime's at both binders: its domains
are inhabited and its values are types. -/
theorem psigmaV_eq_lamR (u v : Nat) :
    psigmaV V u v = lamR (Nat.max u v + 1) (univ u : V) fun A =>
      lamR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun B =>
        sigmaSet (Nat.max u v) A fun x => app B x := by
  have hin : ∀ A, A ∈ˢ (univ u : V) →
      (lamV (psigmaFibreSpace V v A) fun B => sigmaSet (Nat.max u v) A fun x => app B x)
        = lamR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun B =>
          sigmaSet (Nat.max u v) A fun x => app B x := fun A hA =>
    lamV_eq_pos (Nat.succ_ne_zero _) (lamV_empty_mem_psigmaFibreSpace V v A)
      (ne_pt_of_mem_univ (sigma_mem_univ hA fun _ hx =>
        psigmaFibre_apply V (lamV_empty_mem_psigmaFibreSpace V v A) hx))
  rw [psigmaV, lamV_eq_pos (Nat.succ_ne_zero _) (empty_mem_univ u)
    (by rw [hin _ (empty_mem_univ u)]; exact lamR_ne_pt (Nat.succ_ne_zero _))]
  exact lamR_congr hin

/-- Its constructor `.psigmaMk.{u,v}`.  At `max u v = 0` the pair type
is a truth value, so the pair is the point; the abstractions over it
are the point too. -/
noncomputable def psigmaMkV (u v : Nat) : V :=
  lamV (univ u) fun A =>
    lamV (psigmaFibreSpace V v A) fun B =>
      lamV A fun a =>
        lamV (app B a) fun b => if Nat.max u v = 0 then pt else spair a b

theorem psigmaMkV_app {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    app (app (app (app (psigmaMkV V u v) A) B) a) b =
      if Nat.max u v = 0 then pt else spair a b := by
  rw [psigmaMkV, app_lamV hA, app_lamV hB, app_lamV ha, app_lamV hb]

/-- Where the pair type is a truth value the constructor is the point. -/
theorem psigmaMkV_eq_pt {u v : Nat} (hw : Nat.max u v = 0) : psigmaMkV V u v = pt :=
  lamV_eq_pt fun _ _ => lamV_eq_pt fun _ _ => lamV_eq_pt fun _ _ => lamV_eq_pt fun _ _ =>
    ite_eq_left hw

/-- The pair constructor inhabits its type. -/
theorem psigmaMkV_mem (u v : Nat) :
    psigmaMkV V u v ∈ˢ piV (univ u : V) fun A =>
      piV (psigmaFibreSpace V v A) fun B =>
        piV A fun a => piV (app B a) fun _ =>
          sigmaSet (Nat.max u v) A fun x => app B x := by
  refine lamV_mem (fun A hA => lamV_mem (fun B hB => lamV_mem (fun a ha =>
    lamV_mem (fun b hb => ?_) fun _ _ =>
      IsTy_of_mem_univ (sigma_mem_univ hA fun _ hx => psigmaFibre_apply V hB hx))
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV
  split
  · rename_i hw
    rw [hw]
    exact pt_mem_sigma ha hb
  · rename_i hw
    exact spair_mem hw ha hb

/-! ## `Quot` -/

/-- `A → A → Prop`.  Over an inhabited `A` both function spaces are
graph spaces (`Prop` is a type, not a truth value); over an empty `A`
the space is `{pt}`. -/
noncomputable def relSpace (A : V) : V :=
  piV A fun _ => piV A fun _ => univ 0

/-- `Quot.{u}` — a type former over `Sort u`, building its quotient at the construction level
`c` (`ConLeche.Term.quotCl`). -/
noncomputable def quotV (u c : Nat) : V :=
  lamV (univ u) fun A =>
    lamV (relSpace V A) fun R => quotSet c A R

theorem quotV_app {u c : Nat} {A R : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) :
    app (app (quotV V u c) A) R = quotSet c A R := by
  rw [quotV, app_lamV hA, app_lamV hR]

/-- `Quot.mk.{u}`, at the construction level `c`. -/
noncomputable def quotMkV (u c : Nat) : V :=
  lamV (univ u) fun A =>
    lamV (relSpace V A) fun R =>
      lamV A fun a => quotClass c A R a

theorem quotMkV_app {u c : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u c) A) R) a = quotClass c A R a := by
  rw [quotMkV, app_lamV hA, app_lamV hR, app_lamV ha]

/-- The lift of `f` to the quotient: the abstraction over the quotient
set applying `f` to each class's representative. -/
noncomputable def quotLiftR (u : Nat) (A R f : V) : V :=
  lamV (quotSet u A R) fun q => app f (qrep u A R q)

theorem quotLiftR_app {u : Nat} {A R f q : V} (hq : q ∈ˢ quotSet u A R) :
    app (quotLiftR V u A R f) q = app f (qrep u A R q) := by
  rw [quotLiftR]; exact app_lamV hq

theorem quotLiftR_mem {u : Nat} {A R f B : V}
    (hf : f ∈ˢ piV A fun _ => B) (hB : IsTy B) :
    quotLiftR V u A R f ∈ˢ piV (quotSet u A R) fun _ => B :=
  lamV_mem (fun _q hq => app_mem_piV hf (qrep_spec hq).1) fun _ _ => hB

/-! ## `Quot.lift` -/

/-- `∀ a b, r a b → f a = f b`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  piV A fun a => piV A fun b =>
    piV (app (app R a) b) fun _ => eqv (app f a) (app f b)

/-- The invariance premise, read off a proof's membership: three
eliminations. -/
theorem quotInv_of_mem {A R f h : V} (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      app f a = app f b := by
  intro a b ha hb hw
  obtain ⟨wv, hwv⟩ := hw
  rw [quotInvSpace] at hh
  have h1 : app h a ∈ˢ piV A fun b =>
      piV (app (app R a) b) fun _ => eqv (app f a) (app f b) := app_mem_piV hh ha
  have h2 : app (app h a) b ∈ˢ
      piV (app (app R a) b) fun _ => eqv (app f a) (app f b) := app_mem_piV h1 hb
  have h3 := app_mem_piV h2 hwv
  exact eq_of_mem_eqv h3

/-- `Quot.lift.{u,v}`, over the quotient at the construction level `c`. -/
noncomputable def quotLiftV (u v c : Nat) : V :=
  lamV (univ u) fun A =>
    lamV (relSpace V A) fun R =>
      lamV (univ v) fun B =>
        lamV (piV A fun _ => B) fun f =>
          lamV (quotInvSpace V A R f) fun _ => quotLiftR V c A R f

/-- **ι for `Quot.lift`**: five βs, no premise but domain membership. -/
theorem quotLiftV_app {u v c : Nat} {A R B f h : V}
    (hA : A ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V A)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piV A fun _ => B)
    (hh : h ∈ˢ quotInvSpace V A R f) :
    app (app (app (app (app (quotLiftV V u v c) A) R) B) f) h =
      quotLiftR V c A R f := by
  rw [quotLiftV, app_lamV hA, app_lamV hR, app_lamV hB, app_lamV hf, app_lamV hh]

/-- `Quot.lift` inhabits its type. -/
theorem quotLiftV_mem (u v c : Nat) :
    quotLiftV V u v c ∈ˢ piV (univ u : V) fun A =>
      piV (relSpace V A) fun R =>
        piV (univ v : V) fun B =>
          piV (piV A fun _ => B) fun f =>
            piV (quotInvSpace V A R f) fun _ =>
              piV (quotSet c A R) fun _ => B :=
  lamV_mem (fun _ _ => lamV_mem (fun _ _ => lamV_mem (fun _ hB =>
    lamV_mem (fun _ hf => lamV_mem (fun _ _ => quotLiftR_mem V hf (IsTy_of_mem_univ hB))
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV)
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV

/-! ## `Classical.choice` -/

/-- `¬¬A`, i.e. `(A → False) → False`: a truth value. -/
noncomputable def dnegSpace (A : V) : V :=
  piR 0 (piR 0 A fun _ => empty) fun _ => empty

theorem piR_zero_empty (B : V → V) : piR 0 (empty : V) B = unitSet := by
  rw [piR_zero, truthVal_eq_unitSet (fun x hx => absurd hx (not_mem_empty x))]

/-- `empty` (`False`) is a truth value. -/
theorem empty_mem_univZero : (empty : V) ∈ˢ (univZero : V) := by
  have h0 := empty_mem_univ (V := V) 0
  rwa [univ_zero] at h0

/-- The value-read `¬¬A` is `dnegSpace`: every fibre is `False`. -/
theorem piV_dneg_eq (A : V) :
    (piV (piV A fun _ => (empty : V)) fun _ => (empty : V)) = dnegSpace V A := by
  rw [piV_eq_zero fun _ _ => empty_mem_univZero V, dnegSpace,
    piV_eq_zero fun _ _ => empty_mem_univZero V]

/-- A `¬¬A` inhabitant witnesses that `A` is inhabited. -/
theorem exists_mem_of_dneg {A h : V} (hh : h ∈ˢ dnegSpace V A) :
    ∃ x, x ∈ˢ A := by
  rcases Classical.em (∃ x, x ∈ˢ A) with hex | hne
  · exact hex
  · exfalso
    have hA : A = empty := eq_empty fun z hz => hne ⟨z, hz⟩
    subst hA
    have hpt : (pt : V) ∈ˢ piR 0 (empty : V) fun _ => (empty : V) := by
      rw [piR_zero_empty]; exact pt_mem_unitSet
    rw [dnegSpace] at hh
    exact not_mem_empty _ (app_mem_piR hh hpt fun _ _ _ => empty_mem_univZero V)

/-- `Classical.choice.{u}`. -/
noncomputable def choiceV (u : Nat) : V :=
  lamV (univ u) fun A => lamV (dnegSpace V A) fun _ => schoice A

theorem choiceV_app {u : Nat} {A h : V} (hA : A ∈ˢ (univ u : V))
    (hh : h ∈ˢ dnegSpace V A) : app (app (choiceV V u) A) h = schoice A := by
  rw [choiceV, app_lamV hA, app_lamV hh]

/-- `Classical.choice` inhabits its type. -/
theorem choiceV_mem (u : Nat) :
    choiceV V u ∈ˢ piV (univ u : V) fun A => piV (dnegSpace V A) fun _ => A :=
  lamV_mem (fun _ hA => lamV_mem (fun _ hh => schoice_mem (exists_mem_of_dneg V hh).choose_spec)
    fun _ _ => IsTy_of_mem_univ hA) fun _ _ => IsTy_piV

/-! ## `Empty.rec` -/

/-- `Empty.{u} → Sort v`: `{pt}`, the domain being empty. -/
noncomputable def emptyMotiveSpace (v : Nat) : V :=
  piV empty fun _ => univ v

/-- `Empty.rec.{u,v}`: an abstraction over an abstraction over `∅`,
the point. -/
noncomputable def emptyRecV (v : Nat) : V :=
  lamV (emptyMotiveSpace V v) fun _ => lamV empty fun _ => empty

/-! ## `lfpFam` (task #188, indexed)

The least pre-fixed point of a functor on FAMILIES over an index set `I`
(`lfpFamSet`, `ConLeche/SetTheory/Derive/LfpFam.lean`).  The family space
`I → Sort w` is the value reading's (`piV`: `{pt}` over an empty `I`,
the graphs into `univ w` otherwise), and the least fixed points are its
members (`famOf`).  Total: the value is a member of the family space
for EVERY functor. -/

/-- `I → Sort w`, the family space, as the value reading has it. -/
noncomputable def lfpFamSpace (w : Nat) (I : V) : V := piV I fun _ => univ w

/-- **The family space is the families of types** (`famSpaceIn`, whose
empty-index case is the value reading's `{pt}`; task #342, L16). -/
theorem lfpFamSpace_eq (w : Nat) (I : V) : lfpFamSpace V w I = famSpaceIn (univ w) I := by
  unfold lfpFamSpace
  by_cases hI : ∃ i, i ∈ˢ I
  · obtain ⟨i, hi⟩ := hI
    rw [famSpaceIn_of_ne ⟨i, hi⟩, piV_univ_eq_pos (Nat.succ_ne_zero w) hi _
      (fun _ _ => ⟨w, rfl⟩), piR_pos (Nat.succ_ne_zero w)]
  · rw [famSpaceIn_of_empty hI, piV_of_empty fun x hx => hI ⟨x, hx⟩]

/-- Over an inhabited index set the family space is the graph space. -/
theorem lfpFamSpace_eq_pos (w : Nat) {I i : V} (hi : i ∈ˢ I) :
    lfpFamSpace V w I = piR (w + 1) I fun _ => univ w :=
  piV_univ_eq_pos (Nat.succ_ne_zero w) hi _ fun _ _ => ⟨w, rfl⟩

/-- **The value reading's abstraction of a family of non-points is the
family** (`famOf`): the graph over an inhabited domain, the point over an
empty one. -/
theorem lamV_eq_famOf {A : V} {F : V → V} (h : ∀ x, x ∈ˢ A → F x ≠ pt) :
    lamV A F = famOf F A := by
  by_cases hA : ∃ x, x ∈ˢ A
  · obtain ⟨x, hx⟩ := hA
    rw [famOf_of_ne ⟨x, hx⟩]
    exact lamV_eq_graph (lamV_ne_pt_of hx (h x hx))
  · rw [famOf_of_empty hA]
    exact lamV_of_empty fun x hx => hA ⟨x, hx⟩

/-- A family of types is in the type `I → Sort w`. -/
theorem famOf_mem_lfpFamSpace {w : Nat} {I : V} {G : V → V}
    (h : ∀ i, i ∈ˢ I → G i ∈ˢ (univ w : V)) : famOf G I ∈ˢ lfpFamSpace V w I := by
  rw [lfpFamSpace_eq]; exact famOf_mem_famSpaceIn h

/-- The least fixed points' family space is inside the type `I → Sort w`. -/
theorem famSpace_subset_lfpFamSpace (w : Nat) (I : V) : famSpace w I ⊆ˢ lfpFamSpace V w I := by
  rw [lfpFamSpace_eq]
  exact famSpace_subset_univ w I

/-- `(I → Sort w) → (I → Sort w)`, the functor space. -/
noncomputable def lfpFamFunSpace (w : Nat) (I : V) : V :=
  piV (lfpFamSpace V w I) fun _ => lfpFamSpace V w I

/-- `lfpFam.{u,w}`. -/
noncomputable def lfpFamV (u w : Nat) : V :=
  lamV (univ u) fun I =>
    lamV (lfpFamFunSpace V w I) fun F => lfpFamSet w I F

theorem max_succ_ne_zero (u w : Nat) : Nat.max u (w + 1) ≠ 0 := by
  show max u (w + 1) ≠ 0
  rw [Nat.max_def]
  split <;> omega

theorem lfpFamSet_mem_space (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ lfpFamSpace V w I :=
  famSpace_subset_lfpFamSpace V w I _ (lfpFamSet_mem w I F)

theorem lfpFamV_mem (u w : Nat) :
    lfpFamV V u w ∈ˢ piV (univ u : V) fun I =>
      piV (lfpFamFunSpace V w I) fun _ => lfpFamSpace V w I :=
  lamV_mem (fun I _ => lamV_mem (fun F _ => lfpFamSet_mem_space V w I F)
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV

section LfpTuple

open ConLeche.SetTheory.Tower (mkTower projS projS_mkTower)

/-! ## `lfpTuple k` (task #315)

The least pre-fixed point of a functor on **tuples** of `k` families
(`lfpTuple`, `ConLeche/SetTheory/Derive/LfpTuple.lean`), member `m`'s
family living over its own index set `I_m : Sort u_m`.  Both of the
constant's binders range over a right-nested pair tower: the index-set
tuple `Is` over `⟨Sort u_0, …⟩` and the operator over the arrow on
`⟨proj_0 Is → Sort w, …⟩`.  Both towers are NON-dependent, so their
carriers are the plain iterated `sigmaSet` below rather than the
telescope-indexed `towerSet`; the members' index sets are read off `Is`
by the uniform projection family `projS`.  Total: the value is a member
of the family tuple for EVERY operator. -/

/-- The non-dependent pair tower's carrier at level `r`: the components
`F s, …, F (s + n - 1)`, terminated by the unit at level `r`. -/
noncomputable def ndTowerSet (r : Nat) (F : Nat → V) : Nat → Nat → V
  | _, 0 => unitSetAt r
  | s, n + 1 => sigmaSet r (F s) fun _ => ndTowerSet r F (s + 1) n

theorem ndTowerSet_mem_univ {r : Nat} {F : Nat → V} :
    ∀ (n s : Nat), (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      ndTowerSet V r F s n ∈ˢ (univ r : V)
  | 0, _, _ => unitSetAt_mem_univ r
  | n + 1, s, hF => by
    show sigmaSet r (F s) (fun _ => ndTowerSet V r F (s + 1) n) ∈ˢ _
    have h := sigma_mem_univ (u := r) (v := r) (hF s (by omega))
      (fun _ _ => ndTowerSet_mem_univ n (s + 1) fun m hm => hF m (by omega))
    rwa [show Nat.max r r = r from Nat.max_self r] at h

/-- **Regime** of the non-dependent tower: a truth value at `0`, strict
above (task #342, L6). -/
theorem Fib_ndTowerSet (r : Nat) (F : Nat → V) :
    ∀ (s n : Nat), Fib (decide (r = 0)) (ndTowerSet V r F s n)
  | _, 0 => Fib_unitSetAt r
  | s, _ + 1 => Fib_sigmaSet r (F s) _

theorem IsTy_ndTowerSet (r : Nat) (F : Nat → V) (s n : Nat) : IsTy (ndTowerSet V r F s n) :=
  IsTy_of_Fib (Fib_ndTowerSet V r F s n)

/-- **Intro**: a tuple whose components sit in the tower's components
is a member (graph regime — the towers here are always at a positive
level). -/
theorem mkTower_mem_ndTowerSet {r : Nat} (hr : r ≠ 0) {F : Nat → V} :
    ∀ (n : Nat) (as : List V) (s : Nat), as.length = n →
      (∀ i, ∀ h : i < as.length, as[i] ∈ˢ F (s + i)) →
      mkTower as ∈ˢ ndTowerSet V r F s n
  | 0, [], _, _, _ => by
    show (empty : V) ∈ˢ unitSetAt r
    rw [← unitAt_pos hr]; exact unitAt_mem_unitSetAt r
  | 0, _ :: _, _, hlen, _ => by simp at hlen
  | _ + 1, [], _, hlen, _ => by simp at hlen
  | n + 1, a :: as, s, hlen, h => by
    show spair a (mkTower as) ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n
    refine spair_mem hr ?_
      (mkTower_mem_ndTowerSet hr n as (s + 1) (by simpa using hlen) fun i hi => ?_)
    · have := h 0 (by simp)
      simpa using this
    · have := h (i + 1) (by simpa using hi)
      rw [show s + (i + 1) = s + 1 + i from by omega] at this
      simpa using this

/-- The intro law at a tower given by a function on positions. -/
theorem mkTower_map_mem_ndTowerSet {r : Nat} (hr : r ≠ 0) {F : Nat → V} (G : Nat → V)
    (n s : Nat) (hG : ∀ i, i < n → G i ∈ˢ F (s + i)) :
    mkTower ((List.range n).map G) ∈ˢ ndTowerSet V r F s n := by
  refine mkTower_mem_ndTowerSet V hr n _ s (by simp) fun i hi => ?_
  have hin : i < n := by simpa using hi
  rw [List.getElem_map, List.getElem_range]
  exact hG i hin

/-- The tower reads its components below its own length only. -/
theorem ndTowerSet_congr {r : Nat} {F F' : Nat → V} :
    ∀ (n s : Nat), (∀ m, m < s + n → F m = F' m) →
      ndTowerSet V r F s n = ndTowerSet V r F' s n
  | 0, _, _ => rfl
  | n + 1, s, h => by
    show sigmaSet r (F s) _ = sigmaSet r (F' s) _
    rw [h s (by omega), ndTowerSet_congr n (s + 1) fun m hm => h m (by omega)]

/-- **Elim**: every component of a member sits in the tower's own. -/
theorem projS_mem_ndTowerSet {r : Nat} (hr : r ≠ 0) {F : Nat → V} :
    ∀ (n s : Nat) {x : V}, x ∈ˢ ndTowerSet V r F s n →
      ∀ i, i < n → projS i x ∈ˢ F (s + i)
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, s, x, hx, i, hi => by
    have hx' : x ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n := hx
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hx'
    subst_vars
    rw [hpos hr]
    cases i with
    | zero => rw [show projS 0 (spair a b) = sfst (spair a b) from rfl, sfst_spair]; simpa using ha
    | succ i =>
      rw [show projS (i + 1) (spair a b) = projS i (ssnd (spair a b)) from rfl, ssnd_spair,
        show s + (i + 1) = s + 1 + i from by omega]
      exact projS_mem_ndTowerSet hr n (s + 1) hb i (Nat.lt_of_succ_lt_succ hi)

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`'s carrier — the index-set tuples. -/
noncomputable def tupleSortsSpace (k : Nat) (us : List Nat) : V :=
  ndTowerSet V (ConLeche.Term.tupleIdxSort us) (fun m => (univ (lv us m) : V)) 0 k

/-- `⟨proj_0 Is → Sort w, …⟩`'s carrier at an index-set tuple `Is`. -/
noncomputable def tupleFamsSpace (k : Nat) (us : List Nat) (Is : V) : V :=
  ndTowerSet V (ConLeche.Term.tupleFamSort k us)
    (fun m => lfpFamSpace V (lv us k) (projS m Is)) 0 k

/-- The tuple operator an argument `F` of `lfpTuple k` induces:
component `m` of `F` applied to the tuple of the argument's first `k`
components. -/
noncomputable def tupleOpV (k : Nat) (F : V) : (Nat → V) → Nat → V :=
  fun X m => projS m (app F (mkTower ((List.range k).map X)))

/-- `lfpTuple k.{u_0 … u_{k-1}, w}`. -/
noncomputable def lfpTupleV (k : Nat) (us : List Nat) : V :=
  lamV (tupleSortsSpace V k us) fun Is =>
    lamV (piV (tupleFamsSpace V k us Is) fun _ => tupleFamsSpace V k us Is) fun F =>
      mkTower ((List.range k).map fun m =>
        lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k F) m)

theorem tupleFamSort_ne_zero (k : Nat) (us : List Nat) :
    ConLeche.Term.tupleFamSort k us ≠ 0 :=
  max_succ_ne_zero _ _

theorem tupleIdxSort_ne_zero (us : List Nat) :
    ConLeche.Term.tupleIdxSort us ≠ 0 := Nat.succ_ne_zero _

/-- Every level a list mentions has its universe inside the list's own
bound universe — the sorts tower's formation premise, global in the
index. -/
theorem univ_lv_mem_tupleIdxSort (us : List Nat) (m : Nat) :
    (univ (lv us m) : V) ∈ˢ (univ (ConLeche.Term.tupleIdxSort us) : V) :=
  univ_mono (Nat.succ_le_succ (ConLeche.Term.lv_le_levMax us m)) _ (univ_mem_univ _)

/-- The block carrier's tuple is a member of the family tuple, at every
index-set tuple and every operator — the constant's totality. -/
theorem lfpTuple_mkTower_mem (k : Nat) (us : List Nat) (Is Φ : V) :
    mkTower ((List.range k).map fun m =>
        lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ) m)
      ∈ˢ tupleFamsSpace V k us Is := by
  unfold tupleFamsSpace
  refine mkTower_map_mem_ndTowerSet V (tupleFamSort_ne_zero k us) _ k 0 fun i hi => ?_
  show lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ) i
    ∈ˢ lfpFamSpace V (lv us k) (projS (0 + i) Is)
  rw [Nat.zero_add]
  exact famSpace_subset_lfpFamSpace V _ _ _
    (lfpTuple_mem (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ) i hi)

theorem lfpTupleV_app {k : Nat} {us : List Nat} {Is F : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us)
    (hF : F ∈ˢ piV (tupleFamsSpace V k us Is) fun _ => tupleFamsSpace V k us Is) :
    app (app (lfpTupleV V k us) Is) F
      = mkTower ((List.range k).map fun m =>
          lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k F) m) := by
  rw [lfpTupleV, app_lamV hIs, app_lamV hF]

theorem lfpTupleV_mem (k : Nat) (us : List Nat) :
    lfpTupleV V k us ∈ˢ piV (tupleSortsSpace V k us) fun Is =>
      piV (piV (tupleFamsSpace V k us Is) fun _ => tupleFamsSpace V k us Is)
        fun _ => tupleFamsSpace V k us Is :=
  lamV_mem (fun Is _ => lamV_mem (fun F _ => lfpTuple_mkTower_mem V k us Is F)
    fun _ _ => IsTy_ndTowerSet V _ _ _ _) fun _ _ => IsTy_piV

end LfpTuple

/-! ## The value assignment -/

/-- The value of each built-in constant at a concrete level
instantiation — `ConLeche.Term.bval`'s transpose.  `quotInd`, `quotSound`
and `propext` are the canonical proof because their result sorts *are*
`0`.  `PUnit` is level-indexed (task #342 B): `{pt}`/`pt` at `0`,
`{∅}`/`∅` above, so a positive-level unit is neither the proof point
nor contains it. -/
noncomputable def bval : BConst → List Nat → V
  | .nat, _ => omega
  | .natZero, _ => natzero
  | .natSucc, _ => natSuccV V
  | .natRec, us => natRecV V (lv us 0)
  | .punit, us => unitSetAt (lv us 0)
  | .punitUnit, us => unitAt (lv us 0)
  | .psigma, us => psigmaV V (lv us 0) (lv us 1)
  | .psigmaMk, us => psigmaMkV V (lv us 0) (lv us 1)
  | .empty, _ => empty
  | .emptyRec, us => emptyRecV V (lv us 1)
  | .quot, us => quotV V (lv us 0) (quotCl us 1)
  | .quotMk, us => quotMkV V (lv us 0) (quotCl us 1)
  | .quotLift, us => quotLiftV V (lv us 0) (lv us 1) (quotCl us 2)
  | .quotInd, _ => pt
  | .quotSound, _ => pt
  | .propext, _ => pt
  | .choice, us => choiceV V (lv us 0)
  | .lfpFam, us => lfpFamV V (lv us 0) (lv us 1)
  | .lfpTuple k, us => lfpTupleV V k us

end ConLeche.SetModel
