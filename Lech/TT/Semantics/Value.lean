import Lech.TT.Const
import Lech.SetTheory.Basic

/-!
# Set-theoretic values of the built-in constants

Each `BConst` gets a value in the target set theory, as a function of
its (concrete) level instantiation.  The values are the hand-written
basis models of `Lech/Model/BasisVal.lean`, restated here against the
`SetTheory` interface alone: this module imports **only**
`Lech/SetTheory/*`, never the checker or its model layer.

Note the two places where the domain-relative collapse (task #100) is
visible:

* `psigmaMkV` is the proof point when the joint level is `0` — at
  `Prop` the pair set is a truth value, so a Kuratowski pair could not
  inhabit it;
* `quotIndV`, `quotSoundV`, `propextV` and `emptyRecV` are *just* the
  proof point, because their whole λ-tower ends in a `Prop` and
  therefore collapses.
-/

namespace Lech.TT

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-- The space of relations on `A`: `A → A → Prop`. -/
noncomputable def relSpace (A : V) : V := piC A fun _ => piC A fun _ => univ 0

/-- The minor-premise space of `Nat.rec` at motive `M`. -/
noncomputable def natStepSpace (M : V) : V :=
  piC omega fun n => piC (app M n) fun _ => app M (natsucc n)

/-- `Nat.succ`. -/
noncomputable def natSuccV : V := lamC omega natsucc

theorem natSuccV_app {n : V} (hn : n ∈ˢ (omega : V)) :
    app (natSuccV V) n = natsucc n := app_lamC hn

theorem natSuccV_mem : natSuccV V ∈ˢ piC (omega : V) fun _ => omega :=
  lamC_mem fun _ hx => natsucc_mem hx

/-- `Nat.rec.{u}`. -/
noncomputable def natRecV (u : Nat) : V :=
  lamC (piC omega fun _ => univ u) fun M =>
    lamC (app M natzero) fun z =>
      lamC (natStepSpace V M) fun s =>
        lamC omega fun n => natrec z s n

/-- `PUnit.rec.{u,v}`. -/
noncomputable def punitRecV (v : Nat) : V :=
  lamC (piC unitSet fun _ => univ v) fun M =>
    lamC (app M pt) fun m =>
      lamC unitSet fun _ => m

/-- `PSigma'.{u,v}`. -/
noncomputable def psigmaV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      sigmaSet (Nat.max u v) A fun x => app B x

/-- `PSigma'.mk.{u,v}`. -/
noncomputable def psigmaMkV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      lamC A fun a =>
        lamC (app B a) fun b =>
          if Nat.max u v = 0 then pt else spair a b

/-- `Quot.{u}`. -/
noncomputable def quotV (u : Nat) : V :=
  lamC (univ u) fun A => lamC (relSpace V A) fun R => quotSet u A R

/-- `Quot.mk.{u}`. -/
noncomputable def quotMkV (u : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (relSpace V A) fun R => lamC A fun a => quotClass u A R a

/-- The invariance space of `Quot.lift`: `∀ a b, r a b → f a = f b`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  piC A fun a => piC A fun b =>
    piC (app (app R a) b) fun _ => eqv (app f a) (app f b)

/-- `Quot.lift.{u,v}`. -/
noncomputable def quotLiftV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (relSpace V A) fun R =>
      lamC (univ v) fun B =>
        lamC (piC A fun _ => B) fun f =>
          lamC (quotInvSpace V A R f) fun _ => SetTheory.quotLift u v A R f

/-- `Classical.choice.{u}`, in the primitive double-negation form. -/
noncomputable def choiceV (u : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC (piC A fun _ => empty) fun _ => empty) fun _ => schoice A

/-- `lfp.{u}` (task #188): the least pre-fixed point of a set-level
functor inside `Sort u` (`lfpSet`, `Lech/SetTheory/Derive/Lfp.lean`). -/
noncomputable def lfpV (u : Nat) : V :=
  lamC (piC (univ u) fun _ => univ u) fun F => lfpSet u F

/-- `lfpFam.{u,w}` (task #188, indexed).  The collapsed model is not the
one the direct routes are proved against (they live on the P tier), so
the inhabitant here is the EMPTY family — any member of the type will
do for `bval_mem_type`. -/
noncomputable def lfpFamV (u w : Nat) : V :=
  lamC (univ u) fun I =>
    lamC (piC (piC I fun _ => univ w) fun _ => piC I fun _ => univ w) fun _ =>
      lamC I fun _ => empty

/-! ## Application laws

The collapsed `app_lamC` fires on domain membership alone, so each
constant's value computes as soon as its arguments are typed — which is
exactly what the premises of the corresponding rule supply. -/

theorem natRecV_app {u : Nat} {M z s n : V}
    (hM : M ∈ˢ piC (omega : V) fun _ => univ u)
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V M)
    (hn : n ∈ˢ (omega : V)) :
    app (app (app (app (natRecV V u) M) z) s) n = natrec z s n := by
  rw [natRecV, app_lamC hM, app_lamC hz, app_lamC hs, app_lamC hn]

theorem natRecV_mem_fibre {M z s n : V}
    (hz : z ∈ˢ app M natzero) (hs : s ∈ˢ natStepSpace V M)
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n :=
  natrec_mem hz (fun _ hk _ hih => app_mem_piC (app_mem_piC hs hk) hih) hn

theorem punitRecV_app {v : Nat} {M m t : V}
    (hM : M ∈ˢ piC (unitSet : V) fun _ => univ v)
    (hm : m ∈ˢ app M pt) (ht : t ∈ˢ (unitSet : V)) :
    app (app (app (punitRecV V v) M) m) t = m := by
  rw [punitRecV, app_lamC hM, app_lamC hm, app_lamC ht]

theorem psigmaV_app {u v : Nat} {A B : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v) :
    app (app (psigmaV V u v) A) B = sigmaSet (Nat.max u v) A fun x => app B x := by
  rw [psigmaV, app_lamC hA, app_lamC hB]

theorem psigmaMkV_app {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    app (app (app (app (psigmaMkV V u v) A) B) a) b =
      if Nat.max u v = 0 then pt else spair a b := by
  rw [psigmaMkV, app_lamC hA, app_lamC hB, app_lamC ha, app_lamC hb]

/-- At a `Prop`-level pair the joint level is `0`, hence both component
levels are, and the collapse identifies every component with the proof
point. -/
theorem psigma_zero_levels {u v : Nat} (h : Nat.max u v = 0) : u = 0 ∧ v = 0 :=
  ⟨Nat.le_zero.mp (h ▸ Nat.le_max_left u v),
   Nat.le_zero.mp (h ▸ Nat.le_max_right u v)⟩

theorem psigmaMkV_mem {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    app (app (app (app (psigmaMkV V u v) A) B) a) b ∈ˢ
      sigmaSet (Nat.max u v) A fun x => app B x := by
  rw [psigmaMkV_app V hA hB ha hb]
  split
  · next h => rw [h]; exact pt_mem_sigma ha hb
  · next h => exact spair_mem h ha hb

/-! ### The projections

`sfst`/`ssnd` are what the `proj` former interprets to — literally the
checker-side `interpExpr`'s clause.  The two membership lemmas are what
the former's *typing* rules need, and they are exactly the facts the
premise `p ∈ˢ sigmaSet …` supplies (compare the set model, where the
`AnnotOk` proj clause has to carry them). -/

/-- The first field of a pair is in the domain. -/
theorem sfst_mem {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) : sfst p ∈ˢ A := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · rw [h0 hw, sfst_pt]
    exact (mem_univ_zero ((psigma_zero_levels hw).1 ▸ hA) ha) ▸ ha
  · rw [hne hw, sfst_spair]; exact ha

/-- The second field lands in the fibre over the first. -/
theorem ssnd_mem {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v)
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) :
    ssnd p ∈ˢ app B (sfst p) := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · obtain ⟨hu, hv⟩ := psigma_zero_levels hw
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ app_mem_piC hB ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    rw [h0 hw, ssnd_pt, sfst_pt, show app B pt = app B a by rw [hapt]]
    exact hbpt ▸ hb
  · rw [hne hw, ssnd_spair, sfst_spair]; exact hb

/-! ### The `PSigma'` computation laws -/

theorem sfst_mk {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    sfst (app (app (app (app (psigmaMkV V u v) A) B) a) b) = a := by
  rw [psigmaMkV_app V hA hB ha hb]
  split
  · next h =>
    rw [sfst_pt]
    exact (mem_univ_zero ((psigma_zero_levels h).1 ▸ hA) ha).symm
  · next _ => exact sfst_spair a b

theorem ssnd_mk {u v : Nat} {A B a b : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v) (ha : a ∈ˢ A) (hb : b ∈ˢ app B a) :
    ssnd (app (app (app (app (psigmaMkV V u v) A) B) a) b) = b := by
  rw [psigmaMkV_app V hA hB ha hb]
  split
  · next h =>
    rw [ssnd_pt]
    obtain ⟨_, hv⟩ := psigma_zero_levels h
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ app_mem_piC hB ha
    exact (mem_univ_zero hBa hb).symm
  · next _ => exact ssnd_spair a b

/-- **Structure η** for the basis pair.  At a `Prop`-level pair both the
subject and the reassembled pair collapse to the proof point; above it
the Kuratowski pair is literally rebuilt. -/
theorem psigmaEta_law {u v : Nat} {A B p : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ piC A fun _ => univ v)
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A fun x => app B x) :
    app (app (app (app (psigmaMkV V u v) A) B) (sfst p)) (ssnd p) = p := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · obtain ⟨hu, hv⟩ := psigma_zero_levels hw
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : app B a ∈ˢ (univ 0 : V) := hv ▸ app_mem_piC hB ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    have hpa : (pt : V) ∈ˢ A := hapt ▸ ha
    have hpb : (pt : V) ∈ˢ app B pt := by
      have h1 : (pt : V) ∈ˢ app B a := hbpt ▸ hb
      rwa [hapt] at h1
    rw [h0 hw, sfst_pt, ssnd_pt, psigmaMkV_app V hA hB hpa hpb, if_pos hw]
  · rw [hne hw, sfst_spair, ssnd_spair, psigmaMkV_app V hA hB ha hb, if_neg hw]

theorem quotV_app {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) :
    app (app (quotV V u) A) R = quotSet u A R := by
  rw [quotV, app_lamC hA, app_lamC hR]

theorem quotMkV_app {u : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u) A) R) a = quotClass u A R a := by
  rw [quotMkV, app_lamC hA, app_lamC hR, app_lamC ha]

theorem quotLiftV_app {u v : Nat} {A R B f h : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) (hB : B ∈ˢ (univ v : V))
    (hf : f ∈ˢ piC A fun _ => B) (hh : h ∈ˢ quotInvSpace V A R f) :
    app (app (app (app (app (quotLiftV V u v) A) R) B) f) h =
      SetTheory.quotLift u v A R f := by
  rw [quotLiftV, app_lamC hA, app_lamC hR, app_lamC hB, app_lamC hf, app_lamC hh]

/-- The invariance premise, read off the membership of a proof in the
invariance space. -/
theorem quotInv_of_mem {A R f h : V} (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      app f a = app f b := by
  intro a b ha hb hw
  obtain ⟨wv, hwv⟩ := hw
  rw [quotInvSpace] at hh
  have h1 : app h a ∈ˢ
      piC A fun b => piC (app (app R a) b) fun _ => eqv (app f a) (app f b) :=
    app_mem_piC hh ha
  have h2 : app (app h a) b ∈ˢ
      piC (app (app R a) b) fun _ => eqv (app f a) (app f b) :=
    app_mem_piC h1 hb
  have h3 : app (app (app h a) b) wv ∈ˢ eqv (app f a) (app f b) :=
    app_mem_piC h2 hwv
  exact mem_eqv h3

/-- A `¬¬A` inhabitant witnesses that `A` is inhabited: if `A` were
empty, `¬A` would be `{pt}` and applying the proof would land in `∅`. -/
theorem exists_mem_of_dneg {A h : V}
    (hh : h ∈ˢ piC (piC A fun _ => (empty : V)) fun _ => empty) :
    ∃ x, x ∈ˢ A := by
  rcases Classical.em (∃ x, x ∈ˢ A) with hex | hne
  · exact hex
  · exfalso
    have hA : A = empty := eq_empty fun z hz => hne ⟨z, hz⟩
    subst hA
    have hpt : (pt : V) ∈ˢ piC (empty : V) fun _ => (empty : V) := by
      rw [piC_empty]; exact pt_mem_unitSet
    exact not_mem_empty _ (app_mem_piC hh hpt)

theorem choiceV_app {u : Nat} {A h : V} (hA : A ∈ˢ (univ u : V))
    (hh : h ∈ˢ piC (piC A fun _ => (empty : V)) fun _ => empty) :
    app (app (choiceV V u) A) h = schoice A := by
  rw [choiceV, app_lamC hA, app_lamC hh]

/-- The value of each built-in constant at a concrete level
instantiation. -/
noncomputable def bval : BConst → List Nat → V
  | .nat, _ => omega
  | .natZero, _ => natzero
  | .natSucc, _ => natSuccV V
  | .natRec, us => natRecV V (lv us 0)
  | .punit, _ => unitSet
  | .punitUnit, _ => pt
  | .punitRec, us => punitRecV V (lv us 1)
  | .psigma, us => psigmaV V (lv us 0) (lv us 1)
  | .psigmaMk, us => psigmaMkV V (lv us 0) (lv us 1)
  | .empty, _ => empty
  | .emptyRec, _ => pt
  | .quot, us => quotV V (lv us 0)
  | .quotMk, us => quotMkV V (lv us 0)
  | .quotLift, us => quotLiftV V (lv us 0) (lv us 1)
  | .quotInd, _ => pt
  | .quotSound, _ => pt
  | .propext, _ => pt
  | .choice, us => choiceV V (lv us 0)
  | .lfp, us => lfpV V (lv us 0)
  | .lfpFam, us => lfpFamV V (lv us 0) (lv us 1)

end Lech.TT
