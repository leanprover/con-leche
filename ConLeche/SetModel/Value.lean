module

public import ConLeche.SetModel.Ops
public import ConLeche.Term.Const
public import ConLeche.SetTheory.Derive.Quot
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
`quotLiftR` is the choice-free bounded separation graph over
`prod (quotSet u A R) B` (or `pt` when all values of `f` on `A` are
`pt`), with `quotLiftV` definable without `qrep`.  `choiceV` uses the
internal universe choice function `univChoiceFn u` (no global `schoice`).
`natRecV` uses internal Dedekind recursion `natrec`.  The least fixed
points' families are members of the value-read family space
`lfpFamSpace` (`famOf`), and `lfpTupleV` packages `DefTupleOp`.
-/

namespace ConLeche.SetModel

open SetTheory
open ConLeche.Term (BConst lv)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat.succ` -/

/-- `Nat.succ : Nat → Nat`. -/
noncomputable def natSuccV : V :=
  lamV omega natsucc (hasGraph_of_defFun1 (DefFun.natsucc_apply (DefFun.proj 0)))

theorem natSuccV_app {n : V} (hn : n ∈ˢ (omega : V)) :
    app (natSuccV V) n = natsucc n := app_lamV hn

/-- A successor is not the point: it is a natural number. -/
theorem natsucc_ne_pt {n : V} (hn : n ∈ˢ (omega : V)) : natsucc n ≠ pt := fun h =>
  pt_not_mem_omega (h ▸ natsucc_mem hn)

/-- `Nat.succ`'s abstraction is the graph regime's. -/
theorem natSuccV_eq_lamR :
    natSuccV V = lamR 1 (omega : V) natsucc
      (hasGraph_of_defFun1 (DefFun.natsucc_apply (DefFun.proj 0))) :=
  lamV_eq_pos Nat.one_ne_zero natzero_mem (natsucc_ne_pt V natzero_mem)

theorem natSuccV_mem :
    natSuccV V ∈ˢ piR 1 (omega : V) (fun _ => omega) (hasSigmaPairs_const _ _) := by
  rw [natSuccV_eq_lamR]; exact lamR_mem fun _ hx => natsucc_mem hx

theorem natSuccV_memV :
    natSuccV V ∈ˢ piV (omega : V) (fun _ => omega) (hasSigmaPairs_const _ _) :=
  lamV_mem (fun _ hx => natsucc_mem hx) fun _ _ => IsTy_omega

/-! ## `Nat.rec` -/

/-- `Nat → Sort u`, the motive space. -/
noncomputable def natMotiveSpace (u : Nat) : V :=
  piV omega (fun _ => univ u) (hasSigmaPairs_const _ _)

theorem defFun_natStep_fib {V : Type w} [SetTheory V] {k : Nat} {M : (Fin k → V) → V}
    (hM : DefFun k M) :
    DefFun (k + 1) fun v =>
      piV (app (M (ftail v)) (v 0)) (fun _ => app (M (ftail v)) (natsucc (v 0)))
        (hasSigmaPairs_const _ _) :=
  DefFun.piV_apply_curry
    (DefFun.app_apply hM.weaken (DefFun.proj 0))
    (DefFun.app_apply hM.weaken.weaken (DefFun.natsucc_apply (DefFun.proj 1)))

/-- `(n : Nat) → M n → M (n+1)`, the minor-premise space. -/
noncomputable def natStepSpace (M : V) : V :=
  piV omega
    (fun n => piV (app M n) (fun _ => app M (natsucc n)) (hasSigmaPairs_const _ _))
    (hasSigmaPairs_of_defFun1 (defFun_natStep_fib (DefFun.const M)))

theorem defFun_natStepSpace {V : Type w} [SetTheory V] {k : Nat} {M : (Fin k → V) → V}
    (hM : DefFun k M) : DefFun k fun env => natStepSpace V (M env) := by
  unfold natStepSpace
  exact DefFun.piV_apply_curry DefFun.omega_const (defFun_natStep_fib hM)

theorem defFun_natRecV_s {V : Type w} [SetTheory V] (z : V) :
    DefFun 1 fun v =>
      lamV omega (fun n => natrec z (v 0) n)
        (hasGraph_of_defFun1 (DefFun.natrec_apply (DefFun.const z) (DefFun.const (v 0)) (DefFun.proj 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.natrec_apply (DefFun.const z) (DefFun.proj 1) (DefFun.proj 0))
    DefFun.omega_const

theorem defFun_natRecV_z {V : Type w} [SetTheory V] (M : V) :
    DefFun 1 fun v =>
      lamV (natStepSpace V M)
        (fun s => lamV omega (fun n => natrec (v 0) s n)
          (hasGraph_of_defFun1 (DefFun.natrec_apply (DefFun.const (v 0)) (DefFun.const s) (DefFun.proj 0))))
        (hasGraph_of_defFun1 (defFun_natRecV_s (v 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.natrec_apply (DefFun.proj 2) (DefFun.proj 1) (DefFun.proj 0))
      DefFun.omega_const)
    (defFun_natStepSpace (DefFun.const M))

theorem defFun_natRecV_M {V : Type w} [SetTheory V] :
    DefFun 1 fun v =>
      lamV (app (v 0) natzero)
        (fun z => lamV (natStepSpace V (v 0))
          (fun s => lamV omega (fun n => natrec z s n)
            (hasGraph_of_defFun1 (DefFun.natrec_apply (DefFun.const z) (DefFun.const s) (DefFun.proj 0))))
          (hasGraph_of_defFun1 (defFun_natRecV_s z)))
        (hasGraph_of_defFun1 (defFun_natRecV_z (v 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.lamV_apply_curry
        (DefFun.natrec_apply (DefFun.proj 2) (DefFun.proj 1) (DefFun.proj 0))
        DefFun.omega_const)
      (defFun_natStepSpace (DefFun.proj 1)))
    (DefFun.app_apply (DefFun.proj 0) DefFun.natzero)

/-- `Nat.rec.{u}`. -/
noncomputable def natRecV (u : Nat) : V :=
  lamV (natMotiveSpace V u) (fun M =>
    lamV (app M natzero) (fun z =>
      lamV (natStepSpace V M) (fun s =>
        lamV omega (fun n => natrec z s n)
          (hasGraph_of_defFun1
            (DefFun.natrec_apply (DefFun.const z) (DefFun.const s) (DefFun.proj 0))))
        (hasGraph_of_defFun1 (defFun_natRecV_s z)))
      (hasGraph_of_defFun1 (defFun_natRecV_z M)))
    (hasGraph_of_defFun1 (defFun_natRecV_M (V := V)))

theorem natMotive_apply {u : Nat} {M n : V} (hM : M ∈ˢ natMotiveSpace V u)
    (hn : n ∈ˢ (omega : V)) : app M n ∈ˢ (univ u : V) :=
  app_mem_piV hM hn

/-- The step premise, unpacked: two eliminations, no fibre premise. -/
theorem natStep_apply {M s : V} (hs : s ∈ˢ natStepSpace V M) :
    ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (natsucc k) :=
  fun k hk _ hih => by
    have h1 : app s k ∈ˢ piV (app M k) (fun _ => app M (natsucc k)) (hasSigmaPairs_const _ _) :=
      app_mem_piV hs hk
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
    natRecV V u ∈ˢ piV (natMotiveSpace V u) (fun M =>
      piV (app M natzero) (fun _ =>
        piV (natStepSpace V M) (fun _ =>
          piV omega (fun n => app M n)
            (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const M) (DefFun.proj 0))))
          (hasSigmaPairs_const _ _))
        (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry (DefFun.app_apply (DefFun.proj 0) DefFun.natzero)
          (DefFun.piV_apply_curry (defFun_natStepSpace (DefFun.proj 1))
            (DefFun.piV_apply_curry DefFun.omega_const
              (DefFun.app_apply (DefFun.proj 3) (DefFun.proj 0)))))) := by
  refine lamV_mem (fun M hM => lamV_mem (fun z hz => lamV_mem (fun s hs =>
    lamV_mem (fun n hn => natRecV_mem_fibre V hz hs hn)
      fun n hn => IsTy_of_mem_univ (natMotive_apply V hM hn))
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV

/-! ## The dependent pair `.psigma` -/

/-- `A → Sort v`, the fibre space, as the value reading has it: over an
empty `A` it is `{pt}` (task #342, L16). -/
noncomputable def psigmaFibreSpace (v : Nat) (A : V) : V :=
  piV A (fun _ => univ v) (hasSigmaPairs_const _ _)

theorem defFun_psigmaFibreSpace {V : Type w} [SetTheory V] {k : Nat} (v : Nat)
    {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => psigmaFibreSpace V v (A env) := by
  unfold psigmaFibreSpace
  exact DefFun.piV_apply_curry hA (DefFun.univ_const v)

theorem psigmaFibre_apply {v : Nat} {A B a : V} (hB : B ∈ˢ psigmaFibreSpace V v A)
    (ha : a ∈ˢ A) : app B a ∈ˢ (univ v : V) :=
  app_mem_piV hB ha

/-- Over an inhabited `A` the fibre space is the graph space. -/
theorem lamR_mem_psigmaFibreSpace {v : Nat} {A x : V} {F : V → V}
    {hG : HasGraph A F} (hx : x ∈ˢ A)
    (hF : ∀ y, y ∈ˢ A → F y ∈ˢ (univ v : V)) :
    lamR (v + 1) A F hG ∈ˢ psigmaFibreSpace V v A := by
  unfold psigmaFibreSpace
  rw [piV_univ_eq_pos (Nat.succ_ne_zero v) hx _ fun _ _ => ⟨v, rfl⟩]
  exact lamR_mem hF

/-- A family of types over `A` is in the fibre space. -/
theorem lamV_mem_psigmaFibreSpace {v : Nat} {A : V} {F : V → V}
    {hG : HasGraph A F} (hF : ∀ x, x ∈ˢ A → F x ∈ˢ (univ v : V)) :
    lamV A F hG ∈ˢ psigmaFibreSpace V v A :=
  lamV_mem hF fun _ _ => IsTy_univ v

/-- The fibre space is inhabited: by the constant family `∅` (the
point over an empty domain). -/
theorem lamV_empty_mem_psigmaFibreSpace (v : Nat) (A : V) :
    lamV A (fun _ => (empty : V)) (hasGraph_of_defFun1 DefFun.empty) ∈ˢ psigmaFibreSpace V v A :=
  lamV_mem_psigmaFibreSpace V fun _ _ => empty_mem_univ v

theorem defFun_psigmaBody {V : Type w} [SetTheory V] {k : Nat} (u v : Nat)
    {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun (k + 1) fun w =>
      sigmaSet (Nat.max u v) (A (ftail w)) (fun x => app (w 0) x)
        (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const (w 0)) (DefFun.proj 0))) :=
  DefFun.sigmaSet_apply_curry (Nat.max u v) hA.weaken
    (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0))

/-- The dependent pair `.psigma.{u,v}` — a type former. -/
noncomputable def psigmaV (u v : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (psigmaFibreSpace V v A) (fun B =>
      sigmaSet (Nat.max u v) A (fun x => app B x)
        (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))
      (hasGraph_of_defFun1 (defFun_psigmaBody u v (DefFun.const A))))
    (hasGraph_of_defFun1
      (DefFun.lamV_apply_curry (defFun_psigmaBody u v (DefFun.proj 0))
        (defFun_psigmaFibreSpace v (DefFun.proj 0))))

theorem psigmaV_app {u v : Nat} {A B : V} (hA : A ∈ˢ (univ u : V))
    (hB : B ∈ˢ psigmaFibreSpace V v A) :
    app (app (psigmaV V u v) A) B =
      sigmaSet (Nat.max u v) A (fun x => app B x)
        (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))) := by
  rw [psigmaV, app_lamV hA, app_lamV hB]

/-- The pair former inhabits its type. -/
theorem psigmaV_mem (u v : Nat) :
    psigmaV V u v ∈ˢ piV (univ u : V) (fun A =>
      piV (psigmaFibreSpace V v A) (fun _ => (univ (Nat.max u v) : V))
        (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry (defFun_psigmaFibreSpace v (DefFun.proj 0))
          (DefFun.univ_const (Nat.max u v)))) :=
  lamV_mem (fun _ hA => lamV_mem (fun _ hB =>
      sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx) _)
    fun _ _ => IsTy_univ _) fun _ _ => IsTy_piV

/-- The pair former is the graph regime's at both binders: its domains
are inhabited and its values are types. -/
theorem psigmaV_eq_lamR (u v : Nat) :
    psigmaV V u v =
      lamR (Nat.max u v + 1) (univ u : V) (fun A =>
        lamR (Nat.max u v + 1) (psigmaFibreSpace V v A) (fun B =>
          sigmaSet (Nat.max u v) A (fun x => app B x)
            (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))
          (hasGraph_of_defFun1 (defFun_psigmaBody u v (DefFun.const A))))
        (hasGraph_of_defFun1
          (DefFun.lamR_apply_curry (Nat.max u v + 1) (defFun_psigmaBody u v (DefFun.proj 0))
            (defFun_psigmaFibreSpace v (DefFun.proj 0)))) := by
  have hin : ∀ A, A ∈ˢ (univ u : V) →
      (lamV (psigmaFibreSpace V v A) (fun B =>
          sigmaSet (Nat.max u v) A (fun x => app B x)
            (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))
          (hasGraph_of_defFun1 (defFun_psigmaBody u v (DefFun.const A))))
        = lamR (Nat.max u v + 1) (psigmaFibreSpace V v A) (fun B =>
            sigmaSet (Nat.max u v) A (fun x => app B x)
              (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))
            (hasGraph_of_defFun1 (defFun_psigmaBody u v (DefFun.const A))) := fun A hA =>
    lamV_eq_pos (Nat.succ_ne_zero _) (lamV_empty_mem_psigmaFibreSpace V v A)
      (ne_pt_of_mem_univ (sigma_mem_univ hA (fun _ hx =>
        psigmaFibre_apply V (lamV_empty_mem_psigmaFibreSpace V v A) hx) _))
  rw [psigmaV, lamV_eq_pos (Nat.succ_ne_zero _) (empty_mem_univ u)
    (by rw [hin _ (empty_mem_univ u)]; exact lamR_ne_pt (Nat.succ_ne_zero _))]
  exact lamR_congr _ _ hin

theorem defFun_psigmaMk_body {V : Type w} [SetTheory V] {k : Nat} (u v : Nat)
    {A B : (Fin k → V) → V} (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => if Nat.max u v = 0 then pt else spair (A env) (B env) := by
  by_cases hw : Nat.max u v = 0
  · simp only [hw, ↓reduceIte]
    exact DefFun.pt
  · simp only [hw, ↓reduceIte]
    exact DefFun.spair_apply hA hB

theorem defFun_psigmaMk_a {V : Type w} [SetTheory V] (u v : Nat) (a : V) :
    DefFun 1 fun w => if Nat.max u v = 0 then pt else spair a (w 0) :=
  defFun_psigmaMk_body u v (DefFun.const a) (DefFun.proj 0)

theorem defFun_psigmaMk_B {V : Type w} [SetTheory V] (u v : Nat) (B : V) :
    DefFun 1 fun w =>
      lamV (app B (w 0)) (fun b => if Nat.max u v = 0 then pt else spair (w 0) b)
        (hasGraph_of_defFun1 (defFun_psigmaMk_a u v (w 0))) :=
  DefFun.lamV_apply_curry
    (defFun_psigmaMk_body u v (DefFun.proj 1) (DefFun.proj 0))
    (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))

theorem defFun_psigmaMk_A {V : Type w} [SetTheory V] (u v : Nat) (A : V) :
    DefFun 1 fun w =>
      lamV A (fun a =>
        lamV (app (w 0) a) (fun b => if Nat.max u v = 0 then pt else spair a b)
          (hasGraph_of_defFun1 (defFun_psigmaMk_a u v a)))
        (hasGraph_of_defFun1 (defFun_psigmaMk_B u v (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (defFun_psigmaMk_body u v (DefFun.proj 1) (DefFun.proj 0))
      (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0)))
    (DefFun.const A)

theorem defFun_psigmaMk_top {V : Type w} [SetTheory V] (u v : Nat) :
    DefFun 1 fun w =>
      lamV (psigmaFibreSpace V v (w 0)) (fun B =>
        lamV (w 0) (fun a =>
          lamV (app B a) (fun b => if Nat.max u v = 0 then pt else spair a b)
            (hasGraph_of_defFun1 (defFun_psigmaMk_a u v a)))
          (hasGraph_of_defFun1 (defFun_psigmaMk_B u v B)))
        (hasGraph_of_defFun1 (defFun_psigmaMk_A u v (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.lamV_apply_curry
        (defFun_psigmaMk_body u v (DefFun.proj 1) (DefFun.proj 0))
        (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0)))
      (DefFun.proj 1))
    (defFun_psigmaFibreSpace v (DefFun.proj 0))

/-- Its constructor `.psigmaMk.{u,v}`.  At `max u v = 0` the pair type
is a truth value, so the pair is the point; the abstractions over it
are the point too. -/
noncomputable def psigmaMkV (u v : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (psigmaFibreSpace V v A) (fun B =>
      lamV A (fun a =>
        lamV (app B a) (fun b => if Nat.max u v = 0 then pt else spair a b)
          (hasGraph_of_defFun1 (defFun_psigmaMk_a u v a)))
        (hasGraph_of_defFun1 (defFun_psigmaMk_B u v B)))
      (hasGraph_of_defFun1 (defFun_psigmaMk_A u v A)))
    (hasGraph_of_defFun1 (defFun_psigmaMk_top u v))

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
    psigmaMkV V u v ∈ˢ piV (univ u : V) (fun A =>
      piV (psigmaFibreSpace V v A) (fun B =>
        piV A (fun a => piV (app B a) (fun _ =>
          sigmaSet (Nat.max u v) A (fun x => app B x)
            (hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))
          (hasSigmaPairs_const _ _))
          (hasSigmaPairs_of_defFun1
            (DefFun.piV_apply_curry (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))
              (DefFun.sigmaSet_apply_curry (Nat.max u v) (DefFun.const A)
                (DefFun.app_apply (DefFun.const B) (DefFun.proj 0))))))
        (hasSigmaPairs_of_defFun1
          (DefFun.piV_apply_curry (DefFun.const A)
            (DefFun.piV_apply_curry (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0))
              (DefFun.sigmaSet_apply_curry (Nat.max u v) (DefFun.const A)
                (DefFun.app_apply (DefFun.proj 3) (DefFun.proj 0)))))))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry (defFun_psigmaFibreSpace v (DefFun.proj 0))
          (DefFun.piV_apply_curry (DefFun.proj 1)
            (DefFun.piV_apply_curry (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0))
              (DefFun.sigmaSet_apply_curry (Nat.max u v) (DefFun.proj 3)
                (DefFun.app_apply (DefFun.proj 3) (DefFun.proj 0))))))) := by
  refine lamV_mem (fun A hA => lamV_mem (fun B hB => lamV_mem (fun a ha =>
    lamV_mem (fun b hb => ?_) fun _ _ =>
      IsTy_of_mem_univ (sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx) _))
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
  piV A (fun _ => piV A (fun _ => univ 0) (hasSigmaPairs_const _ _))
    (hasSigmaPairs_const _ _)

theorem defFun_relSpace {V : Type w} [SetTheory V] {k : Nat} {A : (Fin k → V) → V}
    (hA : DefFun k A) : DefFun k fun env => relSpace V (A env) := by
  unfold relSpace
  exact DefFun.piV_apply_curry hA
    (DefFun.piV_apply_curry hA.weaken (DefFun.univ_const 0))

/-- `Quot.{u}` — a type former. -/
noncomputable def quotV (u : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (relSpace V A) (fun R => quotSet u A R)
      (hasGraph_of_defFun1 (defFun_quotSet_apply u (DefFun.const A) (DefFun.proj 0))))
    (hasGraph_of_defFun1
      (DefFun.lamV_apply_curry
        (defFun_quotSet_apply u (DefFun.proj 1) (DefFun.proj 0))
        (defFun_relSpace (DefFun.proj 0))))

theorem quotV_app {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) :
    app (app (quotV V u) A) R = quotSet u A R := by
  rw [quotV, app_lamV hA, app_lamV hR]

theorem defFun_quotMk_R {V : Type w} [SetTheory V] (u : Nat) (A : V) :
    DefFun 1 fun w =>
      lamV A (fun a => quotClass u A (w 0) a)
        (hasGraph_of_defFun1 (defFun_quotClass_apply u (DefFun.const A) (DefFun.const (w 0)) (DefFun.proj 0))) :=
  DefFun.lamV_apply_curry
    (defFun_quotClass_apply u (DefFun.const A) (DefFun.proj 1) (DefFun.proj 0))
    (DefFun.const A)

theorem defFun_quotMk_A {V : Type w} [SetTheory V] (u : Nat) :
    DefFun 1 fun w =>
      lamV (relSpace V (w 0)) (fun R =>
        lamV (w 0) (fun a => quotClass u (w 0) R a)
          (hasGraph_of_defFun1 (defFun_quotClass_apply u (DefFun.const (w 0)) (DefFun.const R) (DefFun.proj 0))))
        (hasGraph_of_defFun1 (defFun_quotMk_R u (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (defFun_quotClass_apply u (DefFun.proj 2) (DefFun.proj 1) (DefFun.proj 0))
      (DefFun.proj 1))
    (defFun_relSpace (DefFun.proj 0))

/-- `Quot.mk.{u}`. -/
noncomputable def quotMkV (u : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (relSpace V A) (fun R =>
      lamV A (fun a => quotClass u A R a)
        (hasGraph_of_defFun1
          (defFun_quotClass_apply u (DefFun.const A) (DefFun.const R) (DefFun.proj 0))))
      (hasGraph_of_defFun1 (defFun_quotMk_R u A)))
    (hasGraph_of_defFun1 (defFun_quotMk_A u))

theorem quotMkV_app {u : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u) A) R) a = quotClass u A R a := by
  rw [quotMkV, app_lamV hA, app_lamV hR, app_lamV ha]

theorem defRel_quotLiftR_pred {V : Type w} [SetTheory V] {k : Nat} (u : Nat)
    {A R f P : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (hf : DefFun k f) (hP : DefFun k P) :
    DefRel k fun env =>
      ∃ a, a ∈ˢ A env ∧ ∃ x y,
        P env = kpair x y ∧ x = quotClass u (A env) (R env) a ∧ y = app (f env) a := by
  refine DefRel.bExists_curry hA (DefRel.exists_curry (DefRel.exists_curry ?_))
  refine DefRel.and ?_ (DefRel.and ?_ ?_)
  · exact DefRel.eq_apply hP.weaken.weaken.weaken
      (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
  · exact DefRel.eq_apply (DefFun.proj 1)
      (defFun_quotClass_apply u hA.weaken.weaken.weaken hR.weaken.weaken.weaken (DefFun.proj 2))
  · exact DefRel.eq_apply (DefFun.proj 0)
      (DefFun.app_apply hf.weaken.weaken.weaken (DefFun.proj 2))

theorem hasSep_quotLiftR {V : Type w} [SetTheory V] (u : Nat) (A R B f : V) :
    HasSep (prod (quotSet u A R) B)
      (fun p => ∃ a, a ∈ˢ A ∧ ∃ x y, p = kpair x y ∧ x = quotClass u A R a ∧ y = app f a) :=
  hasSep_of_defPred
    (defRel_quotLiftR_pred u (DefFun.const A) (DefFun.const R) (DefFun.const f) (DefFun.proj 0))

open Classical in
/-- Choice-free quotient lift: `pt` if `f` sends every member of `A` to
`pt`, otherwise the bounded separation graph inside
`prod (quotSet u A R) B`. -/
noncomputable def quotLiftR (u : Nat) (A R B f : V) : V :=
  if ∀ a, a ∈ˢ A → app f a = pt then pt
  else sep (prod (quotSet u A R) B)
    (fun p => ∃ a, a ∈ˢ A ∧ ∃ x y, p = kpair x y ∧ x = quotClass u A R a ∧ y = app f a)
    (hasSep_quotLiftR u A R B f)

theorem DefFun.quotLiftR_apply {V : Type w} [SetTheory V] {k : Nat} (u : Nat)
    {A R B f : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (hB : DefFun k B) (hf : DefFun k f) :
    DefFun k fun env => quotLiftR V u (A env) (R env) (B env) (f env) := by
  unfold quotLiftR
  exact DefFun.ite
    (DefRel.bForall_curry hA (DefRel.eq_apply (DefFun.app_apply hf.weaken (DefFun.proj 0)) DefFun.pt))
    DefFun.pt
    (DefFun.sep_apply_curry (DefFun.prod_apply (defFun_quotSet_apply u hA hR) hB)
      (defRel_quotLiftR_pred u hA.weaken hR.weaken hf.weaken (DefFun.proj 0)))

theorem quotLiftR_app {u : Nat} {A R B f a : V}
    (hA : A ∈ˢ (univ u : V))
    (hf : f ∈ˢ piV A (fun _ => B) (hasSigmaPairs_const _ _))
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (ha : a ∈ˢ A) :
    app (quotLiftR V u A R B f) (quotClass u A R a) = app f a := by
  unfold quotLiftR
  by_cases hc : ∀ x, x ∈ˢ A → app f x = pt
  · rw [ite_eq_left hc, app_pt, hc a ha]
  · rw [ite_eq_right hc]
    let S := sep (prod (quotSet u A R) B)
      (fun p => ∃ a', a' ∈ˢ A ∧ ∃ x y, p = kpair x y ∧ x = quotClass u A R a' ∧ y = app f a')
      (hasSep_quotLiftR u A R B f)
    have hSne : S ≠ pt := by
      intro heq
      have htag : (ptTag : V) ∈ˢ S := heq ▸ ptTag_mem_pt
      obtain ⟨x, -, y, -, hkp⟩ := mem_prod.mp (sep_subset _ htag)
      exact ptTag_ne_kpair x y hkp
    have hmem : kpair (quotClass u A R a) (app f a) ∈ˢ S :=
      mem_sep.mpr ⟨mem_prod.mpr ⟨quotClass u A R a, quotClass_mem ha,
          app f a, app_mem_piV hf ha, rfl⟩,
        a, ha, quotClass u A R a, app f a, rfl, rfl, rfl⟩
    refine app_eq_of_unique hSne hmem fun y' hy' => ?_
    obtain ⟨_, a', ha', x, y, hkp, rfl, rfl⟩ := mem_sep.mp hy'
    obtain ⟨hcls, rfl⟩ := kpair_inj hkp
    exact (app_eq_of_quotClass_eq hA ha ha' hinv hcls).symm

theorem quotLiftR_mem {u : Nat} {A R B f : V}
    (hA : A ∈ˢ (univ u : V)) (hB : IsTy B)
    (hf : f ∈ˢ piV A (fun _ => B) (hasSigmaPairs_const _ _))
    (hinv : ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      app f a = app f b) :
    quotLiftR V u A R B f ∈ˢ piV (quotSet u A R) (fun _ => B) (hasSigmaPairs_const _ _) := by
  unfold quotLiftR
  by_cases hc : ∀ a, a ∈ˢ A → app f a = pt
  · rw [ite_eq_left hc]
    refine (pt_mem_piV_iff (fun _ _ => hB)).mpr fun q hq => ?_
    obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
    rw [← hc a ha]
    exact app_mem_piV hf ha
  · rw [ite_eq_right hc]
    have hnex : ∃ a₀, a₀ ∈ˢ A ∧ app f a₀ ≠ pt :=
      Classical.byContradiction fun hne => hc fun a ha =>
        Classical.byContradiction fun hne_pt => hne ⟨a, ha, hne_pt⟩
    obtain ⟨a₀, ha₀, hne_pt⟩ := hnex
    have hB0 : ¬ B ∈ˢ (univZero : V) := fun hz =>
      hne_pt (eq_pt_of_mem_univZero hz (app_mem_piV hf ha₀))
    rw [piV_eq_pos Nat.one_ne_zero (quotClass_mem (u := u) (R := R) ha₀) hB0,
      piR_pos Nat.one_ne_zero, mem_piSet]
    refine ⟨sep_subset, fun q hq => ?_⟩
    obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
    refine ⟨app f a, mem_sep.mpr ⟨mem_prod.mpr ⟨quotClass u A R a, quotClass_mem ha,
        app f a, app_mem_piV hf ha, rfl⟩,
      a, ha, quotClass u A R a, app f a, rfl, rfl, rfl⟩, fun y' hy' => ?_⟩
    obtain ⟨_, a', ha', x, y, hkp, rfl, rfl⟩ := mem_sep.mp hy'
    obtain ⟨hcls, rfl⟩ := kpair_inj hkp
    exact (app_eq_of_quotClass_eq hA ha ha' hinv hcls).symm

/-! ## `Quot.lift` -/

theorem defFun_quotInvSpace_inner {V : Type w} [SetTheory V] {k : Nat}
    {A R f : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (hf : DefFun k f) :
    DefFun (k + 1) fun v =>
      piV (A (ftail v)) (fun b =>
        piV (app (app (R (ftail v)) (v 0)) b)
          (fun _ => eqv (app (f (ftail v)) (v 0)) (app (f (ftail v)) b))
          (hasSigmaPairs_const _ _))
        (hasSigmaPairs_of_defFun1
          (DefFun.piV_apply_curry
            (DefFun.app_apply (DefFun.app_apply (DefFun.const (R (ftail v))) (DefFun.const (v 0)))
              (DefFun.proj 0))
            (DefFun.eqv_apply (DefFun.const (app (f (ftail v)) (v 0)))
              (DefFun.app_apply (DefFun.const (f (ftail v))) (DefFun.proj 1))))) :=
  DefFun.piV_apply_curry hA.weaken
    (DefFun.piV_apply_curry
      (DefFun.app_apply (DefFun.app_apply hR.weaken.weaken (DefFun.proj 1)) (DefFun.proj 0))
      (DefFun.eqv_apply
        (DefFun.app_apply hf.weaken.weaken.weaken (DefFun.proj 2))
        (DefFun.app_apply hf.weaken.weaken.weaken (DefFun.proj 1))))

/-- `∀ a b, r a b → f a = f b`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  piV A (fun a =>
    piV A (fun b =>
      piV (app (app R a) b) (fun _ => eqv (app f a) (app f b)) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry
          (DefFun.app_apply (DefFun.app_apply (DefFun.const R) (DefFun.const a)) (DefFun.proj 0))
          (DefFun.eqv_apply (DefFun.const (app f a)) (DefFun.app_apply (DefFun.const f) (DefFun.proj 1))))))
    (hasSigmaPairs_of_defFun1
      (defFun_quotInvSpace_inner (DefFun.const A) (DefFun.const R) (DefFun.const f)))

theorem defFun_quotInvSpace {V : Type w} [SetTheory V] {k : Nat}
    {A R f : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (hf : DefFun k f) :
    DefFun k fun env => quotInvSpace V (A env) (R env) (f env) := by
  unfold quotInvSpace
  exact DefFun.piV_apply_curry hA (defFun_quotInvSpace_inner hA hR hf)

/-- The invariance premise, read off a proof's membership: three
eliminations. -/
theorem quotInv_of_mem {A R f h : V} (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      app f a = app f b := by
  intro a b ha hb hw
  obtain ⟨wv, hwv⟩ := hw
  rw [quotInvSpace] at hh
  have h1 : app h a ∈ˢ piV A (fun b =>
      piV (app (app R a) b) (fun _ => eqv (app f a) (app f b)) (hasSigmaPairs_const _ _)) _ :=
    app_mem_piV hh ha
  have h2 : app (app h a) b ∈ˢ
      piV (app (app R a) b) (fun _ => eqv (app f a) (app f b)) (hasSigmaPairs_const _ _) :=
    app_mem_piV h1 hb
  have h3 := app_mem_piV h2 hwv
  exact eq_of_mem_eqv h3

theorem defFun_quotLift_f {V : Type w} [SetTheory V] (u : Nat) (A R B : V) :
    DefFun 1 fun w =>
      lamV (quotInvSpace V A R (w 0)) (fun _ => quotLiftR V u A R B (w 0))
        (hasGraph_of_defFun1 (DefFun.const _)) :=
  DefFun.lamV_apply_curry
    (DefFun.quotLiftR_apply u (DefFun.const A) (DefFun.const R) (DefFun.const B) (DefFun.proj 1))
    (defFun_quotInvSpace (DefFun.const A) (DefFun.const R) (DefFun.proj 0))

theorem defFun_quotLift_B {V : Type w} [SetTheory V] (u : Nat) (A R : V) :
    DefFun 1 fun w =>
      lamV (piV A (fun _ => w 0) (hasSigmaPairs_const _ _)) (fun f =>
        lamV (quotInvSpace V A R f) (fun _ => quotLiftR V u A R (w 0) f)
          (hasGraph_of_defFun1 (DefFun.const _)))
        (hasGraph_of_defFun1 (defFun_quotLift_f u A R (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.quotLiftR_apply u (DefFun.const A) (DefFun.const R) (DefFun.proj 2) (DefFun.proj 1))
      (defFun_quotInvSpace (DefFun.const A) (DefFun.const R) (DefFun.proj 0)))
    (DefFun.piV_apply_curry (DefFun.const A) (DefFun.proj 1))

theorem defFun_quotLift_R {V : Type w} [SetTheory V] (u v : Nat) (A : V) :
    DefFun 1 fun w =>
      lamV (univ v) (fun B =>
        lamV (piV A (fun _ => B) (hasSigmaPairs_const _ _)) (fun f =>
          lamV (quotInvSpace V A (w 0) f) (fun _ => quotLiftR V u A (w 0) B f)
            (hasGraph_of_defFun1 (DefFun.const _)))
          (hasGraph_of_defFun1 (defFun_quotLift_f u A (w 0) B)))
        (hasGraph_of_defFun1 (defFun_quotLift_B u A (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.lamV_apply_curry
        (DefFun.quotLiftR_apply u (DefFun.const A) (DefFun.proj 3) (DefFun.proj 2) (DefFun.proj 1))
        (defFun_quotInvSpace (DefFun.const A) (DefFun.proj 2) (DefFun.proj 0)))
      (DefFun.piV_apply_curry (DefFun.const A) (DefFun.proj 1)))
    (DefFun.univ_const v)

theorem defFun_quotLift_A {V : Type w} [SetTheory V] (u v : Nat) :
    DefFun 1 fun w =>
      lamV (relSpace V (w 0)) (fun R =>
        lamV (univ v) (fun B =>
          lamV (piV (w 0) (fun _ => B) (hasSigmaPairs_const _ _)) (fun f =>
            lamV (quotInvSpace V (w 0) R f) (fun _ => quotLiftR V u (w 0) R B f)
              (hasGraph_of_defFun1 (DefFun.const _)))
            (hasGraph_of_defFun1 (defFun_quotLift_f u (w 0) R B)))
          (hasGraph_of_defFun1 (defFun_quotLift_B u (w 0) R)))
        (hasGraph_of_defFun1 (defFun_quotLift_R u v (w 0))) :=
  DefFun.lamV_apply_curry
    (DefFun.lamV_apply_curry
      (DefFun.lamV_apply_curry
        (DefFun.lamV_apply_curry
          (DefFun.quotLiftR_apply u (DefFun.proj 4) (DefFun.proj 3) (DefFun.proj 2) (DefFun.proj 1))
          (defFun_quotInvSpace (DefFun.proj 3) (DefFun.proj 2) (DefFun.proj 0)))
        (DefFun.piV_apply_curry (DefFun.proj 2) (DefFun.proj 1)))
      (DefFun.univ_const v))
    (defFun_relSpace (DefFun.proj 0))

/-- `Quot.lift.{u,v}`. -/
noncomputable def quotLiftV (u v : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (relSpace V A) (fun R =>
      lamV (univ v) (fun B =>
        lamV (piV A (fun _ => B) (hasSigmaPairs_const _ _)) (fun f =>
          lamV (quotInvSpace V A R f) (fun _ => quotLiftR V u A R B f)
            (hasGraph_of_defFun1 (DefFun.const _)))
          (hasGraph_of_defFun1 (defFun_quotLift_f u A R B)))
        (hasGraph_of_defFun1 (defFun_quotLift_B u A R)))
      (hasGraph_of_defFun1 (defFun_quotLift_R u v A)))
    (hasGraph_of_defFun1 (defFun_quotLift_A u v))

/-- **ι for `Quot.lift`**: five βs, no premise but domain membership. -/
theorem quotLiftV_app {u v : Nat} {A R B f h : V}
    (hA : A ∈ˢ (univ u : V)) (hR : R ∈ˢ relSpace V A)
    (hB : B ∈ˢ (univ v : V)) (hf : f ∈ˢ piV A (fun _ => B) (hasSigmaPairs_const _ _))
    (hh : h ∈ˢ quotInvSpace V A R f) :
    app (app (app (app (app (quotLiftV V u v) A) R) B) f) h =
      quotLiftR V u A R B f := by
  rw [quotLiftV, app_lamV hA, app_lamV hR, app_lamV hB, app_lamV hf, app_lamV hh]

/-- `Quot.lift` inhabits its type. -/
theorem quotLiftV_mem (u v : Nat) :
    quotLiftV V u v ∈ˢ piV (univ u : V) (fun A =>
      piV (relSpace V A) (fun R =>
        piV (univ v : V) (fun B =>
          piV (piV A (fun _ => B) (hasSigmaPairs_const _ _)) (fun f =>
            piV (quotInvSpace V A R f) (fun _ =>
              piV (quotSet u A R) (fun _ => B) (hasSigmaPairs_const _ _))
              (hasSigmaPairs_const _ _))
            (hasSigmaPairs_of_defFun1
              (DefFun.piV_apply_curry
                (defFun_quotInvSpace (DefFun.const A) (DefFun.const R) (DefFun.proj 0))
                (DefFun.piV_apply_curry (DefFun.const (quotSet u A R)) (DefFun.const B)))))
          (hasSigmaPairs_of_defFun1
            (DefFun.piV_apply_curry (DefFun.piV_apply_curry (DefFun.const A) (DefFun.proj 1))
              (DefFun.piV_apply_curry
                (defFun_quotInvSpace (DefFun.const A) (DefFun.const R) (DefFun.proj 0))
                (DefFun.piV_apply_curry (DefFun.const (quotSet u A R)) (DefFun.proj 3))))))
        (hasSigmaPairs_of_defFun1
          (DefFun.piV_apply_curry (DefFun.univ_const v)
            (DefFun.piV_apply_curry (DefFun.piV_apply_curry (DefFun.const A) (DefFun.proj 1))
              (DefFun.piV_apply_curry
                (defFun_quotInvSpace (DefFun.const A) (DefFun.proj 2) (DefFun.proj 0))
                (DefFun.piV_apply_curry
                  (defFun_quotSet_apply u (DefFun.const A) (DefFun.proj 3))
                  (DefFun.proj 3)))))))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry (defFun_relSpace (DefFun.proj 0))
          (DefFun.piV_apply_curry (DefFun.univ_const v)
            (DefFun.piV_apply_curry (DefFun.piV_apply_curry (DefFun.proj 2) (DefFun.proj 1))
              (DefFun.piV_apply_curry
                (defFun_quotInvSpace (DefFun.proj 3) (DefFun.proj 2) (DefFun.proj 0))
                (DefFun.piV_apply_curry
                  (defFun_quotSet_apply u (DefFun.proj 4) (DefFun.proj 3))
                  (DefFun.proj 3))))))) :=
  lamV_mem (fun _ hA => lamV_mem (fun _ _ => lamV_mem (fun _ hB =>
    lamV_mem (fun _ hf => lamV_mem (fun _ hh =>
      quotLiftR_mem V hA (IsTy_of_mem_univ hB) hf (quotInv_of_mem V hh))
      fun _ _ => IsTy_piV) fun _ _ => IsTy_piV) fun _ _ => IsTy_piV)
    fun _ _ => IsTy_piV) fun _ _ => IsTy_piV

/-! ## `Classical.choice` -/

/-- `¬¬A`, i.e. `(A → False) → False`: a truth value. -/
noncomputable def dnegSpace (A : V) : V :=
  piR 0 (piR 0 A (fun _ => empty) (hasSigmaPairs_const _ _)) (fun _ => empty)
    (hasSigmaPairs_const _ _)

theorem defFun_dnegSpace {V : Type w} [SetTheory V] {k : Nat} {A : (Fin k → V) → V}
    (hA : DefFun k A) : DefFun k fun env => dnegSpace V (A env) := by
  unfold dnegSpace
  exact DefFun.piR_apply_curry 0 (DefFun.piR_apply_curry 0 hA DefFun.empty) DefFun.empty

theorem piR_zero_empty (B : V → V) :
    piR 0 (empty : V) B (hasSigmaPairs_empty B) = unitSet := by
  rw [piR_zero, truthVal_eq_unitSet (fun x hx => absurd hx (not_mem_empty x))]

/-- `empty` (`False`) is a truth value. -/
theorem empty_mem_univZero : (empty : V) ∈ˢ (univZero : V) := by
  have h0 := empty_mem_univ (V := V) 0
  rwa [univ_zero] at h0

/-- The value-read `¬¬A` is `dnegSpace`: every fibre is `False`. -/
theorem piV_dneg_eq (A : V) :
    (piV (piV A (fun _ => (empty : V)) (hasSigmaPairs_const _ _)) (fun _ => (empty : V))
      (hasSigmaPairs_const _ _)) = dnegSpace V A := by
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
    have hpt : (pt : V) ∈ˢ piR 0 (empty : V) (fun _ => (empty : V)) (hasSigmaPairs_empty _) := by
      rw [piR_zero_empty]; exact pt_mem_unitSet
    rw [dnegSpace] at hh
    exact not_mem_empty _ (app_mem_piR hh hpt fun _ _ _ => empty_mem_univZero V)

/-- `Classical.choice.{u}`, using the internal universe choice function
`univChoiceFn u`. -/
noncomputable def choiceV (u : Nat) : V :=
  lamV (univ u) (fun A =>
    lamV (dnegSpace V A) (fun _ => app (univChoiceFn u) A)
      (hasGraph_of_defFun1 (DefFun.const _)))
    (hasGraph_of_defFun1
      (DefFun.lamV_apply_curry
        (DefFun.app_apply (DefFun.univChoiceFn_const u) (DefFun.proj 1))
        (defFun_dnegSpace (DefFun.proj 0))))

theorem choiceV_app {u : Nat} {A h : V} (hA : A ∈ˢ (univ u : V))
    (hh : h ∈ˢ dnegSpace V A) : app (app (choiceV V u) A) h = app (univChoiceFn u) A := by
  rw [choiceV, app_lamV hA, app_lamV hh]

/-- `Classical.choice` inhabits its type. -/
theorem choiceV_mem (u : Nat) :
    choiceV V u ∈ˢ piV (univ u : V) (fun A =>
      piV (dnegSpace V A) (fun _ => A) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry (defFun_dnegSpace (DefFun.proj 0)) (DefFun.proj 1))) :=
  lamV_mem (fun _ hA => lamV_mem (fun _ hh => app_univChoiceFn_mem hA (exists_mem_of_dneg V hh))
    fun _ _ => IsTy_of_mem_univ hA) fun _ _ => IsTy_piV

/-! ## `Empty.rec` -/

/-- `Empty.{u} → Sort v`: `{pt}`, the domain being empty. -/
noncomputable def emptyMotiveSpace (v : Nat) : V :=
  piV empty (fun _ => univ v) (hasSigmaPairs_const _ _)

/-- `Empty.rec.{u,v}`: an abstraction over an abstraction over `∅`,
the point. -/
noncomputable def emptyRecV (v : Nat) : V :=
  lamV (emptyMotiveSpace V v)
    (fun _ => lamV empty (fun _ => (empty : V)) (hasGraph_empty _))
    (hasGraph_of_defFun1 (DefFun.const _))

/-! ## `lfpFam` (task #188, indexed)

The least pre-fixed point of a functor on FAMILIES over an index set `I`
(`lfpFamSet`, `ConLeche/SetTheory/Derive/LfpFam.lean`).  The family space
`I → Sort w` is the value reading's (`piV`: `{pt}` over an empty `I`,
the graphs into `univ w` otherwise), and the least fixed points are its
members (`famOf`).  Total: the value is a member of the family space
for EVERY functor. -/

/-- `I → Sort w`, the family space, as the value reading has it. -/
noncomputable def lfpFamSpace (w : Nat) (I : V) : V :=
  piV I (fun _ => univ w) (hasSigmaPairs_const _ _)

theorem defFun_lfpFamSpace {V : Type w} [SetTheory V] {k : Nat} (w : Nat)
    {I : (Fin k → V) → V} (hI : DefFun k I) :
    DefFun k fun env => lfpFamSpace V w (I env) := by
  unfold lfpFamSpace
  exact DefFun.piV_apply_curry hI (DefFun.univ_const w)

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
    lfpFamSpace V w I = piR (w + 1) I (fun _ => univ w) (hasSigmaPairs_const _ _) :=
  piV_univ_eq_pos (Nat.succ_ne_zero w) hi _ fun _ _ => ⟨w, rfl⟩

/-- **The value reading's abstraction of a family of non-points is the
family** (`famOf`): the graph over an inhabited domain, the point over an
empty one. -/
theorem lamV_eq_famOf {A : V} {F : V → V} {hG : HasGraph A F}
    (h : ∀ x, x ∈ˢ A → F x ≠ pt) :
    lamV A F hG = famOf F A hG := by
  by_cases hA : ∃ x, x ∈ˢ A
  · obtain ⟨x, hx⟩ := hA
    rw [famOf_of_ne ⟨x, hx⟩]
    exact lamV_eq_graph (lamV_ne_pt_of hx (h x hx))
  · rw [famOf_of_empty hA]
    exact lamV_of_empty fun x hx => hA ⟨x, hx⟩

/-- A family of types is in the type `I → Sort w`. -/
theorem famOf_mem_lfpFamSpace {w : Nat} {I : V} {G : V → V} {hG : HasGraph I G}
    (h : ∀ i, i ∈ˢ I → G i ∈ˢ (univ w : V)) : famOf G I hG ∈ˢ lfpFamSpace V w I := by
  rw [lfpFamSpace_eq]; exact famOf_mem_famSpaceIn h

/-- The least fixed points' family space is inside the type `I → Sort w`. -/
theorem famSpace_subset_lfpFamSpace (w : Nat) (I : V) : famSpace w I ⊆ˢ lfpFamSpace V w I := by
  rw [lfpFamSpace_eq]
  exact famSpace_subset_univ w I

/-- `(I → Sort w) → (I → Sort w)`, the functor space. -/
noncomputable def lfpFamFunSpace (w : Nat) (I : V) : V :=
  piV (lfpFamSpace V w I) (fun _ => lfpFamSpace V w I) (hasSigmaPairs_const _ _)

theorem defFun_lfpFamFunSpace {V : Type w} [SetTheory V] {k : Nat} (w : Nat)
    {I : (Fin k → V) → V} (hI : DefFun k I) :
    DefFun k fun env => lfpFamFunSpace V w (I env) := by
  unfold lfpFamFunSpace
  exact DefFun.piV_apply_curry (defFun_lfpFamSpace w hI)
    (defFun_lfpFamSpace w hI.weaken)

/-- `lfpFam.{u,w}`. -/
noncomputable def lfpFamV (u w : Nat) : V :=
  lamV (univ u) (fun I =>
    lamV (lfpFamFunSpace V w I) (fun F => lfpFamSet w I F)
      (hasGraph_of_defFun1 (DefFun.lfpFamSet_apply w (DefFun.const I) (DefFun.proj 0))))
    (hasGraph_of_defFun1
      (DefFun.lamV_apply_curry
        (DefFun.lfpFamSet_apply w (DefFun.proj 1) (DefFun.proj 0))
        (defFun_lfpFamFunSpace w (DefFun.proj 0))))

theorem max_succ_ne_zero (u w : Nat) : Nat.max u (w + 1) ≠ 0 := by
  show max u (w + 1) ≠ 0
  rw [Nat.max_def]
  split <;> omega

theorem lfpFamSet_mem_space (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ lfpFamSpace V w I :=
  famSpace_subset_lfpFamSpace V w I _ (lfpFamSet_mem w I F)

theorem lfpFamV_mem (u w : Nat) :
    lfpFamV V u w ∈ˢ piV (univ u : V) (fun I =>
      piV (lfpFamFunSpace V w I) (fun _ => lfpFamSpace V w I) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry
          (defFun_lfpFamFunSpace w (DefFun.proj 0))
          (defFun_lfpFamSpace w (DefFun.proj 1)))) :=
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
  | s, n + 1 => sigmaSet r (F s) (fun _ => ndTowerSet r F (s + 1) n) (hasSigmaPairs_const _ _)

theorem ndTowerSet_mem_univ {r : Nat} {F : Nat → V} :
    ∀ (n s : Nat), (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      ndTowerSet V r F s n ∈ˢ (univ r : V)
  | 0, _, _ => unitSetAt_mem_univ r
  | n + 1, s, hF => by
    show sigmaSet r (F s) (fun _ => ndTowerSet V r F (s + 1) n) (hasSigmaPairs_const _ _) ∈ˢ _
    have h := sigma_mem_univ (u := r) (v := r) (hF s (by omega))
      (fun _ _ => ndTowerSet_mem_univ n (s + 1) fun m hm => hF m (by omega))
      (hasSigmaPairs_const _ _)
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
    show spair a (mkTower as) ∈ˢ
      sigmaSet r (F s) (fun _ => ndTowerSet V r F (s + 1) n) (hasSigmaPairs_const _ _)
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
    show sigmaSet r (F s) _ _ = sigmaSet r (F' s) _ _
    exact sigmaSet_ext (h s (by omega)) (hasSigmaPairs_const _ _) (hasSigmaPairs_const _ _)
      fun _ _ => ndTowerSet_congr n (s + 1) fun m hm => h m (by omega)

/-- **Elim**: every component of a member sits in the tower's own. -/
theorem projS_mem_ndTowerSet {r : Nat} (hr : r ≠ 0) {F : Nat → V} :
    ∀ (n s : Nat) {x : V}, x ∈ˢ ndTowerSet V r F s n →
      ∀ i, i < n → projS i x ∈ˢ F (s + i)
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, s, x, hx, i, hi => by
    have hx' : x ∈ˢ
        sigmaSet r (F s) (fun _ => ndTowerSet V r F (s + 1) n) (hasSigmaPairs_const _ _) := hx
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hx'
    subst_vars
    rw [hpos hr]
    cases i with
    | zero => rw [show projS 0 (spair a b) = sfst (spair a b) from rfl, sfst_spair]; simpa using ha
    | succ i =>
      rw [show projS (i + 1) (spair a b) = projS i (ssnd (spair a b)) from rfl, ssnd_spair,
        show s + (i + 1) = s + 1 + i from by omega]
      exact projS_mem_ndTowerSet hr n (s + 1) hb i (Nat.lt_of_succ_lt_succ hi)

theorem defFun_ndTowerSet {V : Type w} [SetTheory V] {k : Nat} (r : Nat) :
    ∀ (n s : Nat) {F : (Fin k → V) → Nat → V},
      (∀ m, m < s + n → DefFun k fun env => F env m) →
      DefFun k fun env => ndTowerSet V r (F env) s n
  | 0, _, _, _ => DefFun.unitSetAt_const r
  | n + 1, s, F, hF => by
    show DefFun k fun env =>
      sigmaSet r (F env s) (fun _ => ndTowerSet V r (F env) (s + 1) n) (hasSigmaPairs_const _ _)
    exact DefFun.sigmaSet_apply_curry r (hF s (by omega))
      ((defFun_ndTowerSet r n (s + 1) fun m hm => hF m (by omega)).weaken)

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`'s carrier — the index-set tuples. -/
noncomputable def tupleSortsSpace (k : Nat) (us : List Nat) : V :=
  ndTowerSet V (ConLeche.Term.tupleIdxSort us) (fun m => (univ (lv us m) : V)) 0 k

/-- `⟨proj_0 Is → Sort w, …⟩`'s carrier at an index-set tuple `Is`. -/
noncomputable def tupleFamsSpace (k : Nat) (us : List Nat) (Is : V) : V :=
  ndTowerSet V (ConLeche.Term.tupleFamSort k us)
    (fun m => lfpFamSpace V (lv us k) (projS m Is)) 0 k

theorem defFun_tupleFamsSpace {V : Type w} [SetTheory V] {p : Nat} (k : Nat)
    (us : List Nat) {Is : (Fin p → V) → V} (hIs : DefFun p Is) :
    DefFun p fun env => tupleFamsSpace V k us (Is env) := by
  unfold tupleFamsSpace
  exact defFun_ndTowerSet (ConLeche.Term.tupleFamSort k us) k 0
    fun m _ => defFun_lfpFamSpace (lv us k) (DefFun.projS_apply m hIs)

/-- The tuple operator an argument `F` of `lfpTuple k` induces:
component `m` of `F` applied to the tuple of the argument's first `k`
components. -/
noncomputable def tupleOpV (k : Nat) (F : V) : (Nat → V) → Nat → V :=
  fun X m => projS m (app F (mkTower ((List.range k).map X)))

theorem defTupleOp_tupleOpV {V : Type w} [SetTheory V] (k : Nat) (F : V) :
    DefTupleOp (V := V) k (tupleOpV V k F) := by
  refine ⟨fun X Y hXY m _ => ?_, fun m _ => ?_⟩
  · unfold tupleOpV
    have hmap : (List.range k).map X = (List.range k).map Y :=
      List.map_congr_left fun i hi => hXY i (List.mem_range.mp hi)
    rw [hmap]
  · unfold tupleOpV
    have hmk : DefFun k fun xs : Fin k → V => mkTower ((List.range k).map (padTuple xs)) :=
      DefFun.mkTower_range_apply k fun i hi =>
        (DefFun.proj ⟨i, hi⟩).congr fun xs => (padTuple_lt xs hi).symm
    exact DefFun.projS_apply m (DefFun.app_apply (DefFun.const F) hmk)

theorem defFun_lfpTupleV_mkTower {V : Type w} [SetTheory V] {p : Nat} (k : Nat)
    (us : List Nat) {Is F : (Fin p → V) → V} (hIs : DefFun p Is) (hF : DefFun p F) :
    DefFun p fun env =>
      mkTower ((List.range k).map fun m =>
        lfpTuple (lv us k) k (fun c => projS c (Is env)) (tupleOpV V k (F env))
          (defTupleOp_tupleOpV k (F env)) m) := by
  refine DefFun.mkTower_range_apply k fun m hm => ?_
  refine DefFun.lfpTuple_apply
    (Is := fun env c => projS c (Is env))
    (Φ := fun env => tupleOpV V k (F env))
    (fun c _ => DefFun.projS_apply c hIs)
    (fun env => defTupleOp_tupleOpV k (F env))
    (fun j _ => ?_) hm
  unfold tupleOpV
  have hmk : DefFun (V := V) (k + p) fun v => mkTower ((List.range k).map (padTuple (ftake v))) :=
    DefFun.mkTower_range_apply k fun i hi =>
      (DefFun.ftake_proj ⟨i, hi⟩).congr fun v => (padTuple_lt (ftake v) hi).symm
  exact DefFun.projS_apply j (DefFun.app_apply (DefFun.fdrop_apply hF) hmk)

/-- `lfpTuple k.{u_0 … u_{k-1}, w}`. -/
noncomputable def lfpTupleV (k : Nat) (us : List Nat) : V :=
  lamV (tupleSortsSpace V k us) (fun Is =>
    lamV (piV (tupleFamsSpace V k us Is) (fun _ => tupleFamsSpace V k us Is)
        (hasSigmaPairs_const _ _)) (fun F =>
      mkTower ((List.range k).map fun m =>
        lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k F)
          (defTupleOp_tupleOpV k F) m))
      (hasGraph_of_defFun1 (defFun_lfpTupleV_mkTower k us (DefFun.const Is) (DefFun.proj 0))))
    (hasGraph_of_defFun1
      (DefFun.lamV_apply_curry
        (defFun_lfpTupleV_mkTower k us (DefFun.proj 1) (DefFun.proj 0))
        (DefFun.piV_apply_curry
          (defFun_tupleFamsSpace k us (DefFun.proj 0))
          (defFun_tupleFamsSpace k us (DefFun.proj 1)))))

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
        lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ)
          (defTupleOp_tupleOpV k Φ) m)
      ∈ˢ tupleFamsSpace V k us Is := by
  unfold tupleFamsSpace
  refine mkTower_map_mem_ndTowerSet V (tupleFamSort_ne_zero k us) _ k 0 fun i hi => ?_
  show lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ)
      (defTupleOp_tupleOpV k Φ) i
    ∈ˢ lfpFamSpace V (lv us k) (projS (0 + i) Is)
  rw [Nat.zero_add]
  exact famSpace_subset_lfpFamSpace V _ _ _
    (lfpTuple_mem (lv us k) k (fun c => projS c Is) (tupleOpV V k Φ)
      (defTupleOp_tupleOpV k Φ) i hi)

theorem lfpTupleV_app {k : Nat} {us : List Nat} {Is F : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us)
    (hF : F ∈ˢ piV (tupleFamsSpace V k us Is) (fun _ => tupleFamsSpace V k us Is)
      (hasSigmaPairs_const _ _)) :
    app (app (lfpTupleV V k us) Is) F
      = mkTower ((List.range k).map fun m =>
          lfpTuple (lv us k) k (fun c => projS c Is) (tupleOpV V k F)
            (defTupleOp_tupleOpV k F) m) := by
  rw [lfpTupleV, app_lamV hIs, app_lamV hF]

theorem lfpTupleV_mem (k : Nat) (us : List Nat) :
    lfpTupleV V k us ∈ˢ piV (tupleSortsSpace V k us) (fun Is =>
      piV (piV (tupleFamsSpace V k us Is) (fun _ => tupleFamsSpace V k us Is)
          (hasSigmaPairs_const _ _))
        (fun _ => tupleFamsSpace V k us Is) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1
        (DefFun.piV_apply_curry
          (DefFun.piV_apply_curry
            (defFun_tupleFamsSpace k us (DefFun.proj 0))
            (defFun_tupleFamsSpace k us (DefFun.proj 1)))
          (defFun_tupleFamsSpace k us (DefFun.proj 1)))) :=
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
  | .quot, us => quotV V (lv us 0)
  | .quotMk, us => quotMkV V (lv us 0)
  | .quotLift, us => quotLiftV V (lv us 0) (lv us 1)
  | .quotInd, _ => pt
  | .quotSound, _ => pt
  | .propext, _ => pt
  | .choice, us => choiceV V (lv us 0)
  | .lfpFam, us => lfpFamV V (lv us 0) (lv us 1)
  | .lfpTuple k, us => lfpTupleV V k us

end ConLeche.SetModel
