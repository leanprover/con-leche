module

public import ConLeche.Verify.Denote.Lemmas
public import ConLeche.Model.Rules.IORel

public section

/-!
# The soundness motives: derivation ⇒ P currency (task #305)

One motive per relation of the rules tier, in the currency of
`Model/Claims.lean` (`interp` equality, `WellDenoted` grading,
membership), with the claims' own premises — the subject's frame
(`WScoped`, `looseBVarsBounded`, `LeavesBounded`), its context
discipline, its reading, its grading where the claim takes it — stated
at one valuation at a time and conditional on the point where the claim
is (task #342, L9; the section below), and with THREE deliberate
strengthenings over the claim statements, all forced by the
recursive-structure rules (ruling 1):

1. **Existence form.**  `RedSem` and the two `InferSem`s conclude the
   reduct's / the type's reading (`∃ ea', denote … e' = some ea'`)
   instead of taking it as a premise.  A rule like `DefEq.redL` needs
   the middle term's reading to apply the continuation's motive, and
   nothing else can supply it: reading totality is part of the main
   statements.  The dual-success claims follow by
   `Option.some.inj`.
2. **The frame in the conclusion.**  `RedSem` and `InferSem` also
   conclude the reduct's / the type's frame and leaf inclusion, so the
   continuation's `CtxOkS` is `CtxOkS.of_subset` — the run lemmas
   `whnfCore_WScoped`/`inferTypeCore_fvarLeaves` become conjuncts of
   the semantic induction rather than a second induction.
3. **The grade splits the inference motive**: full grade establishes
   the subject's grading (`InferClaim`'s shape), io grade consumes it
   (`InferClaimIO`'s premise form) — the establishment/consumption
   asymmetry, verbatim.

The motives are `@[expose]` because the per-rule lemma files and the
master induction unfold them.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V]

/-- A subject's syntactic frame — the three scoping premises every
claim carries. -/
@[expose] def Frame (d : Nat) (e : Expr) : Prop :=
  Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e

/-- A reading is graded under every satisfying valuation. -/
@[expose] def Graded (V : Type w) [SetTheory V] (Δa : List Term)
    (ea : Term) : Prop :=
  ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ea

/-- A reading is a graded type under every satisfying valuation — the
inferred type's currency (task #342, L5: `IsTy ⟦T⟧`). -/
@[expose] def GradedTy (V : Type w) [SetTheory V] (Δa : List Term)
    (ta : Term) : Prop :=
  ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta

/-- A graded type is graded. -/
theorem GradedTy.graded {Δa : List Term} {ta : Term}
    (h : GradedTy V Δa ta) : Graded V Δa ta := fun ρ hρ => (h ρ hρ).1

/-- No new free-variable leaf. -/
@[expose] def LeavesSub (e' e : Expr) : Prop :=
  ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves

/-! ## The per-valuation motives (task #342, L9)

Every motive speaks about ONE valuation at a time, as the fragment's
claims do (`whitepaper/Fragment/Motive.lean`): the subject's grading, its
leaves' grading (`LeavesGr`) and the context's satisfaction are premises at
`ρ`, and so are the conclusions.  The context discipline outside `ρ` is the
structural `CtxOkS`.

`RedSem`, `DefEqSem` and `DefEqListSem` are **conditional on the point**:
they equate two readings only at a valuation where neither is the point
(a reduction: where the subject is not).  They say nothing about proofs,
which is what lets β fire with no certificate (`Red.beta_sound`).  The
inference motives are not conditional: an inferred type is a type, never
the point.

The `…U` motives are the same statements without the point condition.
Some rules conclude them, a strengthening (ι and the K/`And` rescues,
`RedSemU`; the λ-telescope congruence, `DefEqLamsSem`), and reach the
conditional motives through `RedSemU.cond`/`DefEqSemU.cond`. -/

/-- **`Red`'s motive**: a reduction of a framed, readable subject
preserves the frame and reads; at a valuation where the subject is
graded and not the point, the reduct is graded and has the same
interpretation. -/
@[expose] def RedSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e e' : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List Term} {ea : Term},
    CtxOkS m φ d Δa e →
    denote m.acval env φ d e = some ea →
    Frame d e' ∧ LeavesSub e' e ∧
      ∃ ea', denote m.acval env φ d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          WellDenoted V ρ ea → interp V ρ ea ≠ pt →
          WellDenoted V ρ ea' ∧ interp V ρ ea = interp V ρ ea'

/-- `RedSem` without the point condition (a strengthening some rules conclude). -/
@[expose] def RedSemU {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e e' : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List Term} {ea : Term},
    CtxOkS m φ d Δa e →
    denote m.acval env φ d e = some ea →
    Frame d e' ∧ LeavesSub e' e ∧
      ∃ ea', denote m.acval env φ d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          WellDenoted V ρ ea →
          WellDenoted V ρ ea' ∧ interp V ρ ea = interp V ρ ea'

/-- **`DefEq`'s motive**: at a valuation where both sides are graded and
neither is the point, they are equal. -/
@[expose] def DefEqSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (a b : Expr) : Prop :=
  Frame d a → Frame d b →
  ∀ {Δa : List Term} {aa ba : Term},
    CtxOkS m φ d Δa a → CtxOkS m φ d Δa b →
    denote m.acval env φ d a = some aa →
    denote m.acval env φ d b = some ba →
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d a ρ → LeavesGr m φ d b ρ →
      WellDenoted V ρ aa → WellDenoted V ρ ba →
      interp V ρ aa ≠ pt → interp V ρ ba ≠ pt →
      interp V ρ aa = interp V ρ ba

/-- `DefEqSem` without the point condition (a strengthening some rules conclude). -/
@[expose] def DefEqSemU {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (a b : Expr) : Prop :=
  Frame d a → Frame d b →
  ∀ {Δa : List Term} {aa ba : Term},
    CtxOkS m φ d Δa a → CtxOkS m φ d Δa b →
    denote m.acval env φ d a = some aa →
    denote m.acval env φ d b = some ba →
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d a ρ → LeavesGr m φ d b ρ →
      WellDenoted V ρ aa → WellDenoted V ρ ba →
      interp V ρ aa = interp V ρ ba

/-- **`DefEqLams`' motive** (task #349): UNCONDITIONAL — at a valuation
where both λ-telescopes are graded they are equal, the point included.
The innermost level's body-type comparison puts the two bodies in one
type, whose members are all the point or none, so the bodies' conditional
claim is an equation; an equation of the bodies at every value of the
variable is an equation of the λs, so the claim propagates outward with
no further type comparison (the fragment's `LamsSem`). -/
@[expose] def DefEqLamsSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (a b : Expr) : Prop :=
  Frame d a → Frame d b →
  ∀ {Δa : List Term} {aa ba : Term},
    CtxOkS m φ d Δa a → CtxOkS m φ d Δa b →
    denote m.acval env φ d a = some aa →
    denote m.acval env φ d b = some ba →
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d a ρ → LeavesGr m φ d b ρ →
      WellDenoted V ρ aa → WellDenoted V ρ ba →
      interp V ρ aa = interp V ρ ba

/-- **`Infer`'s motive at the full grade** — establishment: the
subject's grading is a conclusion; the type is a graded type
(`WellDenotedTy`: its denotation is a type). -/
@[expose] def InferSemFull {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e t : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List Term} {ea : Term},
    CtxOkS m φ d Δa e →
    denote m.acval env φ d e = some ea →
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denote m.acval env φ d t = some ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          WellDenoted V ρ ea ∧ WellDenotedTy V ρ ta ∧
            interp V ρ ea ∈ˢ interp V ρ ta

/-- **`Infer`'s motive at the io grade** — consumption: the subject's
grading is a premise (`InferClaimIO`'s premise form), and the claim is
the hereditary `IORel` of task #346 (`IORel.lean`), keyed on the type's
syntax: at Lean's `infer_only` (no argument check at an application) an
io-inferred type need not hold its term.  At a subject whose head is
no λ and no `let` (`Expr.ioNeutral`) the claim is not hereditary
(`IORelN`): η's consumer. -/
@[expose] def InferSemIO {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (e t : Expr) : Prop :=
  Frame d e →
  ∀ {Δa : List Term} {ea : Term},
    CtxOkS m φ d Δa e →
    denote m.acval env φ d e = some ea →
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denote m.acval env φ d t = some ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          WellDenoted V ρ ea → IORelN m φ d e t ρ (interp V ρ ea)

/-- **A proposition's io claim is the point** (proof irrelevance at the
io grade): at every satisfying valuation, a value satisfying the io
claim at the type `T` is the point.  What the io inference of `T`'s
own sort, reducing to `Prop`, gives (`Sound.lean`, `prop_pt_io`): the
member half by the type's sort, the hereditary half by the ∀'s body's
sort, at the hereditary clause's witness. -/
@[expose] def PropPt {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (T : Expr) : Prop :=
  Frame d T →
  ∀ {Δa : List Term} {ta : Term},
    CtxOkS m φ d Δa T →
    denote m.acval env φ d T = some ta →
    ∀ (ρ : Nat → V) (v : V), Sat V Δa ρ → LeavesGr m φ d T ρ →
      IORel m φ d T ρ v → v = pt

/-- **The guard rows' motive** (`GuardRows`): each row's io claim, its
type's reduction to a sort, and that sort's vanishing with `guardSort`. -/
@[expose] def GuardRowsSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (guardSort : Level) (rows : List (Nat × Expr)) : Prop :=
  ∀ p ∈ rows, ∃ (t : Expr) (u : Level), InferSemIO m φ p.1 p.2 t ∧ RedSem m φ p.1 t (.sort u) ∧
    Red env p.1 t (.sort u) ∧ Level.zeroWhereZero guardSort u = true

/-- **A projection's guard's motive** (`ProjGuard`): at a stored constructor, the
typing law's premise. -/
@[expose] def ProjGuardSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (entry : ProjEntry) (us : List Level) : Prop :=
  ∀ (cvC : ConstantVal) (nP nF : Nat),
    env.find? entry.ctor = some (.ctorInfo cvC nP nF) → us.length = cvC.levelParams.length →
    (∀ cvT caps, env.find? entry.structName = some (.indInfo cvT caps) →
      us.length = cvT.levelParams.length) →
    TowerGuardAt m φ entry us cvC

/-- **The walk to a sort's motive** (`FormerSort`): where the subject is graded its
value is a tower of function spaces over the universe of the walk's sort, unless
a stage is the point, of which a reduction claims nothing. -/
@[expose] def FormerSortSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d n : Nat) (e : Expr) (s : Level) : Prop :=
  Frame d e →
  ∀ {Δa : List Term} {ea : Term},
    CtxOkS m φ d Δa e →
    denote m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ → WellDenoted V ρ ea →
      TowerEndsPt n (interp V ρ ea) (s.eval φ)

/-- **The ι case split's motive** (`IotaCase`): off a K rule, `false` means the
family is never `Prop` at the levels. -/
@[expose] def IotaCaseSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (isK : Bool) (cvj : ConstantVal) (us : List Level) (c3 : Bool) : Prop :=
  c3 = false → isK = false → FamNZ (V := V) m.acval env φ cvj us

/-- The grade-dispatched inference motive. -/
@[expose] def InferSem {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Grade → Nat → Expr → Expr → Prop
  | .full, d, e, t => InferSemFull m φ d e t
  | .io, d, e, t => InferSemIO m φ d e t

/-- **The arity-checked telescope's motive**: a spine of the subject
whose head's telescope has the spine's syntactic arity fits the
telescope's reading, substitution-peeling, where the spine is graded,
its head a member of the telescope's reading and the application not
the point ("not pt" source (2): a reduction claims nothing of a redex
that is the point) — premises exactly there. -/
@[expose] def TeleAritySem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (ty : Expr) (args : List Expr) : Prop :=
  Frame d ty →
  ∀ {Δa : List Term} {Ta fa : Term} {vs : List Term},
    CtxOkS m φ d Δa ty →
    denote m.acval env φ d ty = some Ta →
    (∀ x ∈ args, Frame d x ∧ CtxOkS m φ d Δa x) →
    DenoteSpine m.acval env φ d args vs →
    ∃ resta : Term,
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d ty ρ →
        (∀ x ∈ args, LeavesGr m φ d x ρ) →
        WellDenoted V ρ Ta → (∀ x ∈ vs, WellDenoted V ρ x) →
        (WellDenoted V ρ (Term.mkAppN fa vs) ∧
            interp V ρ fa ∈ˢ interp V ρ Ta ∧
            interp V ρ (Term.mkAppN fa vs) ≠ pt) →
        TeleFitPA V ρ Ta vs resta ∧ WellDenoted V ρ resta

/-- **`CertsF`' motive** (task #342 L10): the full-grade certificate
ESTABLISHES its arguments' grading (each slot ran `Infer .full`), so,
unlike `TeleAritySem`, it takes no grading of the spine and concludes it,
with the fit and the residual's grading. -/
@[expose] def CertsFSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (ty : Expr) (args : List Expr) : Prop :=
  Frame d ty →
  ∀ {Δa : List Term} {Ta : Term} {vs : List Term},
    CtxOkS m φ d Δa ty →
    denote m.acval env φ d ty = some Ta →
    (∀ x ∈ args, Frame d x ∧ CtxOkS m φ d Δa x) →
    DenoteSpine m.acval env φ d args vs →
    ∃ resta : Term,
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d ty ρ →
        (∀ x ∈ args, LeavesGr m φ d x ρ) →
        WellDenoted V ρ Ta →
        (∀ x ∈ vs, WellDenoted V ρ x) ∧ TeleFitPA V ρ Ta vs resta ∧
          WellDenoted V ρ resta

/-- **`DefEqList`'s motive**: the walk's LENGTH, and pointwise `interp`
equality where neither side is the point.  The length is a conclusion
of its own because the pointwise equality is only available once both
lists have been handed over as read spines — and a consumer
(`Red.iota_sound`'s `.nested` pin block) needs the length to BUILD the
second spine. -/
@[expose] def DefEqListSem {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (d : Nat) (as bs : List Expr) : Prop :=
  as.length = bs.length ∧
  ∀ {Δa : List Term} {asa bsa : List Term},
    (∀ x ∈ as, Frame d x ∧ CtxOkS m φ d Δa x) →
    (∀ x ∈ bs, Frame d x ∧ CtxOkS m φ d Δa x) →
    DenoteSpine m.acval env φ d as asa →
    DenoteSpine m.acval env φ d bs bsa →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      (∀ x ∈ as, LeavesGr m φ d x ρ) → (∀ x ∈ bs, LeavesGr m φ d x ρ) →
      (∀ x ∈ asa, WellDenoted V ρ x) → (∀ x ∈ bsa, WellDenoted V ρ x) →
      ∀ p ∈ (asa.map (interp V ρ)).zip (bsa.map (interp V ρ)),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2

/-! ### The unconditional motives weaken to the conditional ones -/

theorem RedSemU.cond {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {d : Nat} {e e' : Expr} (h : RedSemU m φ d e e') : RedSem m φ d e e' := by
  intro hf Δa ea hC hea
  obtain ⟨hf', hsub, ea', hea', hs⟩ := h hf hC hea
  exact ⟨hf', hsub, ea', hea', fun ρ hρ hL hw _ => hs ρ hρ hL hw⟩

theorem DefEqSemU.cond {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {d : Nat} {a b : Expr} (h : DefEqSemU m φ d a b) : DefEqSem m φ d a b :=
  fun hfa hfb _ _ _ hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _ =>
    h hfa hfb hCa hCb haa hba ρ hρ hLa hLb hwa hwb

theorem DefEqLamsSem.cond {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {d : Nat} {a b : Expr} (h : DefEqLamsSem m φ d a b) : DefEqSem m φ d a b :=
  fun hfa hfb _ _ _ hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _ =>
    h hfa hfb hCa hCb haa hba ρ hρ hLa hLb hwa hwb

end ConLeche.Model.Rules
