import Setlec.SetR.Interp2.Step2.ReadsP
import Setlec.SetR.Annot.ValidVSpine
import Setlec.SetR.Interp2.Step2.Lit
import Setlec.Verify.EnvGuards

/-!
# The literal tier, P currency (task #161)

The three routed literal rows — `ReduceNatReadsP` (`Step2/ReadsP.lean`),
`ReduceNatStepP` (`Step2/WhnfP.lean`), `ReduceNatStepPQ`
(`Step2/DefEqP.lean`) — all key on the same run: `reduceNatP`'s success.

## What lands here, and what does not

`reduceNat`'s reduct is a **leaf**: a `Nat` literal, or a `Bool`
constructor constant applied to nothing (`Setlec.reduceNat_inv`).  So
every conjunct of the three rows *except one* is a fact about a leaf,
and this file proves them all, unconditionally:

* the reduct **reads** (`denoteP_of_natLeafP`) — the literal under the
  support guard, the constant under its stored-arity guard, both of
  which the accelerating branch's own condition supplies
  (`reduceNat_natLeafP`, the branch analysis);
* the reduct's **frame conditions** (`frame_of_natLeafP`) — a leaf has
  no `fvar` and no loose `bvar`, so `WScoped`/`looseBVarsBounded`/
  `LeavesBounded`/`CtxOkP` are free, exactly as in the collapse lane's
  `reduceNat_frameR`;
* the reduct's **grading** (`annotOkP_of_natLeafP`) — `natLit_facts2`
  and `AnnotValidV_natLitT2` on the numeral spine, `acval_ok2` and
  `AcvalValidP` on the constant.

That closes `ReduceNatReadsP` outright (`reduceNatReadsP_of`, **no
premises at all**).

The one conjunct that does **not** land is the `interp2` equality of
`ReduceNatStepP`/`ReduceNatStepPQ`.  It is isolated below as
`NatOpSemP`, and `reduceNatStepP_of_sem`/`reduceNatStepPQ_of_sem`
prove that `NatOpSemP` is *all* that is missing.  Those two are
**NOT discharges** — they are the wall, machine-checked to be exactly
one law wide.

## The wall, and why the erasure route cannot climb it (FINDING)

The natural plan is to reuse the collapse lane, which proved this row
at `Setlec/SetR/Bridge/ReduceNat.lean` (`reduceNat_stepR`): read the
subject through `denoteP_erase`, run the v1 row, and transport the
answer back along `EnvS2Core.acval_erase`.  **That route is refuted,
and the refutation is already on record** — `Interp2/EnvLaws2.lean`'s
module docstring names `ReduceNatStep2` as one of three residues
"blocked not on proofs but on environment laws that do not exist over
`interp2`", because "the erasure link cannot carry it: `interp2` is
the two-regime annotation-driven interpretation, **not**
`interp ∘ erase`".

Two independent confirmations, both checked here rather than assumed:

1. **The species lemma is false at the generality the row needs.**
   `interp2 V ρ ea = interp V ρ ea.erase` holds only where the two
   interpretations agree clause for clause, i.e. on `AVExpr`s with no
   `.lam`/`.pi` node (`lamR v`/`piR v` vs `lamC`/`piC`) *and* no
   `.const` node where `bval2` and `bval` differ (`natSuccV2 =
   lamR 1 omega natsucc` vs `natSuccV = lamC omega natsucc`;
   `Interp2/Value.lean` records `emptyRec` as differing outright).
   The subject of this row is `.app (acval c ψ) …` with `acval c ψ`
   the *stored* leaf of a `Nat` operation — a λ-tower.  So the
   factoring is unavailable exactly where it would be used.  Stated
   for the record: it *is* available on the reduct — a numeral spine
   over the two head leaves — but the reduct side is not what the
   equality needs.

2. **The v1 row does not conclude an equality anyway.**
   `reduceNat_stepR` concludes `Red μ env cval φ Δ v w`, whose
   soundness (`Red.sound`, `Sound/Main.lean`) consumes
   `EnvSHyp.nat_ops` — the `NatOpsV` battery of
   `Sound/NatOps.lean` (892 lines) at the *collapse* `interp`/`cval`.
   The P quarters conclude the `interp2` equality directly, so that
   battery would have to exist again at `interp2`/`acval`.  It does
   not: `NatOpsV2` (`Interp2/EnvLaws2.lean`) is a first-draft
   statement, deliberately unwired from `EnvS2` ("stated, queued"),
   and it is stated over `denote2`, not `denoteP`.

A third gap, independent of the first two: `reduceNatP` calls `whnf`
on its arguments, so the equality needs whnf soundness at the
arguments.  The collapse lane takes exactly that as a premise
(`reduceNat_stepR`'s `ihw : WhnfClaimsR mode m φ fuel`).  The P row's
consumer does not offer one — `WhnfInputsP.nat` is
`∀ m φ fuel, ReduceNatStepP μ m φ fuel` with no IH — although
`whnfStepP_of` has `WhnfClaims2P μ m φ fuel` in scope and discards it.
Wiring it through is a *statement* change to `WhnfInputsP`
(`Step2/WhnfP.lean`), which this file is not sanctioned to make.

So the literal tier's remaining owed work is: (a) a `NatOpsP` law over
`denoteP`/`interp2`/`acval` with an install-tier supplier, (b) the
`Sound/NatOps.lean` transport re-proved at `interp2`, and (c) the
`WhnfInputsP.nat` signature widened to carry the whnf IH.  None is a
proof step; all three are tier work.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo natOpResult
  natOpGuard natLitSupported reduceNatP)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The reduct's shape, with the guard that makes it read

`Setlec.reduceNat_inv` already reports the reduct's *shape* — a `Nat`
literal or a bare constant.  A reading needs more: the literal clause
of `denoteP` is guarded by `natLitSupported`, and the constant clause
needs the name stored at the right arity.  Both are supplied by the
accelerating branch's own `if` condition, so the strengthening below
is the same branch analysis with the condition retained. -/

/-- **The reduct's shape, guarded.**  What `reduceNat` can hand back,
together with the stored-environment fact that makes it read. -/
def NatLeafP (env : Env) (e : Expr) : Prop :=
  (∃ n, e = .lit (.natVal n) ∧ natLitSupported env = true) ∨
    ∃ (bn : Name) (ci : ConstantInfo), e = .const bn [] ∧
      env.find? bn = some ci ∧ ci.toConstantVal.levelParams = []

/-- Every `natOpResult` under its guard is a guarded leaf: a `Nat`
literal (and `natOpGuard` implies `natLitSupported`) or one of the two
`Bool` constructors (which `natOpGuard` pins, with no level
parameters, for exactly the names that can produce them).  This is
`Bridge/ReduceNat.lean`'s `denote_natOpResultR` with the denotation
stripped off. -/
private theorem natLeafP_of_natOpResult {c : Name} {n₁ n₂ : Nat}
    {r : Expr} (hguard : natOpGuard env c = true)
    (hres : natOpResult c n₁ n₂ = some r) : NatLeafP env r := by
  obtain ⟨hnat, -⟩ := Setlec.natOpGuard_deps hguard
  rcases Setlec.natOpResult_atom hres with ⟨k, rfl⟩ | ⟨hc, hbool⟩
  · exact Or.inl ⟨k, rfl, hnat⟩
  · have hc' : c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        Setlec.natDivModNames.contains c = true := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    obtain ⟨⟨ciT, hfT, hlpT⟩, ciF, hfF, hlpF⟩ :=
      Setlec.natOpGuard_bools hguard hc'
    rcases hbool with rfl | rfl
    · exact Or.inr ⟨_, ciT, rfl, hfT, hlpT⟩
    · exact Or.inr ⟨_, ciF, rfl, hfF, hlpF⟩

/-- The unary clause's branch analysis: `Nat.succ` packing, `Nat.pred`,
the certified `Nat.log2`, and the capless `log2` safety net (which
throws on a literal and returns `none` without one, so it never hands
back a reduct). -/
private theorem natLeafP_unary {fuel d : Nat} {c : Name} {a e₂ : Expr}
    (h : reduceNatP μ env fuel d (.app (.const c []) a)
      = .ok (some e₂)) : NatLeafP env e₂ := by
  simp only [reduceNatP, Setlec.reduceNat, Bind.bind, Except.bind,
    Setlec.whnf_def] at h
  split at h
  · -- `Nat.succ` packing
    next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : Setlec.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : Setlec.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n =>
      rw [hra] at h
      simp only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at h
      subst h
      exact Or.inl ⟨n + 1, rfl, hnat⟩
  · split at h
    · -- `Nat.pred`
      next hcond =>
      obtain ⟨rfl, hguard⟩ := hcond
      cases hwa : Setlec.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : Setlec.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n =>
        rw [hra] at h
        dsimp only at h
        cases hres : natOpResult Setlec.natPredName n 0 with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h
          subst h
          exact natLeafP_of_natOpResult hguard hres
    · split at h
      · -- the certified `Nat.log2`
        next hcond =>
        obtain ⟨rfl, hguard⟩ := hcond
        cases hwa : Setlec.whnf μ env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok a0 =>
        rw [hwa] at h
        dsimp only at h
        cases hra : Setlec.rawNatLit? a0 with
        | none => rw [hra] at h; simp [pure, Except.pure] at h
        | some n =>
          rw [hra] at h
          dsimp only at h
          cases hres : natOpResult Setlec.natLog2Name n 0 with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            subst h
            exact natLeafP_of_natOpResult hguard hres
      · split at h
        · -- the capless `log2` safety net
          cases hwa : Setlec.whnf μ env fuel d a with
          | error err => rw [hwa] at h; exact nomatch h
          | ok a0 =>
          rw [hwa] at h
          dsimp only at h
          cases hra : Setlec.rawNatLit? a0 with
          | none => rw [hra] at h; simp [pure, Except.pure] at h
          | some n =>
            rw [hra] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [pure, Except.pure] at h

/-- The binary clause's branch analysis: the fourteen certified
operations, and the WF-pin safety net (which throws on literal
arguments and returns `none` otherwise). -/
private theorem natLeafP_binary {fuel d : Nat} {c : Name}
    {a b e₂ : Expr}
    (h : reduceNatP μ env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂)) : NatLeafP env e₂ := by
  simp only [reduceNatP, Setlec.reduceNat, Bind.bind, Except.bind,
    Setlec.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨-, hguard⟩ := hcond
    cases hwa : Setlec.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hwb : Setlec.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hra : Setlec.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    cases hrb : Setlec.rawNatLit? b0 with
    | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hra, hrb] at h
      dsimp only at h
      cases hres : natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        subst h
        exact natLeafP_of_natOpResult hguard hres
  · split at h
    · -- the WF-pin safety net
      cases hwa : Setlec.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hwb : Setlec.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hra : Setlec.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      cases hrb : Setlec.rawNatLit? b0 with
      | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hra, hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-- **`Setlec.reduceNat_inv`, strengthened with the guard.**  The two
accelerating shapes are the only ones that reduce, and each carries the
stored-environment fact its reading needs. -/
theorem reduceNat_natLeafP {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatP μ env fuel d e = .ok (some e₂)) :
    NatLeafP env e₂ := by
  match e, h with
  | .app (.const c []) a, h => exact natLeafP_unary h
  | .app (.app (.const c []) a) b, h => exact natLeafP_binary h
  | .bvar _, h | .fvar _ _ _, h | .sort _, h | .lam _ _ _ _, h
  | .forallE _ _ _ _, h | .letE _ _ _ _, h | .lit _, h
  | .proj _ _ _, h | .const _ _, h =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h | .app (.fvar _ _ _) _, h
  | .app (.sort _) _, h | .app (.lam _ _ _ _) _, h
  | .app (.forallE _ _ _ _) _, h | .app (.letE _ _ _ _) _, h
  | .app (.lit _) _, h | .app (.proj _ _ _) _, h =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h | .app (.app (.fvar _ _ _) _) _, h
  | .app (.app (.sort _) _) _, h | .app (.app (.app _ _) _) _, h
  | .app (.app (.lam _ _ _ _) _) _, h
  | .app (.app (.forallE _ _ _ _) _) _, h
  | .app (.app (.letE _ _ _ _) _) _, h
  | .app (.app (.lit _) _) _, h
  | .app (.app (.proj _ _ _) _) _, h =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h

/-! ## What a guarded leaf gives: the reading, the frame, the grading -/

/-- **A guarded leaf reads**, at every depth. -/
theorem denoteP_of_natLeafP {acval : Name → (Name → Nat) → AVExpr}
    {e : Expr} (h : NatLeafP env e) (d : Nat) :
    ∃ ea, denoteP acval env φ d e = some ea := by
  rcases h with ⟨n, rfl, hg⟩ | ⟨bn, ci, rfl, hf, hlp⟩
  · exact ⟨_, denoteP_natLit hg⟩
  · exact ⟨_, denoteP_const hf (by simp [hlp])⟩

/-- **A guarded leaf has no leaves**: a literal and a bare constant are
both `fvar`-free. -/
theorem fvarLeaves_of_natLeafP {e : Expr} (h : NatLeafP env e) :
    e.fvarLeaves = [] := by
  rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;>
    simp [Expr.fvarLeaves]

/-- **A guarded leaf's frame conditions are free** — the P-currency
`reduceNat_frameR`. -/
theorem frame_of_natLeafP {d : Nat} {e : Expr} (h : NatLeafP env e) :
    Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e := by
  have hnf : e.hasFvar = false := by
    rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;> rfl
  refine ⟨Expr.WScoped.of_not_hasFvar hnf, ?_,
    Expr.LeavesBounded.of_not_hasFvar hnf⟩
  rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;> rfl

/-- A guarded leaf inherits any telescope the subject sat under: it has
no leaves to discipline, so only the length conjunct is transported. -/
theorem ctxOkP_of_natLeafP {m : EnvS2Core V env} {d : Nat}
    {Δa : List AVExpr} {e e' : Expr} (h : NatLeafP env e)
    (hC : CtxOkP m φ d Δa e') : CtxOkP m φ d Δa e := by
  refine ⟨hC.1, fun l hl => ?_⟩
  rw [fvarLeaves_of_natLeafP h] at hl
  exact nomatch hl

/-- **A guarded leaf's reading is graded.**  The numeral spine by
`natLit_facts2` (`AnnotOk2`) and `AnnotValidV_natLitT2`
(`AnnotValidV`); the constant by `acval_ok2` and `AcvalValidP`.  The
two premises are the P tier's own leaf residues — the same pair
`infer_natLit_claimP` takes. -/
theorem annotOkP_of_natLeafP (m : EnvS2Core V env)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m) {d : Nat} {e : Expr}
    {ea : AVExpr} (h : NatLeafP env e)
    (hea : denoteP m.acval env φ d e = some ea) (ρ : Nat → V) :
    AnnotOkP V ρ ea := by
  rcases h with ⟨n, rfl, hg⟩ | ⟨bn, ci, rfl, hf, hlp⟩
  · obtain ⟨-, rfl⟩ := denoteP_natLit_inv hea
    exact ⟨(natLit_facts2 (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ)
        (hnh hg ρ).1 (hnh hg ρ).2 n).1,
      AnnotValidV_natLitT2 (hval _ _ ρ) (hval _ _ ρ) n⟩
  · rw [denoteP_const hf (by simp [hlp])] at hea
    obtain rfl : ea = m.acval bn (Level.substFn φ ci.toConstantVal.levelParams []) :=
      (Option.some.inj hea).symm
    exact ⟨m.acval_ok2 _ _ ρ, hval _ _ ρ⟩

/-! ## `ReduceNatReadsP`, discharged

The readings row asks for the reduct's reading and its frame
conditions and nothing else, so the leaf analysis closes it outright —
with **no premises**: neither `NatHeadsP` nor `AcvalValidP` is needed,
because nothing here is graded. -/

/-- **`ReduceNatReadsP`, proved**, for every carrier, mode, assignment
and fuel. -/
theorem reduceNatReadsP_of (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat) : ReduceNatReadsP μ m φ fuel := by
  intro d e e₂ ea h _hws _hb _hLb _hea
  have hleaf := reduceNat_natLeafP h
  obtain ⟨ea', hea'⟩ := denoteP_of_natLeafP (acval := m.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeafP (d := d) hleaf
  exact ⟨ea', hea', hws₂, hb₂, hLb₂⟩

/-! ## The two step rows: the residue, isolated

`ReduceNatStepP` and `ReduceNatStepPQ` are the same statement up to
the binding site of the subject's annotation, and both ask for one
thing the leaf analysis cannot give: the `interp2` equality between
the subject's reading and the reduct's.  It is named below and
consumed below, so that the wall is exactly one law wide and the
supplier tier has a target.

**These are not discharges.**  Per the project's standing ruling that
a conditional form is not a solution, `ReduceNatStepP` and
`ReduceNatStepPQ` remain OPEN; see the module docstring for the three
pieces of tier work they wait on. -/

/-- **The literal tier's semantic residue.**  The `interp2` half of
`ReduceNatStepP`, alone: literal acceleration preserves the
interpretation.

This is the P-currency slot of `NatOpsV2`
(`Interp2/EnvLaws2.lean` — stated, unwired, and over `denote2` rather
than `denoteP`), composed with the whnf soundness at the operation's
arguments that `reduceNat` runs and the P row's consumer does not
offer.  Its collapse-lane counterpart is not a statement at all but a
consequence: `Red.sound` at `Red.natSucc`/`natOp1`/`natOp2`, over
`EnvSHyp.nat_ops`. -/
def NatOpSemP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {ea ea₂ : AVExpr},
    reduceNatP μ env fuel d e = .ok (some e₂) →
    denoteP m.acval env φ d e = some ea →
    denoteP m.acval env φ d e₂ = some ea₂ →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ea = interp2 V ρ ea₂

/-- **`ReduceNatStepP` is exactly `NatOpSemP` away**: every other
conjunct — the reduct's reading, its grading, and its four frame
conditions — is proved here.  NOT a discharge (see the section
docstring). -/
theorem reduceNatStepP_of_sem (m : EnvS2Core V env)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m) {fuel : Nat}
    (hsem : NatOpSemP μ m φ fuel) : ReduceNatStepP μ m φ fuel := by
  intro d e e₂ Δa h _hws _hb _hLb ea hC hea _hok
  have hleaf := reduceNat_natLeafP h
  obtain ⟨ea₂, hea₂⟩ := denoteP_of_natLeafP (acval := m.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeafP (d := d) hleaf
  have hC₂ := ctxOkP_of_natLeafP hleaf hC
  exact ⟨ea₂, hea₂,
    fun ρ _ => annotOkP_of_natLeafP m hnh hval hleaf hea₂ ρ,
    hsem h hea hea₂, hws₂, hb₂, hLb₂, hC₂⟩

/-- **`ReduceNatStepPQ` is exactly `NatOpSemP` away**, likewise: the
defeq quarter's row differs from the whnf quarter's only in where the
subject's annotation is bound.  NOT a discharge. -/
theorem reduceNatStepPQ_of_sem (m : EnvS2Core V env)
    (hnh : NatHeadsP m φ) (hval : AcvalValidP m) {fuel : Nat}
    (hsem : NatOpSemP μ m φ fuel) : ReduceNatStepPQ μ m φ fuel := by
  intro d e e₂ Δa ea h hws hb hLb hC hea hok
  exact reduceNatStepP_of_sem m hnh hval hsem h hws hb hLb hC hea hok

end Setlec.SetR.Interp2

