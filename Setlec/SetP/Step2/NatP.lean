import Setlec.SetP.Step2.ReadsP
import Setlec.SetP.Annot.ValidVSpine
import Setlec.Semantics.LitStep2
import Setlec.Verify.EnvGuards

/-!
# The literal tier, P currency (task #161)

The three routed literal rows — `ReduceNatReadsP` (`Step2/ReadsP.lean`),
`ReduceNatStepP` (`Step2/WhnfP.lean`), `ReduceNatStepPQ`
(`Step2/DefEqP.lean`) — all key on the same run: `reduceNatP`'s success.

## What lands here

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

That closes `ReduceNatReadsP` outright (`reduceNatReadsP_of`) — with
one environment law since task #161's item B3: `NatOpGuardLawP`, the
`nat_ops`/`div_mod` fields read in the direction the shrunk
reduction-time test needs (see `NatOpGuardLawP` below).

## The wall that stood here, and how it fell (SUPERSEDED)

The one conjunct the leaf analysis cannot give is the `interp2`
equality of `ReduceNatStepP`/`ReduceNatStepPQ`.  It was isolated here
as `NatOpSemP` — the campaign's first named wall (task #161 LITERAL
TIER seal II) — with `reduceNatStepP_of_sem`/`PQ_of_sem` machine-
checking that it was *all* that was missing.  All three are now
**deleted**: the law landed, and the two rows are proved outright in
`Interp2/NatStepP.lean` (`reduceNatStepP_of`/`reduceNatStepPQ_of`),
which consumes this file's leaf analysis unchanged.

The route was the one the wall record named: **not** the erasure
transfer, but `EnvS2PM.nat_ops`/`EnvS2PM.div_mod` — the stored
operations' recurrences at `interp2`, established at their own
installs from the recorded run certificates (`Interp2/NatEqsP.lean`,
`Interp2/DivModCertP.lean`) — plus the numeral transports
(`Interp2/NatSemP.lean`, `Interp2/NatWfP.lean`) and the widened
`WhnfInputsP.nat`/`TierInputsAtP.nat_step` signature, which now carries
the whnf IH the wall record recorded as owed.

## The refuted erasure factoring (PERMANENT RECORD)

The natural plan was to reuse the collapse lane, which proved this row
at `Setlec/SetR/Bridge/ReduceNat.lean` (`reduceNat_stepR`): read the
subject through `denoteP_erase`, run the v1 row, and transport the
answer back along `EnvS2Core.acval_erase`.  **That route is refuted,
and the refutation is already on record** — `Interp2/EnvLaws2.lean`'s
module docstring names `ReduceNatStep2` as one of three residues
"blocked not on proofs but on environment laws that do not exist over
`interp2`", because "the erasure link cannot carry it: `interp2` is
the two-regime annotation-driven interpretation, **not**
`interp ∘ erase`".

Two independent confirmations, both checked rather than assumed:

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
   battery had to exist again at `interp2`/`acval`.  It now does
   (`Interp2/NatSemP.lean` + `Interp2/NatWfP.lean`), built on the
   run-certificate laws rather than transported.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
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

/-- **The install fold's `Nat`-op invariant, in the form the literal
tier reads it** (task #161 de-gating item B3, harvest site 37 / list
entry P7).  `reduceNat` tests `natOpStored` — one `Env.find?` — where
it used to re-derive `natOpGuard` per literal hit; the guard is what
the leaf analysis below needs (`natLitSupported` for the numeral
shapes, the two `Bool` constructors for the comparison shapes), and it
is carried by `NatOpsP`/`DivModP`, whose statement is exactly "stored
as a `defnInfo` → guard ∧ the recurrences".  So the tier reads the
guard off the environment, and nothing about the shapes changes. -/
def NatOpGuardLawP (env : Env) : Prop :=
  ∀ c, (c ∈ Setlec.natOpNames ∨ c ∈ Setlec.natDivModNames) →
    Setlec.natOpStored env c = true → Setlec.natOpGuard env c = true

/-- `EnvS2PM` supplies it, from `nat_ops` and `div_mod`. -/
theorem natOpGuardLawP_of (mp : EnvS2PM V μ env) : NatOpGuardLawP env := by
  intro c hmem hst
  obtain ⟨cv, v, hh, hf⟩ := Setlec.natOpStored_inv hst
  rcases hmem with hm | hm
  · exact (mp.nat_ops (fun _ => 0) c hm cv v hh hf).1
  · exact (mp.div_mod (fun _ => 0) c hm cv v hh hf).1

/-- The unary clause's branch analysis: `Nat.succ` packing, the only
unary fold. -/
private theorem natLeafP_unary (_hlaw : NatOpGuardLawP env)
    {fuel d : Nat} {c : Name} {a e₂ : Expr}
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
  · simp [pure, Except.pure] at h

/-- The binary clause's branch analysis: the fourteen certified
operations, and the WF-pin safety net (which throws on literal
arguments and returns `none` otherwise). -/
private theorem natLeafP_binary (hlaw : NatOpGuardLawP env)
    {fuel d : Nat} {c : Name}
    {a b e₂ : Expr}
    (h : reduceNatP μ env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂)) : NatLeafP env e₂ := by
  simp only [reduceNatP, Setlec.reduceNat, Bind.bind, Except.bind,
    Setlec.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨hnames, hstored⟩ := hcond
    have hmem : c ∈ Setlec.natOpNames ∨ c ∈ Setlec.natDivModNames := by
      rcases hnames with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
    have hguard := hlaw _ hmem hstored
    -- first argument first; the second only behind a literal (D15)
    cases hwa : Setlec.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : Setlec.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    rw [hra] at h
    dsimp only at h
    cases hwb : Setlec.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hrb : Setlec.rawNatLit? b0 with
    | none => rw [hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hrb] at h
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
      cases hra : Setlec.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : Setlec.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : Setlec.rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-- **`Setlec.reduceNat_inv`, strengthened with the guard.**  The two
accelerating shapes are the only ones that reduce, and each carries the
stored-environment fact its reading needs. -/
theorem reduceNat_natLeafP (hlaw : NatOpGuardLawP env)
    {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatP μ env fuel d e = .ok (some e₂)) :
    NatLeafP env e₂ := by
  match e, h with
  | .app (.const c []) a, h => exact natLeafP_unary hlaw h
  | .app (.app (.const c []) a) b, h => exact natLeafP_binary hlaw h
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
theorem reduceNatReadsP_of (m : EnvS2Core V env) (hlaw : NatOpGuardLawP env)
    (φ : Name → Nat)
    (fuel : Nat) : ReduceNatReadsP μ m φ fuel := by
  intro d e e₂ ea h _hws _hb _hLb _hea
  have hleaf := reduceNat_natLeafP hlaw h
  obtain ⟨ea', hea'⟩ := denoteP_of_natLeafP (acval := m.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeafP (d := d) hleaf
  refine ⟨ea', hea', hws₂, hb₂, hLb₂, ?_⟩
  intro l hl
  rw [fvarLeaves_of_natLeafP hleaf] at hl
  exact nomatch hl

end Setlec.SetP

