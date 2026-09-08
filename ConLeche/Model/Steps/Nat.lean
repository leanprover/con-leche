import ConLeche.Model.Steps.Reads
import ConLeche.Model.Annot.ValidSpine
import ConLeche.Semantics.LitStep
import ConLeche.Verify.EnvGuards

/-!
# The literal tier, P currency (task #161)

The three routed literal rows — `ReduceNatReads` (`Steps/Reads.lean`),
`ReduceNatStep` (`Steps/Whnf.lean`), `ReduceNatStepPQ`
(`Steps/DefEq.lean`) — all key on the same run: `reduceNatFueled`'s success.

## What lands here

`reduceNat`'s reduct is a **leaf**: a `Nat` literal, or a `Bool`
constructor constant applied to nothing (`ConLeche.reduceNat_inv`).  So
every conjunct of the three rows *except one* is a fact about a leaf,
and this file proves them all, unconditionally:

* the reduct **reads** (`denoteMeta_of_natLeaf`) — the literal under the
  support guard, the constant under its stored-arity guard, both of
  which the accelerating branch's own condition supplies
  (`reduceNat_natLeaf`, the branch analysis);
* the reduct's **frame conditions** (`frame_of_natLeaf`) — a leaf has
  no `fvar` and no loose `bvar`, so `WScoped`/`looseBVarsBounded`/
  `LeavesBounded`/`CtxOk` are free, exactly as in the collapse lane's
  `reduceNat_frameR`;
* the reduct's **grading** (`wellDenotedV_of_natLeaf`) — `natLit_factsAV`
  and `AnnotValid_natLitAV` on the numeral spine, `acval_wellDenoted` and
  `AcvalValid` on the constant.

That closes `ReduceNatReads` outright (`reduceNatReads_of`) — with
one environment law since task #161's item B3: `NatOpGuardLaw`, the
`nat_ops`/`div_mod` fields read in the direction the shrunk
reduction-time test needs (see `NatOpGuardLaw` below).

## The wall that stood here, and how it fell (SUPERSEDED)

The one conjunct the leaf analysis cannot give is the `interp`
equality of `ReduceNatStep`/`ReduceNatStepPQ`.  It was isolated here
as `NatOpSemP` — the campaign's first named wall (task #161 LITERAL
TIER seal II) — with `reduceNatStepP_of_sem`/`PQ_of_sem` machine-
checking that it was *all* that was missing.  All three are now
**deleted**: the law landed, and the two rows are proved outright in
`Interp/NatStepP.lean` (`reduceNatStep_of`/`reduceNatStepPQ_of`),
which consumes this file's leaf analysis unchanged.

The route was the one the wall record named: **not** the erasure
transfer, but `EnvModelM.nat_ops`/`EnvModelM.div_mod` — the stored
operations' recurrences at `interp`, established at their own
installs from the recorded run certificates (`Interp/NatEqsP.lean`,
`Interp/DivModCertP.lean`) — plus the numeral transports
(`Interp/NatSemP.lean`, `Interp/NatWfP.lean`) and the widened
`WhnfInputs.nat`/`TierInputsAt.nat_step` signature, which now carries
the whnf IH the wall record recorded as owed.

## The refuted erasure factoring (PERMANENT RECORD)

The natural plan was to reuse the collapse lane, which proved this row
at `ConLeche/SetR/Bridge/ReduceNat.lean` (`reduceNat_stepR`): read the
subject through `denoteMeta_erase`, run the v1 row, and transport the
answer back along `EnvModel.acval_erase`.  **That route is refuted,
and the refutation is already on record** — `Interp/EnvLaws2.lean`'s
module docstring names `ReduceNatStep2` as one of three residues
"blocked not on proofs but on environment laws that do not exist over
`interp`", because "the erasure link cannot carry it: `interp` is
the two-regime annotation-driven interpretation, **not**
`interp ∘ erase`".

Two independent confirmations, both checked rather than assumed:

1. **The species lemma is false at the generality the row needs.**
   `interp V ρ ea = interp V ρ ea.erase` holds only where the two
   interpretations agree clause for clause, i.e. on `AnnotTerm`s with no
   `.lam`/`.pi` node (`lamR v`/`piR v` vs `lamC`/`piC`) *and* no
   `.const` node where `bval` and `bval` differ (`natSuccV =
   lamR 1 omega natsucc` vs `natSuccV = lamC omega natsucc`;
   `Interp/Value.lean` records `emptyRec` as differing outright).
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
   The P quarters conclude the `interp` equality directly, so that
   battery had to exist again at `interp`/`acval`.  It now does
   (`Interp/NatSemP.lean` + `Interp/NatWfP.lean`), built on the
   run-certificate laws rather than transported.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo natOpResult
  natOpGuard natLitSupported reduceNatFueled)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The reduct's shape, with the guard that makes it read

`ConLeche.reduceNat_inv` already reports the reduct's *shape* — a `Nat`
literal or a bare constant.  A reading needs more: the literal clause
of `denoteMeta` is guarded by `natLitSupported`, and the constant clause
needs the name stored at the right arity.  Both are supplied by the
accelerating branch's own `if` condition, so the strengthening below
is the same branch analysis with the condition retained. -/

/-- **The reduct's shape, guarded.**  What `reduceNat` can hand back,
together with the stored-environment fact that makes it read. -/
def NatLeaf (env : Env) (e : Expr) : Prop :=
  (∃ n, e = .lit (.natVal n) ∧ natLitSupported env = true) ∨
    ∃ (bn : Name) (ci : ConstantInfo), e = .const bn [] ∧
      env.find? bn = some ci ∧ ci.toConstantVal.levelParams = []

/-- Every `natOpResult` under its guard is a guarded leaf: a `Nat`
literal (and `natOpGuard` implies `natLitSupported`) or one of the two
`Bool` constructors (which `natOpGuard` pins, with no level
parameters, for exactly the names that can produce them).  This is
`Bridge/ReduceNat.lean`'s `denote_natOpResultR` with the denotation
stripped off. -/
private theorem natLeaf_of_natOpResult {c : Name} {n₁ n₂ : Nat}
    {r : Expr} (hguard : natOpGuard env c = true)
    (hres : natOpResult c n₁ n₂ = some r) : NatLeaf env r := by
  obtain ⟨hnat, -⟩ := ConLeche.natOpGuard_deps hguard
  rcases ConLeche.natOpResult_atom hres with ⟨k, rfl⟩ | ⟨hc, hbool⟩
  · exact Or.inl ⟨k, rfl, hnat⟩
  · have hc' : c = ConLeche.natBeqName ∨ c = ConLeche.natBleName ∨
        ConLeche.natDivModNames.contains c = true := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    obtain ⟨⟨ciT, hfT, hlpT⟩, ciF, hfF, hlpF⟩ :=
      ConLeche.natOpGuard_bools hguard hc'
    rcases hbool with rfl | rfl
    · exact Or.inr ⟨_, ciT, rfl, hfT, hlpT⟩
    · exact Or.inr ⟨_, ciF, rfl, hfF, hlpF⟩

/-- **The install fold's `Nat`-op invariant, in the form the literal
tier reads it** (task #161 de-gating item B3, harvest site 37 / list
entry P7).  `reduceNat` tests `natOpStored` — one `Env.find?` — where
it used to re-derive `natOpGuard` per literal hit; the guard is what
the leaf analysis below needs (`natLitSupported` for the numeral
shapes, the two `Bool` constructors for the comparison shapes), and it
is carried by `NatOps`/`DivMod`, whose statement is exactly "stored
as a `defnInfo` → guard ∧ the recurrences".  So the tier reads the
guard off the environment, and nothing about the shapes changes. -/
def NatOpGuardLaw (env : Env) : Prop :=
  ∀ c, (c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames) →
    ConLeche.natOpStored env c = true → ConLeche.natOpGuard env c = true

/-- `EnvModelM` supplies it, from `nat_ops` and `div_mod`. -/
theorem natOpGuardLaw_of (mp : EnvModelM V μ env) : NatOpGuardLaw env := by
  intro c hmem hst
  obtain ⟨cv, v, hh, hf⟩ := ConLeche.natOpStored_inv hst
  rcases hmem with hm | hm
  · exact (mp.nat_ops (fun _ => 0) c hm cv v hh hf).1
  · exact (mp.div_mod (fun _ => 0) c hm cv v hh hf).1

/-- The unary clause's branch analysis: `Nat.succ` packing, the only
unary fold. -/
private theorem natLeaf_unary (_hlaw : NatOpGuardLaw env)
    {fuel d : Nat} {c : Name} {a e₂ : Expr}
    (h : reduceNatFueled μ env fuel d (.app (.const c []) a)
      = .ok (some e₂)) : NatLeaf env e₂ := by
  simp only [reduceNatFueled, ConLeche.reduceNat, Bind.bind, Except.bind,
    ConLeche.whnf_def] at h
  split at h
  · -- `Nat.succ` packing
    next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
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
private theorem natLeaf_binary (hlaw : NatOpGuardLaw env)
    {fuel d : Nat} {c : Name}
    {a b e₂ : Expr}
    (h : reduceNatFueled μ env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂)) : NatLeaf env e₂ := by
  simp only [reduceNatFueled, ConLeche.reduceNat, Bind.bind, Except.bind,
    ConLeche.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨hnames, hstored⟩ := hcond
    have hmem : c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames := by
      rcases hnames with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
    have hguard := hlaw _ hmem hstored
    -- first argument first; the second only behind a literal (D15)
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    rw [hra] at h
    dsimp only at h
    cases hwb : ConLeche.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hrb : ConLeche.rawNatLit? b0 with
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
        exact natLeaf_of_natOpResult hguard hres
  · split at h
    · -- the WF-pin safety net
      cases hwa : ConLeche.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : ConLeche.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : ConLeche.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : ConLeche.rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-- **`ConLeche.reduceNat_inv`, strengthened with the guard.**  The two
accelerating shapes are the only ones that reduce, and each carries the
stored-environment fact its reading needs. -/
theorem reduceNat_natLeaf (hlaw : NatOpGuardLaw env)
    {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatFueled μ env fuel d e = .ok (some e₂)) :
    NatLeaf env e₂ := by
  match e, h with
  | .app (.const c []) a, h => exact natLeaf_unary hlaw h
  | .app (.app (.const c []) a) b, h => exact natLeaf_binary hlaw h
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _ _, h
  | .forallE _ _ _, h | .letE _ _ _, h | .lit _, h
  | .proj _ _ _, h | .const _ _, h =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h | .app (.fvar _ _) _, h
  | .app (.sort _) _, h | .app (.lam _ _ _) _, h
  | .app (.forallE _ _ _) _, h | .app (.letE _ _ _) _, h
  | .app (.lit _) _, h | .app (.proj _ _ _) _, h =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h | .app (.app (.fvar _ _) _) _, h
  | .app (.app (.sort _) _) _, h | .app (.app (.app _ _) _) _, h
  | .app (.app (.lam _ _ _) _) _, h
  | .app (.app (.forallE _ _ _) _) _, h
  | .app (.app (.letE _ _ _) _) _, h
  | .app (.app (.lit _) _) _, h
  | .app (.app (.proj _ _ _) _) _, h =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h

/-! ## What a guarded leaf gives: the reading, the frame, the grading -/

/-- **A guarded leaf reads**, at every depth. -/
theorem denoteMeta_of_natLeaf {acval : Name → (Name → Nat) → AnnotTerm}
    {e : Expr} (h : NatLeaf env e) (d : Nat) :
    ∃ ea, denoteMeta acval env φ d e = some ea := by
  rcases h with ⟨n, rfl, hg⟩ | ⟨bn, ci, rfl, hf, hlp⟩
  · exact ⟨_, denoteMeta_natLit hg⟩
  · exact ⟨_, denoteMeta_const hf (by simp [hlp])⟩

/-- **A guarded leaf has no leaves**: a literal and a bare constant are
both `fvar`-free. -/
theorem fvarLeaves_of_natLeaf {e : Expr} (h : NatLeaf env e) :
    e.fvarLeaves = [] := by
  rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;>
    simp [Expr.fvarLeaves]

/-- **A guarded leaf's frame conditions are free** — the P-currency
`reduceNat_frameR`. -/
theorem frame_of_natLeaf {d : Nat} {e : Expr} (h : NatLeaf env e) :
    Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e := by
  have hnf : e.hasFvar = false := by
    rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;> rfl
  refine ⟨Expr.WScoped.of_not_hasFvar hnf, ?_,
    Expr.LeavesBounded.of_not_hasFvar hnf⟩
  rcases h with ⟨n, rfl, -⟩ | ⟨bn, ci, rfl, -, -⟩ <;> rfl

/-- A guarded leaf inherits any telescope the subject sat under: it has
no leaves to discipline, so only the length conjunct is transported. -/
theorem ctxOk_of_natLeaf {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {e e' : Expr} (h : NatLeaf env e)
    (hC : CtxOk m φ d Δa e') : CtxOk m φ d Δa e := by
  refine ⟨hC.1, fun l hl => ?_⟩
  rw [fvarLeaves_of_natLeaf h] at hl
  exact nomatch hl

/-- **A guarded leaf's reading is graded.**  The numeral spine by
`natLit_factsAV` (`WellDenoted`) and `AnnotValid_natLitAV`
(`AnnotValid`); the constant by `acval_wellDenoted` and `AcvalValid`.  The
two premises are the P tier's own leaf residues — the same pair
`infer_natLit_claim` takes. -/
theorem wellDenotedV_of_natLeaf (m : EnvModel V env)
    (hnh : NatHeads m φ) (hval : AcvalValid m) {d : Nat} {e : Expr}
    {ea : AnnotTerm} (h : NatLeaf env e)
    (hea : denoteMeta m.acval env φ d e = some ea) (ρ : Nat → V) :
    WellDenotedV V ρ ea := by
  rcases h with ⟨n, rfl, hg⟩ | ⟨bn, ci, rfl, hf, hlp⟩
  · obtain ⟨-, rfl⟩ := denoteMeta_natLit_inv hea
    exact ⟨(natLit_factsAV (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ)
        (hnh hg ρ).1 (hnh hg ρ).2 n).1,
      AnnotValid_natLitAV (hval _ _ ρ) (hval _ _ ρ) n⟩
  · rw [denoteMeta_const hf (by simp [hlp])] at hea
    obtain rfl : ea = m.acval bn (Level.substFn φ ci.toConstantVal.levelParams []) :=
      (Option.some.inj hea).symm
    exact ⟨m.acval_wellDenoted _ _ ρ, hval _ _ ρ⟩

/-! ## `ReduceNatReads`, discharged

The readings row asks for the reduct's reading and its frame
conditions and nothing else, so the leaf analysis closes it outright —
with **no premises**: neither `NatHeads` nor `AcvalValid` is needed,
because nothing here is graded. -/

/-- **`ReduceNatReads`, proved**, for every carrier, mode, assignment
and fuel. -/
theorem reduceNatReads_of (m : EnvModel V env) (hlaw : NatOpGuardLaw env)
    (φ : Name → Nat)
    (fuel : Nat) : ReduceNatReads μ m φ fuel := by
  intro d e e₂ ea h _hws _hb _hLb _hea
  have hleaf := reduceNat_natLeaf hlaw h
  obtain ⟨ea', hea'⟩ := denoteMeta_of_natLeaf (acval := m.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeaf (d := d) hleaf
  refine ⟨ea', hea', hws₂, hb₂, hLb₂, ?_⟩
  intro l hl
  rw [fvarLeaves_of_natLeaf hleaf] at hl
  exact nomatch hl

end ConLeche.Model

