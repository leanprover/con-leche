module

public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# The declaration fold

`checkDecls mode pins maxNatSize ds` is the verified implementation: the pure fold the main theorem and
main corollary are stated about (`ConLeche/MainTheorem.lean`).  At each position it checks the
record (`checkDeclStepC`, from a fresh memo state: nothing but the index crosses from one record to
the next), and what the record adds to the index is a function of the record alone (`declConstants`,
`declTables`, `ConLeche/Kernel/Install.lean`; `checkDeclStepC_pushes`).

The binary's driver (`ConLeche/Driver/*`) builds the index of the whole stream first and runs the
checks in any order, each at the view of its position (`ConLeche/Cached/StreamIndex.lean`); that
every check passing is an accept of this fold is `checkDecls_of_jobs`
(`ConLeche/Verify/Cached/StreamIndex.lean`), so the driver's accept comes with the proof that
`checkDecls` accepts.

**The pin list is a parameter.**  `checkDecls`, `declStep` and below them `checkDeclStepC` and the
`Expr`-level `checkDecl` take the list of `Nat.div`/`Nat.mod` pin variants the gate tries, as their
second argument, right after `mode`.  The shipped checker runs at `natOpPinSets`, the variants this
toolchain committed; the main theorem and the main corollary are stated for every list, because
nothing the model tier consumes reads which list the matched variant came from.

**So is the maximum `Nat` size.**  `maxNatSize`, right after the pin list, is the largest `Nat` numeral
in bytes the core takes in or computes (`natOpRefusal`, `ConLeche/Cached/StateC.lean`); each
record's fresh memo state carries it (`CState.maxNatSize`).  The shipped checker runs at
`maxNatSizeDefault` unless `--max-nat-size` says otherwise; the theorems hold at every `maxNatSize`,
because a refusal only ever throws.

Nothing here is `IO`.  A rejection carries the fold position of the declaration it names, so the
driver reports the declaration by indexing the record array it already holds.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- **One record of the fold**: the `And` pin, then the record's check from a fresh memo state.
The accumulator is the position and the index; a failure is tagged with the position.

The pin comes first (`andPinOk`, `ConLeche/Kernel/Basis.lean`): a record that declares `And`,
`And.intro` or `And.rec` and is not the toolchain's `And` block is rejected whatever its kind, so
the name `And` in an accepted environment is the pinned block, and the stuck-proof rescue that
serves it (`majorToCtor`'s `And` branch) is always available.  The soundness proofs never read it
(the rescue is sound for any `And`), so `checkDecl` does not repeat it. -/
def declStep (pins : List NatOpPinSet) (maxNatSize : Nat) (p : Nat × FEnv) (pd : Declaration) :
    Except (CheckError × Nat) (Nat × FEnv) :=
  if andPinOk pd then
    match checkDeclStepC mode pins p.2 pd { maxNatSize := maxNatSize } with
    | .ok (fe', _) => .ok (p.1 + 1, fe')
    | .error e => .error (e, p.1)
  else .error (.invalid "`And` must be the standard `And`", p.1)

/-- An accepting run of the fold: a chain of accepting `declStep`s. -/
inductive DeclsRun (pins : List NatOpPinSet) (maxNatSize : Nat) :
    List Declaration → Nat × FEnv → Nat × FEnv → Prop where
  | nil (p : Nat × FEnv) : DeclsRun pins maxNatSize [] p p
  | cons {pd : Declaration} {ds : List Declaration} {p p₁ p' : Nat × FEnv}
      (h : declStep mode pins maxNatSize p pd = .ok p₁) (rest : DeclsRun pins maxNatSize ds p₁ p') :
      DeclsRun pins maxNatSize (pd :: ds) p p'

/-- The accepting step's result, unfolded. -/
theorem declStep_ok {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat} {p q : Nat × FEnv}
    {pd : Declaration} (h : declStep mode pins maxNatSize p pd = .ok q) :
    ∃ fe' s', q = (p.1 + 1, fe') ∧ checkDeclStepC mode pins p.2 pd { maxNatSize := maxNatSize } = .ok (fe', s') := by
  unfold declStep at h
  split at h
  case isFalse => exact nomatch h
  cases hs : checkDeclStepC mode pins p.2 pd { maxNatSize := maxNatSize } with
  | error e => rw [hs] at h; exact nomatch h
  | ok r =>
    obtain ⟨fe', s₁⟩ := r
    rw [hs] at h
    simp only [Except.ok.injEq] at h
    exact ⟨fe', s₁, h.symm, rfl⟩

/-- **The declaration fold.**

The records are the array the frontend produces (`Frontend.preparePrelude`); the proofs read the
fold as `ds.toList.foldlM` (`Array.foldlM_toList`), which is where `DeclsRun` lives.  The `× Nat` of
the error is the failure's position: here the record's position in the fold, in the frontend's half
of the same error type the input's line number (`ConLeche/Frontend/Export.lean`). -/
def checkDecls (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration) :
    Except (CheckError × Nat) Env := do
  let p ← ds.foldlM (declStep mode pins maxNatSize) (0, mkFEnv Env.empty)
  pure p.2.env

/-- An accepting run is an accepting `foldlM`. -/
theorem DeclsRun.foldlM {pins : List NatOpPinSet} {maxNatSize : Nat} {ds : List Declaration} {p p' : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize ds p p') : ds.foldlM (declStep mode pins maxNatSize) p = .ok p' := by
  induction h with
  | nil p => rfl
  | cons hstep _ ih =>
    rw [List.foldlM_cons]
    simp only [Bind.bind, hstep, Except.bind]
    exact ih

/-- An accepting `foldlM` is an accepting run. -/
theorem DeclsRun.of_foldlM {pins : List NatOpPinSet} {maxNatSize : Nat} :
    ∀ (ds : List Declaration) (p : Nat × FEnv) {p' : Nat × FEnv},
      ds.foldlM (declStep mode pins maxNatSize) p = .ok p' → DeclsRun mode pins maxNatSize ds p p'
  | [], p, p', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil p
  | pd :: ds, p, p', h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind] at h
    cases hstep : declStep mode pins maxNatSize p pd with
    | error e => simp only [hstep, Except.bind] at h; exact nomatch h
    | ok p₁ =>
      simp only [hstep, Except.bind] at h
      exact .cons hstep (DeclsRun.of_foldlM ds p₁ h)

/-- A run extends at its end by one accepting step. -/
theorem DeclsRun.snoc {pins : List NatOpPinSet} {maxNatSize : Nat} {ds : List Declaration} {p p' p₁ : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize ds p p') {pd : Declaration} (hstep : declStep mode pins maxNatSize p' pd = .ok p₁) :
    DeclsRun mode pins maxNatSize (ds ++ [pd]) p p₁ := by
  induction h with
  | nil p => exact .cons hstep (.nil _)
  | cons h₀ _ ih => exact .cons h₀ (ih hstep)

/-- **Every accept of the fold is an accepting run from the empty index.** -/
theorem checkDecls_run {pins : List NatOpPinSet} {maxNatSize : Nat} {ds : Array Declaration} {env : Env}
    (h : checkDecls mode pins maxNatSize ds = .ok env) :
    ∃ n fe, DeclsRun mode pins maxNatSize ds.toList (0, mkFEnv Env.empty) (n, fe) ∧ fe.env = env := by
  unfold checkDecls at h
  rw [← Array.foldlM_toList] at h
  cases hrun : ds.toList.foldlM (declStep mode pins maxNatSize) (0, mkFEnv Env.empty) with
  | error e => rw [hrun] at h; exact nomatch h
  | ok r =>
    obtain ⟨n, fe⟩ := r
    rw [hrun] at h
    obtain rfl : fe.env = env := Except.ok.inj h
    exact ⟨n, fe, DeclsRun.of_foldlM mode ds.toList _ hrun, rfl⟩

/-- **An accepting run is an accept of the fold.** -/
theorem checkDecls_of_run {pins : List NatOpPinSet} {maxNatSize : Nat} {ds : Array Declaration} {n : Nat} {fe : FEnv}
    (h : DeclsRun mode pins maxNatSize ds.toList (0, mkFEnv Env.empty) (n, fe)) :
    checkDecls mode pins maxNatSize ds = .ok fe.env := by
  unfold checkDecls
  rw [← Array.foldlM_toList, h.foldlM]
  rfl

end ConLeche.Cached
