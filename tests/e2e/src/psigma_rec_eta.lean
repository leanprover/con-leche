--#export psigmaRecStuckEta

import Lean

/- End-to-end test (task #61): a **stuck-major structure-eta rescue on
   the pinned `PSigma'` basis block**.

   `PSigma'` — the lean-inductive-models preprocessor's tight dependent
   pair, `{α : Sort u} → (α → Sort v) → Sort (max u v)`, with no `max 1`
   floor — cannot be written with Lean's `inductive` command (the
   surface checker refuses a result sort that may be `Prop`), so it is
   *kernel-added* here exactly as the preprocessor splices it
   (`InductiveModels.psigmaPrimeDecl`).  setlec's frontend matches the
   resulting block against its pinned basis declarations, so this
   fixture runs the real pin.

   The theorem is also kernel-added (`addDecl` → the official C++
   kernel), so nothing here depends on the *elaborator* knowing about
   `PSigma'` (it is not registered as a structure, so `Meta`-level
   struct eta is unavailable — the kernel's is not).  That the file
   compiles at all is therefore the record of the *official* verdict:
   Lean 4.29.1's kernel accepts this shape.

   Committed as a *raw* lean4export result (regenerate with
   `LEAN_INDUCTIVE_MODELS_FILTER=0`); `tests/arena.sh` runs it with
   `SETLEC_INDUCTIVE_MODELS=/nonexistent` (the `raw` marker in
   `tests/e2e-expected.txt`).

   What it forces, at a **neutral** major `t : PSigma'.{1,1} α β`
   (levels concrete so that the official rescue's `is_never_zero` gate
   on `max u v` passes):

   * `Eq.refl (motive t) (minor t.1 t.2)` must have type
     `Eq (motive t) …`, i.e. `motive (PSigma'.mk α β t.1 t.2) ≡
     motive t` — defeq-side pair eta (`pairEtaCert` in setlec,
     `try_eta_struct` officially);
   * the stated left-hand side `PSigma'.rec α β motive minor t` must
     be identified with `minor t.1 t.2` — the *stuck-major* rescue
     (`to_cnstr_when_structure` / lean4lean `toCtorWhenStruct`), which
     for the pinned `PSigma'` is inert in setlec (the generic
     `structEtaCertWith` excludes reserved basis names and the 0-field
     `PUnit` fallback needs `etaFields = 0`).

   Note that `PSigma'.rec` is **Prop-eliminating only** (`PSigma'`'s
   result sort `max u v` may be zero, so Lean's kernel derives a small
   eliminator: `motive : PSigma' α β → Sort 0`, two level parameters).
   Every term the rescue could produce is therefore a *proof*, and
   setlec identifies the two sides by proof irrelevance instead — the
   verdict is the same.  This fixture pins that equality of verdicts.
-/

open Lean

/- The preprocessor's tight pair, spliced through the kernel. -/
run_cmd Lean.Elab.Command.liftCoreM do
  let lu := Level.param `u
  let lv := Level.param `v
  let ty : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.sort (mkLevelMax' lu lv)) .default) .implicit
  let mkTy : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.forallE `fst (.bvar 1)
        (.forallE `snd (.app (.bvar 1) (.bvar 0))
          (mkAppN (.const `PSigma' [lu, lv]) #[.bvar 3, .bvar 2]) .default)
        .default) .implicit) .implicit
  Lean.addDecl (.inductDecl [`u, `v] 2
    [{ name := `PSigma', type := ty,
       ctors := [{ name := `PSigma'.mk, type := mkTy }] }] false)

/- The stuck-major statement, checked by the official kernel. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let one : Level := .succ .zero
  Lean.Meta.withLocalDeclD `α (.sort one) fun α => do
  let βty : Expr := .forallE `x α (.sort one) .default
  Lean.Meta.withLocalDeclD `β βty fun β => do
  let pair := mkAppN (.const `PSigma' [one, one]) #[α, β]
  let motiveTy : Expr := .forallE `t pair (.sort .zero) .default
  Lean.Meta.withLocalDeclD `motive motiveTy fun motive => do
  let minorTy ← Lean.Meta.withLocalDeclD `fst α fun fst => do
    Lean.Meta.withLocalDeclD `snd (mkApp β fst) fun snd =>
      Lean.Meta.mkForallFVars #[fst, snd]
        (mkApp motive (mkAppN (.const `PSigma'.mk [one, one]) #[α, β, fst, snd]))
  Lean.Meta.withLocalDeclD `minor minorTy fun minor => do
  Lean.Meta.withLocalDeclD `t pair fun t => do
    let lhs := mkAppN (.const `PSigma'.rec [one, one]) #[α, β, motive, minor, t]
    let rhs := mkAppN minor #[.proj `PSigma' 0 t, .proj `PSigma' 1 t]
    let stmt := mkAppN (.const `Eq [.zero]) #[mkApp motive t, lhs, rhs]
    let type ← Lean.Meta.mkForallFVars #[α, β, motive, minor, t] stmt
    let value ← Lean.Meta.mkLambdaFVars #[α, β, motive, minor, t]
      (mkAppN (.const `Eq.refl [.zero]) #[mkApp motive t, rhs])
    Lean.addDecl (.thmDecl
      { name := `psigmaRecStuckEta, levelParams := [], type, value })
