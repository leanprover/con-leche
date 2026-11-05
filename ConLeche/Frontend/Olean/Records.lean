module

public import ConLeche.Frontend.Olean.Emit
public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# `con-leche --olean`: the import closure as one record stream

`con-leche --olean M₁ … Mₙ` checks the modules `Mᵢ` and everything they
import, read from their `.olean` files.  This file ends the reader's
pipeline in the same `Declaration` records the lean4export reader produces
(`ConLeche/Frontend/ExportC.lean`), so that everything after the parse — the
prelude preparation, the install and the check, and the main theorem about
them — is the stream path's, unchanged.

**What is merged is what lean4export exports**: the closure loaded at the
PRIVATE level (each module-system module's `.olean.private`, whose
`ModuleData` holds the full constants; a module outside the module system has
only its `.olean`), merged as Lean's own `finalizeImport` merges them, and
emitted in lean4export's order.  Each emitted record becomes a `Declaration`
through the stream reader's own builder `declOfF`, so the validation of
inductive records (`validateIndF`) and every decline are the stream path's.
The tool `olean-compare` compares the two readers record for record.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **The `Declaration` records**, through the stream reader's builder.
A record's verdict (a decline, a contradiction between its fields) is
the stream path's, at the record's position. -/
def declsOf (em : Emit) : Except (CheckError × Nat) (Array Declaration) :=
  let nm (i : Nat) : M Name := match em.names[i]? with
    | some n => pure n | none => throw s!"undefined name index {i}"
  let lv (_ : Nat) : M Level := throw "no level table"
  let ex (i : Nat) : M Expr := match em.exprs[i]? with
    | some e => pure e | none => throw s!"undefined expr index {i}"
  em.out.size.fold (init := .ok #[]) fun k _ acc => do
    let ds ← acc
    match declOfF nm lv ex em.out[k] with
    | .ok (.inl d) => pure (ds.push d)
    | .ok (.inr v) => throw (v.toError, k)
    | .error msg => throw (.internal msg, k)

/-- The constants the emission starts from: the named ones, each of which the closure
must hold, or all of them. -/
def rootConstants (mg : Merged) : Option (Array Name) → Except CheckError (Array Name)
  | none => pure mg.order
  | some cs =>
    match cs.find? (!mg.map.contains ·) with
    | some c => throw (.internal s!"the constant {c} is not in the import closure")
    | none => pure cs

/-- **The whole read**: load, merge, emit, build.  `constants` names the constants to
start from, as lean4export's arguments after `--` do; `none` is every constant of the
closure. -/
def readOleans {μ : Type → Type} [CheckerIO μ] (sp : SearchPath)
    (roots : Array Name) (constants : Option (Array Name) := none) (jobs : Nat := 1) :
    μ (Except (CheckError × Nat) (Array Declaration)) := do
  match ← loadClosure sp roots jobs with
  | .error e => pure (.error (e, 0))
  | .ok ls =>
    match mergeAll ls with
    | .error e => pure (.error (e, 0))
    | .ok mg =>
      match rootConstants mg constants with
      | .error e => pure (.error (e, 0))
      | .ok cs =>
        let em := emitAll mg cs
        match coverageOk mg em with
        | .error e => pure (.error (e, 0))
        | .ok () => pure (declsOf em)

end ConLeche.Frontend.Olean
