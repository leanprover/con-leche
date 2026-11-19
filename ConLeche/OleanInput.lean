module

public import ConLeche.IsModel
public import ConLeche.Frontend.Prepare
public import ConLeche.Verify.Frontend.Olean.Files

@[expose] public section

/-!
# The `.olean` input as records

`con-leche --olean -- M` checks the module `M` and everything it imports, read from the
`.olean` files on a snapshot of the file system.  This module says, with the specification's
notions of `ConLeche/Verify/Frontend/Olean/Files.lean`, which records that input is — the set
`IsModel` (`ConLeche/IsModel.lean`) is stated over — with nothing of how the reader reads them:

* **the closure** (`InClosure`): the roots, and every import of the private view of a module of
  it;
* **a module's view** (`ViewOf`): what its files hold at the private level, its constants among
  it;
* **a constant's record** (`entryRecords`): its declaration's records, as the stream reader
  would read them from lean4export's output.  Unsafe and partial constants have none: lean4export
  leaves them out.  A recursor's rules fire as its own type says against its block's type
  formers, the names its `all` lists (`inputFire`);
* **the input** (`InputRecords`): every record of every constant of every module of the closure,
  and the records of each prelude declaration the closure does not declare (the preparation
  synthesises those; `ConLeche/Frontend/Prepare.lean`).

There is no order and no merge here.  A name two modules store is one of Lean's: Lean's import
keeps one copy, and refuses the closure unless the two copies are one constant, or proofs of
one statement (a theorem for a theorem or for its axiom, an axiom for an axiom of a proposition;
`subsumesInfo`).  Two such copies have records with one statement, which hold in a model
together, so the set of both is the input.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- A stored constant's name, level parameters and type. -/
def CEntryF.cv (c : CEntryF Name Expr) : ConstantVal := ⟨c.name, c.levelParams, c.type⟩

/-- A definition's reducibility hint, as a stored constant carries it. -/
def _root_.ConLeche.Frontend.HintsRec.toHint : HintsRec → ReducibilityHint
  | .«abbrev» => .«abbrev»
  | .«opaque» => .«opaque»
  | .regular n => .regular n

/-- **The declaration a stored constant is**, outside an inductive block: an axiom, a safe
definition, a theorem, a safe opaque constant, a quotient constant. -/
def declOfEntry (c : CEntryF Name Expr) : Option Declaration :=
  match c.kind with
  | .ax false => some (.axiomDecl c.cv)
  | .defn v h "safe" => some (.defnDecl c.cv v h.toHint)
  | .thm v _ => some (.thmDecl c.cv v)
  | .opaq v false => some (.opaqueDecl c.cv v)
  | .quot "type" => some (.quotDecl .type c.cv)
  | .quot "ctor" => some (.quotDecl .ctor c.cv)
  | .quot "lift" => some (.quotDecl .lift c.cv)
  | .quot "ind" => some (.quotDecl .ind c.cv)
  | _ => none

/-- **The records of a stored constant**: a type former, a constructor and a recursor of a safe
inductive block are one record each, the recursor's rules firing as its type says against its
block's type formers (`all`); any other constant has the records of its declaration
(`declOfEntry`), an unsafe or partial one none. -/
def entryRecords (c : CEntryF Name Expr) : List ConstantInfo :=
  match c.kind with
  | .induct _ _ _ _ _ _ false _ => [.indInfo c.cv {}]
  | .ctor ind _ np nf false => [.ctorInfo c.cv np nf ind]
  | .recur all np ni nmo nmi rules k false =>
    let mI := np + nmo + nmi + ni
    let rP := np + nmo + nmi
    [.recInfo c.cv mI rP k (rules.map fun (cn, nf, rhs) =>
      { ctor := cn, nfields := nf, fire := inputFire all c.cv mI rP, rhs })]
  | _ => ((declOfEntry c).map Declaration.records).getD []

/-- **The closure's records**: every record of every constant of the private view of every
module of the closure of `roots`. -/
def ClosureRecords (sp : Roots) (fs : FS) (roots : Array Name) : Records := fun r =>
  ∃ m d c, InClosure sp fs roots m ∧ ViewOf sp fs m d ∧ c ∈ d.constants ∧ r ∈ entryRecords c

/-- The closure of `roots` stores a constant named `n`. -/
def ClosureStores (sp : Roots) (fs : FS) (roots : Array Name) (n : Name) : Prop :=
  ∃ m d c, InClosure sp fs roots m ∧ ViewOf sp fs m d ∧ c ∈ d.constants ∧ c.name = n

/-- **The input of `--olean`**: the closure's records, and the records of every declaration of
the prelude `pre` the closure does not declare (`preludeKey`: a block's first type former, the
constant otherwise). -/
def InputRecords (pre : PreludeIx) (sp : Roots) (fs : FS) (roots : Array Name) : Records :=
  fun r => ClosureRecords sp fs roots r ∨
    ∃ p ∈ pre.decls, ¬ ClosureStores sp fs roots (preludeKey p) ∧ r ∈ p.records

end ConLeche.Frontend.Olean
