module

public import ConLeche.IsModel
public import ConLeche.Frontend.Olean.Snapshot

@[expose] public section

/-!
# The `.olean` input as constants

`con-leche --olean -- M` checks the module `M` and everything it imports, read from the
`.olean` files on a snapshot of the file system.  This module says, with the specification's
notions of `ConLeche/Frontend/Olean/Snapshot.lean`, which constants that input is — the set
`IsModel` (`ConLeche/IsModel.lean`) is stated over — with nothing of how the reader reads them:

* **the closure** (`InClosure`): the roots, and every import of the private view of a module of
  it;
* **a module's view** (`ViewOf`): what its files hold at the private level, its imports and
  constants among it;
* **a stored constant's constants** (`entryConstants`): its declaration's, as the stream reader
  would read them from lean4export's output.  Unsafe and partial constants have none: lean4export
  leaves them out.  A recursor is one constant with its rules as stored (their firing mode is
  the reader's placeholder: the statement reads none);
* **a part's constants** (`InModulePart`): those of a module's part, exported or private; a
  module's constants (`moduleConstants`) are its private part's, the closure's
  (`closureConstants`) those of its modules.

There is no order and no merge here.  A name two modules store is one of Lean's: Lean's import
keeps one copy, and refuses the closure unless the two copies are one constant, or proofs of
one statement (a theorem for a theorem or for its axiom, an axiom for an axiom of a proposition;
`subsumesInfo`).  Two such copies are constants of one statement, which hold in a model
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

/-- **The constants of a stored constant**: a type former, a constructor and a recursor of a safe
inductive block are one constant each (a recursor with its rules as stored); any other constant has the constants of its declaration
(`declOfEntry`), an unsafe or partial one none. -/
def entryConstants (c : CEntryF Name Expr) : List ConstantInfo :=
  match c.kind with
  | .induct _ _ _ _ _ _ false _ => [.indInfo c.cv {}]
  | .ctor ind _ np nf false => [.ctorInfo c.cv np nf ind]
  | .recur _ np ni nmo nmi rules k false =>
    let mI := np + nmo + nmi + ni
    let rP := np + nmo + nmi
    [.recInfo c.cv mI rP k (rules.map fun (cn, nf, rhs) =>
      { ctor := cn, nfields := nf, fire := .plain, rhs })]
  | _ => ((declOfEntry c).map Declaration.constants).getD []

/-- **The constant `c` is in part `p` of module `m`**: `m`'s files on the search path, decoded
at the level `p` (`.exported`, or `.private`: the whole module), hold a stored constant `e` with
`c` among its constants (`entryConstants`).  Every `ConstantInfo` is one constant: a type former,
a constructor and a recursor of a block are one each, and every other kind of stored constant
gives at most one, so `c.name` is its single name.  It is the stored constant's own name except
at a quotient constant (and the axiom `Quot.sound`), which is the quotient package's constant of
its kind (`quotAt`), under that constant's name. -/
def InModulePart (sp : Roots) (fs : FS) (m : Name) (p : OLeanLevel) (c : ConstantInfo) : Prop :=
  ∃ f d e, ModelIO.CanGive (readFiles sp m p) fs (.ok f) ∧ decodeModuleSpec f p = some d ∧
    e ∈ d.constants ∧ c ∈ entryConstants e

/-- **A module's constants**: those of its private part, the whole module. -/
def moduleConstants (sp : Roots) (fs : FS) (m : Name) : ConstantInfo → Prop :=
  InModulePart sp fs m .private

/-- **The closure's constants**: every constant of every module of the closure of `roots`. -/
def closureConstants (sp : Roots) (fs : FS) (roots : Array Name) : ConstantInfo → Prop := fun c =>
  ∃ m, InClosure sp fs roots m ∧ moduleConstants sp fs m c

/-- **Module `m` sees `n` as `m'`'s**: `m`'s header loads a part of `m'` (`Loads`) that holds a
constant named `n`. -/
def Sees (sp : Roots) (fs : FS) (m n m' : Name) : Prop :=
  ∃ p c, Loads sp fs m m' p ∧ InModulePart sp fs m' p c ∧ c.name = n

end ConLeche.Frontend.Olean
