module

public import ConLeche.Frontend.Olean.Files

@[expose] public section

/-!
# What a snapshot's `.olean` files say

The specification's notions over a snapshot of the file system (`FS`,
`ConLeche/Frontend/CheckerIO.lean`), in terms of the reader's file lookup (`readFiles`,
`moduleImports`, `ConLeche/Frontend/Olean/Files.lean`) and the decoder's specification
(`decodeModuleSpec`, `ConLeche/Frontend/Olean/View.lean`).  Nothing here is run: the main
theorems (`ConLeche/MainTheorem.lean`) and the input they speak about
(`ConLeche/OleanInput.lean`) are stated with them.

* **a module's private view** (`ViewOf`): its files on the search path and what they decode to;
* **the closure** of some roots (`InClosure`): the roots, and every import of the private view of
  a module of it; **by the headers** (`HdrClosure`): the same, each module's imports as its header
  read answers;
* **what a header loads** (`LoadsAt`, `Loads`): Lean's import walk, each part loaded whole or not;
* **two snapshots that agree under some directories** (`FS.AgreeUnder`): on every path the reader
  forms there.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Views and closures -/

/-- **The private view of a module on a snapshot**, by the specification: the module's files
on the search path, and what `decodeModuleSpec` says they hold at that level. -/
def ViewOf (sp : Roots) (fs : FS) (m : Name) (d : ModDecoded) : Prop :=
  ∃ f, ModelIO.CanGive (readFiles sp m .private) fs (.ok f) ∧ decodeModuleSpec f .private = some d

/-- **The modules of the closure of some roots**, on a snapshot: a root, or an import of the
private view of one. -/
inductive InClosure (sp : Roots) (fs : FS) (roots : Array Name) : Name → Prop
  | root {r : Name} : r ∈ roots → InClosure sp fs roots r
  | step {m : Name} {d : ModDecoded} {i : ImportRec} : InClosure sp fs roots m →
      ViewOf sp fs m d → i ∈ d.imports → InClosure sp fs roots i.module

/-- **The modules a header loads, and whether whole** (Lean v4.35's `importModulesCore`,
`Lean/Environment.lean`; ours `levelsGo`/`headerFixpoint`, `ConLeche/Frontend/Olean/Levels.lean`):
the least relation over the imports `imps0` of a root, `g` for a root outside the module system.
`LoadsAt … m true` says `m`'s private part is loaded (`importAll`), `LoadsAt … m false` that `m`
is loaded.  The root's imports are loaded, whole under `g` or `import all`; an import of a
loaded module is followed when it is public (`isExported`) or the module is loaded whole, and is
loaded whole under `g`, or where the module is and the import is an `import all`.  Each
module's imports are those of its private view's header. -/
inductive LoadsAt (sp : Roots) (fs : FS) (g : Bool) (imps0 : Array ImportRec) : Name → Bool → Prop
  | root {i : ImportRec} : i ∈ imps0 → LoadsAt sp fs g imps0 i.module (g || i.importAll)
  | step {a : Name} {all : Bool} {d : ModDecoded} {i : ImportRec} :
      LoadsAt sp fs g imps0 a all → ViewOf sp fs a d → i ∈ d.imports →
      (i.isExported || all) = true → LoadsAt sp fs g imps0 i.module (g || all && i.importAll)

/-- **Module `m`'s header loads part `p` of `m'`**: the private part where some path loads it
whole, else the exported part (`LoadsAt`, from `m`'s private view's header). -/
def Loads (sp : Roots) (fs : FS) (m m' : Name) (p : OLeanLevel) : Prop :=
  ∃ d, ViewOf sp fs m d ∧
    match p with
    | .private => LoadsAt sp fs (!d.isModule) d.imports m' true
    | .exported => LoadsAt sp fs (!d.isModule) d.imports m' false ∧
        ¬ LoadsAt sp fs (!d.isModule) d.imports m' true
    | .server => False

/-- **The import closure of some roots by the headers**: a root, or an import of a module of it,
as its header read answers on the snapshot (`moduleImports`). -/
inductive HdrClosure (sp : Roots) (fs : FS) (roots : List Name) : Name → Prop
  | root {r : Name} : r ∈ roots → HdrClosure sp fs roots r
  | step {m : Name} {is : Array ImportRec} {i : ImportRec} : HdrClosure sp fs roots m →
      ModelIO.CanGive (moduleImports sp m) fs (.ok is) → i ∈ is → HdrClosure sp fs roots i.module


/-! ## Agreement under directories -/

/-- **A path the reader forms under the directories**: a module's directory, the directory
itself included, or a module's file. -/
def _root_.ConLeche.Under (dirs : List System.FilePath) (p : System.FilePath) : Prop :=
  ∃ d ∈ dirs, ∃ m, p = modDir d m ∨ ∃ ext, p = modFile d m ext

/-- **Two snapshots agree under the directories**: every path the reader forms there has the
same real path, is a directory on both or on neither, and names the same bytes. -/
def _root_.ConLeche.FS.AgreeUnder (dirs : List System.FilePath) (fs₁ fs₂ : FS) : Prop :=
  ∀ p, Under dirs p → fs₁.real p = fs₂.real p ∧ fs₁.dir p = fs₂.dir p ∧ fs₁.file p = fs₂.file p

end ConLeche.Frontend.Olean
