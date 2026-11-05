module

public import ConLeche.Frontend.Olean.Records

@[expose] public section

/-!
# Reading `.olean` files: the public interface

**Import this module.**  Outside `ConLeche/Frontend/Olean/` and its proofs
`ConLeche/Verify/Frontend/Olean/`, nothing imports the tree's other modules
(`tests/layering.sh`).  The names below are the interface; everything else the
tree declares (`moduleSkel`, `parseAt`, `runPasses`, `sGo`, `locateHits`, `findModule`,
`readPart`, `readImportsAt`, ...) is public only because checker code
is exposed and its proofs unfold it: a definition an exposed definition mentions
cannot be `private`.  It is not an interface, and may change at will.

**Files.**  `Part.ofBytes path bytes : Except CheckError Part` validates one file's
header; `ModFiles` holds a module's (`M.olean`, and the two others where a view needs
them).  A view is named by its level, `OLeanLevel`: `.exported`, `.server`, `.private`.

**Views.**

| name | theorem (`ConLeche/Verify/Frontend/Olean/`) |
|---|---|
| `decodeModuleSpec f level : Option ModDecoded`, not executable | the definition of a valid view |
| `parseView f level : Option ModDecoded` | `parseView_eq_spec` |
| `parseAllViews f : Option AllViews`, each object once | `parseAllViews_eq` |
| `checkViews m f v : Except CheckError (Array Expo)` | the views against each other, a home's check |

**Reads of a part of a view.**

| name | theorem: where the view parses, the read returns its part |
|---|---|
| `readNamePositions f level : Option NamePositions` | `readNamePositions_of_view` |
| `readEntry f level c : Option (CEntryF Name Expr)` | `readEntry_of_view` |
| `readStmts f level cs : Option (List ConstantVal)` | `readStmts_of_view` |
| `importsPre bytes : Option (Array ImportRec)`, on a prefix of `M.olean` | `importsPre_extract`, `importsPre_prefix` |

**Through the IO class** (`CheckerIO`), by module name along a search path.

| name | theorem (in the model, on a snapshot) |
|---|---|
| `parseModName string : Option Name` | |
| `readFiles sp m level : μ (Except CheckError ModFiles)` | `readFiles_ok`, `readFiles_of_all` |
| `readView sp m level : μ (Except CheckError ModDecoded)` | `readView_of_all` |
| `readAllViews sp m : μ (Except CheckError (AllViews × Array Expo))` | |
| `moduleImports sp m : μ (Except CheckError (Array ImportRec))` | `moduleImports_of_view` |

**The import closure.**

| name | theorem |
|---|---|
| `closureOrder sp roots : μ (Except CheckError (Array Name))` | `closureOrder_ok`: holds the roots, each module after its imports |
| `loadClosure sp roots jobs : μ (Except CheckError (Array Loaded))` | through `readOleans_ok` |
| `mergeAll ls : Except CheckError Merged` | `mergeAll_ok`: every constant stands in the merge |
| `emitAll mg rs : Emit`, `declsOf em` | `emitAll_spec`, `declsOf_thm`, `declsOf_from` |
| `readOleans sp roots constants jobs : μ (Except (CheckError × Nat) (Array Declaration))` | `readOleans_ok`, `readOleans_thm` |

Here `roots` are the modules the closure starts from, and `constants` the constants the
records start from (`none`: every constant of the closure), as lean4export's arguments after
`--` do.

Where a view parses, the other reads succeed and return their part of it.  Not the
converse, on purpose: a read looks only at what it needs, and a reader may rely on a
file only through a full parse of it.
-/
