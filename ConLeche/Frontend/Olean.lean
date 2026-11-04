module

public import ConLeche.Frontend.Olean.Records

@[expose] public section

/-!
# Reading `.olean` files: the public interface

**Import this module.**  Outside `ConLeche/Frontend/Olean/` and its proofs
`ConLeche/Verify/Frontend/Olean/`, nothing imports the tree's other modules
(`tests/layering.sh`).  The names below are the interface; everything else the
tree declares (`moduleSkel`, `runPasses`, `sGo`, `parsePart`, `locateHits`,
`readImportsAt`, `mergeAll`, `emitAll`, ...) is public only because checker code
is exposed and its proofs unfold it: a definition an exposed definition mentions
cannot be `private`.  It is not an interface, and may change at will.

**Bytes and regions.**

| name | |
|---|---|
| `Part.ofBytes path bytes : Except CheckError Part` | one file's header validated: nothing else about it is trusted or looked at yet |
| `Region.single part`, `Region.ofParts #[ex, s, p]` | the address space of one file, or of a module's three |
| `Part.root part` | the root pointer the reads start from |

**The full parse**, and the reads that take less of the same region and root.

| name | theorem (`ConLeche/Verify/Frontend/Olean/`) |
|---|---|
| `parseFull r root : Option ModDecoded` | `parseFull_eq_spec`: is `decodeModuleSpec`, the definition of what a valid module is; `parseFull_some` |
| `readNamePositions r root : Option NamePositions` | `readNamePositions_of_full` |
| `readEntry r c : Option (CEntryF Name Expr)` | `readEntry_eq`, `readEntry_of_full` |
| `readStmts r cs : Option (List ConstantVal)` | `readStmts_eq`, `readStmts_of_full` |
| `importsPre bytes : Option (Array ImportRec)`, on a prefix of the file | `importsPre_extract`, `importsPre_prefix` |

**A module's parts**, which validate them against each other.

| name | theorem |
|---|---|
| `parseExported m ex : Except CheckError ModDecoded` | `parseExported_full` |
| `parseModule m er ex s p : Except CheckError ModRead` | `parseModule_full` |

**Through the IO class** (`CheckerIO`), by module name along a search path.

| name | theorem (in the model, on a snapshot) |
|---|---|
| `parseModName string : Option Name` | |
| `findModule sp m : μ (Except CheckError Located)` | `findModule_ok` |
| `readPart path : μ (Except CheckError Part)` | `readPart_ok`, `readPart_det` |
| `readExportedPart sp m : μ (Except CheckError Part)` | `readExportedPart_of_home` |
| `moduleImports sp m : μ (Except CheckError (Array ImportRec))` | `moduleImports_of_home` |
| `readModule sp m : μ (Except CheckError ModRead)` | `readModule_ok`, `home_exported` |

**The import closure.**

| name | theorem |
|---|---|
| `closureOrder sp roots : μ (Except CheckError (Array Name))` | none of its own |
| `loadClosure sp roots jobs : μ (Except CheckError (Array Loaded))` | none of its own |
| `readOleans sp roots jobs : μ (Except (CheckError × Nat) (Array Declaration))` | `readOleans_ok` |

A theorem above says where a full parse succeeds, the other reads succeed and
return their part of it.  Not the converse, on purpose: a read looks only at what
it needs, and a reader may rely on a file only through a full parse of it.
-/
