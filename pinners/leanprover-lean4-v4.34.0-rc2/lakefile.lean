import Lake

open System Lake DSL

-- A PINNER (task #275): the Lake project that regenerates ONE committed
-- pin dump, on the toolchain that dump describes.
--
--     cd pinners/<toolchain> && lake exe natop-pins-export ../../pins
--
-- The toolchain is `lean-toolchain` beside this file — elan reads it,
-- so `lake` here runs the Lean this dump is a dump of, and the
-- generator reads the same file to label the dump
-- (`ConLeche.PinGen.readToolchainString`).  See `pinners/README.md`.
--
-- WHAT IS SHARED, AND WHY IT CAN BE.  Nothing is copied: both targets
-- take their sources from the repository root with `srcDir = "../.."`,
-- so there is exactly ONE copy of the generator in the tree — the one
-- the repository's own `lake exe natop-pins-export` builds.  The cone
-- reached from `PinDump` is
--
--     PinDump                                the executable root
--     ConLeche.PinGen{,.Dump,.Prelude}       the generator
--     ConLeche.PinGen.Certs                  the certificate theorems
--     ConLeche.Kernel.{Name,PropWhen,Expr}   the checker's Expr datatypes
--     ConLeche.Kernel.NatHash                the literal hash (its C below)
--
-- — and the last two lines are the reason the generator is not free-standing:
-- a dump is an encoding of `ConLeche.Expr`, so the generator builds the
-- checker's expression datatypes.  Those three files, and the five
-- above them, are written in the subset every toolchain accepts;
-- that claim is not a hope, it is what this project's cold build
-- checks, on every toolchain, in `tests/pindump.sh` and in CI.
--
-- IF A TOOLCHAIN CANNOT SHARE A FILE, fork it — but note HOW, because
-- the obvious way silently does nothing (measured, task #275).  Lake
-- resolves a module through the first library whose ROOTS COVER it, and
-- listing a `srcDir = "."` library first does NOT shadow a covering
-- library that comes later: the shared copy still wins and the fork is
-- dead code.  So a fork means narrowing the coverage:
--
--   1. replace `roots = ["ConLeche"]` below with the explicit cone —
--      the `ConLeche.*` modules listed above — MINUS the module
--      being forked;
--   2. add a `lean_lib` with `srcDir = "."` whose root IS that module;
--   3. put the fixed copy in THIS directory under its module path (say
--      `ConLeche/PinGen/Certs.lean`) and say at its top why it is
--      forked and how it differs.
--
-- No fork exists today, which is why the root stays the whole
-- `ConLeche` hierarchy: any module the cone grows into then resolves
-- without editing this file.  `lake build` here builds the executable
-- and nothing else, so that root is never built as a library.

package pinner

lean_lib ConLecheShared where
  srcDir := "../.."
  roots := #[`ConLeche]

@[default_target]
lean_exe «natop-pins-export» where
  srcDir := "../.."
  root := `PinDump

-- THE LITERAL HASH'S C (task #547).  `ConLeche.Kernel.Expr` hashes a big
-- `Nat` literal with `natBigHash`, the C of lean4#16146 vendored as
-- `native/nat_hash.c` (see the root `lakefile.lean`), so the executable
-- links it: compiled by the toolchain's own C compiler, linked as a static
-- library through the module's own library, declared last so that it owns
-- the module.  This is why a pinner is a `lakefile.lean`: a custom target
-- needs code.  Once the toolchains have lean4#16146, the section goes with
-- the root's.
target nat_hash.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "nat_hash.o"
  let srcJob ← inputTextFile <| pkg.dir / ".." / ".." / "native" / "nat_hash.c"
  buildLeanO oFile srcJob #[] #["-fPIC", "-O3"]

target libconleche_native pkg : FilePath := do
  let o ← fetch <| pkg.target ``nat_hash.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "conleche_native") #[o]

lean_lib ConLecheNative where
  srcDir := "../.."
  roots := #[`ConLeche.Kernel.NatHash]
  moreLinkObjs := #[libconleche_native]
