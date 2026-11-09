module

public import ConLeche.Kernel.Expr
public import Std.Data.HashSet
/- The `#guard`s are EVALUATED, so the module is needed at the meta level
too; the evaluation calls the vendored C through the precompiled
`ConLecheNative` library. -/
meta import ConLeche.Kernel.Expr
meta import Std.Data.HashSet

public section

/-!
# The literal hash

`natHash` is lean4#16146's `Literal.natHash` (fixes lean4#15686): the
number itself below `2^64`, all its 64-bit words mixed with `mixHash`
above.  The checks are the PR's own test (`tests/elab/issue15686.lean`)
on our hash, plus its value on a few words.
-/

namespace ConLecheTests.LitHash

open ConLeche

-- `65536 ^ i` is a multiple of `2^64` for `i ≥ 4`: 4000 different hashes.
#guard (Std.HashSet.ofList ((List.range 4000).map fun i =>
  (Expr.lit (.natVal (65536 ^ i))).hash)).size == 4000

-- Below `2^64`, the hash is the number itself, also for numbers that are not scalars.
#guard natHash 12345 == 12345
#guard natHash (2^63) == (2^63 : Nat).toUInt64
#guard natHash (2^64 - 1) == (2^64 - 1 : Nat).toUInt64
#guard natHash (2^64) != natHash (2^65)

-- Above, the words `w₀, w₁, …` least significant first, folded with `mixHash`.
#guard natHash (2^64) == mixHash 0 1
#guard natHash (3 * 2^128 + 2 * 2^64 + 1) == mixHash (mixHash 1 2) 3

-- The numbers the e2e fixture `lit_hash_low_bits` builds, `k * 2^64 - 1`: all
-- different.
#guard (Std.HashSet.ofList ((List.range 1000).map fun k =>
  natHash ((k + 2) * 2^64 - 1))).size == 1000

-- Strings hash all their bytes.
#guard Literal.hash (.strVal "ab") != Literal.hash (.strVal "ba")

end ConLecheTests.LitHash
