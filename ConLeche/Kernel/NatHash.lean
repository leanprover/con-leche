module

@[expose] public section

/-!
# The hash of a big `Nat` literal: the one native function

`natBigHash n` mixes all 64-bit words of `n` with Lean's `mixHash`
(`native/nat_hash.c`).  It is VENDORED FROM lean4#16146 (which fixes
lean4#15686): the C of that PR's `Literal.natHash`, under upstream's own
symbol `lean_nat_big_hash`.  The v4.35.0 runtime does not export it; a
toolchain that ships lean4#16146 does, and then the link fails on the
duplicate definition.  That failure is the reminder to delete this
module and `native/nat_hash.c` and to hash literals with the
toolchain's `Literal.natHash`.

Why C (task #547, the maintainer's one deliberate exception to "no C"):
`Hashable Nat` is `n mod 2^64`, so literals that agree in their low 64
bits — all multiples of `2^64` (lean4#15686), the packed matrices of
CFSG's certificate computations (DESIGN #543) — shared one hash, and
every memo lookup among them walked one bucket.  A hash that reads every
word is one linear pass in C; Lean has no word access to a big `Nat`,
and reading the words with `% 2^64` and `>>> 64` costs a copy per word,
quadratic in the literal's size.

To the proofs `natBigHash` is an opaque function of the number: equal
literals have equal hashes whatever it computes, which is all a
`LawfulHashable` instance asks.  It is its own library (`ConLecheNative`
in `lakefile.lean`), compiled to native code, so that the interpreter
(elaboration-time code and the test library's `#eval`s) can call it too.
-/

namespace ConLeche

/-- **The hash of a `Nat` reading all its bits** (`native/nat_hash.c`,
vendored from lean4#16146; remove once the toolchain provides
`Literal.natHash`): all 64-bit words of a big number mixed.  Only for
`n ≥ 2^64`, which is an mpz object, as upstream's `lean_nat_big_hash`
(`natHash` in `Kernel/Expr.lean` answers below). -/
@[extern "lean_nat_big_hash"]
opaque natBigHash (n : @& Nat) : UInt64

end ConLeche
