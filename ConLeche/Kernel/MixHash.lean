module

@[expose] public section

/-!
# The 32-bit hash combinator of `Expr` nodes

`mixHash32 h k` is the block step of MurmurHash3_x86_32 (Austin Appleby,
public domain), with `k = ROTL32(k, 15)` replaced by `k ^= k >> 15`: the
arithmetic of lean4#16107's `lean_uint32_mix_hash`, copied operation for
operation.  The v4.36.0 toolchain does not have it; from v4.37 (first
v4.37.0-rc1) Init declares `mixHash32` with that C as a `static inline`
function in `lean.h`.

THE PLAN AT THAT BUMP: this module is deleted, and `Expr.data`
(`Kernel/Expr.lean`) uses Init's `mixHash32`, the same function.

Why Lean and not vendored C: Lean's generated C sees a vendored function only
through a prototype, so every combine would be an out-of-line call; these
`UInt32` operations compile to `lean.h`'s `static inline` arithmetic and are
inlined into `Expr.data`, the code v4.37's inline C gives (task #638).

Why it matters: with either argument fixed, `mixHash32` is a bijection in
the other (the `k` steps are an odd multiplication, a xorshift and another
odd multiplication; the `h` steps a xor, a rotation and `h * 5 + c`; each is
invertible on 32 bits).  `Expr.data` combines the 32-bit hashes of a node's
children with it, so on a chain `x ↦ C[x]` with a fixed context (an
accumulator `acc + 1`, a successor tower) the hash step is a bijection, and
the hashes repeat only by returning to the hash of the start, after about
2³¹ steps on average.  The 64-bit `mixHash` truncated to 32 bits loses
information in its second slot, and such a chain's hashes ran into a cycle
after about 82k steps; from there every memo lookup on a chain element
collided with an older one and the structural comparison walked the chain
(DESIGN #580, #634, #638).  The test library pins its values against
upstream's C (`ExprHashTests`).
-/

namespace ConLeche

/-- **The 32-bit hash combinator** (lean4#16107's `lean_uint32_mix_hash`; at
the bump to a toolchain that ships it, replaced by Init's `mixHash32`, see the
module header): bijective in each argument when the other is fixed. -/
@[inline] def mixHash32 (h k : UInt32) : UInt32 :=
  let k := k * 0xcc9e2d51
  let k := k ^^^ (k >>> 15)
  let k := k * 0x1b873593
  let h := h ^^^ k
  let h := (h <<< 13) ||| (h >>> 19)
  h * 5 + 0xe6546b64

end ConLeche
