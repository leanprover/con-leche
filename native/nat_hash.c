/*
 * The hash of a big `Nat` literal (`natBigHash`, ConLeche/Kernel/NatHash.lean),
 * VENDORED FROM lean4#16146 (fixes lean4#15686): that PR's `hash_digits` and
 * `lean_nat_big_hash`, under upstream's own symbol and signature.  The v4.35.0
 * runtime does not export `lean_nat_big_hash`; a toolchain that ships
 * lean4#16146 does, and then the link fails on the duplicate definition.  That
 * failure is the reminder: delete this file and `Kernel/NatHash.lean`, and
 * hash literals with the toolchain's `Literal.natHash`.
 *
 * The value: a number `n` with 64-bit words `w0, ..., wk` (`wk != 0`, least
 * significant first) hashes to `w0` if `k = 0` and to
 * `mix(... mix(mix(w0, w1), w2) ..., wk)` otherwise, `mix` being the runtime's
 * `lean_uint64_mix_hash` (Lean's `mixHash`).  So a number below 2^64 hashes to
 * itself.  As upstream's, the function takes a big `Nat` only (an mpz object);
 * the Lean side (`natHash`, ConLeche/Kernel/Expr.lean) answers below 2^64
 * itself and calls this for nothing smaller.
 *
 * PLATFORM ASSUMPTIONS, checked at compile time where C can check them:
 *   - a 64-bit platform (`size_t`, pointers and GMP limbs of 64 bits): the
 *     toolchains con-leche builds with;
 *   - the runtime is built with GMP (the `.olean` reader refuses non-GMP
 *     bignums, `ConLeche/Frontend/Olean/Region.lean`), so a big `Nat` is an
 *     `mpz_object` (`src/runtime/object.h`): the object header, then GMP's
 *     `__mpz_struct` (`int _mp_alloc`, `int _mp_size`, `mp_limb_t *_mp_d`).
 *     The struct below restates that layout, since the toolchain ships no
 *     `gmp.h`; it is the layout the `.olean` compactor writes and our reader
 *     reads (`Region.mpzAt`).  A `Nat` is not negative, so `_mp_size` is the
 *     number of limbs; GMP keeps the top limb non-zero, and the loop strips
 *     zero top words all the same, as upstream does.
 */
#include <lean/lean.h>
#include <stdint.h>

_Static_assert(sizeof(size_t) == 8, "nat_hash.c needs a 64-bit platform");
_Static_assert(sizeof(void *) == 8, "nat_hash.c needs 64-bit pointers");

typedef struct {
    lean_object m_header;
    int         m_alloc;
    int         m_size;
    uint64_t *  m_limbs;
} conleche_mpz_object;

uint64_t lean_nat_big_hash(b_lean_obj_arg a) {
    conleche_mpz_object const * o = (conleche_mpz_object const *)a;
    uint64_t const * ds = o->m_limbs;
    size_t sz = o->m_size < 0 ? (size_t)(-(int64_t)o->m_size) : (size_t)o->m_size;
    while (sz > 0 && ds[sz - 1] == 0) sz--;
    uint64_t h = 0;
    for (size_t i = 0; i < sz; i++)
        h = i == 0 ? ds[i] : lean_uint64_mix_hash(h, ds[i]);
    return h;
}
