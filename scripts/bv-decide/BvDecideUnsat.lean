/-
The `bv_decide` stream of `scripts/bv-decide-check.sh` (task #368): one
theorem proved by `bv_decide`, and one that uses its native axiom
directly.  Compiled and exported with the checker's own toolchain; the
stream (about 80 MB: it carries Std's LRAT checker and its soundness
proofs) is not committed.
-/
import Std.Tactic.BVDecide

theorem bvAndOr (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by bv_decide

theorem bvLeak :
    Std.Tactic.BVDecide.Reflect.verifyBVExpr bvAndOr._expr_def_1_1 bvAndOr._cert_def_1_1 = true :=
  bvAndOr._native.bv_decide.ax_1_5
