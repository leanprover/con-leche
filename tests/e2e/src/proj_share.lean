/-
The projection-type SHARING fixture (the affine frontier, 2026-09-06;
DESIGN.md "The affine frontier").

`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen` (Mathlib record
181 570) killed the checker with an out-of-memory at 22 GB: the
executable `.proj` inference clause computed the field type through the
specification's `ProjEntry.typeAt`, whose `Expr.instantiateList` is an
unmemoized TREE walk that re-traverses every replacement — so the
subject and every parameter of the structure came back as a fresh tree
copy of a term that was a DAG.  The theorem's value is a 3 106-node DAG
with a 3.9 · 10⁸-node tree.

This file is that shape in miniature: `big% n` is the type
`Prod (Prod … ) (Prod …)` built as a DAG of `n + 1` nodes whose tree has
`2^(n+1) - 1` nodes (both children of every node are the SAME object;
lean4export hash-conses, so the stream carries `n + 1` records), and
`boxval% b` is a literal `Expr.proj Box 0 b` node — the elaborator
emits projection-function applications for `b.val`, and it is the raw
`.proj` node whose inference instantiates the field type.  The type of
`boxval% b` is the parameter `big% n`; a tree-copying instantiation
materializes 2^(n+1) nodes for it and then compares that copy against
the declared type node by node.  At n = 26 the copy alone is 134 M
nodes.  Official's `infer_proj` instantiates by pointer and accepts in
milliseconds; so does the fixed checker.

Expected verdict: accept (exit 0), both modes; the direct
simple-structure route installs `Box`.
-/
--#export unbox unbox2
import Lean
open Lean Elab Term

/-- `T 0 = Nat`, `T (n+1) = Prod (T n) (T n)` with the two children the
same `Expr` object. -/
def mkBig : Nat → Expr
  | 0 => mkConst ``Nat
  | n + 1 =>
    let t := mkBig n
    mkApp2 (mkConst ``Prod [.zero, .zero]) t t

elab "big%" n:num : term => return mkBig n.getNat

structure Box (α : Type) where
  val : α
  tag : Nat

/-- A raw `Expr.proj Box 0 b` node. -/
elab "boxval%" b:term : term => do
  let b ← elabTerm b none
  return mkProj ``Box 0 b

noncomputable def unbox (b : Box (big% 26)) : big% 26 := boxval% b

noncomputable def unbox2 (b : Box (Box (big% 26))) : big% 26 := boxval% (boxval% b)
