module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The recursor stage as CHECKING, at k members (milestone M5)

The one-member route GENERATES the recursor and its rules and compares
them with the stream's (`checkNativeRec`/`nativeRulesOk`,
now the reject-only conformance check in `ConLeche/Conformance/`).  At k members that
comparison decides nothing useful, and — the maintainer's ruling of
2026-09-21 — **the check must not know about motives at all**: a
motive is a parameter like any other, and the family is simply the
recursors that arrive in the group.  So the uniform route CHECKS, and
what it checks is a SHAPE:

```
rec_m : ∀ (p⃗ : the block's parameter domains)        -- binders 0 … nP-1
          (x⃗ : ANYTHING)                             -- binders nP … rP-1
          (ı⃗ : the member's indices)                 -- binders rP … mI-1
          (t : T_m p⃗ ı⃗),                             -- binder mI, the MAJOR
        <anything>                                    -- the conclusion
```

`rP` and `mI` are READ OFF THE RECORD (`RecShape.rP`/`mI`,
`BlockShape.rulePrefixAt`/`majorIdxAt`); the stretch official fills
with the motives and the minor premises is never looked inside; the
major assigns the recursor to its member; and **the stored type is the
STREAM's own**, checked as a constant's type and nothing more.

* the ELIMINATION guard is official's `elim_only_at_universe_zero`
  said declaratively (`blockLargeElimAllowed`): unless the block's
  sort is never `0`, a large eliminator needs the generated large
  SHAPE (a fresh elimination level parameter, `BlockShape.large`), ONE
  member, no container occurrence and at most one constructor — and
  when it is not allowed, the recursor's CONCLUSION must be a
  proposition, which is the same statement once the conclusion is
  arbitrary.  The `large` conjunct is what keys the guard to the
  eliminator the stream DECLARES rather than to the block alone; see
  `blockLargeElimAllowed`'s own docstring for the witness that made it;
* every RULE binds `rP + nF` variables — the recursor's own prefix and
  the constructor's fields — whose domains are compared BINDER BY
  BINDER with the opened stored type and the constructor's telescope;
* its body goes through **the primitive-recursion abstraction**
  (`abstractIh`): every occurrence of a block recursor must head a
  maximal spine `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)` of `mI_{c'} + 1`
  arguments, where `x⃗` is the rule's OWN prefix (all `rP` of them, as
  bound variables lifted by the binders crossed — primitive recursion
  fixes the frame, and a call at another frame would name a different
  recursion instance), `f_i` a field of THIS constructor whose kind
  names the member `rec_{c'}` eliminates, and `e⃗` SYNTACTICALLY the
  field's index expressions at `a⃗`.  The spine is replaced by the
  opener of the (field, callee) pair applied to `a⃗`, whose
  opener's type is `rec_{c'}`'s own type INSTANTIATED at exactly those
  arguments under `∀ a⃗`; any other occurrence of a block recursor — a
  partial spine, a recursor passed as an argument, a call on something
  that is not a field of this constructor — is INVALID.
* the residue is TYPED at the CONSTRUCTORS' environment, under the
  opened frame `x⃗ f⃗ ih⃗`, against `rec_m`'s own conclusion
  instantiated at `x⃗`, at the constructor's index expressions and at
  the major `C_J p⃗ f⃗`.

Official's `minor f⃗ ih⃗` bodies satisfy every requirement, so no
official recursor is lost.  What is gained is every mutual block, and
a documented ACCEPT-SUPERSET: a rule body that is typed but is not the
generated term.

Nothing of the abstracted body is STORED: the stored rule carries the
ANNOTATED STREAM right-hand side (`ConLeche/Kernel/Inductives/SumInstall.lean`'s
`sumRules`), and the abstraction is the model's reading of it.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-! ## The frames

A rule of `rec_m` binds `rP` prefix variables and then the
constructor's `nF` fields, so under `d` further binders inside its
body

* `x_l` (`l < rP`) is `bvar (d + nF + rP - 1 - l)`,
* `f_i` is `bvar (d + nF - 1 - i)`.

A field's own data (its telescope and its index expressions) is
spelled at the CONSTRUCTOR's frame — the `nP` parameters, then the `i`
earlier fields — so moving it to a rule's frame lifts the earlier
fields to all `nF` of them and the parameters past the `rP - nP`
binders that stand between them and the fields: that is
`structIdxAt nF (rP - nP) i l m` and `structTeleAt nF (rP - nP) i l`
(`ConLeche/Kernel/Inductives/FieldTele.lean`). -/

/-- **The rule's own prefix variables**, in order, as seen from under
the `nF` fields and `d` further binders. -/
def blockRulePrefixVars (rP nF d : Nat) : List Expr :=
  (List.range rP).map fun l => Expr.bvar (d + nF + rP - 1 - l)

/-- **The inductive hypothesis' guarded call**, as a `∀`-telescope over
the field's own telescope so that it can be instantiated at the
spine's actual arguments: `∀ a⃗, rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)`, spelled
at a rule body's frame under the `nF` fields and `d` further
binders. -/
def blockIhSpinePis (recName : Name) (rlvls : List Level) (pw : PropWhen)
    (nP rP nF i d : Nat) (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr :=
  let m := tele.length
  Expr.mkPisOf (structTeleAt nF (rP - nP) i d pw tele)
    (Expr.mkAppN (.const recName rlvls)
      (blockRulePrefixVars rP nF (d + m) ++ idx.map (structIdxAt nF (rP - nP) i d m) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + d + m)) (structTeleVars m)]))

/-- **The `ih` binders of a rule's frame**, one per (recursive FIELD,
CALLEE recursor) key (`blockIhKeys`): `∀ a⃗, <rec_c's own conclusion at
the rule's prefix, at the field's index expressions and at `f_i a⃗`>`.
The conclusion is THAT CALLEE's STORED type instantiated at exactly the
arguments the guarded call carries, which is what makes `ih_{(i,c)} a⃗`
and the call interchangeable — the ruling of 2026-09-21: the family is
primitively MUTUALLY recursive, so a rule may call ANY recursor of the
group on a field, and each call gets its own opener typed from its own
callee.  `recTyOf` is the stored type of a RECURSOR; `none` when one of
them does not have the binders the instantiation needs. -/
def blockIhPis (nP rP nF : Nat) (pw : PropWhen) (recTyOf : Nat → Expr)
    (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) :
    List (Nat × Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (i, c) :: is, l, body =>
    let m := (teleOf i).length
    let o := rP - nP
    match Expr.instPisAtLift
        (blockRulePrefixVars rP nF (l + m) ++ (idxOf i).map (structIdxAt nF o i l m) ++
          [Expr.mkAppN (.bvar (nF - 1 - i + l + m)) (structTeleVars m)])
        (recTyOf c) with
    | none => none
    | some concl =>
      (blockIhPis nP rP nF pw recTyOf teleOf idxOf is (l + 1) body).map fun rest =>
        .forallE (Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i)) concl) rest ⟨pw⟩

/-! ## The elimination restriction, declaratively -/

/-- **A container occurrence anywhere in the block.**  Official's
`elim_only_at_universe_zero` is evaluated on the AUX block, so a
nested block counts as several types there; this is the bit that says
so.  The classification declines a block with one today
(`classifyMemberKinds`), so it is `false` for every block that
reaches the route — it is named because the nested rung sets it. -/
def blockNested (kinds : List (List (List BlockFieldKind))) : Bool :=
  kinds.any fun kss => kss.any fun ks => ks.any (· == .unsupported)

/-- **When a large eliminator is allowed**, official's
`elim_only_at_universe_zero` said declaratively: always when the
block's sort is never `0`; otherwise only for ONE member with no
container occurrence and at most one constructor — and at one
constructor the per-field subsingleton criterion, which the
CONSTRUCTORS' stage has already applied (`checkStructFieldSortsI`'s
`large` arm).  When this is `false` the recursor's conclusion must be
a proposition.

**Why `p.large` is a CONJUNCT of the second disjunct** (lane SEC1, the
falsifier's witness of 2026-09-22).  The route CHECKS the recursor
instead of generating it, so the two halves of official's criterion
are split: this one is keyed on the block's counts, while the per-field
subsingleton half runs in the constructors' stage under `p.isProp &&
p.large` — and `BlockShape.large` is a LEVEL-PARAMETER SHAPE ("a fresh
elimination level parameter in front"), not a property of the
elimination.  A MONOMORPHIC large motive (`{motive : ∀ n, T n → Type}`,
which needs no level parameter) therefore has `large = false`, so the
per-field half did not run at all, and this guard — had it kept letting
a one-member, one-constructor `Prop` block through unconditionally —
would not have asked for a propositional conclusion either.  Neither
half fired, and `Hidden : Nat → Prop | mk (n m : Nat) : Hidden (n+1)`
eliminated into `Type`: proof irrelevance collapses `mk 0 0` and
`mk 0 1` while the eliminator tells them apart, which is a proof of
`0 = 1` (fixture `corner_rec_mono_large_bad`).

With `p.large` required, a recursor that does NOT declare the generated
large shape must conclude in `Sort 0` — checked, not assumed, by the
`isDefEq` beside the call — so the one flag now implies the other:
`large = false` ⇒ the elimination level is provably `0`.  That is the
invariant the model's per-field clause (`CtorDataI.srcProp`, keyed on
the same `large`) needs to be about the blocks it is used at, and it is
what the fixpoint route gets for free by GENERATING the recursor
(`structElimLevel`, which is `Level.zero` at `large = false`).  Nothing
official emits is lost: official's own recursor for a large-eliminating
block always carries the fresh parameter. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  p.resSort.isNeverZero ||
    (p.large && p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

/-! ## The primitive-recursion abstraction -/

/-- **The member a field's kind names**, when the field has an
inductive hypothesis (`blockTgtsOf`'s answer as an `Option`: a field
with no hypothesis has no target, rather than the placeholder `0`). -/
def BlockFieldKind.tgt? : BlockFieldKind → Option Nat
  | .recursive t => some t
  | .reflexive t => some t
  | _ => none

/-- The position of a name in a list (`none` when absent). -/
def nameIdxOf? (names : List Name) (n : Name) : Option Nat :=
  (List.range names.length).find? fun i => names.getD i default == n

/-- The position of a pair in a list (`none` when absent) — the `ih`
binder a (field, callee) key owns. -/
def pairIdxOf? (ps : List (Nat × Nat)) (p : Nat × Nat) : Option Nat :=
  (List.range ps.length).find? fun i => ps.getD i (0, 0) == p

end ConLeche
