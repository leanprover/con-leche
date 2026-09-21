module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The recursor stage as CHECKING, at k members (milestone M5)

The one-member route GENERATES the recursor and its rules and compares
them with the stream's (`checkNativeRec`/`nativeRulesOk`,
`ConLeche/Kernel/Inductives/NativeInstall.lean`).  At k members that
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
  sort is never `0`, a large eliminator needs ONE member, no container
  occurrence and at most one constructor — and when it is not allowed,
  the recursor's CONCLUSION must be a proposition, which is the same
  statement once the conclusion is arbitrary;
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
(`ConLeche/Kernel/Inductives/NativeParts.lean`). -/

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
a proposition. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  p.resSort.isNeverZero ||
    (p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

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

/-- **The `ih` openers a rule's frame carries**, in order: for every
recursive FIELD of the constructor, one per RECURSOR of the block that
can be called on it — one whose MAJOR names the field's target member
and whose rule prefix is this rule's own, which is what makes the
spine's argument count come out.  A family with one recursor per member
gives exactly one opener per recursive field, which is official's shape
and the shape the one-member route has always had. -/
def blockIhKeys (rP : Nat) (rPs recTgts : List Nat) (ks : List BlockFieldKind) :
    List (Nat × Nat) :=
  (blockRecIdxOf ks).flatMap fun i =>
    (List.range recTgts.length).filterMap fun c =>
      if (ks.getD i .ordinary).tgt? == some (recTgts.getD c recTgts.length) &&
          rPs.getD c 0 == rP then some (i, c) else none

/-- **The data one rule's abstraction walks against**: the block's
recursor names and their shared level arguments, every member's
argument sums, the frame's widths, the constructor's field kinds,
telescopes and index expressions, and the recursive positions (the
`ih` binders, in order). -/
structure BlockRuleFrame where
  /-- the block's recursor names, in the record's recursor order -/
  recNames : List Name
  /-- the level arguments every recursive call carries -/
  rlvls : List Level
  /-- every RECURSOR's major-premise index, in recursor order -/
  mIs : List Nat
  /-- every RECURSOR's rule prefix, in recursor order -/
  rPs : List Nat
  /-- every RECURSOR's target member, in recursor order -/
  recTgts : List Nat
  /-- the block's parameter count -/
  nP : Nat
  /-- THIS rule's recursor's rule prefix -/
  rP : Nat
  /-- this constructor's field count -/
  nF : Nat
  /-- this constructor's field kinds -/
  ks : List BlockFieldKind
  /-- field `i`'s own telescope -/
  teleOf : Nat → List (Expr × BinderMeta)
  /-- field `i`'s index expressions -/
  idxOf : Nat → List Expr
  /-- the `ih` binders, in order: one per (recursive field, callee
  recursor) key (`blockIhKeys`) -/
  ihKeys : List (Nat × Nat)
  /-- the block's elimination datum -/
  pw : PropWhen

/-- The number of `ih` binders the rule's frame carries. -/
def BlockRuleFrame.nR (fr : BlockRuleFrame) : Nat := fr.ihKeys.length

/-- **A guarded recursive call**, read at a rule body's frame under
`d` binders: the node must be

    rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)

with `rec_{c'}` a block recursor at the block's own level arguments,
`x⃗` the rule's OWN `rP` prefix variables (which forces `rec_{c'}` to
carry the same prefix), `f_i` a field of THIS constructor whose kind
names the member `rec_{c'}` eliminates, `a⃗` as many arguments as the field's
telescope has binders and free of any block recursor, and the whole
spine SYNTACTICALLY the generated call at those arguments (`blockIhSpinePis` instantiated at
`a⃗`, compared at the parse placeholder's binder data).  The answer is
the position of the (field, callee) key among the frame's openers —
the `ih` binder that replaces the call — together with `a⃗`. -/
def blockIhCall? (fr : BlockRuleFrame) (d : Nat) (e : Expr) : Option (Nat × List Expr) :=
  match e.getAppFn with
  | .const r us =>
    match nameIdxOf? fr.recNames r with
    | none => none
    | some c' =>
      if us != fr.rlvls then none else
      if fr.rPs.getD c' 0 != fr.rP then none else
      let args := e.getAppArgs
      let mI := fr.mIs.getD c' 0
      if args.length != mI + 1 then none else
      match args[mI]? with
      | none => none
      | some maj =>
        match maj.getAppFn with
        | .bvar b =>
          if !(decide (d ≤ b) && decide (b < d + fr.nF)) then none else
          let i := d + fr.nF - 1 - b
          -- the field's kind names the member the CALLEE eliminates
          if (fr.ks.getD i .ordinary).tgt? !=
              some (fr.recTgts.getD c' fr.recTgts.length) then none else
          let as := maj.getAppArgs
          let tele := fr.teleOf i
          if as.length != tele.length then none else
          if as.any (fun a => a.mentionsAnyConst fr.recNames) then none else
          -- `instPisAtLift`, not `instPisAt`: the call's arguments are
          -- terms of the RULE BODY's frame and may mention its binders,
          -- so the substitution has to lift them past the telescope
          -- binders it crosses (`instantiate1` requires a `bvar`-closed
          -- replacement and would capture)
          match Expr.instPisAtLift as
              (blockIhSpinePis r fr.rlvls fr.pw fr.nP fr.rP fr.nF i d tele (fr.idxOf i)) with
          | none => none
          | some expected =>
            if Expr.resetMeta e != Expr.resetMeta expected then none
            else match pairIdxOf? fr.ihKeys (i, c') with
              | none => none
              | some rpos => some (rpos, as)
        | _ => none
  | _ => none

/-- **The abstraction itself**: `body` at the frame `x⃗ f⃗`, under `d`
binders, rewritten to the frame `x⃗ f⃗ ih⃗` — every guarded recursive
call replaced by `ih_r a⃗`, every other variable shifted past the `nR`
new binders — or `none` when the body mentions a block recursor
anywhere else.

The walk is structural: a guarded call is recognised and consumed at
the `.app` node that heads it, and any recursor occurrence that is not
consumed there is reached as a bare `.const` leaf and refused.  The
call's arguments `a⃗` are required to be free of block recursors (they
are the inductive hypothesis' own arguments; official's are the
telescope's variables), which is what makes the walk structural — on a
recursor-free term the walk IS `liftLooseBVars nR d`. -/
def abstractIh (fr : BlockRuleFrame) : Nat → Expr → Option Expr
  | d, .bvar j => some (if j < d then .bvar j else .bvar (j + fr.nR))
  | _, .sort u => some (.sort u)
  | _, .lit l => some (.lit l)
  | _, .const n us => if fr.recNames.contains n then none else some (.const n us)
  | _, .fvar _ _ => none
  | d, .lam ty b bi =>
    (abstractIh fr d ty).bind fun ty' =>
      (abstractIh fr (d + 1) b).map fun b' => .lam ty' b' bi
  | d, .forallE ty b bi =>
    (abstractIh fr d ty).bind fun ty' =>
      (abstractIh fr (d + 1) b).map fun b' => .forallE ty' b' bi
  | d, .letE ty v b =>
    (abstractIh fr d ty).bind fun ty' =>
      (abstractIh fr d v).bind fun v' =>
        (abstractIh fr (d + 1) b).map fun b' => .letE ty' v' b'
  | d, .proj s i e =>
    if fr.recNames.contains s then none
    else (abstractIh fr d e).map fun e' => .proj s i e'
  | d, .app f a =>
    match blockIhCall? fr d (.app f a) with
    | some (rpos, as) =>
      some (Expr.mkAppN (.bvar (d + fr.nR - 1 - rpos))
        (as.map fun x => x.liftLooseBVars fr.nR d))
    | none =>
      (abstractIh fr d f).bind fun f' =>
        (abstractIh fr d a).map fun a' => .app f' a'

end ConLeche
