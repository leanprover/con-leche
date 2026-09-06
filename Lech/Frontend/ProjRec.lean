import Lech.Kernel.Direct.Parts
import Lech.Kernel.Level

/-!
# Projection functions of non-direct structure-likes, as recursor
# applications (the frontend rewrite, 2026-09-06)

The elaborator spells a structure's projection functions with the
kernel's primitive projection node:

    def T.f : ∀ p⃗ (self : T p⃗), F_i[f_j := T.f_j p⃗ self]   -- the type
      := fun p⃗ (self : T p⃗) => .proj T i self               -- the value

(`hints := abbrev`; parent projections `T.toParent` have the same
shape.)  The official kernel types `.proj T i` on every *structure-like*
type — one constructor, zero indices, whatever the block's recursion:
a member of a mutual block, a recursive structure, a nested one.  This
checker serves `.proj` only on the class its direct install recognises
(`directParts?`: single type, non-recursive, non-nested — task #175 W5,
".proj on anything else declines"), so on the Mathlib stream the first
such projection function declines the run
(`Lean.Meta.Grind.AC.DiseqCnstr.lhs`, `DiseqCnstr` a mutual member).

**The user's design (2026-09-06, verbatim): "replace these projection
functions, only for mutual (not direct) inductives, by recursor
applications, before installation.  Completely transparent to the
verified code."**  This module is that rewrite, a pure function on the
parsed declaration:

    fun p⃗ (self : T p⃗) =>
      T.rec.{ℓ, u⃗} p⃗ motive_1 … motive_m minor_1 … minor_k self

* the motive for `T` itself is `fun (t : T p⃗) => R`, `R` the
  projection's own declared codomain (its earlier-field references
  are the already-installed earlier projection functions `T.f_j p⃗
  self`, which precede in the stream);
* every other motive of the block (the other mutual members, the
  nested containers' auxiliary motives) is the constant `PUnit.{ℓ}`
  at the same motive sort, over whatever binder telescope the
  recursor gives it (indices included);
* the minor premise for `T`'s constructor returns field `i` of its
  telescope (the inductive hypotheses recursion adds come after the
  fields and are ignored); every other minor returns `PUnit.unit.{ℓ}`;
* `ℓ`, the recursor's elimination level, is the sort of `R`.  The
  frontend has no type inference, and the level is not syntactic in
  `R`; it is read off the preprocessor's own artifact for the same
  field, `T._model.proj_i.iota : ∀ …, @Eq.{ℓ} α _ _` — the `Eq` level
  IS the field's sort (lean-inductive-models computes it with the
  elaborator's `getLevel`, over model types that match the public
  ones syntactically by the preprocessor contract).  No artifact, no
  rewrite: the declaration stays as it is and declines as before.

Every binder domain of the motives and minors is read off the
recursor's *own* type, instantiated step by step with the terms built
so far (`Expr.instantiate1Lift`, the open-argument substitution), so
the construction never guesses a telescope: whatever shape the
recursor has (mutual, reflexive, nested auxiliaries), the value is
built at exactly its binders.  The rewritten definition is then
checked by the ordinary definition path — type inferred, compared
against the declared type — and nothing in `Kernel/Core`, `Cached`,
`SetP` or `Verify` knows it happened.  Verdict semantics: a use of
`T.f` unfolds to the recursor form, and iota reduces it on a
constructor application exactly where `.proj` would reduce.

Excluded, deliberately: direct-shaped blocks (they keep their native
tower entries — `directPartsCore?` and non-recursiveness decide, the
recognizer's own verdict), propositional owners (`T : Prop` — their
recursor eliminates into `Prop` only, and the official `infer_proj`
restriction on such owners is a different question), and any block
whose recursor carries no elimination level parameter.
-/

namespace Lech.Frontend

/-- What the rewrite needs to know about one structure-like owner `T`
of a parsed inductive block that the direct install does not serve. -/
structure ProjRecOwner where
  /-- the type former -/
  T : Name
  /-- the block's level parameters (the owner's, the constructor's,
  and the recursor's after its elimination level) -/
  lps : List Name
  /-- parameter count -/
  nP : Nat
  /-- the single constructor -/
  ctor : Name
  /-- its field count -/
  nF : Nat
  /-- the owner's recursor `T.rec`: name, level parameters, type -/
  recName : Name
  recLps : List Name
  recType : Expr
  /-- the recursor's motive and minor counts (the export's own) -/
  numMotives : Nat
  numMinors : Nat
  deriving Repr, Inhabited

/-- The name of the preprocessor's constructor-reduction theorem for
field `i` of `T`: `T._model.proj_i.iota` (lean-inductive-models'
`Naming.projectionIotaName`). -/
def projIotaName (T : Name) (i : Nat) : Name :=
  ((T.str "_model").str s!"proj_{i}").str "iota"

/-- Is `n` of the shape `X._model.proj_i.iota`?  Cheap pre-filter for
the theorem records (the last component decides before anything is
compared). -/
def isProjIotaName : Name → Bool
  | .str (.str (.str _ "_model") s) "iota" => s.startsWith "proj_"
  | _ => false

/-- The `Eq` level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`:
the field's sort.  `none` on any other shape. -/
def projIotaLevel (ty : Expr) : Option Level :=
  match (ty.piResult.getAppFn) with
  | .const n [l] => if n == eqName then some l else none
  | _ => none

/-- Does the constant `n` occur in `e`?  (Not through fvar type
annotations — parsed declarations are fvar-free.) -/
def occursConst (n : Name) : Expr → Bool
  | .const m _ => m == n
  | .app f a => occursConst n f || occursConst n a
  | .lam _ ty b _ => occursConst n ty || occursConst n b
  | .forallE _ ty b _ => occursConst n ty || occursConst n b
  | .letE _ t v b => occursConst n t || occursConst n v || occursConst n b
  | .proj _ _ e => occursConst n e
  | _ => false

/-- The body under every leading `λ` (the projection shape's
pre-filter: the node under the value's binders). -/
def lamBody : Expr → Expr
  | .lam _ _ b _ => lamBody b
  | e => e

/-- Strip every leading `∀`: the binder list (outermost first) and the
body. -/
def stripPisAll : Expr → List (Name × Expr × BinderMeta) × Expr
  | .forallE n ty b m =>
    let (bs, e) := stripPisAll b
    ((n, ty, m) :: bs, e)
  | e => ([], e)

/-- Rebuild a `λ`-telescope over a binder list (outermost first). -/
def mkLams (bs : List (Name × Expr × BinderMeta)) (body : Expr) : Expr :=
  bs.foldr (fun (n, ty, m) acc => .lam n ty acc m) body

/-- Instantiate the leading `∀`-binders at *open* arguments (the
body-frame variables and the built motives/minors), one binder per
argument, returning the residual telescope. -/
def instPisOpen : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ body _, a :: as => instPisOpen (body.instantiate1Lift a) as
  | _, _ :: _ => none

/-- Peel `k` binders of a telescope, building one term per binder from
its (progressively instantiated) domain, and instantiating the
telescope with that term before the next binder is read. -/
def buildBinders (mk : Expr → Option Expr) :
    Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | k + 1, .forallE _ dom body _ => do
    let t ← mk dom
    let (ts, rest) ← buildBinders mk k (body.instantiate1Lift t)
    pure (t :: ts, rest)
  | _ + 1, _ => none

/-- Is `T` the head of the owner's own carrier: the motive domain
`∀ (t : T p⃗), Sort ℓ` (exactly one binder) or the major-premise
domain. -/
def headIs (T : Name) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n == T
  | _ => false

/-- **The rewrite.**  `ty`/`val` are the definition's declared type and
value, `i` the projected field, `ℓ` the field's sort (from the
artifact).  `none` = the value is not of the projection shape (the
caller keeps the declaration unchanged). -/
def projRecValue (o : ProjRecOwner) (ℓ : Level) (ty val : Expr) (i : Nat) :
    Option Expr := do
  let (lbs, body) ← val.stripLams (o.nP + 1)
  guard (body == .proj o.T i (.bvar 0))
  guard (i < o.nF)
  let (_, R) ← ty.stripPis (o.nP + 1)
  let us := o.lps.map Level.param
  -- the recursor's type at the chosen elimination level; the body
  -- frame is the value's own `nP + 1` binders: parameter `k` is
  -- `bvar (nP - k)`, the subject `bvar 0`
  let rty := o.recType.instantiateLevelParams o.recLps (ℓ :: us)
  let params := (List.range o.nP).map fun k => Expr.bvar (o.nP - k)
  let rty ← instPisOpen rty params
  -- motives: the owner's is `fun (t : T p⃗) => R` (R's parameter
  -- references skip the new binder; its subject reference IS the new
  -- binder); every other one is the constant `PUnit.{ℓ}` over its
  -- telescope
  let mkMotive : Expr → Option Expr := fun dom =>
    match stripPisAll dom with
    | ([(n, d, m)], .sort _) =>
      if headIs o.T d then some (.lam n d (R.liftLooseBVars 1 1) m)
      else some (.lam n d (.const punitName [ℓ]) m)
    | (bs, .sort _) => some (mkLams bs (.const punitName [ℓ]))
    | _ => none
  let (motives, rty) ← buildBinders mkMotive o.numMotives rty
  -- minors: the owner constructor's returns field `i` of its telescope
  -- (fields first, then the inductive hypotheses); every other one
  -- returns `PUnit.unit.{ℓ}`.  The owner's minor is the one whose
  -- codomain applies a motive to the owner constructor
  let mkMinor : Expr → Option Expr := fun dom =>
    let (bs, cod) := stripPisAll dom
    match cod.getAppArgs.getLast? with
    | some major =>
      if headIs o.ctor major then
        if i < bs.length then some (mkLams bs (.bvar (bs.length - 1 - i)))
        else none
      else some (mkLams bs (.const punitUnitName [ℓ]))
    | none => none
  let (minors, rty) ← buildBinders mkMinor o.numMinors rty
  -- the major premise: the owner has no indices, so the next binder is
  -- the subject itself
  match rty with
  | .forallE _ majDom _ _ =>
    guard (headIs o.T majDom)
    let app := Expr.mkAppN (.const o.recName (ℓ :: us))
      (params ++ motives ++ minors ++ [.bvar 0])
    pure (mkLams lbs app)
  | _ => none

/-- Which block members the rewrite serves: the officially
structure-like ones (one constructor, zero indices) of a block the
direct install does not recognise — `directPartsCore?` rejects it
(mutual, multi-constructor, indexed, shape mismatch) or it is
recursive (the export's `isRec`, or a block name occurring in a
constructor's binder domains: `directNonRec`'s verdict on a
well-formed stream).  Propositional owners and owners whose recursor
carries no elimination level parameter are left out.

`types` are `(name, levelParams, type, numParams, numIndices, ctors,
isRec)`, `ctors` `(name, numFields, type)`, `recs` `(name, levelParams,
type, numMotives, numMinors)` — the export record's own data. -/
def projRecOwners (block : List ConstantInfo)
    (types : List (Name × List Name × Expr × Nat × Nat × List Name × Bool))
    (ctors : List (Name × Nat × Expr))
    (recs : List (Name × List Name × Expr × Nat × Nat)) : List ProjRecOwner :=
  let blockNames := types.map (·.1)
  -- a block name in a constructor's binder *domains* (its result names
  -- the owner by definition)
  let recursive := types.any (·.2.2.2.2.2.2) ||
    ctors.any fun (_, _, cty) => (stripPisAll cty).1.any fun (_, d, _) =>
      blockNames.any fun n => occursConst n d
  if (directPartsCore? block).isSome && !recursive then []
  else
    types.filterMap fun (T, lps, tty, nP, nI, cs, _) => do
      let [C] := cs | none
      guard (nI == 0)
      let (_, .sort s) ← tty.stripPis nP | none
      guard (Level.isEquiv s .zero != some true)
      let (_, nF, _) ← ctors.find? (·.1 == C)
      let (rn, rlps, rty, nM, nm) ← recs.find? (·.1 == T.str "rec")
      guard (rlps.length == lps.length + 1)
      pure ⟨T, lps, nP, C, nF, rn, rlps, rty, nM, nm⟩

end Lech.Frontend
