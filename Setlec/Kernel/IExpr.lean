import Std.Data.HashMap
import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level

/-!
# Interned (cons-hashed) expressions

An arena of expression nodes whose children are plain indices (`EIdx`),
together with a cons-table mapping each node to its index: structurally
equal terms receive the *same* index, so equality and hashing of interned
expressions are O(1) index operations (nanoda's `ExprPtr` design).

`EStore.intern` adds a single node (reusing an existing index when the
node is already present); `EStore.internExpr` interns a whole `Expr`
bottom-up.  The syntactic operations (`instantiate1I`, `abstract1I`,
`instantiateLevelParamsI`, and the pure queries) mirror the corresponding
`Setlec.Expr` operations exactly, but traverse the DAG with a per-call
memo table keyed by node index (plus the traversal cursor where there is
one), so shared subterms are visited once.

Verification (denotation into `Expr`, well-formedness of stores,
commutation of every operation with the denotation) lives in
`Setlec/Verify/IExpr.lean`; this module is implementation-only.
-/

namespace Setlec

/-- Index of an interned expression node in an `EStore` arena. -/
abbrev EIdx := Nat

/-- One interned expression node: the constructors of `Setlec.Expr` with
subexpressions replaced by arena indices.  Leaf data (names, levels,
binder metadata, literals) is carried unchanged. -/
inductive ENode where
  | bvar (i : Nat)
  | fvar (idx : Nat) (name : Name) (type : EIdx)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : EIdx)
  | lam (n : Name) (type body : EIdx) (m : BinderMeta)
  | forallE (n : Name) (type body : EIdx) (m : BinderMeta)
  | letE (n : Name) (type value body : EIdx)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : EIdx)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The interning arena: the node table (index = position) and the
cons-table sending every stored node to its index.  Invariant (stated
and maintained in `Setlec/Verify/IExpr.lean`): children of a node are
strictly smaller indices, and `cons` is exactly the graph of `nodes`. -/
structure EStore where
  nodes : Array ENode
  cons : Std.HashMap ENode EIdx

namespace EStore

/-- The empty arena. -/
def empty : EStore := ⟨#[], {}⟩

instance : Inhabited EStore := ⟨empty⟩

/-- Intern one node: the existing index when the node is already in the
cons-table, else the next fresh index (pushing the node and recording it).
The store is destructured before updating so the node table and the
cons-table are uniquely referenced during `push`/`insert` (avoiding
whole-table copies). -/
def intern (st : EStore) (n : ENode) : EIdx × EStore :=
  match st.cons[n]? with
  | some i => (i, st)
  | none =>
    match st with
    | ⟨nodes, cons⟩ =>
      let i := nodes.size
      (i, ⟨nodes.push n, cons.insert n i⟩)

/-- Intern a whole expression bottom-up. -/
def internExpr (st : EStore) : Expr → EIdx × EStore
  | .bvar i => st.intern (.bvar i)
  | .fvar idx n ty =>
    let (t, st) := st.internExpr ty
    st.intern (.fvar idx n t)
  | .sort u => st.intern (.sort u)
  | .const n us => st.intern (.const n us)
  | .app f a =>
    let (f', st) := st.internExpr f
    let (a', st) := st.internExpr a
    st.intern (.app f' a')
  | .lam n ty body m =>
    let (t, st) := st.internExpr ty
    let (b, st) := st.internExpr body
    st.intern (.lam n t b m)
  | .forallE n ty body m =>
    let (t, st) := st.internExpr ty
    let (b, st) := st.internExpr body
    st.intern (.forallE n t b m)
  | .letE n ty val body =>
    let (t, st) := st.internExpr ty
    let (v, st) := st.internExpr val
    let (b, st) := st.internExpr body
    st.intern (.letE n t v b)
  | .lit l => st.intern (.lit l)
  | .proj s i e =>
    let (e', st) := st.internExpr e
    st.intern (.proj s i e')

/-!
## Syntactic operations on indices

Each operation mirrors its `Setlec.Expr` counterpart exactly (same
recursion structure, same semantics) and threads a per-call memo table
keyed by the node index plus the traversal cursor, so DAG traversals are
linear in the number of distinct (node, cursor) pairs.

The traversals recurse on child indices, which are strictly smaller than
the parent's for well-formed stores; the `if _h : c < e` guards make
termination unconditional (on an ill-formed store a guard can fail, and
the operation returns the child unchanged — garbage in, garbage out; the
verification only speaks about well-formed stores).
-/

/-- Memo table for index→index traversals with a `Nat` cursor. -/
private abbrev MemoN := Std.HashMap (EIdx × Nat) EIdx

/-- Core of `instantiate1I`; `v` is the replacement index, `d` the
binder depth cursor (mirrors `Expr.instantiate1 e v d`). -/
def instantiate1IGo (v : EIdx) (st : EStore) (memo : MemoN) (e : EIdx) (d : Nat) :
    EIdx × EStore × MemoN :=
  match memo[(e, d)]? with
  | some r => (r, st, memo)
  | none =>
    let (r, st, memo) : EIdx × EStore × MemoN :=
      match st.nodes[e]? with
      | none => (e, st, memo)
      | some n =>
        match n with
        | .bvar i =>
          if i = d then (v, st, memo)
          else if i > d then
            let (r, st) := st.intern (.bvar (i - 1))
            (r, st, memo)
          else (e, st, memo)
        | .fvar _ _ _ => (e, st, memo)
        | .sort _ => (e, st, memo)
        | .const _ _ => (e, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := instantiate1IGo v st memo f d
            let (a', st, memo) := instantiate1IGo v st memo a d
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.lam n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.forallE n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := instantiate1IGo v st memo ty d
            let (val', st, memo) := instantiate1IGo v st memo val d
            let (body', st, memo) := instantiate1IGo v st memo body (d + 1)
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := instantiate1IGo v st memo sub d
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
    (r, st, memo.insert (e, d) r)
termination_by (e, d)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.instantiate1 e v d`: replace `bvar d`
by `v` (which must denote a `bvar`-closed expression; it is not shifted),
lowering loose `bvar`s above `d` by one. -/
def instantiate1I (st : EStore) (e v : EIdx) (d : Nat := 0) : EIdx × EStore :=
  let (r, st, _) := instantiate1IGo v st {} e d
  (r, st)

/-- Core of `abstract1I`; `d` is the abstracted fvar's de Bruijn level
(fixed), `k` the binder cursor (mirrors `Expr.abstract1 e d k`). -/
def abstract1IGo (d : Nat) (st : EStore) (memo : MemoN) (e : EIdx) (k : Nat) :
    EIdx × EStore × MemoN :=
  match memo[(e, k)]? with
  | some r => (r, st, memo)
  | none =>
    let (r, st, memo) : EIdx × EStore × MemoN :=
      match st.nodes[e]? with
      | none => (e, st, memo)
      | some n =>
        match n with
        | .bvar _ => (e, st, memo)
        | .fvar idx _ _ =>
          if idx = d then
            let (r, st) := st.intern (.bvar k)
            (r, st, memo)
          else (e, st, memo)
        | .sort _ => (e, st, memo)
        | .const _ _ => (e, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := abstract1IGo d st memo f k
            let (a', st, memo) := abstract1IGo d st memo a k
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.lam n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.forallE n ty' body' m)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := abstract1IGo d st memo ty k
            let (val', st, memo) := abstract1IGo d st memo val k
            let (body', st, memo) := abstract1IGo d st memo body (k + 1)
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := abstract1IGo d st memo sub k
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
    (r, st, memo.insert (e, k) r)
termination_by (e, k)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.abstract1 e d k`: replace `fvar d …`
leaves by `bvar k`, bumping `k` under binders (`fvar` type annotations
are not descended into). -/
def abstract1I (st : EStore) (e : EIdx) (d : Nat) (k : Nat := 0) : EIdx × EStore :=
  let (r, st, _) := abstract1IGo d st {} e k
  (r, st)

/-- Memo table for cursor-free index→index traversals. -/
private abbrev Memo0 := Std.HashMap EIdx EIdx

/-- Core of `instantiateLevelParamsI` (no cursor; mirrors
`Expr.instantiateLevelParams ks us`). -/
def instantiateLevelParamsIGo (ks : List Name) (us : List Level)
    (st : EStore) (memo : Memo0) (e : EIdx) : EIdx × EStore × Memo0 :=
  match memo[e]? with
  | some r => (r, st, memo)
  | none =>
    let (r, st, memo) : EIdx × EStore × Memo0 :=
      match st.nodes[e]? with
      | none => (e, st, memo)
      | some n =>
        match n with
        | .bvar _ => (e, st, memo)
        | .fvar idx nm ty =>
          if _h : ty < e then
            let (ty', st, memo) := instantiateLevelParamsIGo ks us st memo ty
            let (r, st) := st.intern (.fvar idx nm ty')
            (r, st, memo)
          else (e, st, memo)
        | .sort u =>
          let (r, st) := st.intern (.sort (Level.subst ks us u))
          (r, st, memo)
        | .const n vs =>
          let (r, st) := st.intern (.const n (vs.map (Level.subst ks us)))
          (r, st, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (f', st, memo) := instantiateLevelParamsIGo ks us st memo f
            let (a', st, memo) := instantiateLevelParamsIGo ks us st memo a
            let (r, st) := st.intern (.app f' a')
            (r, st, memo)
          else (e, st, memo)
        | .lam n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiateLevelParamsIGo ks us st memo ty
            let (body', st, memo) := instantiateLevelParamsIGo ks us st memo body
            let (r, st) := st.intern (.lam n ty' body' ⟨m.bi, m.cod.map (Level.subst ks us)⟩)
            (r, st, memo)
          else (e, st, memo)
        | .forallE n ty body m =>
          if _h : ty < e ∧ body < e then
            let (ty', st, memo) := instantiateLevelParamsIGo ks us st memo ty
            let (body', st, memo) := instantiateLevelParamsIGo ks us st memo body
            let (r, st) := st.intern (.forallE n ty' body' ⟨m.bi, m.cod.map (Level.subst ks us)⟩)
            (r, st, memo)
          else (e, st, memo)
        | .letE n ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (ty', st, memo) := instantiateLevelParamsIGo ks us st memo ty
            let (val', st, memo) := instantiateLevelParamsIGo ks us st memo val
            let (body', st, memo) := instantiateLevelParamsIGo ks us st memo body
            let (r, st) := st.intern (.letE n ty' val' body')
            (r, st, memo)
          else (e, st, memo)
        | .lit _ => (e, st, memo)
        | .proj s i sub =>
          if _h : sub < e then
            let (sub', st, memo) := instantiateLevelParamsIGo ks us st memo sub
            let (r, st) := st.intern (.proj s i sub')
            (r, st, memo)
          else (e, st, memo)
    (r, st, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.instantiateLevelParams ks us`:
substitute level parameters throughout (sorts, constant level arguments,
binder codomain annotations, and `fvar` type annotations). -/
def instantiateLevelParamsI (st : EStore) (ks : List Name) (us : List Level)
    (e : EIdx) : EIdx × EStore :=
  let (r, st, _) := instantiateLevelParamsIGo ks us st {} e
  (r, st)

/-!
## Pure queries (no store change)

Boolean/list queries mirror their `Expr` counterparts; each threads a
per-call memo where the recursion can revisit shared children.
-/

/-- Core of `hasFvarI` (mirrors `Expr.hasFvar`; `fvar` leaves are hits
without descending into their annotations, so no cursor). -/
def hasFvarIGo (st : EStore) (memo : Std.HashMap EIdx Bool) (e : EIdx) :
    Bool × Std.HashMap EIdx Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap EIdx Bool :=
      match st.nodes[e]? with
      | none => (false, memo)
      | some n =>
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => (false, memo)
        | .fvar _ _ _ => (true, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := hasFvarIGo st memo f
            if rf then (true, memo)
            else hasFvarIGo st memo a
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := hasFvarIGo st memo ty
            if rt then (true, memo)
            else hasFvarIGo st memo body
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := hasFvarIGo st memo ty
            if rt then (true, memo)
            else
              let (rv, memo) := hasFvarIGo st memo val
              if rv then (true, memo)
              else hasFvarIGo st memo body
          else (false, memo)
        | .proj _ _ sub =>
          if _h : sub < e then hasFvarIGo st memo sub
          else (false, memo)
    (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.hasFvar`. -/
def hasFvarI (st : EStore) (e : EIdx) : Bool :=
  (hasFvarIGo st {} e).1

/-- Core of `looseBVarsBoundedI`; `k` is the bound cursor (mirrors
`Expr.looseBVarsBounded k`). -/
def looseBVarsBoundedIGo (st : EStore) (memo : Std.HashMap (EIdx × Nat) Bool)
    (k : Nat) (e : EIdx) : Bool × Std.HashMap (EIdx × Nat) Bool :=
  match memo[(e, k)]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap (EIdx × Nat) Bool :=
      match st.nodes[e]? with
      | none => (false, memo)
      | some n =>
        match n with
        | .bvar i => (decide (i < k), memo)
        | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => (true, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := looseBVarsBoundedIGo st memo k f
            if rf then looseBVarsBoundedIGo st memo k a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := looseBVarsBoundedIGo st memo k ty
            if rt then looseBVarsBoundedIGo st memo (k + 1) body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := looseBVarsBoundedIGo st memo k ty
            if rt then
              let (rv, memo) := looseBVarsBoundedIGo st memo k val
              if rv then looseBVarsBoundedIGo st memo (k + 1) body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj _ _ sub =>
          if _h : sub < e then looseBVarsBoundedIGo st memo k sub
          else (false, memo)
    (r, memo.insert (e, k) r)
termination_by (e, k)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.looseBVarsBounded k`. -/
def looseBVarsBoundedI (st : EStore) (k : Nat) (e : EIdx) : Bool :=
  (looseBVarsBoundedIGo st {} k e).1

/-- Core of `wscopedBI`; `d` is the scope cursor (mirrors
`Expr.wscopedB d`; an `fvar idx _ ty` leaf checks `idx < d` and recurses
into the annotation at cutoff `idx`). -/
def wscopedBIGo (st : EStore) (memo : Std.HashMap (EIdx × Nat) Bool)
    (d : Nat) (e : EIdx) : Bool × Std.HashMap (EIdx × Nat) Bool :=
  match memo[(e, d)]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap (EIdx × Nat) Bool :=
      match st.nodes[e]? with
      | none => (false, memo)
      | some n =>
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => (true, memo)
        | .fvar idx _ ty =>
          if _h : ty < e then
            if idx < d then wscopedBIGo st memo idx ty else (false, memo)
          else (false, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := wscopedBIGo st memo d f
            if rf then wscopedBIGo st memo d a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := wscopedBIGo st memo d ty
            if rt then wscopedBIGo st memo d body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := wscopedBIGo st memo d ty
            if rt then
              let (rv, memo) := wscopedBIGo st memo d val
              if rv then wscopedBIGo st memo d body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj _ _ sub =>
          if _h : sub < e then wscopedBIGo st memo d sub
          else (false, memo)
    (r, memo.insert (e, d) r)
termination_by (e, d)
decreasing_by all_goals (apply Prod.Lex.left; first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h)

/-- Interned counterpart of `Expr.wscopedB d`. -/
def wscopedBI (st : EStore) (d : Nat) (e : EIdx) : Bool :=
  (wscopedBIGo st {} d e).1

/-- Core of `fvarLeavesI` (mirrors `Expr.fvarLeaves`: reachable `fvar`
leaves including, hereditarily, those inside their type annotations; the
annotation component of each triple is an index).  The memo shares the
sub-lists, so the traversal is linear in the number of distinct nodes
(the *resulting list* can still repeat leaves, exactly as the `Expr`
version does). -/
def fvarLeavesIGo (st : EStore)
    (memo : Std.HashMap EIdx (List (Nat × Name × EIdx))) (e : EIdx) :
    List (Nat × Name × EIdx) × Std.HashMap EIdx (List (Nat × Name × EIdx)) :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : List (Nat × Name × EIdx) × Std.HashMap EIdx (List (Nat × Name × EIdx)) :=
      match st.nodes[e]? with
      | none => ([], memo)
      | some n =>
        match n with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => ([], memo)
        | .fvar idx nm ty =>
          if _h : ty < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            ((idx, nm, ty) :: rt, memo)
          else ([(idx, nm, ty)], memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := fvarLeavesIGo st memo f
            let (ra, memo) := fvarLeavesIGo st memo a
            (rf ++ ra, memo)
          else ([], memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            let (rb, memo) := fvarLeavesIGo st memo body
            (rt ++ rb, memo)
          else ([], memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := fvarLeavesIGo st memo ty
            let (rv, memo) := fvarLeavesIGo st memo val
            let (rb, memo) := fvarLeavesIGo st memo body
            (rt ++ rv ++ rb, memo)
          else ([], memo)
        | .proj _ _ sub =>
          if _h : sub < e then fvarLeavesIGo st memo sub
          else ([], memo)
    (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.fvarLeaves`: the reachable `fvar`
leaves as `(idx, name, type-index)` triples. -/
def fvarLeavesI (st : EStore) (e : EIdx) : List (Nat × Name × EIdx) :=
  (fvarLeavesIGo st {} e).1

/-- Core of `constsResolveI` (mirrors `Expr.constsResolve env`; no
cursor). -/
def constsResolveIGo (st : EStore) (env : Env)
    (memo : Std.HashMap EIdx Bool) (e : EIdx) : Bool × Std.HashMap EIdx Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap EIdx Bool :=
      match st.nodes[e]? with
      | none => (false, memo)
      | some n =>
        match n with
        | .bvar _ | .sort _ | .lit _ => (true, memo)
        | .const n _ => ((env.find? n).isSome, memo)
        | .fvar _ _ ty =>
          if _h : ty < e then constsResolveIGo st env memo ty
          else (false, memo)
        | .app f a =>
          if _h : f < e ∧ a < e then
            let (rf, memo) := constsResolveIGo st env memo f
            if rf then constsResolveIGo st env memo a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : ty < e ∧ body < e then
            let (rt, memo) := constsResolveIGo st env memo ty
            if rt then constsResolveIGo st env memo body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : ty < e ∧ val < e ∧ body < e then
            let (rt, memo) := constsResolveIGo st env memo ty
            if rt then
              let (rv, memo) := constsResolveIGo st env memo val
              if rv then constsResolveIGo st env memo body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj s _ sub =>
          if _h : sub < e then
            if (env.find? s).isSome then constsResolveIGo st env memo sub
            else (false, memo)
          else (false, memo)
    (r, memo.insert e r)
termination_by e
decreasing_by all_goals first | exact _h.1 | exact _h.2.1 | exact _h.2.2 | exact _h.2 | exact _h

/-- Interned counterpart of `Expr.constsResolve env`. -/
def constsResolveI (st : EStore) (env : Env) (e : EIdx) : Bool :=
  (constsResolveIGo st env {} e).1

end EStore

end Setlec
