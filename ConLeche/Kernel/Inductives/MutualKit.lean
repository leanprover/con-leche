module

public import ConLeche.Kernel.Inductives.StructParts

@[expose] public section

/-!
# The mutual reduction's kit (task #278)

Telescope helpers over `ConLeche.Expr`, the syntactic rewrite of every
member occurrence of a mutual block into its auxiliary family
(`specFam`), the name-mention walk and the definitional-height rule —
the pieces of the in-process modeller's kit
(`ConLeche/Frontend/InModel/Kit.lean`, task #200) that the KERNEL's
mutual install now runs itself: a mutual block is reduced to one
tagged family inside `checkMutual`
(`ConLeche/Kernel/Inductives/MutualInstall.lean`), so the reduction's
syntactic pieces live below the frontend.  The frontend's kit re-exports
them for the nested rung, which still runs at parse time.

Nothing here is trusted: what the rewrite emits is installed through
`checkNative` and the block's own constants are checked against it by
the type checker, so no walk below carries a specification lemma —
the memoised walks are plain functions.
-/

namespace ConLeche.MutualKit

open ConLeche

/-! ## Binders and frames -/

/-- The default binder datum of a generated binder: `.never` — what the
frontend gives every parsed binder (task #161; the annotate pass
recomputes the datum before it is validated). -/
def bm : BinderMeta := ⟨.never⟩

/-- `λ`-telescope over domains (outermost first). -/
def mkLams (bs : List Expr) (body : Expr) : Expr :=
  bs.foldr (fun d acc => .lam d acc bm) body

/-- `∀`-telescope over domains (outermost first). -/
def mkPis (bs : List Expr) (body : Expr) : Expr :=
  bs.foldr (fun d acc => .forallE d acc bm) body

/-- The variables `bvar (o + n - 1 - k)`, `k < n`: a telescope of `n`
binders seen from `o` binders below it (`structPsAt`). -/
def varsAt (o n : Nat) : List Expr := structPsAt o n

/-- A constant at its level parameters. -/
def constP (n : Name) (lps : List Name) : Expr := .const n (lps.map .param)

/-- The domains of a `∀`-telescope's binder list. -/
def piBinders (bs : List (Expr × BinderMeta)) : List Expr :=
  bs.map (·.1)

/-- A level-parameter name not among `lps`: `u`, then `u_1`, `u_2`, …
— the official kernel's `mk_fresh_lvl_name` convention for a
recursor's elimination level (`inductive.cpp`), so a generated
recursor's level parameters are the ones Lean's own kernel would
mint for the same block. -/
partial def freshLevelName (lps : List Name) (base : String := "u") : Name :=
  if lps.contains (Name.str .anonymous base) then go 1 else Name.str .anonymous base
where
  go (i : Nat) : Name :=
    let n := Name.str .anonymous s!"{base}_{i}"
    if lps.contains n then go (i + 1) else n

/-- A member's or constructor's telescope `ty` re-spelled over the
FIRST member's parameter binders: the first `nP` binders of `former`
(the first member's type) with `ty`'s residual after its own `nP`
parameter binders under them.  Task #218: official compares the
members' (and constructors') parameter domains with `is_def_eq`, so a
member may spell a domain differently from the first (`id Type` for
`Type`); the auxiliary family is built over the first's telescope, and
this is where every generated constructor of it gets that telescope.
The re-spelling is checked, not trusted: the residual was typed under
the member's own domains, and the typing of the generated record is
what compares them (a genuinely different domain makes the record
ill-typed and the check rejects it). -/
def overFirstParams (nP : Nat) (former ty : Expr) : Option Expr :=
  (ty.stripPis nP).bind fun q => Expr.replacePiBody nP former q.2

/-! ## Family occurrences -/

mutual

/-- Rewrite every occurrence `T_m a⃗` (exactly `nP + nIdx_m` arguments)
of a member of the block into `aux a⃗_P (tagCtor m a⃗_P a⃗_I)` — the
auxiliary family at the member's tag constructor carrying the index
arguments.  `members` lists `(T_m, m, nIdx_m)`.  An occurrence with any
other arity is left alone (the caller's field classification declines
such blocks).

One memoized DAG walk (keyed by the node — the rewrite reads no binder
cursor).  Without it the rebuild runs once per path, which is what
`tests/e2e/tower_mutual.ndjson` exposes. -/
partial def specFamGo (aux : Name) (tagCtor : Nat → Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (memo : Std.HashMap Expr Expr) :
    Expr → Expr × Std.HashMap Expr Expr
  | .bvar i => (.bvar i, memo)
  | .sort u => (.sort u, memo)
  | .fvar i t => (.fvar i t, memo)
  | .lit l => (.lit l, memo)
  | .const n us =>
    match members.find? (·.1 == n) with
    | some (_, m, nIdx) =>
      if nP + nIdx == 0 && us == lps.map .param then
        (Expr.mkAppN (constP aux lps) [constP (tagCtor m) lps], memo)
      else (.const n us, memo)
    | none => (.const n us, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Expr × Std.HashMap Expr Expr :=
        match e with
        | e@(.app _ _) =>
          let f := e.getAppFn
          let args := e.getAppArgs
          match f with
          | .const n us =>
            match members.find? (·.1 == n) with
            | some (_, m, nIdx) =>
              if args.length == nP + nIdx && us == lps.map .param then
                let (ps, memo) := specFamGoList aux tagCtor lps nP members memo (args.take nP)
                let (is, memo) := specFamGoList aux tagCtor lps nP members memo (args.drop nP)
                (Expr.mkAppN (constP aux lps)
                  (ps ++ [Expr.mkAppN (constP (tagCtor m) lps) (ps ++ is)]), memo)
              else
                let (f', memo) := specFamGo aux tagCtor lps nP members memo f
                let (as, memo) := specFamGoList aux tagCtor lps nP members memo args
                (Expr.mkAppN f' as, memo)
            | none =>
              let (as, memo) := specFamGoList aux tagCtor lps nP members memo args
              (Expr.mkAppN f as, memo)
          | _ =>
            let (f', memo) := specFamGo aux tagCtor lps nP members memo f
            let (as, memo) := specFamGoList aux tagCtor lps nP members memo args
            (Expr.mkAppN f' as, memo)
        | .lam d b m =>
          let (d', memo) := specFamGo aux tagCtor lps nP members memo d
          let (b', memo) := specFamGo aux tagCtor lps nP members memo b
          (.lam d' b' m, memo)
        | .forallE d b m =>
          let (d', memo) := specFamGo aux tagCtor lps nP members memo d
          let (b', memo) := specFamGo aux tagCtor lps nP members memo b
          (.forallE d' b' m, memo)
        | .letE t v b =>
          let (t', memo) := specFamGo aux tagCtor lps nP members memo t
          let (v', memo) := specFamGo aux tagCtor lps nP members memo v
          let (b', memo) := specFamGo aux tagCtor lps nP members memo b
          (.letE t' v' b', memo)
        | .proj s i x =>
          let (x', memo) := specFamGo aux tagCtor lps nP members memo x
          (.proj s i x', memo)
        | e => (e, memo)
      (r, memo.insert e r)

@[inherit_doc specFamGo]
partial def specFamGoList (aux : Name) (tagCtor : Nat → Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (memo : Std.HashMap Expr Expr) :
    List Expr → List Expr × Std.HashMap Expr Expr
  | [] => ([], memo)
  | x :: xs =>
    let (y, memo) := specFamGo aux tagCtor lps nP members memo x
    let (ys, memo) := specFamGoList aux tagCtor lps nP members memo xs
    (y :: ys, memo)

end

@[inherit_doc specFamGo]
def specFam (aux : Name) (tagCtor : Nat → Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) (e : Expr) : Expr :=
  (specFamGo aux tagCtor lps nP members {} e).1

/-- Does `e` mention any of the names?  One memoized DAG walk: the
answer at a node is a function of the node and `ns`, and `ns` is fixed
for the walk, so the memo is keyed by the node alone and dropped after
each call.  `tests/e2e/tower_mutual.ndjson` is what walks it: the
mutual install asks this of every ordinary field domain, and a domain
carrying a depth-60 shared tower mentions no member, so nothing
short-circuits. -/
def mentionsAnyGo (ns : List Name) (memo : Std.HashMap Expr Bool) :
    Expr → Bool × Std.HashMap Expr Bool
  | .bvar _ => (false, memo)
  | .sort _ => (false, memo)
  | .lit _ => (false, memo)
  | .const n _ => (ns.contains n, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap Expr Bool :=
        match e with
        | .fvar _ ty => mentionsAnyGo ns memo ty
        | .app f a =>
          match mentionsAnyGo ns memo f with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsAnyGo ns memo a
        | .lam ty b _ | .forallE ty b _ =>
          match mentionsAnyGo ns memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) => mentionsAnyGo ns memo b
        | .letE ty v b =>
          match mentionsAnyGo ns memo ty with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match mentionsAnyGo ns memo v with
            | (true, memo) => (true, memo)
            | (false, memo) => mentionsAnyGo ns memo b
        | .proj s _ x =>
          if ns.contains s then (true, memo) else mentionsAnyGo ns memo x
        | _ => (false, memo)
      (r, memo.insert e r)

@[inherit_doc mentionsAnyGo]
def mentionsAny (ns : List Name) (e : Expr) : Bool := (mentionsAnyGo ns {} e).1

/-! ## Definitional heights -/

/-- The highest definitional height of a constant mentioned by `e`
(`heights`: the height of every definition declared so far; `0` for
anything else).  One memoized DAG walk, keyed by the node.  Every
generated value embeds the block's constructor domains, so a tower in
one of them is walked here once per path without it. -/
def maxHeightGo (heights : Name → Nat) (memo : Std.HashMap Expr Nat) :
    Expr → Nat × Std.HashMap Expr Nat
  | .const n _ => (heights n, memo)
  | .bvar _ => (0, memo)
  | .sort _ => (0, memo)
  | .lit _ => (0, memo)
  | e =>
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Nat × Std.HashMap Expr Nat :=
        match e with
        | .fvar _ ty => maxHeightGo heights memo ty
        | .app f a =>
          let (rf, memo) := maxHeightGo heights memo f
          let (ra, memo) := maxHeightGo heights memo a
          (max rf ra, memo)
        | .lam ty b _ | .forallE ty b _ =>
          let (rt, memo) := maxHeightGo heights memo ty
          let (rb, memo) := maxHeightGo heights memo b
          (max rt rb, memo)
        | .letE ty v b =>
          let (rt, memo) := maxHeightGo heights memo ty
          let (rv, memo) := maxHeightGo heights memo v
          let (rb, memo) := maxHeightGo heights memo b
          (max rt (max rv rb), memo)
        | .proj _ _ x => maxHeightGo heights memo x
        | _ => (0, memo)
      (r, memo.insert e r)

@[inherit_doc maxHeightGo]
def maxHeight (heights : Name → Nat) (e : Expr) : Nat :=
  (maxHeightGo heights {} e).1

/-- The reducibility hint of a generated definition: one above the
highest constant its value mentions (the kernel's `getMaxHeight`
rule). -/
def hintFor (heights : Name → Nat) (value : Expr) : ReducibilityHint :=
  .regular (maxHeight heights value + 1)

/-- The height a hint records. -/
def hintHeight : ReducibilityHint → Nat
  | .regular n => n
  | _ => 0

/-- The definitional height of a stored constant: a definition's hint,
`0` for anything else (the kernel's `getMaxHeight` reads the same). -/
def heightOf (find? : Name → Option ConstantInfo) (n : Name) : Nat :=
  match find? n with
  | some (.defnInfo _ _ h) => hintHeight h
  | _ => 0

end ConLeche.MutualKit
