import ConLeche.Kernel.Direct.Parts
import ConLeche.Kernel.Level

/-!
# The in-process modeller's kit (task #200)

Shared pieces of the in-process construction of `_model` families for
nested and mutual inductive blocks (`ConLeche/Frontend/InModel/*`):

* the naming scheme (lean-inductive-models' `_impl` names, so the two
  generators' streams are diffable — none of these names is special to
  the checker: only the public `_model` slots are consumed, and only
  by the modeled install);
* telescope helpers over `ConLeche.Expr` (de Bruijn frames spelled out at
  every use);
* `specFam`, the syntactic rewrite of every member occurrence
  `T_m p⃗` into the auxiliary family at its tag, `aux p⃗ (tag.m p⃗ ı⃗)`;
* the **kernel-shape recursor** of an indexed recursive family with
  inductive hypotheses — `directRecTyI`/`directRecRhsI`
  (`ConLeche/Kernel/Direct/Parts.lean`) with the `ih` binders of the
  official `mk_rec_infos` threaded in; the direct fixpoint route
  regenerates and compares the recursor of the auxiliary family
  against exactly this shape by one `isDefEq`, so binder names are
  display-only but the argument order and the `ih` placement are the
  kernel's;
* a **syntactic sort inferer** over the parsed declaration table (no
  environment, no `whnf`): the sort of a field's or index's type, for
  the `Eq` level of a `proj_i.iota` artifact and the tag's universe.
  Where it fails the artifact is skipped or the block declines —
  never a wrong accept: everything generated is checked by the fold;
* definitional heights, computed as the kernel does (one above the
  highest constant the value mentions).
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-! ## Names -/

/-- `T._model._impl.<s>`. -/
def implName (T : Name) (s : String) : Name := ((T.str "_model").str "_impl").str s

/-- The tag family `T._model._impl.tag` of the block owned by `T`. -/
def tagName (T : Name) : Name := implName T "tag"

/-- The tag constructor of member `k`: `T._model._impl.tag.k`. -/
def tagCtorName (T : Name) (k : Nat) : Name := (tagName T).num k

/-- The auxiliary family `T._model._impl.aux`. -/
def auxName (T : Name) : Name := implName T "aux"

/-- The auxiliary constructor of member `k`'s constructor `C`:
`T._model._impl.aux.k.<last component of C>`. -/
def auxCtorName (T : Name) (k : Nat) (C : Name) : Name :=
  match C with
  | .str _ s => ((auxName T).num k).str s
  | .num _ n => ((auxName T).num k).num n
  | .anonymous => (auxName T).num k

/-- The model companion of a block member: `X._model`. -/
def modelName (n : Name) : Name := n.str "_model"

/-- The iota theorem of rule `j` of a modeled recursor `R`:
`R._model.iota_j` (`ConLeche/Kernel/Modeled.lean`'s lookup). -/
def iotaName (R : Name) (j : Nat) : Name := (modelName R).str s!"iota_{j}"

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
binders seen from `o` binders below it (`directPsAt`). -/
def varsAt (o n : Nat) : List Expr := directPsAt o n

/-- A constant at its level parameters. -/
def constP (n : Name) (lps : List Name) : Expr := .const n (lps.map .param)

/-- The domains of a `∀`-telescope's binder list. -/
def piBinders (bs : List (Expr × BinderMeta)) : List Expr :=
  bs.map (·.1)

/-- A member's or constructor's telescope `ty` re-spelled over the
FIRST member's parameter binders: the first `nP` binders of `former`
(the first member's type) with `ty`'s residual after its own `nP`
parameter binders under them.  Task #218: official compares the
members' (and constructors') parameter domains with `is_def_eq`, so a
member may spell a domain differently from the first (`id Type` for
`Type`); the auxiliary family is built over the first's telescope, and
this is where every generated constructor of it gets that telescope.
The re-spelling is checked, not trusted: the residual was typed under
the member's own domains, and the fold's typing of the generated record
is what compares them (a genuinely different domain makes the record
ill-typed and the fold rejects it). -/
def overFirstParams (nP : Nat) (former ty : Expr) : Option Expr :=
  (ty.stripPis nP).bind fun q => Expr.replacePiBody nP former q.2

/-! ## Family occurrences -/

/-- Rewrite every occurrence `T_m a⃗` (exactly `nP + nIdx_m` arguments)
of a member of the block into `aux a⃗_P (tag.m a⃗_P a⃗_I)` — the
auxiliary family at the member's tag constructor carrying the index
arguments.  `members` lists `(T_m, m, nIdx_m)`.  An occurrence with any
other arity is left alone (the caller's field classification rejects
such blocks). -/
partial def specFam (T : Name) (lps : List Name) (nP : Nat)
    (members : List (Name × Nat × Nat)) : Expr → Expr
  | e@(.app _ _) =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n us =>
      match members.find? (·.1 == n) with
      | some (_, m, nIdx) =>
        if args.length == nP + nIdx && us == lps.map .param then
          let ps := (args.take nP).map (specFam T lps nP members)
          let is := (args.drop nP).map (specFam T lps nP members)
          Expr.mkAppN (constP (auxName T) lps)
            (ps ++ [Expr.mkAppN (constP (tagCtorName T m) lps) (ps ++ is)])
        else Expr.mkAppN (specFam T lps nP members f) (args.map (specFam T lps nP members))
      | none => Expr.mkAppN f (args.map (specFam T lps nP members))
    | _ => Expr.mkAppN (specFam T lps nP members f) (args.map (specFam T lps nP members))
  | .const n us =>
    match members.find? (·.1 == n) with
    | some (_, m, nIdx) =>
      if nP + nIdx == 0 && us == lps.map .param then
        Expr.mkAppN (constP (auxName T) lps) [constP (tagCtorName T m) lps]
      else .const n us
    | none => .const n us
  | .lam d b m => .lam (specFam T lps nP members d) (specFam T lps nP members b) m
  | .forallE d b m => .forallE (specFam T lps nP members d) (specFam T lps nP members b) m
  | .letE t v b =>
    .letE (specFam T lps nP members t) (specFam T lps nP members v) (specFam T lps nP members b)
  | .proj s i e => .proj s i (specFam T lps nP members e)
  | e => e

/-- Simultaneous substitution of a parameter block: under `d` binders,
`bvar (d + j)` (`j < n`, innermost first) becomes `vals[n - 1 - j]`
(`vals` outermost first, spelled at the frame `d` binders below the
block's, lifted past the binders passed on the way), and every loose
`bvar ≥ d + n` is lowered by `n`.  Unlike `instantiateList` the
replacements are never re-traversed, so they may mention variables of
the surrounding frame. -/
partial def substParams (d n : Nat) (vals : List Expr) (e : Expr) : Expr :=
  go 0 e
where
  go (k : Nat) : Expr → Expr
    | .bvar i =>
      if i < d + k then .bvar i
      else if i < d + k + n then (vals.getD (n - 1 - (i - d - k)) default).liftLooseBVars k 0
      else .bvar (i - n)
    | .app f a => .app (go k f) (go k a)
    | .lam t b m => .lam (go k t) (go (k + 1) b) m
    | .forallE t b m => .forallE (go k t) (go (k + 1) b) m
    | .letE t v b => .letE (go k t) (go k v) (go (k + 1) b)
    | .proj s i x => .proj s i (go k x)
    | .fvar i t => .fvar i (go k t)
    | e => e

/-- Does `e` mention any of the names? -/
def mentionsAny (ns : List Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => ns.contains n
  | .fvar _ ty => mentionsAny ns ty
  | .app f a => mentionsAny ns f || mentionsAny ns a
  | .lam ty b _ | .forallE ty b _ => mentionsAny ns ty || mentionsAny ns b
  | .letE ty v b => mentionsAny ns ty || mentionsAny ns v || mentionsAny ns b
  | .proj s _ e => ns.contains s || mentionsAny ns e

/-! ## The kernel-shape recursor of an indexed recursive family

The generators of `ConLeche/Kernel/Direct/Parts.lean` (indexed, task #175)
with the inductive hypotheses of the official `mk_rec_infos`: a minor
premise binds the constructor's fields, then one `ih` per recursive
field in field order — `motive e⃗_i f_i`, the field's own index
expressions read off its domain `T p⃗ e⃗_i` — and concludes
`motive e⃗_C (C p⃗ f⃗)`; rule `j` is
`λ p⃗ motive m⃗ f⃗, minor_j f⃗ (T.rec p⃗ motive m⃗ e⃗_i f_i)…`.  A
constructor is `(C, nF, cty, recIdx)` with `recIdx` the recursive
field positions (ascending). -/

/-- The recursor's leading spine `p⃗ motive m⃗` as seen from under the
`nF` fields and `e` further binders. -/
def recPrefixAt (nP n nF e : Nat) : List Expr :=
  directPsAt (e + nF + n + 1) nP ++ [Expr.bvar (e + nF + n)] ++
    (List.range n).map fun l => Expr.bvar (e + nF + n - 1 - l)

/-- The index arguments of recursive field `i` (domain `T p⃗ e⃗_i`,
spelled at the field's own binder) lifted to the frame `l` binders
below the last field. -/
def recFieldIdx (nP nF i l : Nat) (doms : List Expr) : List Expr :=
  ((doms.getD i default).liftLooseBVars (nF - i + l) 0).getAppArgs.drop nP

/-- The `ih` binders of a minor premise: for each recursive field
position (ascending) `motive e⃗_i f_i`, under the `l` earlier `ih`
binders; the motive sits `nF + o - 1` binders above the fields. -/
def ihPis (nP nF o : Nat) (pw : PropWhen) (doms : List Expr) : List Nat → Nat → Expr → Expr
  | [], _, body => body
  | i :: is, l, body =>
    .forallE
      (Expr.mkAppN (.bvar (nF + o - 1 + l))
        (recFieldIdx nP nF i l doms ++ [.bvar (nF - 1 - i + l)]))
      (ihPis nP nF o pw doms is (l + 1) body) ⟨pw⟩

/-- Constructor `C`'s minor premise: the field telescope lifted under
the `o` extras (every field datum reset to the elimination datum), the
`ih` binders, and `motive e⃗_C (C p⃗ f⃗)` lifted above the `ih`s.  The
residual's index expressions are read off the once-lifted telescope
(`tele`), so unlike `directMinorTyI` they are lifted only above the
`ih`s here. -/
def minorTy (C : Name) (lps : List Name) (nP nF o : Nat) (pw : PropWhen)
    (cty : Expr) (recIdx : List Nat) : Option Expr :=
  (cty.stripPis nP).bind fun q =>
  let tele := q.2.liftLooseBVars o 0
  (tele.stripPis nF).bind fun r =>
    let doms := r.1.map (·.1)
    let nIh := recIdx.length
    Expr.replacePisPw pw nF tele
      (ihPis nP nF o pw doms recIdx 0
        (Expr.mkAppN (.bvar (nF + o - 1 + nIh))
          ((r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars nIh 0) ++
            [(directCtorSpineAt C lps o nP nF).liftLooseBVars nIh 0])))

/-- The minors' `∀`-telescope over `body`, one per constructor, the
first sitting `o` binders below the parameters. -/
def minorsPis (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (minorTy C lps nP nF o pw cty recIdx).bind fun mty =>
      (minorsPis lps nP pw cs (o + 1) body).map fun rest =>
        .forallE mty rest ⟨pw⟩

/-- The `λ` twin of `minorsPis`. -/
def minorsLams (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (minorTy C lps nP nF o pw cty recIdx).bind fun mty =>
      (minorsLams lps nP pw cs (o + 1) body).map fun rest =>
        .lam mty rest ⟨pw⟩

/-- **The recursor type**

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_C : ∀ f⃗ (ih⃗ : motive e⃗_i f_i)…, motive e⃗_C (C p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

over the former's type `tty = ∀ p⃗ ı⃗, Sort w` (`directRecTyI` with
inductive hypotheses). -/
def recTy (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) : Option Expr :=
  let ℓ := directElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  (tty.stripPis nP).bind fun q =>
  (directMotiveTyI T lps nP nIdx ℓ q.2).bind fun motiveTy =>
  (Expr.replacePisPw pw nIdx (q.2.liftLooseBVars (n + 1) 0)
      (.forallE (directFamI T lps nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (directPsAt 1 nIdx ++ [.bvar 0]))
        ⟨pw⟩)).bind fun major =>
  (minorsPis lps nP pw ctors 1 major).bind fun minors =>
    Expr.replacePisPw pw nP tty
      (.forallE motiveTy minors ⟨pw⟩)

/-- **The rule** of constructor `j`:
`λ p⃗ motive m⃗ f⃗, minor_j f⃗ (T.rec p⃗ motive m⃗ e⃗_i f_i)…` (`recC`,
`rlvls`: the recursor's name and its level parameters as levels). -/
def recRhs (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) (j : Nat) : Option Expr :=
  let ℓ := directElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  match ctors[j]? with
  | none => none
  | some (_, nF, cty, recIdx) =>
    (tty.stripPis nP).bind fun tq =>
    (directMotiveTyI T lps nP nIdx ℓ tq.2).bind fun motiveTy =>
    (cty.stripPis nP).bind fun q =>
    let tele := q.2.liftLooseBVars (n + 1) 0
    (tele.stripPis nF).bind fun r =>
    let doms := r.1.map (·.1)
    let body := Expr.mkAppN (.bvar (nF + n - 1 - j))
      (((List.range nF).map fun k => Expr.bvar (nF - 1 - k)) ++
        recIdx.map fun i =>
          Expr.mkAppN (.const recC rlvls)
            (recPrefixAt nP n nF 0 ++ recFieldIdx nP nF i 0 doms ++ [.bvar (nF - 1 - i)]))
    (Expr.pisToLamsPw pw nF tele body).bind fun inner =>
    (minorsLams lps nP pw ctors 1 inner).bind fun minors =>
    Expr.pisToLamsPw pw nP tty
      (.lam motiveTy minors ⟨pw⟩)

/-! ## A syntactic sort inferer

`inferTy tbl ctx e` computes the type of `e` from the declared types
of the constants it mentions (`tbl`) and the binder domains of the
context (`ctx`, innermost first, each spelled at its own frame),
β-reducing only what instantiating a `∀` produces.  No `whnf`, no
definitional unfolding: an application whose function type is not
syntactically a `∀` after instantiation fails.  `sortOf` reads the
result as a sort. -/

/-- The declared type of a constant: its level parameters and type. -/
abbrev ConstTable := Name → Option (List Name × Expr)

/-- Head β-reduction only. -/
partial def betaHead : Expr → Expr
  | .app f a =>
    match betaHead f with
    | .lam _ b _ => betaHead (b.instantiate1 a)
    | f' => .app f' a
  | e => e

partial def inferTy (tbl : ConstTable) (ctx : List Expr) : Expr → Option Expr
  | .bvar i => (ctx[i]?).map (·.liftLooseBVars (i + 1) 0)
  | .sort u => some (.sort (.succ u))
  | .const n us =>
    (tbl n).bind fun (lps, ty) =>
      if lps.length == us.length then some (ty.instantiateLevelParams lps us) else none
  | .app f a =>
    (inferTy tbl ctx f).bind fun ft =>
      match betaHead ft with
      | .forallE _ b _ => some (b.instantiate1 a)
      | _ => none
  | .lam d b m => (inferTy tbl (d :: ctx) b).map fun bt => .forallE d bt m
  | .forallE d b _ =>
    (sortOf tbl ctx d).bind fun u =>
      (sortOf tbl (d :: ctx) b).map fun v => .sort (.imax u v)
  | .letE _ v b => inferTy tbl ctx (b.instantiate1 v)
  | .lit (.natVal _) => some (.const natName [])
  | .lit (.strVal _) => some (.const stringName [])
  | _ => none
where
  /-- The sort of a type. -/
  sortOf (tbl : ConstTable) (ctx : List Expr) (e : Expr) : Option Level :=
    (inferTy tbl ctx e).bind fun t =>
      match betaHead t with
      | .sort u => some u
      | _ => none

/-- The sort of a type at a context. -/
def sortOf (tbl : ConstTable) (ctx : List Expr) (e : Expr) : Option Level :=
  inferTy.sortOf tbl ctx e

/-! ## Definitional heights -/

/-- The highest definitional height of a constant mentioned by `e`
(`heights`: the height of every definition declared so far; `0` for
anything else). -/
def maxHeight (heights : Name → Nat) : Expr → Nat
  | .const n _ => heights n
  | .fvar _ ty => maxHeight heights ty
  | .app f a => max (maxHeight heights f) (maxHeight heights a)
  | .lam ty b _ | .forallE ty b _ => max (maxHeight heights ty) (maxHeight heights b)
  | .letE ty v b => max (maxHeight heights ty) (max (maxHeight heights v) (maxHeight heights b))
  | .proj _ _ e => maxHeight heights e
  | _ => 0

/-- The reducibility hint of a generated definition: one above the
highest constant its value mentions (the kernel's `getMaxHeight`
rule). -/
def hintFor (heights : Name → Nat) (value : Expr) : ReducibilityHint :=
  .regular (maxHeight heights value + 1)

/-- The height a hint records. -/
def hintHeight : ReducibilityHint → Nat
  | .regular n => n
  | _ => 0

end ConLeche.Frontend.InModel
