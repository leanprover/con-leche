import Lech.Frontend.InModel.Kit
import Lech.Frontend.ProjRec
import Lech.Cached.ParsedC

/-!
# In-process models of a MUTUAL inductive block (task #200, B1: index-free)

lean-inductive-models' mutual rung (`Mutual.lean` there), on
`Lech.Expr`, without the tool: a mutual block `T_1 … T_k` over one
parameter telescope `p⃗` becomes

* a **tag** enumeration `T_1._model._impl.tag : ∀ p⃗, Type` with one
  constructor `tag.m p⃗` per member (B2 puts the member's index
  telescope on it);
* an **auxiliary family** `T_1._model._impl.aux : ∀ p⃗ (t : tag p⃗), Sort u`
  — one indexed recursive family; member `m`'s constructor `C` becomes
  `aux.m.C : ∀ p⃗ f⃗', aux p⃗ (tag.m p⃗)` with every field `T_{m'} p⃗`
  rewritten to `aux p⃗ (tag.m' p⃗)` (`specFam`), and the recursor is
  the kernel-shape one with inductive hypotheses (`Kit.recTy`);
* the **public slots** the modeled install consumes
  (`Lech/Kernel/Modeled.lean`): `T_m._model := λ p⃗, aux p⃗ (tag.m p⃗)`,
  `C._model := λ p⃗ f⃗, aux.m.C p⃗ f⃗`, and
  `T_m.rec._model := λ p⃗ M⃗ S⃗ t, aux.rec p⃗ Mot S⃗ (tag.m p⃗) t` with
  `Mot i s := tag.rec p⃗ (λ i', aux p⃗ i' → Sort ℓ) M⃗ i s` — the
  minors pass through unchanged (`Mot (tag.m p⃗) ≡ M_m` by δι), so
  every `iota_j` theorem holds by `Eq.refl`;
* for a structure-like non-`Prop` member, `T_m._model.proj_i` (the
  recursor at a constant motive, the other motives `PUnit`) and
  `proj_i.iota` (by `Eq.refl`: the projection reduces on the modeled
  constructor by δι) — consumed only through the `Eq` level the
  projection rewrite reads (`Lech/Frontend/ProjRec.lean`).

The two generated blocks are ordinary inductive records: the tag is
the direct sum route's, the auxiliary family the direct fixpoint
route's (task #188, at indices).  Every record below is checked by the
fold as a stream declaration; a wrong one rejects or declines, never
accepts.  Declines (`.error`) name the residual: nested members (B3),
indexed members (B2), reflexive members, a `Prop` block with a large
eliminator (the auxiliary family has ≥ 2 constructors, so it
eliminates into `Prop` only), and members whose telescopes differ.
-/

namespace Lech.Frontend.InModel

open Lech
open Lech.Cached (DeclC)

/-- One inductive type of a parsed block, with the export's shape data. -/
structure IndTypeRec where
  cv : ConstantVal
  nP : Nat
  nIdx : Nat
  ctors : List Name
  isRec : Bool
  isReflexive : Bool
  numNested : Nat
  deriving Repr, Inhabited

/-- One constructor of a parsed block. -/
structure IndCtorRec where
  cv : ConstantVal
  nP : Nat
  nF : Nat
  deriving Repr, Inhabited

/-- One recursor of a parsed block (`numParams`, `numMotives`,
`numMinors`, `numIndices` as exported). -/
structure IndRecRec where
  cv : ConstantVal
  nP : Nat
  nM : Nat
  nm : Nat
  nI : Nat
  rules : List RecRule
  deriving Repr, Inhabited

/-- A parsed inductive block. -/
structure BlockRec where
  types : List IndTypeRec
  ctors : List IndCtorRec
  recs : List IndRecRec
  deriving Repr, Inhabited

/-- What the generator reads besides the block: the declared types of
the constants so far, and the definitional heights. -/
structure Ctx where
  tbl : ConstTable
  heights : Name → Nat
  /-- the parsed inductive blocks so far, by member type name (the
  nested rung reads a container's shape off it) -/
  blocks : Name → Option BlockRec := fun _ => none

/-- A constructor of member `m`, classified: its record, its recursive
field positions with the target member of each. -/
structure MCtor where
  m : Nat
  c : IndCtorRec
  recFields : List (Nat × Nat)
  deriving Repr, Inhabited

/-- Is `e` member `m'` of the block applied to the parameter variables
(`o` binders below the parameter frame) and `nIdx_{m'}` index
expressions?  Returns the member. -/
def memberApp? (members : List (Name × Nat × Nat)) (lps : List Name) (nP o : Nat)
    (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .const x us =>
    match members.find? (·.1 == x) with
    | some (_, m', nIdx) =>
      let args := e.getAppArgs
      if us == lps.map .param && args.length == nP + nIdx && args.take nP == varsAt o nP
      then some m' else none
    | none => none
  | _ => none

/-- Classify one constructor's fields: each domain is ordinary (no
member mentioned) or exactly a member at the parameters and some
index expressions (`T_{m'} p⃗ e⃗`); anything else is not this rung's
(nested, reflexive, non-positive).  `members` lists `(T, m, nIdx)`. -/
def classifyCtor (members : List (Name × Nat × Nat)) (lps : List Name) (nP : Nat)
    (m : Nat) (c : IndCtorRec) : Except String MCtor := do
  let memberNames := members.map (·.1)
  let some (bs, resid) := c.cv.type.stripPis (nP + c.nF)
    | throw s!"constructor {c.cv.name} is not a telescope"
  unless memberApp? members lps nP c.nF resid == some m do
    throw s!"constructor {c.cv.name} does not return its member at the parameters"
  let mut recFields : List (Nat × Nat) := []
  for i in List.range c.nF do
    let d := (bs.getD (nP + i) default).1
    match memberApp? members lps nP i d with
    | some m' => recFields := recFields ++ [(i, m')]
    | none =>
      if mentionsAny memberNames d then
        throw s!"field {i} of {c.cv.name} mentions the block other than as a plain \
          member application (nested, reflexive or non-positive occurrence)"
  pure ⟨m, c, recFields⟩

/-- Unwrap a generator step that cannot fail on a well-formed block. -/
def need (what : String) : Option α → Except String α
  | some a => pure a
  | none => throw s!"internal shape failure: {what}"

/-- **The mutual rung** (B1 index-free, B2 indexed).  The records, in stream order:
the tag block, the auxiliary block, the member/constructor/recursor
models, the iota theorems, the projection artifacts. -/
def genMutual (ctx : Ctx) (b : BlockRec) : Except String (List DeclC) := do
  let t0 :: _ := b.types | throw "empty block"
  let T := t0.cv.name
  let lps := t0.cv.levelParams
  let nP := t0.nP
  let k := b.types.length
  unless k ≥ 2 do throw "not a mutual block"
  for t in b.types do
    unless t.numNested == 0 do throw s!"nested member {t.cv.name} (B3)"
    unless !t.isReflexive do throw s!"reflexive member {t.cv.name}"
    unless t.cv.levelParams == lps && t.nP == nP do
      throw s!"member {t.cv.name}: level parameters or parameter count differ"
  let some (pbs, .sort u) := t0.cv.type.stripPis (nP + t0.nIdx)
    | throw s!"former {T} is not a telescope ending in a sort"
  let pbs := pbs.take nP
  for t in b.types do
    match t.cv.type.stripPis (nP + t.nIdx) with
    | some (pbs', .sort u') =>
      unless piBinders (pbs'.take nP) == piBinders pbs && u' == u do
        throw s!"member {t.cv.name}: parameter telescope or sort differs from {T}'s"
    | _ => throw s!"former {t.cv.name} is not a telescope ending in a sort"
  let memberNames := b.types.map (·.cv.name)
  let members : List (Name × Nat × Nat) :=
    (List.range k).map fun m => (memberNames.getD m .anonymous, m, (b.types.getD m default).nIdx)
  let nIdxOf : Nat → Nat := fun m => (b.types.getD m default).nIdx
  -- the constructors, per member, classified
  let mut mctors : List MCtor := []
  for m in List.range k do
    let t := b.types.getD m default
    for cn in t.ctors do
      let some c := b.ctors.find? (·.cv.name == cn)
        | throw s!"constructor {cn} of {t.cv.name} is not in the block"
      unless c.nP == nP && c.cv.levelParams == lps do
        throw s!"constructor {cn}: parameter count or level parameters differ"
      mctors := mctors ++ [← classifyCtor members lps nP m c]
  let n := mctors.length
  unless b.ctors.length == n do throw "constructors not all owned by a member"
  -- the recursors: `T_m.rec`, one per member, `k` motives, `n` minors,
  -- no indices, one eliminator shape
  unless b.recs.length == k do throw "recursor count differs from member count"
  -- the member's recursor, by name (the export's `recs` order is not
  -- the members' in general)
  let recOf : Nat → Except String IndRecRec := fun m => do
    let t := b.types.getD m default
    match b.recs.find? (·.cv.name == t.cv.name.str "rec") with
    | some r => pure r
    | none => throw s!"member {t.cv.name} has no recursor {t.cv.name.str "rec"}"
  let large? : Option Name :=
    match (← recOf 0).cv.levelParams with
    | e :: rest => if rest == lps && !lps.contains e then some e else none
    | [] => none
  let large := large?.isSome
  let elim := large?.getD (freshLevelName lps)
  let rlps := if large then elim :: lps else lps
  for m in List.range k do
    let r ← recOf m
    unless r.nP == nP && r.nM == k && r.nm == n && r.nI == nIdxOf m do
      throw s!"recursor {r.cv.name}: unexpected telescope"
    unless r.cv.levelParams == rlps do throw s!"recursor {r.cv.name}: eliminator shape differs"
    let own := mctors.filter (·.m == m)
    unless r.rules.length == own.length &&
        (List.range own.length).all (fun j =>
          (r.rules.getD j default).ctor == (own.getD j default).c.cv.name) do
      throw s!"recursor {r.cv.name}: rules do not list the member's constructors"
  let isProp := Level.isEquiv u .zero == some true
  if isProp && large then
    throw "Prop block with a large eliminator (the auxiliary family eliminates into Prop only)"
  let ℓ := directElimLevel elim large
  let rlvls : List Level := if large then ℓ :: lps.map .param else lps.map .param
  let elimTag := if large then elim else freshLevelName lps
  -- the block renaming of the modeled install (types, constructors, recursors)
  let blockNames := memberNames ++ b.ctors.map (·.cv.name) ++ b.recs.map (·.cv.name)
  let rn : Expr → Expr := Expr.renameConsts fun x =>
    if blockNames.contains x then modelName x else x
  let tag := tagName T
  let aux := auxName T
  let ps0 := varsAt 0 nP
  let mut out : Array DeclC := #[]
  let mut heights : List (Name × Nat) := []
  let hOf : List (Name × Nat) → Name → Nat := fun hs x =>
    match hs.find? (·.1 == x) with
    | some (_, h) => h
    | none => ctx.heights x
  -- 1. the tag block: `tag : ∀ p⃗, Sort W`, `tag.m : ∀ p⃗ ı⃗_m, tag p⃗`
  -- with `W = max 1 (the sorts of the index domains)` (B2; `Type` at an
  -- index-free block)
  let mut W : Level := .succ .zero
  for t in b.types do
    let some (ibs, _) := t.cv.type.stripPis (nP + t.nIdx) | throw "unreachable"
    for j in List.range t.nIdx do
      let ctxJ := ((ibs.take (nP + j)).map (·.1)).reverse
      let dom := (ibs.getD (nP + j) default).1
      let some ℓj := sortOf ctx.tbl ctxJ dom
        | throw s!"cannot infer the sort of index {j} of {t.cv.name} (the tag's universe)"
      W := .max W ℓj
  let tagTy ← need "tag type" (Expr.replacePiBody nP t0.cv.type (.sort W))
  let tagCtors : List (Name × Nat × Expr × List Nat) ←
    (List.range k).mapM fun m => do
      let t := b.types.getD m default
      let ty ← need "tag constructor type"
        (Expr.replacePiBody (nP + t.nIdx) t.cv.type
          (Expr.mkAppN (constP tag lps) (varsAt t.nIdx nP)))
      pure (tagCtorName T m, t.nIdx, ty, [])
  let tagRecTy ← need "tag recursor type" (recTy tag lps elimTag true nP 0 tagTy tagCtors)
  let tagRules ← (List.range k).mapM fun m => do
    let rhs ← need "tag rule"
      (recRhs tag lps elimTag true nP 0 tagTy tagCtors (tag.str "rec") (.param elimTag :: lps.map .param) m)
    pure (RecRule.mk (tagCtorName T m) (nIdxOf m) 0 .inert rhs)
  out := out.push (.indDecl
    ([.indInfo ⟨tag, lps, tagTy⟩ {}] ++
     tagCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
     [.recInfo ⟨tag.str "rec", elimTag :: lps, tagRecTy⟩ (nP + 1 + k) (nP + 1 + k) tagRules]))
  -- 2. the auxiliary family
  let auxTy ← need "aux type" (Expr.replacePiBody nP t0.cv.type
    (.forallE (Expr.mkAppN (constP tag lps) ps0) (.sort u) bm))
  let auxCtors : List (Name × Nat × Expr × List Nat) := mctors.map fun mc =>
    (auxCtorName T mc.m mc.c.cv.name, mc.c.nF, specFam T lps nP members mc.c.cv.type,
     mc.recFields.map (·.1))
  let auxRecTy ← need "aux recursor type" (recTy aux lps elim large nP 1 auxTy auxCtors)
  let auxRules ← (List.range n).mapM fun j => do
    let rhs ← need "aux rule"
      (recRhs aux lps elim large nP 1 auxTy auxCtors (aux.str "rec") rlvls j)
    pure (RecRule.mk (auxCtors.getD j default).1 (auxCtors.getD j default).2.1 0 .inert rhs)
  out := out.push (.indDecl
    ([.indInfo ⟨aux, lps, auxTy⟩ {}] ++
     auxCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
     [.recInfo ⟨aux.str "rec", rlps, auxRecTy⟩ (nP + 1 + n + 1) (nP + 1 + n) auxRules]))
  -- 3. the member models `T_m._model := λ p⃗ ı⃗, aux p⃗ (tag.m p⃗ ı⃗)`
  for m in List.range k do
    let t := b.types.getD m default
    let nI := t.nIdx
    let value ← need "member model" (Expr.pisToLams (nP + nI) t.cv.type
      (Expr.mkAppN (constP aux lps) (varsAt nI nP ++
        [Expr.mkAppN (constP (tagCtorName T m) lps) (varsAt nI nP ++ varsAt 0 nI)])))
    let h := hintFor (hOf heights) value
    heights := (modelName t.cv.name, hintHeight h) :: heights
    out := out.push (.defnDecl ⟨modelName t.cv.name, lps, t.cv.type⟩ value h)
  -- 4. the constructor models `C._model := λ p⃗ f⃗, aux.m.C p⃗ f⃗`
  for mc in mctors do
    let nF := mc.c.nF
    let ty := rn mc.c.cv.type
    let value ← need "constructor model" (Expr.pisToLams (nP + nF) ty
      (Expr.mkAppN (constP (auxCtorName T mc.m mc.c.cv.name) lps)
        (varsAt nF nP ++ (List.range nF).map fun i => Expr.bvar (nF - 1 - i))))
    let h := hintFor (hOf heights) value
    heights := (modelName mc.c.cv.name, hintHeight h) :: heights
    out := out.push (.defnDecl ⟨modelName mc.c.cv.name, lps, ty⟩ value h)
  -- 5. the recursor models
  let rP := nP + k + n
  let ℓ' : Level := .imax u (.succ ℓ)
  for m in List.range k do
    let r ← recOf m
    let ty := rn r.cv.type
    let nI := nIdxOf m
    -- the body frame: `p⃗ M⃗ S⃗ ı⃗ t` — `rP + nI + 1` binders
    let D := rP + nI + 1
    let e := nI + 1
    -- `Mot := λ (i : tag p⃗) (s : aux p⃗ i), tag.rec p⃗ (λ i', ∀ s, aux p⃗ i' → Sort ℓ) M⃗ i s`
    let motTag : Expr := .lam
      (Expr.mkAppN (constP tag lps) (varsAt (k + n + e + 2) nP))
      (.forallE
        (Expr.mkAppN (constP aux lps) (varsAt (k + n + e + 3) nP ++ [.bvar 0])) (.sort ℓ) bm) bm
    let tagRecApp := Expr.mkAppN (.const (tag.str "rec") (ℓ' :: lps.map .param))
      (varsAt (k + n + e + 2) nP ++ [motTag] ++ varsAt (n + e + 2) k ++ [.bvar 1, .bvar 0])
    let mot : Expr := .lam
      (Expr.mkAppN (constP tag lps) (varsAt (k + n + e) nP))
      (.lam
        (Expr.mkAppN (constP aux lps) (varsAt (k + n + e + 1) nP ++ [.bvar 0])) tagRecApp bm) bm
    let body := Expr.mkAppN (.const (aux.str "rec") rlvls)
      (varsAt (k + n + e) nP ++ [mot] ++ varsAt e n ++
       [Expr.mkAppN (constP (tagCtorName T m) lps) (varsAt (k + n + e) nP ++ varsAt 1 nI),
        .bvar 0])
    let value ← need "recursor model" (Expr.pisToLams D ty body)
    let h := hintFor (hOf heights) value
    heights := (modelName r.cv.name, hintHeight h) :: heights
    out := out.push (.defnDecl ⟨modelName r.cv.name, rlps, ty⟩ value h)
  -- 6. the iota theorems, by `Eq.refl`
  for m in List.range k do
    let r ← recOf m
    let some (prefixBs, _) := (rn r.cv.type).stripPis rP
      | throw s!"recursor {r.cv.name}: type is not the expected telescope"
    let own := mctors.filter (·.m == m)
    for j in List.range own.length do
      let mc := own.getD j default
      let nF := mc.c.nF
      -- the constructor's global minor index
      let J := (mctors.findIdx? (·.c.cv.name == mc.c.cv.name)).getD 0
      let some (_, ctele) := (rn mc.c.cv.type).stripPis nP
        | throw s!"constructor {mc.c.cv.name}: type is not a telescope"
      -- the field telescope at the statement frame: the parameters
      -- sit above the `k + n` motive and minor binders
      let some (fieldBs, cresid) := (ctele.liftLooseBVars (k + n) 0).stripPis nF
        | throw s!"constructor {mc.c.cv.name}: field telescope"
      let doms := fieldBs.map (·.1)
      let fields := (List.range nF).map fun i => Expr.bvar (nF - 1 - i)
      let prefixVars := varsAt (nF + k + n) nP ++ varsAt (nF + n) k ++ varsAt nF n
      let ctorApp := Expr.mkAppN (constP (modelName mc.c.cv.name) lps) (varsAt (nF + k + n) nP ++ fields)
      -- the constructor's index expressions, at the statement frame
      let idxC := cresid.getAppArgs.drop nP
      let α : Expr := Expr.mkAppN (.bvar (nF + n + k - 1 - m)) (idxC ++ [ctorApp])
      let lhs := Expr.mkAppN (.const (modelName r.cv.name) rlvls) (prefixVars ++ idxC ++ [ctorApp])
      let rhs := Expr.mkAppN (.bvar (nF + n - 1 - J))
        (fields ++ mc.recFields.map fun (i, tgt) =>
          -- the recursive field's index expressions, lifted from its
          -- binder to the statement frame
          let idxI := ((doms.getD i default).liftLooseBVars (nF - i) 0).getAppArgs.drop nP
          Expr.mkAppN (.const (modelName ((memberNames.getD tgt .anonymous).str "rec")) rlvls)
            (prefixVars ++ idxI ++ [.bvar (nF - 1 - i)]))
      let stmt := mkPis (piBinders prefixBs ++ piBinders fieldBs)
        (Expr.mkAppN (.const eqName [ℓ]) [α, lhs, rhs])
      let value ← need "iota proof" (Expr.pisToLams (rP + nF) stmt
        (Expr.mkAppN (.const eqReflName [ℓ]) [α, lhs]))
      out := out.push (.thmDecl ⟨iotaName r.cv.name j, rlps, stmt⟩ value)
  -- 7. projection artifacts of structure-like non-`Prop` members
  let genTypes : List (Name × List Name × Expr) :=
    (b.types.map fun t => (modelName t.cv.name, lps, t.cv.type)) ++
    (b.ctors.map fun c => (modelName c.cv.name, lps, rn c.cv.type))
  let tbl' : ConstTable := fun x =>
    match genTypes.find? (·.1 == x) with
    | some (_, l, ty) => some (l, ty)
    | none => ctx.tbl x
  if !isProp then
    for m in List.range k do
      let t := b.types.getD m default
      let own := mctors.filter (·.m == m)
      let [mc] := own | continue
      if t.nIdx != 0 then continue
      let nF := mc.c.nF
      let cty := rn mc.c.cv.type
      let r ← recOf m
      let owner : ProjRecOwner :=
        ⟨modelName t.cv.name, lps, nP, modelName mc.c.cv.name, nF, modelName r.cv.name,
         rlps, rn r.cv.type, k, n⟩
      let some (cbs, _) := cty.stripPis (nP + nF) | continue
      let mut stop := false
      for i in List.range nF do
        if stop then continue
        -- the field's sort, at the constructor frame
        let ctxI := ((cbs.take (nP + i)).map (·.1)).reverse
        let dom := (cbs.getD (nP + i) default).1
        let some ℓi := sortOf tbl' ctxI dom | stop := true; continue
        -- the projection type `∀ p⃗ (x : T._model p⃗), F_i[f_j := proj_j p⃗ x]`
        let args := directProjPs nP ++ (List.range i).map fun j =>
          Expr.mkAppN (constP (projModelName t.cv.name j) lps) (directProjPs nP ++ [.bvar 0])
        let some (.forallE fdom _ _) := Expr.instPisAtLift args cty | stop := true; continue
        let some pty := Expr.replacePiBody nP t.cv.type
            (.forallE
              (Expr.mkAppN (constP (modelName t.cv.name) lps) ps0) fdom bm)
          | stop := true; continue
        let some (pbs', _) := pty.stripPis (nP + 1) | stop := true; continue
        let dummy := mkLams (piBinders pbs') (.proj (modelName t.cv.name) i (.bvar 0))
        let some pval := projRecValue owner ℓi pty dummy i | stop := true; continue
        let h := hintFor (hOf heights) pval
        heights := (projModelName t.cv.name i, hintHeight h) :: heights
        out := out.push (.defnDecl ⟨projModelName t.cv.name i, lps, pty⟩ pval h)
        -- `proj_i.iota : ∀ p⃗ f⃗, proj_i p⃗ (C._model p⃗ f⃗) = f_i`
        let fields := (List.range nF).map fun l => Expr.bvar (nF - 1 - l)
        let slot := dom.liftLooseBVars (nF - i) 0
        let lhs := Expr.mkAppN (constP (projModelName t.cv.name i) lps)
          (varsAt nF nP ++ [Expr.mkAppN (constP (modelName mc.c.cv.name) lps) (varsAt nF nP ++ fields)])
        let stmt := mkPis (piBinders cbs)
          (Expr.mkAppN (.const eqName [ℓi]) [slot, lhs, .bvar (nF - 1 - i)])
        let some pf := Expr.pisToLams (nP + nF) stmt
            (Expr.mkAppN (.const eqReflName [ℓi]) [slot, .bvar (nF - 1 - i)])
          | stop := true; continue
        out := out.push (.thmDecl ⟨(projModelName t.cv.name i).str "iota", lps, stmt⟩ pf)
  pure out.toList

end Lech.Frontend.InModel
