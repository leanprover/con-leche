module

public import ConLeche.Kernel.Inductives.NativeInstall
public import ConLeche.Kernel.Inductives.MutualParts

@[expose] public section

/-!
# The mutual install: the reduction to the fixpoint route, inside (task #278)

A mutual block `T_1 … T_k` (`mutualParts?`,
`ConLeche/Kernel/Inductives/MutualParts.lean`) is installed by REDUCING
it to one tagged family and checking the block's own constants against
that family — inside this install, in a scaffolding environment that
is discarded:

1. **the formers**, each checked and read at official's telescope
   (`checkSumTele`, task #195), then official's cross-member checks
   (`check_inductive_types`): the parameter domains definitionally
   the first former's, the result sorts equivalent, the level
   parameters the block's;
2. **the eliminator**: a mutual block whose sort is not provably
   nonzero eliminates into `Prop` only (`elim_only_at_universe_zero`);
   the stream's recursors must carry the generated level parameters
   (official's replay: "Invalid recursor");
3. **the scaffold**, built over the checked formers at fresh names
   (`mutualScaffoldFresh`): the tag family `tag : Π p⃗, Sort W`, one
   constructor per member carrying that member's index telescope
   (`W` above every index domain's sort, read with the checker), and
   the auxiliary family `aux : Π p⃗ (t : tag p⃗), Sort u` whose
   constructors are the block's with every member occurrence
   `T_{m'} p⃗ e⃗` rewritten to `aux p⃗ (tag.m' p⃗ e⃗)` (`MutualKit.specFam`)
   — both installed through the fixpoint route (`checkNative`), which
   runs official's positivity, universe and index checks on them (the
   rewritten constructor is positive exactly when the member's is);
4. **the block's own constants as definitions** under their own names
   and types: `T_m := λ p⃗ ı⃗, aux p⃗ (tag.m p⃗ ı⃗)`, `C := λ p⃗ f⃗, aux.J p⃗ f⃗`,
   `T_m.rec := λ p⃗ motive⃗ minor⃗ ı⃗ t, aux.rec p⃗ Mot minor⃗ (tag.m p⃗ ı⃗) t`
   with `Mot` dispatching on the tag by `tag.rec`, each through the
   ordinary definition check (`checkDefnVal`) — so a member's
   parameter telescope or sort that is NOT the first's makes its
   definition ill-typed and REJECTS, as official does; the recursor's
   type is the GENERATED one (`mutualRecTy`, official's `mk_rec_infos`
   with `k` motives) and the stream's recursor type is compared with
   it by one `isDefEq`;
5. **the rules**: generated (`mutualRecRhs`, official's
   `mk_rec_rules`), compared with the stream's structurally
   (`mutualRulesOk`), and each CERTIFIED at the scaffold by one
   `isDefEq` of `T_m.rec p⃗ motive⃗ minor⃗ e⃗ (C p⃗ f⃗)` against the rule's
   applied right-hand side (β/δ/ι through the definitions);
6. **the stored block**: the formers as inductives, the constructors,
   the recursors with the generated rules — official's shapes, with
   official's capabilities (none: K never fires on a mutual block,
   η/unit-likeness are the projection story's, M4).  The scaffold and
   the definitions are not stored.

Every official check runs on the stream's records, and every check is
one the type checker makes on a term this install generated, so the
model tier's job is transport: the block's constants denote the
scaffold's fibres.  Verdicts: an official reject is `.invalid`; the one
residual class — a member mentioned other than as a plain member
application (`Id' (T_m p⃗)`), which the syntactic rewrite cannot see
through — is a positive decline; a generated term that fails its own
check is `.internal`.  The index-threaded twins are
`ConLeche/Kernel/Inductives/MutualInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The scaffold's names -/

/-- The scaffold's two families, at a freshening index. -/
structure MutualScaffold where
  tag : Name
  aux : Name
  deriving Repr, Inhabited

/-- The tag constructor of member `m`. -/
def MutualScaffold.tagCtor (sc : MutualScaffold) (m : Nat) : Name := sc.tag.num m
/-- The auxiliary constructor of the block's `J`-th constructor. -/
def MutualScaffold.auxCtor (sc : MutualScaffold) (J : Nat) : Name := sc.aux.num J
/-- The tag family's recursor. -/
def MutualScaffold.tagRec (sc : MutualScaffold) : Name := sc.tag.str "rec"
/-- The auxiliary family's recursor. -/
def MutualScaffold.auxRec (sc : MutualScaffold) : Name := sc.aux.str "rec"

/-- The scaffold names for the block owned by `T` at freshening index `i`. -/
def mutualScaffoldAt (T : Name) (i : Nat) : MutualScaffold :=
  let base := (T.str "_mutual").num i
  ⟨base.str "tag", base.str "aux"⟩

/-- Every name the scaffold at `sc` declares (`k` members, `n` constructors). -/
def MutualScaffold.names (sc : MutualScaffold) (k n : Nat) : List Name :=
  [sc.tag, sc.tagRec, sc.aux, sc.auxRec] ++
    (List.range k).map sc.tagCtor ++ (List.range n).map sc.auxCtor

/-- A scaffold none of whose names is in the environment: the
freshening index runs from `0`; an environment of `e` constants blocks
at most `e` indices, so `e + 1` attempts find one. -/
def mutualScaffoldFresh (find? : Name → Option ConstantInfo) (T : Name) (k n : Nat) :
    Nat → Nat → Option MutualScaffold
  | 0, _ => none
  | fuel + 1, i =>
    let sc := mutualScaffoldAt T i
    if (sc.names k n).all fun x => (find? x).isNone then some sc
    else mutualScaffoldFresh find? T k n fuel (i + 1)

/-! ## The checked formers and the scaffold blocks -/

/-- A former after its stage: the annotated, telescope-shaped constant,
its index count and its result sort. -/
structure MutualFormerA where
  cvTa : ConstantVal
  nIdx : Nat
  s : Level
  deriving Repr, Inhabited

/-- **The tag block** over the first former's parameter telescope:
`tag : Π p⃗, Sort W`, `tag.m : Π p⃗ ı⃗_m, tag p⃗` (member `m`'s index
telescope re-spelled over the first former's parameters,
`overFirstParams`), and its large-eliminating recursor generated by
the fixpoint route's own generators (the block is non-recursive: the
constant-functor arm). -/
def mutualTagBlock (sc : MutualScaffold) (lps : List Name) (nP : Nat) (W : Level)
    (elimTag : Name) (fms : List MutualFormerA) : Option (List ConstantInfo) := do
  let f₀ ← fms[0]?
  let k := fms.length
  let tagTy ← Expr.replacePiBody nP f₀.cvTa.type (.sort W)
  let tagCtors ← fms.zipIdx.mapM fun (f, mIdx) => do
    let ty' ← MutualKit.overFirstParams nP f₀.cvTa.type f.cvTa.type
    let ty ← Expr.replacePiBody (nP + f.nIdx) ty'
      (Expr.mkAppN (MutualKit.constP sc.tag lps) (MutualKit.varsAt f.nIdx nP))
    pure (sc.tagCtor mIdx, f.nIdx, ty, ([] : List Nat))
  let tagRecTy ← structRecTyR sc.tag lps elimTag true nP 0 tagTy tagCtors
  let rules ← (List.range k).mapM fun mIdx => do
    let rhs ← structRecRhsR sc.tag lps elimTag true nP 0 tagTy tagCtors sc.tagRec
      (.param elimTag :: lps.map .param) mIdx
    pure (RecRule.mk (sc.tagCtor mIdx) (fms.getD mIdx default).nIdx 0 .inert rhs false false false)
  pure ([ConstantInfo.indInfo ⟨sc.tag, lps, tagTy⟩ {}] ++
    tagCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
    [ConstantInfo.recInfo ⟨sc.tagRec, elimTag :: lps, tagRecTy⟩ (nP + 1 + k) (nP + 1 + k) rules])

/-- **The auxiliary block** over the first former's parameter
telescope: `aux : Π p⃗ (t : tag p⃗), Sort u`, one constructor per
constructor of the block with every member occurrence rewritten to
the family at its tag (`specFam`; the caller has checked that nothing
of the block remains), and its recursor at the block's eliminator
generated by the fixpoint route's own generators (the recursive
positions classified as that route classifies them, so the record is
the one it regenerates). -/
def mutualAuxBlock (sc : MutualScaffold) (lps : List Name) (nP : Nat) (u : Level)
    (elim : Name) (large : Bool) (f₀ : MutualFormerA) (members : List (Name × Nat × Nat))
    (ctors : List MutualCtor) : Option (List ConstantInfo) := do
  let n := ctors.length
  let rlps := if large then elim :: lps else lps
  let auxTy ← Expr.replacePiBody nP f₀.cvTa.type
    (.forallE (Expr.mkAppN (MutualKit.constP sc.tag lps) (MutualKit.varsAt 0 nP)) (.sort u)
      MutualKit.bm)
  let auxCtors ← ctors.zipIdx.mapM fun (c, J) => do
    let ty ← MutualKit.overFirstParams nP f₀.cvTa.type
      (MutualKit.specFam sc.aux sc.tagCtor lps nP members c.cv.type)
    let ks ← recCtorKinds sc.aux lps nP 1 (⟨sc.auxCtor J, lps, ty⟩, c.nF)
    pure (sc.auxCtor J, c.nF, ty, recIdxOf ks)
  let auxRecTy ← structRecTyR sc.aux lps elim large nP 1 auxTy auxCtors
  let rules ← (List.range n).mapM fun J => do
    let rhs ← structRecRhsR sc.aux lps elim large nP 1 auxTy auxCtors sc.auxRec
      (rlps.map .param) J
    pure (RecRule.mk (sc.auxCtor J) (ctors.getD J default).nF 0 .inert rhs false false false)
  pure ([ConstantInfo.indInfo ⟨sc.aux, lps, auxTy⟩ {}] ++
    auxCtors.map (fun (c, nF, ty, _) => ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) ++
    [ConstantInfo.recInfo ⟨sc.auxRec, rlps, auxRecTy⟩ (nP + 1 + n + 1) (nP + 1 + n) rules])

/-! ## The block's constants over the scaffold -/

/-- Member `m`'s value: `λ p⃗ ı⃗_m, aux p⃗ (tag.m p⃗ ı⃗_m)` over its own
telescope. -/
def mutualFormerValue (sc : MutualScaffold) (lps : List Name) (nP : Nat) (mIdx : Nat)
    (f : MutualFormerA) : Option Expr :=
  Expr.pisToLams (nP + f.nIdx) f.cvTa.type
    (Expr.mkAppN (MutualKit.constP sc.aux lps) (MutualKit.varsAt f.nIdx nP ++
      [Expr.mkAppN (MutualKit.constP (sc.tagCtor mIdx) lps)
        (MutualKit.varsAt f.nIdx nP ++ MutualKit.varsAt 0 f.nIdx)]))

/-- Constructor `J`'s value: `λ p⃗ f⃗, aux.J p⃗ f⃗` over its own
telescope. -/
def mutualCtorValue (sc : MutualScaffold) (lps : List Name) (nP : Nat) (J : Nat)
    (c : MutualCtor) : Option Expr :=
  Expr.pisToLams (nP + c.nF) c.cv.type
    (Expr.mkAppN (MutualKit.constP (sc.auxCtor J) lps)
      (MutualKit.varsAt c.nF nP ++ (List.range c.nF).map fun i => Expr.bvar (c.nF - 1 - i)))

/-- Member `m`'s recursor's value over the generated type `recTy`:

    λ p⃗ motive⃗ minor⃗ ı⃗ t, aux.rec p⃗ Mot minor⃗ (tag.m p⃗ ı⃗) t
    Mot := λ (i : tag p⃗) (s : aux p⃗ i),
             tag.rec.{imax u (ℓ+1)} p⃗ (λ i', Π s, aux p⃗ i' → Sort ℓ) motive⃗ i s

— the minors pass through unchanged, since `Mot (tag.m' p⃗ e⃗) x` is
`motive_{m'} e⃗ x` by β and the tag's iota, and `aux.J p⃗ f⃗` is
`C p⃗ f⃗` by δ. -/
def mutualRecValue (sc : MutualScaffold) (lps : List Name) (rlvls : List Level) (u ℓ : Level)
    (nP k n mIdx nI : Nat) (recTy : Expr) : Option Expr :=
  let bm := MutualKit.bm
  let rP := nP + k + n
  let D := rP + nI + 1
  let e := nI + 1
  let ℓ' : Level := .imax u (.succ ℓ)
  let motTag : Expr := .lam
    (Expr.mkAppN (MutualKit.constP sc.tag lps) (MutualKit.varsAt (k + n + e + 2) nP))
    (.forallE
      (Expr.mkAppN (MutualKit.constP sc.aux lps) (MutualKit.varsAt (k + n + e + 3) nP ++ [.bvar 0]))
      (.sort ℓ) bm) bm
  let tagRecApp := Expr.mkAppN (.const sc.tagRec (ℓ' :: lps.map .param))
    (MutualKit.varsAt (k + n + e + 2) nP ++ [motTag] ++ MutualKit.varsAt (n + e + 2) k ++
      [.bvar 1, .bvar 0])
  let mot : Expr := .lam
    (Expr.mkAppN (MutualKit.constP sc.tag lps) (MutualKit.varsAt (k + n + e) nP))
    (.lam
      (Expr.mkAppN (MutualKit.constP sc.aux lps) (MutualKit.varsAt (k + n + e + 1) nP ++ [.bvar 0]))
      tagRecApp bm) bm
  let body := Expr.mkAppN (.const sc.auxRec rlvls)
    (MutualKit.varsAt (k + n + e) nP ++ [mot] ++ MutualKit.varsAt e n ++
     [Expr.mkAppN (MutualKit.constP (sc.tagCtor mIdx) lps)
        (MutualKit.varsAt (k + n + e) nP ++ MutualKit.varsAt 1 nI),
      .bvar 0])
  Expr.pisToLams D recTy body

/-- The recursive fields of a constructor, off its (annotated) type:
field `i` targets member `m'` when its domain is `Π a⃗, T_{m'} p⃗ e⃗` at
the block's own parameters and member `m'`'s index count (what the
inductive hypotheses of the generated recursor bind; whether every
other occurrence is legal is the auxiliary family's install's
verdict). -/
def mutualRecFields (memberNames : List Name) (nIdxOf : Nat → Nat) (lps : List Name)
    (nP nF : Nat) (cty : Expr) : List (Nat × Nat) :=
  match cty.stripPis (nP + nF) with
  | some (cbs, _) =>
    (List.range nF).filterMap fun i =>
      let (tele, body) := (cbs.getD (nP + i) default).1.piBinders
      match body.getAppFn with
      | .const T us =>
        match memberNames.idxOf? T with
        | some m' =>
          if us == lps.map .param && body.getAppArgs.length == nP + nIdxOf m' &&
              body.getAppArgs.take nP == structPsAt (i + tele.length) nP
          then some (i, m') else none
        | none => none
      | _ => none
  | none => []

/-- The constructors' members are non-decreasing in block order (the
parser lists the constructors member by member; a constructor whose
result names a member other than the one it is listed under is
official's "invalid return type"). -/
def mutualCtorsGrouped : List MutualCtor → Bool
  | [] => true
  | [_] => true
  | c :: c' :: cs => c.member ≤ c'.member && mutualCtorsGrouped (c' :: cs)

/-- Official's `check_inductive_types` parameter check: member `m`'s
parameter domains, opened at variables, are definitionally the first
former's (`checkStructDomsAt` with official's verdict). -/
def mutualDomsOk (ops : CheckerOps m) (env : Env) (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "mutual: parameter index")
    let b ← unwrapOr doms[j]? (.internal "mutual: parameter index")
    unless ← ops.isDefEq env j a.fvarTypeD b do
      throw (.invalid "mutual: parameters of all inductive datatypes must match")
    mutualDomsOk ops env fvs doms j

/-- The sorts of a former's index domains at its opened telescope
(`checkStructFieldSortsI`'s reading, no bound), joined into `W`. -/
def mutualIdxSorts (ops : CheckerOps m) (env : Env) (nP : Nat) (fvs : List Expr) :
    Nat → Level → m Level
  | 0, W => pure W
  | j + 1, W => do
    let fv ← unwrapOr fvs[nP + j]? (.internal "mutual: index binder")
    let ty ← ops.inferType env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort env (nP + j) ty
    mutualIdxSorts ops env nP fvs j (.max W u)

/-- **One generated rule, certified at the scaffold**: the recursor at
the opened prefix variables, the constructor's index expressions and
the constructor at the parameter and field variables, against the
rule's right-hand side applied to the same variables — one `isDefEq`
at the depth of the opened telescope. -/
def mutualCertifyRule (ops : CheckerOps m) (env : Env) (recC : Name) (rlvls : List Level)
    (recTy : Expr) (C : Name) (lps : List Name) (cty : Expr) (nP k n nF : Nat) (rhs : Expr) :
    m Unit := do
  let (fvsP, _) ← unwrapOr (openPisAtFvars (nP + k + n) recTy 0)
    (.internal "mutual: recursor telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsP.take nP) cty)
    (.internal "mutual: constructor telescope")
  let (xFvs, cres) ← unwrapOr (openPisAtFvars nF crest (nP + k + n))
    (.internal "mutual: constructor field telescope")
  let depth := nP + k + n + nF
  let lhs := Expr.mkAppN (.const recC rlvls)
    (fvsP ++ cres.getAppArgs.drop nP ++
      [Expr.mkAppN (.const C (lps.map .param)) (fvsP.take nP ++ xFvs)])
  let (_, rbody) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvs) rhs)
    (.internal "mutual: rule prefix")
  let lhsA ← ops.annotate env depth lhs
  let rhsA ← ops.annotate env depth rbody
  unless ← ops.isDefEq env depth lhsA rhsA do
    throw (.internal s!"mutual: the generated rule of {C} does not certify")

/-- The stored rules of a recursor: the generated right-hand sides
with the rescue bits read off the block's store (`sumRules`'
arrangement), `paramsBlind` unset — the law certified above is a
λ-equality over one parameter spine. -/
def mutualRules (find? : Name → Option ConstantInfo) (recName : Name) (nP mI rP : Nat)
    (recTy : Expr) : List (MutualCtor × Expr) → List RecRule
  | [] => []
  | (c, rhs) :: rest =>
    recRuleBits find? recName
      { ctor := c.cv.name, nfields := c.nF, ctorParams := nP,
        fire := if Expr.recRulePlain recTy mI rP nP then .plain else .inert,
        rhs := rhs, paramsBlind := false }
      :: mutualRules find? recName nP mI rP recTy rest

/-- The block's constants installed as DEFINITIONS at the scaffold —
one ordinary definition check each (`checkConstantVal` then
`checkDefnVal`), the hint by the kernel's height rule. -/
def mutualDefine (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (value : Expr) :
    m (Env × ConstantVal) := do
  let cvA ← checkConstantVal ops env cv
  let env' ← checkDefnVal ops env cvA value
    (MutualKit.hintFor (MutualKit.heightOf env.find?) value)
  pure (env', cvA)

/-- Check and install a **mutual block** (see the module docstring). -/
def checkMutual (ops : CheckerOps m) (env : Env) (p : MutualParts) : m Env := do
  let k := p.k
  let n := p.n
  let nP := p.nP
  let lps := p.lps
  -- 0. the block's shape: official's rejects
  unless p.blockNames.Nodup do
    throw (.invalid "mutual: duplicate declaration in the block")
  unless p.members.all (fun mb => mb.cv.levelParams == lps) &&
      p.ctors.all (fun c => c.cv.levelParams == lps) do
    throw (.invalid "mutual: the block's members do not share its level parameters")
  unless p.ctors.all (fun c => c.member < k) do
    throw (.invalid "mutual: invalid constructor return type")
  unless mutualCtorsGrouped p.ctors do
    throw (.invalid "mutual: a constructor returns a member other than the one it is \
      listed under")
  -- 1. the formers, at official's telescope
  let fms ← p.members.mapM fun mb => do
    let cvTa₀ ← checkConstantVal ops env mb.cv
    let (cvTa, s) ← checkSumTele ops env mb.cv (nP + mb.nIdx) cvTa₀
    pure (⟨cvTa, mb.nIdx, s⟩ : MutualFormerA)
  let f₀ ← unwrapOr fms[0]? (.internal "mutual: no member")
  -- 2. official's cross-member checks: the parameter domains, the sorts
  let tq₀ ← unwrapOr (openPisAtFvars nP f₀.cvTa.type 0) (.internal "mutual: former telescope")
  for f in fms do
    unless ← liftFueled "level comparison" (Level.isEquiv f.s f₀.s) do
      throw (.invalid "mutual: mutually inductive types must live in the same universe")
    let tq ← unwrapOr (openPisAtFvars nP f.cvTa.type 0) (.internal "mutual: former telescope")
    mutualDomsOk ops env tq.1 (tq₀.1.map Expr.fvarTypeD) nP
  -- 3. the eliminator (official's `elim_only_at_universe_zero` at a
  -- mutual block) and the recursor records' pins
  unless p.large == f₀.s.isNeverZero do
    throw (.invalid "mutual: the recursors' level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "mutual: a recursor record is not the generated recursor")
  -- 4. the constructors' and recursors' types mention nothing beyond the
  -- environment and the block itself (they are checked at the scaffold
  -- below, which holds more)
  let envN : Env := ⟨(p.members.map fun mb => ConstantInfo.indInfo mb.cv {}) ++ env.consts⟩
  for c in p.ctors do
    unless c.cv.type.constsResolve envN do
      throw (.invalid s!"unknown constant in type of {c.cv.name}")
  let envR : Env :=
    ⟨(p.members.map fun mb => ConstantInfo.recInfo mb.cvR mb.mI mb.rP []) ++ envN.consts⟩
  for mb in p.members do
    unless mb.cvR.type.constsResolve envR do
      throw (.invalid s!"unknown constant in type of {mb.cvR.name}")
    for r in mb.rules do
      unless r.rhs.constsResolve envR do
        throw (.invalid s!"unknown constant in a rule of {mb.cvR.name}")
  -- 5. the residual: a member mentioned other than as a plain member
  -- application (nested, or under a redex the syntactic rewrite cannot
  -- see through) is a positive decline
  let memberNames := p.memberNames
  let members : List (Name × Nat × Nat) :=
    p.members.zipIdx.map fun (mb, mIdx) => (mb.cv.name, mIdx, mb.nIdx)
  let nIdxOf : Nat → Nat := fun mIdx => (p.members.getD mIdx default).nIdx
  -- the scaffold names, fresh in the environment
  let sc ← unwrapOr (mutualScaffoldFresh env.find? f₀.cvTa.name k n (env.consts.length + 2) 0)
    (.internal "mutual: no fresh scaffold name")
  for c in p.ctors do
    unless (c.cv.type.stripPis (nP + c.nF)).isSome do
      throw (.notImplemented s!"mutual: constructor telescope of {c.cv.name}")
    if MutualKit.mentionsAny memberNames
        (MutualKit.specFam sc.aux sc.tagCtor lps nP members c.cv.type) then
      throw (.notImplemented s!"mutual: a field of {c.cv.name} mentions the block other than \
        as a plain member application (nested, or under a redex)")
  -- 6. the tag's universe: above every index domain's sort
  let mut W : Level := .succ .zero
  for f in fms do
    let (tfvs, _) ← unwrapOr (openPisAtFvars (nP + f.nIdx) f.cvTa.type 0)
      (.internal "mutual: former telescope")
    W ← mutualIdxSorts ops env nP tfvs f.nIdx W
  -- 7. the scaffold: the tag family, then the auxiliary family, through
  -- the fixpoint route
  let elimTag := MutualKit.freshLevelName lps
  let tagBlock ← unwrapOr (mutualTagBlock sc lps nP W elimTag fms) (.internal "mutual: tag block")
  let pTag ← unwrapOr (nativeParts? nP tagBlock) (.internal "mutual: tag block shape")
  let envT ← checkNative ops env pTag
  let auxBlock ← unwrapOr
    (mutualAuxBlock sc lps nP f₀.s p.elim p.large f₀ members p.ctors)
    (.internal "mutual: auxiliary block")
  let pAux ← unwrapOr (nativeParts? nP auxBlock) (.internal "mutual: auxiliary block shape")
  let envA ← checkNative ops envT pAux
  -- 8. the block's constants as definitions at the scaffold
  let mut envS := envA
  for (f, mIdx) in fms.zipIdx do
    let value ← unwrapOr (mutualFormerValue sc lps nP mIdx f) (.internal "mutual: former value")
    let (envS', _) ← mutualDefine ops envS ⟨f.cvTa.name, lps, f.cvTa.type⟩ value
    envS := envS'
  let mut ctorsA : Array ConstantVal := #[]
  for (c, J) in p.ctors.zipIdx do
    let value ← unwrapOr (mutualCtorValue sc lps nP J c) (.internal "mutual: constructor value")
    let (envS', cvCa) ← mutualDefine ops envS c.cv value
    envS := envS'
    ctorsA := ctorsA.push cvCa
  let formers4 : List MutualFormer := fms.map fun f => ⟨f.cvTa.name, f.nIdx, f.cvTa.type⟩
  let ctors4 : List MutualCtor4 := (p.ctors.zip ctorsA.toList).map fun (c, cvCa) =>
    ⟨c.cv.name, c.nF, cvCa.type, c.member,
      mutualRecFields memberNames nIdxOf lps nP c.nF cvCa.type⟩
  let rlvls := p.rlps.map Level.param
  let ℓ := p.elimLevel
  let recOf : Nat → Name := fun mIdx => (p.members.getD mIdx default).cvR.name
  let mut recTys : Array Expr := #[]
  for (mb, mIdx) in p.members.zipIdx do
    let recTy ← unwrapOr (mutualRecTy lps p.elim p.large nP formers4 ctors4 mIdx)
      (.internal "mutual: recursor type")
    -- the stream's recursor is the generated one
    let cvRi ← checkConstantVal ops envS mb.cvR
    let cvRa ← checkConstantVal ops envS ⟨mb.cvR.name, p.rlps, recTy⟩
    unless ← ops.isDefEq envS 0 cvRi.type cvRa.type do
      throw (.invalid s!"mutual: the type of {mb.cvR.name} is not the generated one")
    let value ← unwrapOr (mutualRecValue sc lps rlvls f₀.s ℓ nP k n mIdx mb.nIdx cvRa.type)
      (.internal "mutual: recursor value")
    let envS' ← checkDefnVal ops envS cvRa value
      (MutualKit.hintFor (MutualKit.heightOf envS.find?) value)
    envS := envS'
    recTys := recTys.push cvRa.type
  -- 9. the rules: generated, compared with the stream's, certified
  let mut rulesOf : Array (List (MutualCtor × Expr)) := #[]
  for (mb, mIdx) in p.members.zipIdx do
    let own := p.ownCtors mIdx
    let recTy := recTys.getD mIdx default
    unless mutualRulesOk recOf rlvls nP k n ctors4 (own.map (·.1)) (mb.rules.map (·.rhs))
        mb.cvR.type do
      throw (.invalid s!"mutual: the rules of {mb.cvR.name} are not the generated ones")
    let mut rules : List (MutualCtor × Expr) := []
    for (J, c) in own do
      let rhs ← unwrapOr (mutualRecRhs lps p.elim p.large nP formers4 ctors4 recOf rlvls J)
        (.internal "mutual: recursor rule")
      let cvCa := ctorsA.getD J default
      mutualCertifyRule ops envS mb.cvR.name rlvls recTy c.cv.name lps cvCa.type nP k n c.nF rhs
      rules := rules ++ [(c, rhs)]
    rulesOf := rulesOf.push rules
  -- 10. the stored block: the formers, the constructors, the recursors
  -- as a group
  let envF₁ : Env := fms.foldl (fun e f => ⟨ConstantInfo.indInfo f.cvTa {} :: e.consts⟩) env
  let envF₂ : Env := (p.ctors.zip ctorsA.toList).foldl
    (fun e (c, cvCa) => ⟨ConstantInfo.ctorInfo cvCa nP c.nF :: e.consts⟩) envF₁
  let envF₃ : Env := (p.members.zipIdx).foldl
    (fun e (mb, mIdx) =>
      let recTy := recTys.getD mIdx default
      ⟨ConstantInfo.recInfo ⟨mb.cvR.name, p.rlps, recTy⟩ mb.mI mb.rP
        (mutualRules envF₂.find? mb.cvR.name nP mb.mI mb.rP recTy (rulesOf.getD mIdx []))
        :: e.consts⟩)
    envF₂
  pure envF₃

end ConLeche
