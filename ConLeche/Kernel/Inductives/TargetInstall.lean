module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Conformance.RecConformF

@[expose] public section

/-!
# The TARGET installer, run as a SHADOW (lane TSHADOW)

The maintainer's request (2026-09-23): write the target kernel now,
behind a flag, and run it beside today's install so that kernel
surprises show up before the proofs are written.  Three pieces, ONE
flag (`--target-shadow`, `Main.lean`), none of which changes a verdict:

1. **the target recursor check** (`targetRecCheck`,
   `ConLeche/Kernel/Inductives/RecCheck.lean`): primitive recursion
   with no field kinds and no target member, on the recursor FAMILY the
   stream installs with the block (nested auxiliaries included);
2. **`nestPos` on every block** (`nestedBlockPositivity`,
   `ConLeche/Kernel/Inductives/Positivity.lean`, called and not
   modified), compared field by field with today's classifier
   (`classifyBlockKinds`) on the same stored constructors;
3. **the target installer** (`targetShadow`): the uniform installer's
   stages (`checkBlockIndsF`, `checkBlockCtorsF`, `checkBlockIdxSortsF`,
   the elimination restriction, `checkBlockTablesF`) with `nestPos` in
   place of the classifier and (1) in place of `checkBlockRec`, run on
   EVERY block — nested ones included, which today go to the modelled
   route.  The pieces of today's installer that need field kinds and
   have no replacement from `nestPos`'s output are NOT run as gates here:
   the kinds re-check `blockFieldsOk` is measured on the side (`fields`)
   where `nestPos`'s kinds are expressible as `BlockFieldKind`s, and the
   conformance generator (`checkBlockRecConform`) is not run at all.

The report is one `TargetShadowReport` per block; `Main.lean` prints it
beside today's verdict and `tests/target-shadow.sh` compares.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A shadow stage's verdict: accepted, not reached (why), or the error
it threw. -/
inductive ShadowVerdict where
  | accept
  | skip (why : String)
  | fail (e : CheckError)
  deriving Repr, Inhabited

/-- The verdict word (`accept`/`reject`/`decline`/`error`/`skip`). -/
def ShadowVerdict.word : ShadowVerdict → String
  | .accept => "accept"
  | .skip _ => "skip"
  | .fail (.invalid _) => "reject"
  | .fail (.notImplemented _) => "decline"
  | .fail (.internal _) => "error"

/-- The verdict's message (empty at an accept). -/
def ShadowVerdict.msg : ShadowVerdict → String
  | .accept => ""
  | .skip why => why
  | .fail e => toString e

/-- Run a stage, catching its error. -/
def shadowTry {α : Type} (x : m α) : m (Except CheckError α) :=
  tryCatchThe CheckError (Except.ok <$> x) (fun e => pure (.error e))

/-- The verdict of a caught run. -/
def ShadowVerdict.ofExcept {α : Type} : Except CheckError α → ShadowVerdict
  | .ok _ => .accept
  | .error e => .fail e

/-- **What the shadow found at one block.** -/
structure TargetShadowReport where
  /-- the target installer, end to end (piece 3) -/
  install : ShadowVerdict := .skip "not run"
  /-- the target recursor check on the stream's family (piece 1) -/
  recCheck : ShadowVerdict := .skip "not reached"
  /-- `nestPos` on the stored constructors (piece 2) -/
  pos : ShadowVerdict := .skip "not reached"
  /-- today's classifier on the same constructors -/
  cls : ShadowVerdict := .skip "not reached"
  /-- the kinds compared, when both ran: `same`, `differ`, or `-` -/
  kinds : String := "-"
  /-- the first differing field, when `kinds = differ` -/
  kindsNote : String := ""
  /-- the reject-only conformance check (`checkBlockRecConformF`) at
  `nestPos`'s kinds, after (1); `n/a` where they are not expressible -/
  conf : ShadowVerdict := .skip "not reached"
  /-- today's kinds re-check (`blockFieldsOk`) at `nestPos`'s kinds:
  `ok`, `fail`, or `n/a` (a nested kind it cannot express) -/
  fields : String := "-"
  /-- the container instantiations `nestPos` located -/
  keys : List Name := []
  /-- does the family carry a recursor whose major is outside the block -/
  auxRecs : Nat := 0
  deriving Inhabited

/-- `nestPos`'s kind as today's classifier would spell it (`none` at a
container occurrence, which has no `BlockFieldKind`). -/
def NestFieldKind.toBlock? : NestFieldKind → Option BlockFieldKind
  | .ordinary => some .ordinary
  | .recursive t => some (.recursive t)
  | .reflexive t => some (.reflexive t)
  | _ => none

/-- Do the two kinds agree?  A container occurrence (`nested`,
`inProgress`) agrees with the classifier's `unsupported`. -/
def nestKindAgrees (b : BlockFieldKind) (n : NestFieldKind) : Bool :=
  match n.toBlock? with
  | some b' => b == b'
  | none => b == .unsupported

/-- The first disagreement between the classifier's kinds and
`nestPos`'s, as `(member, ctor, field)`; `none` when they agree
everywhere (shapes included). -/
def kindsDiff (bs : List (List (List BlockFieldKind))) (ns : List (List (List NestFieldKind))) :
    Option String :=
  if bs.length != ns.length then some "member count" else
  let rows := (bs.zip ns).zipIdx.flatMap fun ((bss, nss), mi) =>
    if bss.length != nss.length then [s!"m{mi}: ctor count"] else
    (bss.zip nss).zipIdx.flatMap fun ((b, n), ci) =>
      if b.length != n.length then [s!"m{mi}c{ci}: field count"] else
      (b.zip n).zipIdx.filterMap fun ((bk, nk), fi) =>
        if nestKindAgrees bk nk then none
        else some s!"m{mi}c{ci}f{fi}: classifier {repr bk} / nestPos {repr nk}"
  rows.head?

/-- Is some field recursive in `nestPos`'s reading (official's `is_rec`
on the auxiliary block: a container occurrence counts)? -/
def nestIsRec (ks : List (List (List NestFieldKind))) : Bool :=
  ks.any fun kss => kss.any fun fs => fs.any (· != .ordinary)

/-- One pass over the formers and the constructors at an `is_rec`
verdict (`checkBlockPassF` without the classifier). -/
def targetPass (so : ShadowOps m) (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    m (FEnv × List ConstantVal × BlockShape × List (List (ConstantVal × Nat)) ×
      List (List (List Level))) := do
  so.flush
  let (fe₁, cvTas, p₁) ← checkBlockIndsF (so.opsAt fe) fe p₀ isRec
  so.flush
  let ctx ← unwrapOr (blockNestCtxOf p₁ cvTas fe₁.find? fe₁.env.consts)
    (.internal "target: type former telescope")
  let (ctorsAs, sortsss) ← checkBlockCtorsF (so.opsAt fe₁) fe₁ fe₁ p₁ ctx (p₁.members.zip cvTas)
  pure (fe₁, cvTas, p₁, ctorsAs, sortsss)

/-- **The firing mode of a rule at an OUTSIDE major** (lane L2): the
syntactic reading of the recursor type's major domain
(`Expr.nestedRuleSyn`, the major's parameter count `nPc`, constants
resolving in `fe`) — `.nested lvls pins`, with `pins` the major's
parameters lowered into the rule-prefix context, whose guards are
`EnvWF`'s `.nested` clause (`nestedRuleSyn_inv`); `.inert` when the
reading fails (a matched major then declines at fire time). -/
def auxRuleFire (fe : FEnv) (cv : ConstantVal) (mI rP nPc : Nat) : RecRuleFire :=
  match Expr.nestedRuleSyn (·.constsResolveF fe) cv.levelParams cv.type mI rP nPc with
  | some (lvls, pins) => .nested lvls pins
  | none => .inert

/-- The records the target install conses for the family: each
recursor's stored rules at its major's constructors (`sumRules` with
the major's parameter count); at an OUTSIDE major every rule fires as
`auxRuleFire` reads it (`.nested` at the major's instantiation), at a
member major as `sumRules` builds it. -/
def targetRecInfos (fe : FEnv) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → List ConstantInfo
  | rc :: rcs, (cv, M, rhss) :: rest =>
    let rules := sumRules fe.find? cv.name M.nPc rc.mI rc.rP cv.type M.ctors rhss
    let rules := match M.member with
      | none => rules.map fun rl => { rl with fire := auxRuleFire fe cv rc.mI rc.rP M.nPc }
      | some _ => rules
    .recInfo cv rc.mI rc.rP rules :: targetRecInfos fe rcs rest
  | _, _ => []

/-- Does some recursor at an OUTSIDE major keep its rules inert
(`auxRuleFire` failing — a measurement: the reading is expected to
succeed at every checked outside major)? -/
def targetAuxInert (fe : FEnv) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → Bool
  | rc :: rcs, (cv, M, _) :: rest =>
    (M.member.isNone && match auxRuleFire fe cv rc.mI rc.rP M.nPc with
      | .inert => true
      | _ => false) || targetAuxInert fe rcs rest
  | _, _ => false

/-- **The target installer, as a shadow**, on the raw block at the
pre-block index `fe`: never throws; every stage's verdict is in the
report.  See the module header for what runs. -/
def targetShadow (so : ShadowOps m) (fe : FEnv) (nPd : Nat) (block : List ConstantInfo) :
    m TargetShadowReport := do
  -- the declared parameter count first, for every block (`checkDecl`'s
  -- order: it is a property of the declaration, not of a route)
  unless indParamsOk nPd block do
    return { install := .fail (.invalid "number of parameters mismatch") }
  let some p := blockShape? nPd block
    | -- a block the recogniser does not read: its formers are checked as
      -- constants (a reserved name, a malformed type — official's
      -- rejects), and what survives that is a positive decline
      let r ← shadowTry (block.forM fun ci => match ci with
        | .indInfo cv _ => discard <| checkConstantValF (so.opsAt fe) fe cv
        | _ => pure ())
      match r with
      | .error e => pure { install := .fail e }
      | .ok () =>
        pure { install := .fail (.notImplemented "target: the block's shape is not recognised") }
  let auxRecs := (p.recs.filter fun rc => !(rc.tgt < p.k)).length
  let rep : TargetShadowReport := { auxRecs := auxRecs }
  let p₀ : BlockParts := ⟨p, [], blockRecPinOk p block⟩
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    return { rep with install := .fail (.invalid "direct rec: duplicate constructor") }
  let guess := blockRawRec p₀
  match ← shadowTry (targetPass so fe p₀ guess) with
  | .error e => return { rep with install := .fail e }
  | .ok (fe₁, cvTas, p₁, ctorsAs, sortsss) =>
  -- piece 2: today's classifier and `nestPos`, on the same stored
  -- constructors
  let cls ← shadowTry (classifyBlockKinds (m := m) p₁.memberNames p₁.lps p₁.nP p₁.nIdxs ctorsAs)
  let some cvTa0 := cvTas.head?
    | return { rep with install := .fail (.internal "target: no type former") }
  let some (params, _) := openPisAtFvars p₁.nP cvTa0.type 0
    | return { rep with install := .fail (.notImplemented "target: type former telescope") }
  so.flush
  let pos ← shadowTry (nestedBlockPositivity (so.opsAt fe₁) fe₁.env
    ⟨p₁.memberNames, p₁.lps, p₁.nP, p₁.nIdxs, params, p₁.resSort, fe₁.find?, fe₁.env.consts⟩
    ctorsAs)
  let (kinds, note) := match cls, pos with
    | .ok bs, .ok r =>
      match kindsDiff bs r.kinds with
      | none => ("same", "")
      | some d => ("differ", d)
    | _, _ => ("-", "")
  let rep := { rep with cls := .ofExcept cls, pos := .ofExcept pos, kinds := kinds,
                        kindsNote := note }
  match pos with
  | .error e => return { rep with install := .fail e }
  | .ok r =>
  -- `nestPos`'s normal forms against the stored (already normalised)
  -- constructors: a measurement for the flip, never a verdict
  let rep := if r.normals == ctorsAs.map (·.map (·.1.type)) then rep
    else { rep with kindsNote := rep.kindsNote ++ " [nestPos normal forms differ from the \
      stored constructors]" }
  -- and on the DECLARED constructors: `nestPos`'s normal forms against
  -- the stored ones (`nestNormCtor`'s)
  so.flush
  let decl ← shadowTry (p₁.members.mapM fun ms => ms.ctors.mapM fun c => do
    let cvCa ← checkConstantValF (so.opsAt fe₁) fe₁ c.1
    pure (cvCa, c.2))
  let rep ← match decl with
    | .ok declAs => do
      let posD ← shadowTry (nestedBlockPositivity (so.opsAt fe₁) fe₁.env
        ⟨p₁.memberNames, p₁.lps, p₁.nP, p₁.nIdxs, params, p₁.resSort, fe₁.find?,
          fe₁.env.consts⟩ declAs)
      pure <| match posD with
        | .ok rD =>
          if rD.normals == ctorsAs.map (·.map (·.1.type)) then rep
          else { rep with kindsNote := rep.kindsNote ++ " [normDecl differs]" }
        | .error _ => { rep with kindsNote := rep.kindsNote ++ " [normDecl rejects]" }
    | .error _ => pure rep
  let rep := { rep with keys := r.keys.toList.map fun (k : NestKeyInfo) => k.key.cname }
  -- the capability record at `nestPos`'s `is_rec`, settled as today
  let isRec := nestIsRec r.kinds
  let settled := (List.range p₁.k).all fun i => blockCapsAt p₁ i isRec == blockCapsAt p₁ i guess
  let pass ← if settled then pure (.ok (fe₁, cvTas, p₁, ctorsAs, sortsss))
    else shadowTry (targetPass so fe p₀ isRec)
  match pass with
  | .error e => return { rep with install := .fail e }
  | .ok (fe₁, cvTas, p₁, ctorsAs, sortsss) =>
  let nested := !r.keys.isEmpty || auxRecs != 0
  -- today's kinds re-check, measured where `nestPos`'s kinds are
  -- expressible (it has no arm for a container occurrence)
  let bks := r.kinds.mapM (·.mapM (·.mapM NestFieldKind.toBlock?))
  let fields : String :=
    match bks with
    | some ks =>
      if blockFieldsOkF so.walkers fe p₁.memberNames p₁.lps p₁.nP p₁.nIdxs ctorsAs ks
      then "ok" else "fail"
    | none => "n/a"
  let rep := { rep with fields := fields }
  let tail : m (Except CheckError (FEnv × Except CheckError Unit × ShadowVerdict × Bool)) :=
    shadowTry do
    if p₁.large && !p₁.resSort.isNeverZero && decide (2 ≤ p₁.k ∨ 2 ≤ p₁.numCtors) then
      throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
        whose sort may be Prop")
    so.flush
    let _isorts ← checkBlockIdxSortsF (so.opsAt fe₁) fe₁ p₁ (p₁.members.zip cvTas)
    let fe₂ := consBlockCtorsF p₁.nP ctorsAs fe₁
    so.flush
    -- piece 1, on the stream's family
    match ← shadowTry (targetRecCheck so fe₂ p₁ true nested block cvTas ctorsAs) with
    | .error e => pure (fe₂, .error e, .skip "not reached", false)
    | .ok rs =>
      -- the reject-only conformance check (charter item 6), where the
      -- generator can read `nestPos`'s kinds (not at a container)
      let conf ← match bks with
        | some ks => do
          so.flush
          pure (ShadowVerdict.ofExcept (← shadowTry (checkBlockRecConformF (so.opsAt fe₂)
            so.walkers fe₂ none (⟨p₁, ks, p₀.recPinned⟩ : BlockParts) cvTas ctorsAs)))
        | none => pure (.skip "n/a")
      if let .fail _ := conf then return (fe₂, .ok (), conf, false)
      let fe₃ := FEnv.pushAll (targetRecInfos fe₂ p₁.recs rs) fe₂
      so.flush
      let fe₄ ← checkBlockTablesF so.walkers p₁ (p₁.members.zip (ctorsAs.zip sortsss)) fe₃
      pure (fe₄, .ok (), conf, targetAuxInert fe₂ p₁.recs rs)
  match ← tail with
  | .error e => return { rep with install := .fail e }
  | .ok (_, .error e, _, _) => return { rep with recCheck := .fail e, install := .fail e }
  | .ok (_, .ok (), .fail e, _) =>
    return { rep with recCheck := .accept, conf := .fail e, install := .fail e }
  | .ok (_, .ok (), conf, inert) =>
    let rep := if inert then
      { rep with kindsNote := rep.kindsNote ++ " [an outside major's rules stay inert]" }
      else rep
    return { rep with recCheck := .accept, conf := conf, install := .accept }

end ConLeche
