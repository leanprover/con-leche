module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The recursor stage as CHECKING, at k members (milestone M5)

The one-member route GENERATES the recursor and its rules and compares
them with the stream's (`checkNativeRec`/`nativeRulesOk`,
`ConLeche/Kernel/Inductives/NativeInstall.lean`).  At k members that
comparison no longer decides anything useful: an exported block's
minor premises are the elaborator's, spelled from the declared
constructor types and a weak-head-normalised telescope, and the rules'
bodies are whatever the elaborator emitted.  So the uniform route
CHECKS instead of generating:

* the recursor's TYPE is the generated one **with the stream's own
  minor binders spliced in** — the motive telescope and the tail are
  generated per member, the `N` minor binders are read off the
  stream's type and re-emitted with the block's elimination datum, and
  ONE `isDefEq` compares the whole with the stream's type.  The STORED
  type is the spliced generated one, so the motives and the tail are
  known forms for the model's reading while the minors are arbitrary
  well-formed binders.  This is a SUPERSET of official: a block whose
  minors are not the generated ones but whose rules type-check is
  accepted.
* every RULE's `λ`-prefix is checked against the stored recursor type
  (`blockRulePrefixOk`, `nativeRulePrefixOk` at k), and its body goes
  through **the primitive-recursion abstraction** (`abstractIh`):
  every occurrence of a block recursor must be the head of a maximal
  spine `rec_{c'} p⃗ C⃗ m⃗ e⃗_i(a⃗) (f_i a⃗)` on a field `f_i` of THIS
  constructor whose kind is `.recursive c'`/`.reflexive c'`, with the
  prefix exactly the rule's own parameter/motive/minor variables and
  `e⃗` SYNTACTICALLY the field's index expressions at `a⃗`; the spine is
  replaced by `ih_i a⃗`, and any other occurrence of a block recursor
  — a partial spine, a recursor passed as an argument, a call on
  something that is not a field of this constructor — is INVALID.  The
  residue is then TYPED at the environment holding all `k` RULE-LESS
  recursors, under the opened frame `p⃗ C⃗ m⃗ f⃗ ih⃗`, against the minor's
  conclusion `C_m e⃗_J (C_J p⃗ f⃗)` — which is exactly what official's
  own right-hand side has as its type.

Official's `minor f⃗ ih⃗` bodies abstract to themselves, so no official
recursor is lost.  What is gained is every mutual block: the rules of
`rec_m` recurse into `rec_{c'}` for any member `c'`, which a
generate-and-compare stage can only accept by reproducing the
elaborator's spelling exactly.

Nothing of the abstracted body is STORED: the stored rule carries the
ANNOTATED STREAM right-hand side (`ConLeche/Kernel/Inductives/SumInstall.lean`'s
`sumRules`), and the abstraction is the model's reading of it.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-! ## The gate -/

/-- **THE RECURSOR STAGE'S GATE** (milestone M5): the k-ary recursor
CHECK is written, but the route runs the one-member
generate-and-compare stage at `k = 1` until the model side (lane M)
lands, so that

* the one-member bridge `checkBlock_one`
  (`ConLeche/Verify/Inductives/BlockOneInstall.lean`) keeps closing —
  the k = 1 instance of the new check ACCEPTS MORE than the old stage
  (any primitively recursive rule body, not only the generated one),
  so the two are not equal and the bridge would have to be restated
  against a model that does not exist yet; and
* every intermediate tree stays a complete, proved, sorry-free
  checker.

Flipping this constant makes the new check live at EVERY `k`
(including `k = 1`); it is what a scratch build and the probes of
milestone M5 do.  It goes with `blockRouteK1Only` at the flip. -/
def blockRecCheckOn : Bool := false

/-! ## The generated pieces at k members

The frames, once (`o := k + N` are the extras between the parameters
and a rule's fields — all `k` motives and all `N` minors):

* in a rule body under `nF` fields and `d` further binders,
  `p_l` is `bvar (d + nF + N + k + nP - 1 - l)`,
  `C_c` is `bvar (d + nF + N + k - 1 - c)` and
  `minor_J` is `bvar (d + nF + N - 1 - J)`;
* under an `ih` binder (`l` earlier ones, `m` telescope binders),
  `C_c` is `bvar (nF + o - 1 + l + m - c)` and `f_i` is
  `bvar (nF - 1 - i + l + m)`;
* in `rec_m`'s type after the minors, the `nIdx_m` indices and the
  major, `C_m` is `bvar (nIdx_m + N + k - m)`.

At `k = 1` every formula is the one-member one
(`structRecPrefixAt`/`structIhPis`/`structRecTyR`,
`ConLeche/Kernel/Inductives/NativeParts.lean`). -/

/-- The recursor's leading spine `p⃗ C⃗ m⃗` as seen from inside a rule
body, under the `nF` fields and `d` further binders
(`structRecPrefixAt` at `k` motives). -/
def blockRecPrefixAt (nP k N nF d : Nat) : List Expr :=
  structPsAt (d + nF + N + k) nP ++
    (List.range k).map (fun c => Expr.bvar (d + nF + N + k - 1 - c)) ++
    (List.range N).map (fun j => Expr.bvar (d + nF + N - 1 - j))

/-- **The inductive hypothesis' guarded call**, as a `∀`-telescope over
the field's own telescope so that it can be instantiated at the
spine's actual arguments: `∀ a⃗, rec_{tgt i} p⃗ C⃗ m⃗ e⃗_i(a⃗) (f_i a⃗)`,
spelled at a rule body's frame under the `nF` fields and `d` further
binders (`structIhApp` at `k` motives, with `∀` for `λ` and an
arbitrary depth). -/
def blockIhSpinePis (recName : Name) (rlvls : List Level) (pw : PropWhen)
    (nP k N nF i d : Nat) (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr :=
  let m := tele.length
  Expr.mkPisOf (structTeleAt nF (k + N) i d pw tele)
    (Expr.mkAppN (.const recName rlvls)
      (blockRecPrefixAt nP k N nF (d + m) ++ idx.map (structIdxAt nF (k + N) i d m) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + d + m)) (structTeleVars m)]))

/-- The `ih` binders of a rule's frame at k members: for each
recursive field position, `∀ a⃗, C_{tgt i} e⃗_i(a⃗) (f_i a⃗)`
(`structIhPis` with the motive read at the field's TARGET member and
the extras `o = k + N` — all the motives and all the minors, since a
rule binds them all). -/
def blockIhPis (nF o : Nat) (pw : PropWhen) (tgts : List Nat)
    (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) :
    List Nat → Nat → Expr → Expr
  | [], _, body => body
  | i :: is, l, body =>
    let m := (teleOf i).length
    .forallE
      (Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i))
        (Expr.mkAppN (.bvar (nF + o - 1 + l + m - tgts.getD i 0))
          ((idxOf i).map (structIdxAt nF o i l m) ++
            [Expr.mkAppN (.bvar (nF - 1 - i + l + m)) (structTeleVars m)])))
      (blockIhPis nF o pw tgts teleOf idxOf is (l + 1) body) ⟨pw⟩

/-- The `k` motive binders `∀ (C_0 : ∀ ı⃗_0 (t : T_0 p⃗ ı⃗_0), Sort ℓ) …`
at the parameters' frame, one per member off its own declared index
telescope (`structMotiveTyI`), each lifted under the motives that
precede it.  `mems` is the member list as `(name, nIdx, type former's
annotated type)`. -/
def blockMotivesPis (lps : List Name) (nP : Nat) (ℓ : Level) (pw : PropWhen) :
    List (Name × Nat × Expr) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (T, nIdx, tty) :: rest, c, body =>
    (tty.stripPis nP).bind fun q =>
    (structMotiveTyI T lps nP nIdx ℓ q.2).bind fun mty =>
      (blockMotivesPis lps nP ℓ pw rest (c + 1) body).map fun r =>
        .forallE (mty.liftLooseBVars c 0) r ⟨pw⟩

/-- **Member `m`'s recursor type, generated with the stream's minors
spliced in**:

    ∀ p⃗ (C_0 : …) … (C_{k-1} : …) [the stream's own N minor binders]
      ı⃗_m (t : T_m p⃗ ı⃗_m), C_m ı⃗_m t

The parameter binders are member `m`'s own type former's (the
block's parameter agreement makes them definitionally every member's),
the motive binders are generated per member, the `N` minor DOMAINS are
the stream's — re-emitted with the block's elimination datum, since
their codomains are all `Sort ℓ`-valued Π-chains — and the tail is
generated.  `strTy` is the stream's recursor type, `ttyM` member `m`'s
annotated type former's type, `mems` the member list as
`blockMotivesPis` reads it. -/
def blockRecTySpliced (Tm : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP k N nIdxm m : Nat) (ttyM : Expr) (mems : List (Name × Nat × Expr))
    (strTy : Expr) : Option Expr :=
  let ℓ := structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  (ttyM.stripPis nP).bind fun q =>
  (strTy.stripPis (nP + k)).bind fun sq =>
  (Expr.replacePisPw pw nIdxm (q.2.liftLooseBVars (k + N) 0)
      (.forallE (structFamI Tm lps nP nIdxm (k + N) 0)
        (Expr.mkAppN (.bvar (nIdxm + N + k - m)) (structPsAt 1 nIdxm ++ [.bvar 0]))
        ⟨pw⟩)).bind fun major =>
  (Expr.replacePisPw pw N sq.2 major).bind fun minors =>
  (blockMotivesPis lps nP ℓ pw mems 0 minors).bind fun motives =>
    Expr.replacePisPw pw nP ttyM motives

/-- **The rule's `λ` prefix against the stream's own recursor type**
(`nativeRulePrefixOk` at k members): the rule binds the recursor's
`nP` parameters, its `k` motives, its `N` minor premises and
constructor `J`'s `nF` fields, and every one of those binder types
appears again in the STORED recursor type — the first `nP + k + N` at
exactly the same de Bruijn depths, the fields as the first `nF`
binders of minor `J`'s type, which stands `N - J` binders shallower
than the rule's fields do.  The one-member docstring
(`ConLeche/Kernel/Inductives/NativeParts.lean`) says why the
comparison is against the stream's own recursor type and not against a
generated term. -/
def blockRulePrefixOk (recTy : Expr) (nP k N J nF : Nat) (rhs : Expr) : Bool :=
  match rhs.stripLams (nP + k + N + nF), recTy.stripPis (nP + k + N) with
  | some (rbs, _), some (tbs, _) =>
    (List.range (nP + k + N)).all (fun i =>
      match rbs[i]?, tbs[i]? with
      | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
      | _, _ => false) &&
    (match tbs[nP + k + J]? with
     | some mty =>
       (match (mty.1.liftLooseBVars (N - J) 0).stripPis nF with
        | some (fbs, _) =>
          (List.range nF).all fun i =>
            match rbs[nP + k + N + i]?, fbs[i]? with
            | some b, some f => Expr.resetMeta b.1 == Expr.resetMeta f.1
            | _, _ => false
        | none => false)
     | none => false)
  | _, _ => false

/-! ## The primitive-recursion abstraction -/

/-- The position of a name in a list (`none` when absent). -/
def nameIdxOf? (names : List Name) (n : Name) : Option Nat :=
  (List.range names.length).find? fun i => names.getD i default == n

/-- The position of a number in a list (`none` when absent) — the
`ih` binder a recursive field position owns. -/
def natIdxOf? (ns : List Nat) (n : Nat) : Option Nat :=
  (List.range ns.length).find? fun i => ns.getD i 0 == n

/-- **The data one rule's abstraction walks against**: the block's
recursor names and their shared level arguments, the members' index
counts, the frame's widths, the constructor's field kinds, telescopes
and index expressions, and the recursive positions (the `ih` binders,
in order). -/
structure BlockRuleFrame where
  /-- the block's `k` recursor names, in member order -/
  recNames : List Name
  /-- the level arguments every recursive call carries -/
  rlvls : List Level
  /-- the members' index counts, in member order -/
  nIdxs : List Nat
  /-- the block's parameter count -/
  nP : Nat
  /-- the number of members -/
  k : Nat
  /-- the number of minor premises (the block's constructors) -/
  N : Nat
  /-- this constructor's field count -/
  nF : Nat
  /-- this constructor's field kinds -/
  ks : List BlockFieldKind
  /-- field `i`'s own telescope -/
  teleOf : Nat → List (Expr × BinderMeta)
  /-- field `i`'s index expressions -/
  idxOf : Nat → List Expr
  /-- the recursive field positions, in order (the `ih` binders) -/
  recIdx : List Nat
  /-- the block's elimination datum -/
  pw : PropWhen

/-- The number of `ih` binders the rule's frame carries. -/
def BlockRuleFrame.nR (fr : BlockRuleFrame) : Nat := fr.recIdx.length

/-- **A guarded recursive call**, read at a rule body's frame under
`d` binders: the node must be

    rec_{c'} p⃗ C⃗ m⃗ e⃗_i(a⃗) (f_i a⃗)

with `rec_{c'}` a block recursor at the block's level arguments, `f_i`
a field of THIS constructor whose kind is `.recursive c'` or
`.reflexive c'`, `a⃗` as many arguments as the field's telescope has
binders and free of any block recursor, and the whole spine
SYNTACTICALLY the generated call at those arguments
(`blockIhSpinePis` instantiated at `a⃗`, compared at the parse
placeholder's binder data).  The answer is the field's position among
the recursive ones — the `ih` binder that replaces the call — together
with `a⃗`. -/
def blockIhCall? (fr : BlockRuleFrame) (d : Nat) (e : Expr) : Option (Nat × List Expr) :=
  match e.getAppFn with
  | .const r us =>
    match nameIdxOf? fr.recNames r with
    | none => none
    | some c' =>
      if us != fr.rlvls then none else
      let args := e.getAppArgs
      let nI := fr.nIdxs.getD c' 0
      if args.length != fr.nP + fr.k + fr.N + nI + 1 then none else
      match args[fr.nP + fr.k + fr.N + nI]? with
      | none => none
      | some maj =>
        match maj.getAppFn with
        | .bvar b =>
          if !(decide (d ≤ b) && decide (b < d + fr.nF)) then none else
          let i := d + fr.nF - 1 - b
          let tgtOk :=
            match fr.ks.getD i .ordinary with
            | .recursive t => t == c'
            | .reflexive t => t == c'
            | _ => false
          if !tgtOk then none else
          let as := maj.getAppArgs
          let tele := fr.teleOf i
          if as.length != tele.length then none else
          if as.any (fun a => a.mentionsAnyConst fr.recNames) then none else
          match Expr.instPisAt as
              (blockIhSpinePis r fr.rlvls fr.pw fr.nP fr.k fr.N fr.nF i d tele (fr.idxOf i)) with
          | none => none
          | some (_, expected) =>
            if Expr.resetMeta e != Expr.resetMeta expected then none
            else match natIdxOf? fr.recIdx i with
              | none => none
              | some rpos => some (rpos, as)
        | _ => none
  | _ => none

/-- **The abstraction itself**: `body` at the frame `p⃗ C⃗ m⃗ f⃗`, under
`d` binders, rewritten to the frame `p⃗ C⃗ m⃗ f⃗ ih⃗` — every guarded
recursive call replaced by `ih_r a⃗`, every other variable shifted past
the `nR` new binders — or `none` when the body mentions a block
recursor anywhere else.

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
