module

public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# The mutual block: recognition and the generated recursors (task #278)

A **mutual block** is an inductive declaration with several type
formers `T_1 … T_k` over one parameter telescope, each with its own
index telescope, whose constructors may mention any member as a
recursive field, and with one recursor `T_m.rec` per member.  Official
(`kernel/inductive.cpp`, `mk_rec_infos`/`mk_rec_rules`) generates for
each member the recursor

    T_m.rec : Π p⃗ (motive_1 : Π ı⃗_1 (t : T_1 p⃗ ı⃗_1), Sort ℓ) … (motive_k : …)
                (minor_1 : …) … (minor_n : …)
                ı⃗_m (t : T_m p⃗ ı⃗_m), motive_m ı⃗_m t

with the minors of ALL constructors in member order then constructor
order, minor `J` of constructor `C` of member `m_J` being
`Π f⃗ (ih_i : Π x⃗, motive_{m_i} e⃗_i (f_i x⃗))…, motive_{m_J} e⃗ (C p⃗ f⃗)`
(one `ih` per recursive field, at the member the field targets), and
the rules of `T_m.rec` being member `m`'s constructors at their GLOBAL
minor index, `λ p⃗ motive⃗ minor⃗ f⃗, minor_J f⃗ (λ x⃗, T_{m_i}.rec p⃗ motive⃗ minor⃗ e⃗_i (f_i x⃗))…`.
The level parameters are `u :: lps` at the large eliminator and `lps`
at the small one, and a mutual block whose sort is not provably
nonzero eliminates into `Prop` only (`elim_only_at_universe_zero`).

The generators below are the fixpoint route's
(`ConLeche/Kernel/Inductives/NativeParts.lean`) with `k` motives: the
motive a recursive field's inductive hypothesis names is the one of
the member the field targets, the minor's conclusion names the
constructor's own member's, and the rule's inductive hypotheses call
the target member's recursor.  The install
(`ConLeche/Kernel/Inductives/MutualInstall.lean`) compares the stream's
recursors with these — the types by one `isDefEq` each, the rule
bodies structurally — exactly as the fixpoint route compares its one
recursor, and rejects a record that is not the generated one
(official's replay does the same, `checkPostponedRecursors`).
-/

namespace ConLeche

/-- One member of a mutual block, as recognised: the former, its
index count, its recursor record. -/
structure MutualMember where
  /-- the type former -/
  cv : ConstantVal
  /-- the index count: the declared telescope's length past the
  parameters, or — at a former declared at a definition (task #195) —
  what its recursor record claims -/
  nIdx : Nat
  /-- the recursor `T_m.rec` as exported -/
  cvR : ConstantVal
  /-- the recursor record's major index and rule prefix -/
  mI : Nat
  rP : Nat
  /-- the recursor's rules as exported -/
  rules : List RecRule
  deriving Repr, Inhabited

/-- One constructor of a mutual block: its record, its field count and
the member it belongs to (read off its result's head; `k` — no member
— at a constructor whose result is not a member application, which
the install rejects as official's "invalid return type"). -/
structure MutualCtor where
  cv : ConstantVal
  nF : Nat
  member : Nat
  deriving Repr, Inhabited

/-- The pieces of a recognised mutual block. -/
structure MutualParts where
  /-- the members in block order -/
  members : List MutualMember
  /-- the constructors in block order (member by member, as the parser
  orders them) -/
  ctors : List MutualCtor
  /-- the declared parameter count -/
  nP : Nat
  /-- the block's level parameters (the first former's) -/
  lps : List Name
  /-- the recursors' level-parameter shape: a fresh elimination
  parameter in front at the large eliminator -/
  large : Bool
  /-- the elimination level parameter (`.anonymous` at the small
  eliminator) -/
  elim : Name
  /-- every recursor record passed the structural pin
  (`mutualRecPinOk`): thrown at the install, as official's replay
  rejects a recursor that is not the generated one -/
  recPinned : Bool
  deriving Repr, Inhabited

/-- The member count. -/
def MutualParts.k (p : MutualParts) : Nat := p.members.length
/-- The constructor count. -/
def MutualParts.n (p : MutualParts) : Nat := p.ctors.length
/-- The recursors' rule prefix: parameters, `k` motives, `n` minors. -/
def MutualParts.rulePrefix (p : MutualParts) : Nat := p.nP + p.k + p.n
/-- The elimination level. -/
def MutualParts.elimLevel (p : MutualParts) : Level := structElimLevel p.elim p.large
/-- The recursors' level parameters. -/
def MutualParts.rlps (p : MutualParts) : List Name :=
  if p.large then p.elim :: p.lps else p.lps
/-- The member names. -/
def MutualParts.memberNames (p : MutualParts) : List Name := p.members.map (·.cv.name)
/-- The block's names: formers, constructors, recursors. -/
def MutualParts.blockNames (p : MutualParts) : List Name :=
  p.memberNames ++ p.ctors.map (·.cv.name) ++ p.members.map (·.cvR.name)
/-- The constructors of member `m`, with their global indices. -/
def MutualParts.ownCtors (p : MutualParts) (m : Nat) : List (Nat × MutualCtor) :=
  (p.ctors.zipIdx.map fun (c, J) => (J, c)).filter fun (_, c) => c.member == m

/-! ## Recognition -/

/-- The block's members: the formers, then the constructors, then the
recursors — the parser's own order (`types ++ ctors ++ recs`). -/
def mutualSplit : List ConstantInfo →
    Option (List ConstantVal × List (ConstantVal × Nat × Nat) ×
      List (ConstantVal × Nat × Nat × List RecRule))
  | .indInfo cvT _ :: rest =>
    (mutualSplit rest).map fun q => (cvT :: q.1, q.2)
  | rest => mutualSplitC rest
where
  mutualSplitC : List ConstantInfo →
      Option (List ConstantVal × List (ConstantVal × Nat × Nat) ×
        List (ConstantVal × Nat × Nat × List RecRule))
    | .ctorInfo cvC nP nF :: rest =>
      (mutualSplitC rest).map fun q => (q.1, (cvC, nP, nF) :: q.2.1, q.2.2)
    | rest => mutualSplitR rest
  mutualSplitR : List ConstantInfo →
      Option (List ConstantVal × List (ConstantVal × Nat × Nat) ×
        List (ConstantVal × Nat × Nat × List RecRule))
    | [] => some ([], [], [])
    | .recInfo cvR mI rP rules :: rest =>
      (mutualSplitR rest).map fun q => (q.1, q.2.1, (cvR, mI, rP, rules) :: q.2.2)
    | _ => none

/-- The member a constructor's result names: the head of its
type's Π-residual, looked up among the members (`k` when none). -/
def mutualCtorMember (memberNames : List Name) (cty : Expr) : Nat :=
  match cty.piResult.getAppFn with
  | .const T _ => (memberNames.idxOf? T).getD memberNames.length
  | _ => memberNames.length

/-- **The recursor records' structural pin** (task #220's, per
member): `T_m.rec` carries the rule prefix `nP + k + n` and the major
index `nP + k + n + nIdx_m`, one rule per constructor of member `m` in
block order naming it with its field count, and the level parameters
`elim :: lps` at the large eliminator, `lps` at the small.  A `false`
is thrown at the install as `.invalid`: official's replay compares the
exported recursor with the generated one structurally. -/
def mutualRecPinOk (p : MutualParts) : Bool :=
  (List.range p.k).all fun m =>
    match p.members[m]? with
    | some mb =>
      mb.cvR.name == mb.cv.name.str "rec" &&
      mb.rP == p.rulePrefix && mb.mI == p.rulePrefix + mb.nIdx &&
      mb.cvR.levelParams == p.rlps &&
      (let own := p.ownCtors m
       mb.rules.length == own.length &&
       (List.range own.length).all fun j =>
         match mb.rules[j]?, own[j]? with
         | some rule, some (_, c) => rule.ctor == c.cv.name && rule.nfields == c.nF
         | _, _ => false)
    | none => false

/-- **Recognise a mutual block**: two or more type formers, as many
recursors, each former's recursor found by name (`T_m.rec`).  The
index counts are read as official reads them — off the former's own
syntactic telescope, or, at a former declared at a definition, off its
recursor record's argument sums (`nativeCounts?`'s arrangement).  The
level-parameter shape of the recursors decides which eliminator the
block claims (the large one carries a fresh parameter in front of the
block's).  Nothing else of the recursor records is a condition of
recognition: their structural pin travels with the record and the
install throws on it, so that a block whose recursor record is a stub
is REJECTED by its own type and constructors rather than declined.  A
block with MORE recursors than formers is a nested one (the kernel's
nested→mutual specialisation mints one recursor per mimic) and is not
this route's. -/
def mutualParts? (nPd : Nat) (block : List ConstantInfo) : Option MutualParts :=
  match mutualSplit block with
  | some (formers, cs, recs) =>
    let k := formers.length
    if k < 2 || recs.length != k then none
    else if formers.any (fun cvT => reservedBasisNames.contains cvT.name) ||
        cs.any (fun c => reservedBasisNames.contains c.1.name) ||
        recs.any (fun r => reservedBasisNames.contains r.1.name) then none
    else
      let lps := (formers.headD default).levelParams
      let memberNames := formers.map (·.name)
      let recOf : Name → Option (ConstantVal × Nat × Nat × List RecRule) := fun T =>
        recs.find? fun r => r.1.name == T.str "rec"
      let members? : Option (List MutualMember) := formers.mapM fun cvT => do
        let (cvR, mI, rP, rules) ← recOf cvT.name
        let nIdx ← match cvT.type.piBinders with
          | (bs, .sort _) => if nPd ≤ bs.length then some (bs.length - nPd) else none
          | _ => if rP ≤ mI then some (mI - rP) else none
        pure ⟨cvT, nIdx, cvR, mI, rP, rules⟩
      match members? with
      | none => none
      | some members =>
        let ctors := cs.map fun (cvC, _, nF) => ⟨cvC, nF, mutualCtorMember memberNames cvC.type⟩
        let cvR₀ := (members.headD default).cvR
        let large? : Option Name :=
          match cvR₀.levelParams with
          | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
          | [] => none
        let p : MutualParts :=
          match large? with
          | some elim => ⟨members, ctors, nPd, lps, true, elim, true⟩
          | none => ⟨members, ctors, nPd, lps, false, .anonymous, true⟩
        some { p with recPinned := mutualRecPinOk p }
  | none => none

/-! ## The generated recursors with `k` motives -/

/-- A constructor as the generators take it: name, field count, its
(annotated) type, its member, and its recursive fields — `(i, m')`,
field `i` targets member `m'` — in field order. -/
structure MutualCtor4 where
  name : Name
  nF : Nat
  cty : Expr
  member : Nat
  recFields : List (Nat × Nat)
  deriving Repr, Inhabited

/-- A former as the generators take it: name, index count, its
(annotated, telescope-shaped) type. -/
structure MutualFormer where
  name : Name
  nIdx : Nat
  tty : Expr
  deriving Repr, Inhabited

/-- The parameter, motive and minor variables as seen from under the
`nF` fields and `e` further binders: the recursors' leading spine
`p⃗ motive⃗ minor⃗` at that frame (`structRecPrefixAt` with `k`
motives). -/
def mutualRecPrefixAt (nP k n nF e : Nat) : List Expr :=
  structPsAt (e + nF + n + k) nP ++
    ((List.range k).map fun i => Expr.bvar (e + nF + n + k - 1 - i)) ++
    ((List.range n).map fun l => Expr.bvar (e + nF + n - 1 - l))

/-- The inductive hypothesis' value for recursive field `i` targeting
member `m'` with telescope `tele` and index expressions `idx`, spelled
under the fields of a rule body (the `k` motives and `n` minors are
the extras): `λ a⃗, T_{m'}.rec p⃗ motive⃗ minor⃗ e⃗_i(a⃗) (f_i a⃗)`
(`structIhApp`). -/
def mutualIhApp (recOf : Nat → Name) (rlvls : List Level) (pw : PropWhen)
    (nP k n nF i m' : Nat) (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr :=
  let mm := tele.length
  Expr.mkLamsOf (structTeleAt nF (n + k) i 0 pw tele)
    (Expr.mkAppN (.const (recOf m') rlvls)
      (mutualRecPrefixAt nP k n nF mm ++ idx.map (structIdxAt nF (n + k) i 0 mm) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + mm)) (structTeleVars mm)]))

/-- The right-hand side body of rule `J` (the constructor's global
minor index): minor `J` at the fields, then at the inductive
hypotheses of the recursive fields (`structRuleBodyR`). -/
def mutualRuleBody (recOf : Nat → Name) (rlvls : List Level) (pw : PropWhen)
    (nP k n nF J : Nat) (recFields : List (Nat × Nat))
    (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) : Expr :=
  Expr.mkAppN (.bvar (nF + n - 1 - J))
    (((List.range nF).map fun l => Expr.bvar (nF - 1 - l)) ++
      recFields.map fun (i, m') =>
        mutualIhApp recOf rlvls pw nP k n nF i m' (teleOf i) (idxOf i))

/-- The `ih` binders of a minor premise: for each recursive field
`(i, m')` in order, `∀ a⃗, motive_{m'} e⃗_i(a⃗) (f_i a⃗)` under the `l`
earlier `ih` binders; the `o` extras between the parameters and the
fields are the `k` motives and the earlier minors, so `motive_{m'}`
sits `nF + o - 1 - m'` binders above the fields (`structIhPis`). -/
def mutualIhPis (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (Expr × BinderMeta))
    (idxOf : Nat → List Expr) : List (Nat × Nat) → Nat → Expr → Expr
  | [], _, body => body
  | (i, m') :: is, l, body =>
    let mm := (teleOf i).length
    .forallE
      (Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i))
        (Expr.mkAppN (.bvar (nF + o - 1 + l + mm - m'))
          ((idxOf i).map (structIdxAt nF o i l mm) ++
            [Expr.mkAppN (.bvar (nF - 1 - i + l + mm)) (structTeleVars mm)])))
      (mutualIhPis nF o pw teleOf idxOf is (l + 1) body) ⟨pw⟩

/-- A constructor's minor premise: its field telescope lifted under the
`o` extras (`k` motives and the earlier minors), every binder's block model
reset to the elimination block model, then the `ih` binders, ending in
`motive_{m} e⃗ (C p⃗ f⃗)` at the constructor's own member `m`
(`structMinorTyR`). -/
def mutualMinorTy (lps : List Name) (nP o : Nat) (pw : PropWhen) (c : MutualCtor4) :
    Option Expr :=
  let nF := c.nF
  (c.cty.stripPis nP).bind fun q =>
  (q.2.stripPis nF).bind fun r =>
    Expr.replacePisPw pw nF (q.2.liftLooseBVars o 0)
      (mutualIhPis nF o pw (structFieldTeleOf c.cty nP nF) (structFieldIdxOf c.cty nP nF)
        c.recFields 0
        ((Expr.mkAppN (.bvar (nF + o - 1 - c.member))
          ((r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
            [structCtorSpineAt c.name lps o nP nF])).liftLooseBVars c.recFields.length 0))

/-- The minor premises' `∀`-telescope, one per constructor, the first
sitting `o = k` binders below the parameters. -/
def mutualMinorsPis (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List MutualCtor4 → Nat → Expr → Option Expr
  | [], _, body => some body
  | c :: cs, o, body =>
    (mutualMinorTy lps nP o pw c).bind fun mty =>
      (mutualMinorsPis lps nP pw cs (o + 1) body).map fun rest =>
        .forallE mty rest ⟨pw⟩

/-- The `λ` twin of `mutualMinorsPis`. -/
def mutualMinorsLams (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List MutualCtor4 → Nat → Expr → Option Expr
  | [], _, body => some body
  | c :: cs, o, body =>
    (mutualMinorTy lps nP o pw c).bind fun mty =>
      (mutualMinorsLams lps nP pw cs (o + 1) body).map fun rest =>
        .lam mty rest ⟨pw⟩

/-- Motive `i`'s type, `i` motives below the parameters:
`∀ ı⃗_i (t : T_i p⃗ ı⃗_i), Sort ℓ` (`structMotiveTyI` with the
parameters `i` binders further up). -/
def mutualMotiveTy (lps : List Name) (nP : Nat) (ℓ : Level) (i : Nat) (f : MutualFormer) :
    Option Expr :=
  (f.tty.stripPis nP).bind fun q =>
    Expr.replacePisPw .never f.nIdx (q.2.liftLooseBVars i 0)
      (.forallE (structFamI f.name lps nP f.nIdx i 0) (.sort ℓ) ⟨.never⟩)

/-- The motives' `∀`-telescope over `body`, in member order. -/
def mutualMotivesPis (lps : List Name) (nP : Nat) (ℓ : Level) (pw : PropWhen) :
    List MutualFormer → Nat → Expr → Option Expr
  | [], _, body => some body
  | f :: fs, i, body =>
    (mutualMotiveTy lps nP ℓ i f).bind fun mty =>
      (mutualMotivesPis lps nP ℓ pw fs (i + 1) body).map fun rest =>
        .forallE mty rest ⟨pw⟩

/-- The `λ` twin of `mutualMotivesPis`. -/
def mutualMotivesLams (lps : List Name) (nP : Nat) (ℓ : Level) (pw : PropWhen) :
    List MutualFormer → Nat → Expr → Option Expr
  | [], _, body => some body
  | f :: fs, i, body =>
    (mutualMotiveTy lps nP ℓ i f).bind fun mty =>
      (mutualMotivesLams lps nP ℓ pw fs (i + 1) body).map fun rest =>
        .lam mty rest ⟨pw⟩

/-- **The generated recursor type of member `m`**

    ∀ p⃗ (motive_1 : …) … (motive_k : …) (minor_1 : …) … (minor_n : …)
      ı⃗_m (t : T_m p⃗ ı⃗_m), motive_m ı⃗_m t

over the FIRST former's parameter telescope (official spells every
recursor's parameters at `m_params`, the first former's binders) and
member `m`'s index telescope (`structRecTyR` with `k` motives). -/
def mutualRecTy (lps : List Name) (elim : Name) (large : Bool) (nP : Nat)
    (formers : List MutualFormer) (ctors : List MutualCtor4) (m : Nat) : Option Expr :=
  let ℓ := structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let k := formers.length
  let n := ctors.length
  match formers[m]?, formers[0]? with
  | some f, some f₀ =>
    (f.tty.stripPis nP).bind fun q =>
    (Expr.replacePisPw pw f.nIdx (q.2.liftLooseBVars (k + n) 0)
        (.forallE (structFamI f.name lps nP f.nIdx (k + n) 0)
          (Expr.mkAppN (.bvar (f.nIdx + n + k - m)) (structPsAt 1 f.nIdx ++ [.bvar 0]))
          ⟨pw⟩)).bind fun major =>
    (mutualMinorsPis lps nP pw ctors k major).bind fun minors =>
    (mutualMotivesPis lps nP ℓ pw formers 0 minors).bind fun motives =>
      Expr.replacePisPw pw nP f₀.tty motives
  | _, _ => none

/-- **The generated rule** for constructor `J` (its global minor
index; member `m_J`'s recursor fires it):
`λ p⃗ motive⃗ minor⃗ f⃗_J, minor_J f⃗_J (λ a⃗, T_{m_i}.rec p⃗ motive⃗ minor⃗ e⃗_i(a⃗) (f_i a⃗))…`
(`structRecRhsR` with `k` motives; `recOf m'` is member `m'`'s
recursor's name, `rlvls` the recursors' level parameters as levels). -/
def mutualRecRhs (lps : List Name) (elim : Name) (large : Bool) (nP : Nat)
    (formers : List MutualFormer) (ctors : List MutualCtor4)
    (recOf : Nat → Name) (rlvls : List Level) (J : Nat) : Option Expr :=
  let ℓ := structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let k := formers.length
  let n := ctors.length
  match ctors[J]?, formers[0]? with
  | some c, some f₀ =>
    let nF := c.nF
    (c.cty.stripPis nP).bind fun q =>
    (Expr.pisToLamsPw pw nF (q.2.liftLooseBVars (k + n) 0)
        (mutualRuleBody recOf rlvls pw nP k n nF J c.recFields
          (structFieldTeleOf c.cty nP nF) (structFieldIdxOf c.cty nP nF))).bind fun inner =>
    (mutualMinorsLams lps nP pw ctors k inner).bind fun minors =>
    (mutualMotivesLams lps nP ℓ pw formers 0 minors).bind fun motives =>
      Expr.pisToLamsPw pw nP f₀.tty motives
  | _, _ => none

/-- **The rule's `λ` prefix against the stream's own recursor type**
(`nativeRulePrefixOk` with `k` motives): the first `nP + k + n` binder
types at the same depths, the fields as the first `nF` binders of the
`J`-th minor premise's type, `n - J` binders shallower. -/
def mutualRulePrefixOk (recTy : Expr) (nP k n J nF : Nat) (rhs : Expr) : Bool :=
  match rhs.stripLams (nP + k + n + nF), recTy.stripPis (nP + k + n) with
  | some (rbs, _), some (tbs, _) =>
    (List.range (nP + k + n)).all (fun i =>
      match rbs[i]?, tbs[i]? with
      | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
      | _, _ => false) &&
    (match tbs[nP + k + J]? with
     | some mty =>
       (match (mty.1.liftLooseBVars (n - J) 0).stripPis nF with
        | some (fbs, _) =>
          (List.range nF).all fun i =>
            match rbs[nP + k + n + i]?, fbs[i]? with
            | some b, some f => Expr.resetMeta b.1 == Expr.resetMeta f.1
            | _, _ => false
        | none => false)
     | none => false)
  | _, _ => false

/-- **The stream's rules of member `m` against the generated ones**
(`nativeRulesOk` at a mutual block): rule `j` fires member `m`'s `j`-th
constructor (global index `J`) with its field count, and its body is
the canonical right-hand side with the inductive hypotheses at the
parse placeholder's binder data; the `λ` prefix is checked against the
stream's own recursor type (`mutualRulePrefixOk`).  `own` lists
member `m`'s constructors with their global indices. -/
def mutualRulesOk (recOf : Nat → Name) (rlvls : List Level) (nP k n : Nat)
    (ctors : List MutualCtor4) (own : List Nat) (rhss : List Expr) (recTy : Expr) : Bool :=
  rhss.length == own.length &&
  (List.range own.length).all fun j =>
    match rhss[j]?, own[j]? with
    | some rhs, some J =>
      match ctors[J]? with
      | some c =>
        (match rhs.stripLams (nP + k + n + c.nF) with
         | some (_, rbody) =>
           rbody == Expr.resetMeta (mutualRuleBody recOf rlvls .never nP k n c.nF J c.recFields
             (structFieldTeleOf c.cty nP c.nF) (structFieldIdxOf c.cty nP c.nF))
         | none => false) &&
        mutualRulePrefixOk recTy nP k n J c.nF rhs
      | none => false
    | _, _ => false

end ConLeche
