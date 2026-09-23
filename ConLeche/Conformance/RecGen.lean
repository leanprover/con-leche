module

public import ConLeche.Kernel.Inductives.SumParts
public import ConLeche.Kernel.Inductives.FieldTele
public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# CONFORMANCE: the generated recursor at one member

**Not needed for soundness.**  Everything under `ConLeche/Conformance/`
is an unverified, reject-only check (charter item 6): the fold runs it
after the primitive-recursion check (`thenConform`,
`ConLeche/Kernel/Inductives/BlockInstall.lean`), it can only turn an
accept into a reject, and no model proof reads it.

This file is the one-member route's recursor GENERATOR (task #188,
task #175 S2): the record it reads (`NativeParts`, built from the
uniform route's parts by `BlockParts.toNative`), the recursor type with
the inductive-hypothesis binders (`structRecTyR`, official's
`mk_rec_infos`: each minor premise binds the constructor's fields, then
one `f_i_ih : motive e⃗_i f_i` per recursive field, and concludes
`motive e⃗ (C p⃗ f⃗)`), the rules (`structRecRhsR`, official's
`mk_rec_rules`: `λ p⃗ motive m⃗ f⃗, minor_j f⃗ (T.rec p⃗ motive m⃗ e⃗_i f_i)…`),
and the comparisons of the stream's rules with them (`nativeRulesOk`,
`nativeRulePrefixOk`).  The generators are the indexed ones of
`ConLeche/Kernel/Inductives/StructParts.lean` with the `ih` binders
threaded.  The checks that run them are `RecConform.lean` and its
index-threaded twin `RecConformF.lean`.
-/

namespace ConLeche

/-- The pieces of a recognised direct recursive block: the sum parts
(with the family's index count) and the per-constructor field kinds. -/
structure NativeParts extends InductiveShape where
  /-- per constructor, per field: its kind -/
  kinds : List (List RecFieldKind)
  /-- **the stream's recursor record passed the structural pin**
  (task #220): its rule count, each rule's constructor and field count,
  and the two argument sums the record claims are the generated ones.
  The recogniser records the verdict instead of refusing the block, and
  the recursor stage THROWS on `false` — official's replay generates the
  recursor and compares the exported one with it structurally
  (`checkPostponedRecursors`, `Lean4Checker/Replay.lean`), so a record
  that contradicts the generated recursor is invalid input, not a
  feature this route lacks. -/
  recPinned : Bool
  deriving Repr

/-! ## The generated recursor with inductive hypotheses -/

/-- The parameter, motive and minor variables as seen from under the
`nF` fields (and `e` further binders): the recursor's leading spine
`p⃗ motive m⃗` at that frame. -/
def structRecPrefixAt (nP n nF e : Nat) : List Expr :=
  structPsAt (e + nF + n + 1) nP ++ [Expr.bvar (e + nF + n)] ++
    (List.range n).map fun l => Expr.bvar (e + nF + n - 1 - l)

/-- `λ tele, body` over a binder list (outermost first). -/
def Expr.mkLamsOf : List (Expr × BinderMeta) → Expr → Expr
  | [], body => body
  | (ty, mt) :: bs, body => .lam ty (mkLamsOf bs body) mt

/-- The inductive hypothesis' value for recursive field `i` with
telescope `tele` and index expressions `idx`, spelled under the fields
of a rule body (the motive and the `n` minors are the extras):
`λ a⃗, T.rec p⃗ motive m⃗ e⃗_i(a⃗) (f_i a⃗)` — at a finitary field the
telescope is empty and this is the recursor at the prefix, the field's
indices and the field. -/
def structIhApp (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr :=
  let m := tele.length
  Expr.mkLamsOf (structTeleAt nF (n + 1) i 0 pw tele)
    (Expr.mkAppN (.const recC rlvls)
      (structRecPrefixAt nP n nF m ++ idx.map (structIdxAt nF (n + 1) i 0 m) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + m)) (structTeleVars m)]))

/-- The right-hand side body of rule `j` at a recursive block: minor
`j` at the fields, then at the inductive hypotheses of the recursive
fields (`structRuleBodyAt` with the `ih` arguments; `teleOf i` and
`idxOf i` are field `i`'s telescope and index expressions). -/
def structRuleBodyR (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF j : Nat)
    (recIdx : List Nat)
    (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) : Expr :=
  Expr.mkAppN (.bvar (nF + n - 1 - j))
    (((List.range nF).map fun k => Expr.bvar (nF - 1 - k)) ++
      recIdx.map fun i => structIhApp recC rlvls pw nP n nF i (teleOf i) (idxOf i))

/-- The `ih` binders of a minor premise: for each recursive field
position (in order), `∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)` under the `l`
earlier `ih` binders, the motive sitting `nF + o - 1` binders above the
fields and the field's telescope and index expressions moved to that
frame (a finitary field: `motive e⃗_i f_i`). -/
def structIhPis (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (Expr × BinderMeta))
    (idxOf : Nat → List Expr) : List Nat → Nat → Expr → Expr
  | [], _, body => body
  | i :: is, l, body =>
    let m := (teleOf i).length
    .forallE
      (Expr.mkPisOf (structTeleAt nF o i l pw (teleOf i))
        (Expr.mkAppN (.bvar (nF + o - 1 + l + m))
          ((idxOf i).map (structIdxAt nF o i l m) ++
            [Expr.mkAppN (.bvar (nF - 1 - i + l + m)) (structTeleVars m)])))
      (structIhPis nF o pw teleOf idxOf is (l + 1) body) ⟨pw⟩

/-- A constructor's minor premise at a recursive block: its field
telescope lifted under the `o` extras, every binder's datum reset to
the elimination datum, then the `ih` binders, ending in
`motive e⃗ (C p⃗ f⃗)` — `structMinorTyI`'s conclusion — lifted above
the `ih`s. -/
def structMinorTyR (C : Name) (lps : List Name) (nP nF o : Nat) (pw : PropWhen)
    (cty : Expr) (recIdx : List Nat) : Option Expr :=
  (cty.stripPis nP).bind fun q =>
  (q.2.stripPis nF).bind fun r =>
    Expr.replacePisPw pw nF (q.2.liftLooseBVars o 0)
      (structIhPis nF o pw (structFieldTeleOf cty nP nF) (structFieldIdxOf cty nP nF) recIdx 0
        ((Expr.mkAppN (.bvar (nF + o - 1))
          ((r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
            [structCtorSpineAt C lps o nP nF])).liftLooseBVars recIdx.length 0))

/-- The minor premises' `∀`-telescope at a recursive block, one per
constructor `(C, nF, cty, recIdx)`. -/
def structMinorsPisR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (structMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (structMinorsPisR lps nP pw cs (o + 1) body).map fun rest =>
        .forallE mty rest ⟨pw⟩

/-- The `λ` twin of `structMinorsPisR`. -/
def structMinorsLamsR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (structMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (structMinorsLamsR lps nP pw cs (o + 1) body).map fun rest =>
        .lam mty rest ⟨pw⟩

/-- **The generated recursor type at a recursive block**

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_C : ∀ f⃗ (ih⃗ : motive e⃗_i f_i)…, motive e⃗ (C p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(`structRecTyI` with `ih` binders in the minors; `tty = ∀ p⃗ ı⃗, Sort w`
is the annotated type former's type). -/
def structRecTyR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) : Option Expr :=
  let ℓ := structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  (tty.stripPis nP).bind fun q =>
  (structMotiveTyI T lps nP nIdx ℓ q.2).bind fun motiveTy =>
  (Expr.replacePisPw pw nIdx (q.2.liftLooseBVars (n + 1) 0)
      (.forallE (structFamI T lps nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (structPsAt 1 nIdx ++ [.bvar 0]))
        ⟨pw⟩)).bind fun major =>
  (structMinorsPisR lps nP pw ctors 1 major).bind fun minors =>
    Expr.replacePisPw pw nP tty
      (.forallE motiveTy minors ⟨pw⟩)

/-- **The generated rule** for constructor `j` at a recursive block:
`λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j (T.rec p⃗ motive minor⃗ e⃗_i f_i)…`
(`structRecRhsI` with the inductive hypotheses; `recC`/`rlvls` are the
recursor's name and its level parameters as levels). -/
def structRecRhsR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) (j : Nat) : Option Expr :=
  let ℓ := structElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  match ctors[j]? with
  | none => none
  | some (_, nF, cty, recIdx) =>
    (tty.stripPis nP).bind fun tq =>
    (structMotiveTyI T lps nP nIdx ℓ tq.2).bind fun motiveTy =>
    (cty.stripPis nP).bind fun q =>
    (Expr.pisToLamsPw pw nF (q.2.liftLooseBVars (n + 1) 0)
        (structRuleBodyR recC rlvls pw nP n nF j recIdx (structFieldTeleOf cty nP nF)
          (structFieldIdxOf cty nP nF))).bind
      fun inner =>
    (structMinorsLamsR lps nP pw ctors 1 inner).bind fun minors =>
    Expr.pisToLamsPw pw nP tty
      (.lam motiveTy minors ⟨pw⟩)

/-- The constructors zipped with their recursive positions, as the
generators take them. -/
def nativeCtors4 (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) :
    List (Name × Nat × Expr × List Nat) :=
  List.zipWith (fun cA ks => (cA.1.name, cA.2, cA.1.type, recIdxOf ks)) ctorsA kinds

/-- **The rule's `λ` prefix against the stream's own recursor type**
(task #271, issue #7).

The rule `λ p⃗ motive minor⃗ f⃗_j, …` binds, in order, the recursor's
parameters, its motive, its minor premises and constructor `j`'s
fields — and every one of those binder types appears again in the
recursor RECORD's own type
`∀ p⃗ motive minor⃗ ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t`: the first `nP + 1 + n`
binders at exactly the same de Bruijn depths, and the fields as the
first `nF` binders of the `j`-th minor premise's type, which stands
`n - j` binders shallower than the rule's fields do.  So the rule's
whole `λ` prefix is *elsewhere in the same stream*, and this compares
the two.  Official's replay compares an exported recursor with the
generated one as a whole, so a stream whose recursor IS the generated
one satisfies this; a rule that retargets a binder type does not.

It is deliberately NOT a comparison with `structRecRhsR`.  The
generated rule cannot be compared with the exported one binder for
binder, because the two are generated from different data: this route
generates from the STORED constructors — their field domains
normalised by official's positivity walk — and from the type former's
DECLARED telescope, while official generates from the declared
constructor types and from a telescope reduced to weak head normal
form.  Both directions occur on real streams: at the arena's
`053_reduceCtorParam.mk` the export's minor carries the declared redex
`constType (reduceCtorParam α) …` where this route has the reduct, and
at `HPow` the export's parameter binder is `Sort (w+1)` where this
route's declared telescope still has `outParam (Sort (w+1))`.
Comparing the terms rejects 45 e2e fixtures and three good arena tests
that official accepts.  For the same reason the fields are read off
the recursor's minor and not off the constructor RECORD: at
`Lean.SourceInfo.synthetic` the record's third field is
`optParam Bool false` where the generated recursor — and the rule —
has `Bool`. -/
def nativeRulePrefixOk (recTy : Expr) (nP n j nF : Nat) (rhs : Expr) : Bool :=
  match rhs.stripLams (nP + 1 + n + nF), recTy.stripPis (nP + 1 + n) with
  | some (rbs, _), some (tbs, _) =>
    (List.range (nP + 1 + n)).all (fun i =>
      match rbs[i]?, tbs[i]? with
      | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
      | _, _ => false) &&
    (match tbs[nP + 1 + j]? with
     | some mty =>
       (match (mty.1.liftLooseBVars (n - j) 0).stripPis nF with
        | some (fbs, _) =>
          (List.range nF).all fun i =>
            match rbs[nP + 1 + n + i]?, fbs[i]? with
            | some b, some f => Expr.resetMeta b.1 == Expr.resetMeta f.1
            | _, _ => false
        | none => false)
     | none => false)
  | _, _ => false

/-- **The stream's rules against the generated ones** (task #210 Part
D, at install): rule `j` fires constructor `j` with its field count,
and its body is the canonical right-hand side with the inductive
hypotheses — generated from the STORED constructors (their field
domains normalised by official's positivity walk, which is what the
elaborator generated the stream's rules from), at the parse
placeholder's binder data (`resetMeta`).  Official's replay compares an
exported recursor structurally with the one it generates; this is that
comparison, on the bodies (the type is `isDefEq`'d at
`checkNativeRec`) and — since task #271 — on the `λ` prefix's binder
types, against the stream's own recursor type and constructor records
(`nativeRulePrefixOk`, which says why the comparison is against the
stream's own recursor type and not against the generated term). -/
def nativeRulesOk (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n : Nat)
    (cs : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) (rhss : List Expr)
    (recTy : Expr) :
    Bool :=
  rhss.length == n && kinds.length == n &&
  (List.range n).all fun j =>
    match rhss[j]?, cs[j]?, kinds[j]? with
    | some rhs, some (cA, nF), some ks =>
      ks.length == nF &&
      (match rhs.stripLams (nP + 1 + n + nF) with
       | some (_, rbody) =>
         rbody == Expr.resetMeta (structRuleBodyR recC rlvls pw nP n nF j (recIdxOf ks)
           (structFieldTeleOf cA.type nP nF) (structFieldIdxOf cA.type nP nF))
       | none => false) &&
      nativeRulePrefixOk recTy nP n j nF rhs
    | _, _, _ => false

/-! ## Recognition

**The type-and-constructor gate, split off the recursor pin**
(task #220).  Official never reads the exported recursor as an *input*:
`add_inductive` takes the type formers, the constructors and the
parameter count, checks them (`check_inductive_types`,
`check_constructors`, `check_positivity`) and GENERATES the recursor;
the replay then compares each exported recursor record with the
generated one, structurally, and a mismatch is a REJECT ("Invalid
recursor", "No such recursor" — `Lean4Checker/Replay.lean`).  So the
recogniser below reads the block's parameter and index counts the way
official reads them — the parameters as DECLARED (task #228: the count
official's `add_inductive` is handed, checked against the former's
telescope and against every constructor), the indices off the type
former's own telescope — and pins nothing of the recursor record
beyond the level-parameter shape that decides which recursor is
generated.  Everything the recursor record claims is compared at the
install (`nativeRecPinOk` here, the name and the type and the rule
bodies at `checkNativeRec`/`nativeRulesOk`), where a mismatch
REJECTS.  Before task #220 those pins sat in the recogniser, so a block
whose recursor record was a stub fell through to a DECLINE and the
semantic checks that would have rejected it — positivity, the field
universes, the constructor result — never ran (arena finding F1). -/

/-- **The recursor record's level-parameter pin** (task #220): the
recursor official generates carries the block's own level parameters,
with a fresh elimination parameter in front at the LARGE eliminator.
The recogniser reads which of the two the record claims and records
the verdict here; `checkNativeRec` throws on `false`, as official's
replay rejects a recursor whose level parameters are not the generated
ones. -/
def nativeRecLpsOk (p : InductiveShape) : Bool :=
  if p.large then p.cvR.levelParams == p.elim :: p.cvT.levelParams
  else p.cvR.levelParams == p.cvT.levelParams


/-! ## The one-member reading of the k-ary record (conformance only;
moved from `BlockParts`/`SumInstall` by lane NESTPOS, CONFDIR's follow-up) -/

/-- The recursor's rule prefix (parameters, motive, minors) and its
major index (the rule prefix, then the indices). -/
def InductiveShape.rulePrefix (p : InductiveShape) : Nat := p.nP + 1 + p.ctors.length
def InductiveShape.majorIdx (p : InductiveShape) : Nat := p.rulePrefix + p.nIdx

/-- Every recursor's rule prefix AT THE GENERATED SHAPE: the
parameters, the k motives and the block's minors (official's
`nparams + ntypes + nminors`).  This is what the reject-only
conformance check's generator builds and compares. -/
def BlockShape.rulePrefix (p : BlockShape) : Nat := p.nP + p.k + p.numCtors

/-- Member `m`'s recursor's major-premise index at the GENERATED
shape. -/
def BlockShape.majorIdx (p : BlockShape) (m : Nat) : Nat :=
  p.rulePrefix + (p.members.getD m default).nIdx

/-- **The recursor records' two argument SUMS at the GENERATED
shape**: the pin the one-member conformance check makes (the
ruling of 2026-09-21 moved it there, out of `blockRecPinOk`, because
the motive-free check reads the sums and derives nothing).  It is what
`BlockParts.toNative` adds to the record's own pin. -/
def BlockShape.recSumsOk (p : BlockShape) : Bool :=
  (List.range p.recs.length).all fun r =>
    (p.recs.getD r default).rP == p.rulePrefix &&
      (p.recs.getD r default).mI
        == p.rulePrefix + (p.members.getD (p.recTgtAt r) default).nIdx

@[simp] theorem BlockShape.withSort_rulePrefix (p : BlockShape) (s : Level) :
    (p.withSort s).rulePrefix = p.rulePrefix := rfl
@[simp] theorem BlockShape.withSort_recSumsOk (p : BlockShape) (s : Level) :
    (p.withSort s).recSumsOk = p.recSumsOk := rfl
@[simp] theorem BlockShape.withSort_majorIdx (p : BlockShape) (s : Level) (m : Nat) :
    (p.withSort s).majorIdx m = p.majorIdx m := rfl

/-- **The one-member reading of the shape** (the M1 bridge): at
`k = 1` a `BlockShape` IS an `InductiveShape`.  At `k ≠ 1` it reads
member 0 and is junk — its only consumer is the reject-only
conformance check (`checkBlockRecConform`), which runs at one member
with one recursor and is skipped at every other shape. -/
def BlockShape.toInductive (p : BlockShape) : InductiveShape :=
  let ms := p.members.headD default
  let rc := p.recs.headD default
  ⟨ms.cvT, ms.ctors, p.nP, ms.nIdx, rc.cvR, p.elim, p.resSort, rc.rhss, p.large, p.isProp⟩

/-- **The one-member reading of the record**: the shape's, with the
kinds' targets forgotten and the recursor record's two argument SUMS
added to the pin — at `k = 1` the generate-and-compare arm is where
they belong (the ruling of 2026-09-21), and `toNative` IS that
check's reading. -/
def BlockParts.toNative (p : BlockParts) : NativeParts :=
  ⟨p.toBlockShape.toInductive,
    (p.kinds.headD []).map (List.map BlockFieldKind.toRec),
    p.toBlockShape.recSumsOk && p.recPinned⟩

@[simp] theorem BlockShape.toInductive_withSort (p : BlockShape) (s : Level) :
    (p.withSort s).toInductive = p.toInductive.withSort s := rfl

end ConLeche
