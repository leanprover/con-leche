import ConLeche.Kernel.Direct.SumParts

/-!
# The direct recursive class: recognition and the generated recursor
(task #188)

A **direct recursive** block is a non-nested inductive family with
any number of constructors and any number of indices in which the
type former occurs in some constructor field, every such occurrence
being **finitary and strictly positive**: the field's domain is
exactly the family at the block's parameters followed by index
expressions, `T p⃗ e⃗` (`Nat`, `List`, binary trees, `Vector`-like
families, `Lean.Level`, `Lean.Expr`, `Lean.Name`, …; a structure with a
recursive field is the one-constructor instance).  The model is the
Knaster–Tarski least pre-fixed FAMILY of the constructor-tower functor
over the index-tuple set (`ConLeche/SetTheory/Derive/LfpFam.lean`,
`ConLeche/Semantics/Tower/FixLeafI.lean`), and the recursor the fixed
point of its own one-step unfolding
(`ConLeche/Semantics/Tower/FixRecI.lean`).

**Positivity** mirrors the official `check_positivity`
(`inductive.cpp`; lean4lean `Inductive/Add.lean:184-199`) syntactically
on each field's domain: a domain that does not mention the block is
ordinary (`.ordinary`); one that is `T p⃗ e⃗` with the block's own
parameters and index expressions free of the block is a finitary
recursive field (`.recursive`); one whose own `∀`-telescope binds a domain
mentioning the block is a NON-POSITIVE occurrence, rejected as the
official kernel rejects it (`.negative`, `.invalid` at install); a
family application at the head with other parameters, levels or
argument count is the official "non valid occurrence", also rejected;
anything else the official kernel accepts or handles by nested
elimination — a reflexive field `∀ y⃗, T p⃗ e⃗`, a nested occurrence
`List (T p⃗)`, an occurrence under a redex, an index expression
mentioning the block or an earlier recursive field — is NOT this
route's (`.unsupported`; the block falls through to the modeled path):
the ω-iterate is a closed member only for finitary constructors, the
functor is graded at an arbitrary family, and the nested translation
is a later task.  The recogniser classifies the raw types; the install
re-checks the classification on the annotated types
(`directFixFieldsOk`), so the proof reads it off the stored constants.

**The recursor** is generated and compared (task #175 S2): each
minor premise binds the constructor's fields, then one **inductive
hypothesis** `f_i_ih : motive e⃗_i f_i` per recursive field in field
order (`e⃗_i` the field's index expressions), and concludes
`motive e⃗ (C p⃗ f⃗)` (official `mk_rec_infos`:
`mkForall bu (mkForall v motiveApp)`); rule `j`'s right-hand side is
`λ p⃗ motive m⃗ f⃗, minor_j f⃗ (T.rec p⃗ motive m⃗ e⃗_i f_i)…` (official
`mk_rec_rules`: the minor at the fields, then the recursor at every
recursive field).  The generators below are the indexed ones of
`ConLeche/Kernel/Direct/Parts.lean` with the `ih` binders threaded.
-/

namespace ConLeche

/-- The kind of a constructor field of a recursive block (see the
module docstring). -/
inductive RecFieldKind where
  /-- the domain does not mention the block -/
  | ordinary
  /-- the domain is exactly `T p⃗ e⃗`: a finitary recursive field -/
  | recursive
  /-- the domain is `Π a⃗ : A⃗, T p⃗ e⃗(a⃗)` with `A⃗` free of the block: a
  REFLEXIVE (function-space) recursive field (task #202) -/
  | reflexive
  /-- a non-positive (or non-valid) occurrence: the official kernel
  rejects the block -/
  | negative
  /-- an occurrence the official kernel accepts (reflexive, nested,
  under a redex) that this route does not model yet -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- Is `e` the family at the parameter variables (sitting `o` binders
up) followed by `nIdx` index expressions none of which mentions the
block?  Official's `is_valid_ind_app` exactly: the head, the arity,
the parameters (structurally) and `has_ind_occ` on every index
argument (inductive.cpp, task #210 Part D). -/
def recFamOk (T : Name) (lps : List Name) (nP nIdx o : Nat) (e : Expr) : Bool :=
  e.getAppFn == Expr.const T (lps.map .param) &&
  e.getAppArgs.length == nP + nIdx &&
  e.getAppArgs.take nP == directPsAt o nP &&
  (e.getAppArgs.drop nP).all fun a => !a.mentionsConst T

/-- Official `check_positivity`'s telescope walk on a field domain that
mentions the block, syntactically: `k` binders of the field's own
telescope have been peeled (the parameters sit `o + k` binders up).
A family application at the head whose parameters are not the
block's, with the wrong number of arguments, or whose INDEX expressions
mention the block is the official "non valid occurrence" (`.negative`:
`is_valid_ind_app` rejects all three); an application of another
constant is a nested occurrence (`.unsupported`: the modeled path). -/
def recPositivity (T : Name) (lps : List Name) (nP nIdx o : Nat) : Expr → Nat → RecFieldKind
  | .forallE dom body _, k =>
    if dom.mentionsConst T then .negative else recPositivity T lps nP nIdx o body (k + 1)
  | e, k =>
    if !e.mentionsConst T then .ordinary
    else if e.getAppFn == Expr.const T (lps.map .param) then
      if e.getAppArgs.length == nP + nIdx && e.getAppArgs.take nP == directPsAt (o + k) nP then
        (if recFamOk T lps nP nIdx (o + k) e then
          (if k == 0 then .recursive else .reflexive)
         else .negative)
      else .negative
    else
      match e.getAppFn with
      | .const T' _ => if T' == T then .negative else .unsupported
      | _ => .unsupported

/-- The kind of a field whose domain is `dom`, `o` fields into the
constructor's telescope. -/
def recFieldKind (T : Name) (lps : List Name) (nP nIdx o : Nat) (dom : Expr) : RecFieldKind :=
  if dom.mentionsConst T then recPositivity T lps nP nIdx o dom 0 else .ordinary

/-- The kinds of one constructor's fields, off its (raw or annotated)
type.  A recursive field that a LATER binder or the constructor's
residual mentions (`directUsedLater`) is marked unsupported: the model
reads the ordinary domains and the index expressions at a frame whose
recursive slots hold an arbitrary value, so neither may depend on one.
On a constructor official accepts, with its field domains normalised
(`normPosDom`), the guard cannot fire (task #210 Part D): a term
containing a variable of type `T p⃗ e⃗` contains the constant `T`
(its consumer's domain is a subterm, and a `T`-free term is not
definitionally the block); the normalised later domains that mention
`T` are Π-chains with `T`-free domains ending in the family at
`T`-free indices (official's `is_valid_ind_app`, `recFamOk`) or
invalid, and the residual's index expressions are `T`-free for the
same reason (official's "invalid return type", the last conjunct
below, `.negative`).  So the guard is the model's own invariant, never
a verdict of its own. -/
def recCtorKinds (T : Name) (lps : List Name) (nP nIdx : Nat) (c : ConstantVal × Nat) :
    Option (List RecFieldKind) :=
  match c.1.type.stripPis (nP + c.2) with
  | some (cbs, cbody) =>
    let ks := (List.range c.2).map fun i =>
      match recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
      | .recursive => if directUsedLater c.1.type nP i then .unsupported else .recursive
      | .reflexive => if directUsedLater c.1.type nP i then .unsupported else .reflexive
      | k => k
    if (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) then some ks
    else some (ks.map fun _ => .negative)
  | none => none

/-- All leading `∀` binders of an expression (outermost first) and
the body — a recursive field's own telescope (`[]` at a finitary
field, the `a⃗ : A⃗` of a reflexive one, task #202). -/
def Expr.piBinders : Expr → List (Expr × BinderMeta) × Expr
  | .forallE ty b m =>
    let (bs, e) := piBinders b
    ((ty, m) :: bs, e)
  | e => ([], e)

/-- Field `i`'s own telescope `a⃗ : A⃗` (at the field's frame: the
parameters and the earlier fields), off the constructor's type. -/
def directFieldTeleOf (cty : Expr) (nP nF i : Nat) : List (Expr × BinderMeta) :=
  match cty.stripPis (nP + nF) with
  | some (cbs, _) => ((cbs.getD (nP + i) default).1.piBinders).1
  | none => []

/-- The index expressions of field `i`'s domain `Π a⃗, T p⃗ e⃗` (under
the field's own telescope, at the field's frame), off the
constructor's type; `[]` when the field is not of that shape. -/
def directFieldIdxOf (cty : Expr) (nP nF i : Nat) : List Expr :=
  match cty.stripPis (nP + nF) with
  | some (cbs, _) => ((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs.drop nP
  | none => []

/-- The positions of the recursive fields (finitary or reflexive: the
ones with an inductive hypothesis). -/
def recIdxOf (ks : List RecFieldKind) : List Nat :=
  (List.range ks.length).filter fun i =>
    ks.getD i .ordinary == .recursive || ks.getD i .ordinary == .reflexive

/-- The pieces of a recognised direct recursive block: the sum parts
(with the family's index count) and the per-constructor field kinds. -/
structure DirectFixParts extends DirectSumParts where
  /-- per constructor, per field: its kind -/
  kinds : List (List RecFieldKind)
  deriving Repr

/-- **The record completed by the former's stage** (task #210 Part B):
the sum parts the former's run returned (its result sort read through
`whnf`, task #195) with the recogniser's field kinds.  A definition,
not a literal, so that a proof's `dsimp` keeps it in one piece. -/
def DirectFixParts.complete (p₀ : DirectFixParts) (p₁ : DirectSumParts) : DirectFixParts :=
  ⟨p₁, p₀.kinds⟩

@[simp] theorem DirectFixParts.complete_toDirectSumParts (p₀ : DirectFixParts)
    (p₁ : DirectSumParts) : (p₀.complete p₁).toDirectSumParts = p₁ := rfl
@[simp] theorem DirectFixParts.complete_kinds (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).kinds = p₀.kinds := rfl
@[simp] theorem DirectFixParts.complete_cvT (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).cvT = p₁.cvT := rfl
@[simp] theorem DirectFixParts.complete_ctors (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).ctors = p₁.ctors := rfl
@[simp] theorem DirectFixParts.complete_nP (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).nP = p₁.nP := rfl
@[simp] theorem DirectFixParts.complete_nIdx (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).nIdx = p₁.nIdx := rfl
@[simp] theorem DirectFixParts.complete_cvR (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).cvR = p₁.cvR := rfl
@[simp] theorem DirectFixParts.complete_elim (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).elim = p₁.elim := rfl
@[simp] theorem DirectFixParts.complete_resSort (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).resSort = p₁.resSort := rfl
@[simp] theorem DirectFixParts.complete_rhss (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).rhss = p₁.rhss := rfl
@[simp] theorem DirectFixParts.complete_large (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).large = p₁.large := rfl
@[simp] theorem DirectFixParts.complete_isProp (p₀ : DirectFixParts) (p₁ : DirectSumParts) :
    (p₀.complete p₁).isProp = p₁.isProp := rfl

/-! ## The generated recursor with inductive hypotheses -/

/-- The parameter, motive and minor variables as seen from under the
`nF` fields (and `e` further binders): the recursor's leading spine
`p⃗ motive m⃗` at that frame. -/
def directRecPrefixAt (nP n nF e : Nat) : List Expr :=
  directPsAt (e + nF + n + 1) nP ++ [Expr.bvar (e + nF + n)] ++
    (List.range n).map fun l => Expr.bvar (e + nF + n - 1 - l)

/-- An expression of recursive field `i`'s domain sitting under `m`
binders of the field's own telescope, spelled at the field's frame
(the parameters, the `i` earlier fields), moved under all `nF` fields,
`l` further binders below them and `o` extras between the parameters
and the fields: the earlier fields move by `nF - i + l`, the
parameters by `o` more; the `m` telescope binders stay. -/
def directIdxAt (nF o i l m : Nat) (e : Expr) : Expr :=
  (e.liftLooseBVars (nF - i + l) m).liftLooseBVars o (nF + l + m)

/-- Field `i`'s own telescope moved as `directIdxAt` moves its
expressions (binder `k` sits under `k` earlier telescope binders). -/
def directTeleAt (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr × BinderMeta)) :
    List (Expr × BinderMeta) :=
  (List.range tele.length).map fun k =>
    let b := tele.getD k default
    (directIdxAt nF o i l k b.1, ⟨pw⟩)

/-- The variables of an `m`-binder telescope, innermost last. -/
def directTeleVars (m : Nat) : List Expr := (List.range m).map fun k => Expr.bvar (m - 1 - k)

/-- `∀ tele, body` / `λ tele, body` over a binder list (outermost first). -/
def Expr.mkPisOf : List (Expr × BinderMeta) → Expr → Expr
  | [], body => body
  | (ty, mt) :: bs, body => .forallE ty (mkPisOf bs body) mt
def Expr.mkLamsOf : List (Expr × BinderMeta) → Expr → Expr
  | [], body => body
  | (ty, mt) :: bs, body => .lam ty (mkLamsOf bs body) mt

/-- The inductive hypothesis' value for recursive field `i` with
telescope `tele` and index expressions `idx`, spelled under the fields
of a rule body (the motive and the `n` minors are the extras):
`λ a⃗, T.rec p⃗ motive m⃗ e⃗_i(a⃗) (f_i a⃗)` — at a finitary field the
telescope is empty and this is the recursor at the prefix, the field's
indices and the field. -/
def directIhApp (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr :=
  let m := tele.length
  Expr.mkLamsOf (directTeleAt nF (n + 1) i 0 pw tele)
    (Expr.mkAppN (.const recC rlvls)
      (directRecPrefixAt nP n nF m ++ idx.map (directIdxAt nF (n + 1) i 0 m) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + m)) (directTeleVars m)]))

/-- The right-hand side body of rule `j` at a recursive block: minor
`j` at the fields, then at the inductive hypotheses of the recursive
fields (`directRuleBodyAt` with the `ih` arguments; `teleOf i` and
`idxOf i` are field `i`'s telescope and index expressions). -/
def directRuleBodyR (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF j : Nat)
    (recIdx : List Nat)
    (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) : Expr :=
  Expr.mkAppN (.bvar (nF + n - 1 - j))
    (((List.range nF).map fun k => Expr.bvar (nF - 1 - k)) ++
      recIdx.map fun i => directIhApp recC rlvls pw nP n nF i (teleOf i) (idxOf i))

/-- The `ih` binders of a minor premise: for each recursive field
position (in order), `∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)` under the `l`
earlier `ih` binders, the motive sitting `nF + o - 1` binders above the
fields and the field's telescope and index expressions moved to that
frame (a finitary field: `motive e⃗_i f_i`). -/
def directIhPis (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (Expr × BinderMeta))
    (idxOf : Nat → List Expr) : List Nat → Nat → Expr → Expr
  | [], _, body => body
  | i :: is, l, body =>
    let m := (teleOf i).length
    .forallE
      (Expr.mkPisOf (directTeleAt nF o i l pw (teleOf i))
        (Expr.mkAppN (.bvar (nF + o - 1 + l + m))
          ((idxOf i).map (directIdxAt nF o i l m) ++
            [Expr.mkAppN (.bvar (nF - 1 - i + l + m)) (directTeleVars m)])))
      (directIhPis nF o pw teleOf idxOf is (l + 1) body) ⟨pw⟩

/-- A constructor's minor premise at a recursive block: its field
telescope lifted under the `o` extras, every binder's datum reset to
the elimination datum, then the `ih` binders, ending in
`motive e⃗ (C p⃗ f⃗)` — `directMinorTyI`'s conclusion — lifted above
the `ih`s. -/
def directMinorTyR (C : Name) (lps : List Name) (nP nF o : Nat) (pw : PropWhen)
    (cty : Expr) (recIdx : List Nat) : Option Expr :=
  (cty.stripPis nP).bind fun q =>
  (q.2.stripPis nF).bind fun r =>
    Expr.replacePisPw pw nF (q.2.liftLooseBVars o 0)
      (directIhPis nF o pw (directFieldTeleOf cty nP nF) (directFieldIdxOf cty nP nF) recIdx 0
        ((Expr.mkAppN (.bvar (nF + o - 1))
          ((r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
            [directCtorSpineAt C lps o nP nF])).liftLooseBVars recIdx.length 0))

/-- The minor premises' `∀`-telescope at a recursive block, one per
constructor `(C, nF, cty, recIdx)`. -/
def directMinorsPisR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (directMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (directMinorsPisR lps nP pw cs (o + 1) body).map fun rest =>
        .forallE mty rest ⟨pw⟩

/-- The `λ` twin of `directMinorsPisR`. -/
def directMinorsLamsR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (directMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (directMinorsLamsR lps nP pw cs (o + 1) body).map fun rest =>
        .lam mty rest ⟨pw⟩

/-- **The generated recursor type at a recursive block**

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_C : ∀ f⃗ (ih⃗ : motive e⃗_i f_i)…, motive e⃗ (C p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(`directRecTyI` with `ih` binders in the minors; `tty = ∀ p⃗ ı⃗, Sort w`
is the annotated type former's type). -/
def directRecTyR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
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
  (directMinorsPisR lps nP pw ctors 1 major).bind fun minors =>
    Expr.replacePisPw pw nP tty
      (.forallE motiveTy minors ⟨pw⟩)

/-- **The generated rule** for constructor `j` at a recursive block:
`λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j (T.rec p⃗ motive minor⃗ e⃗_i f_i)…`
(`directRecRhsI` with the inductive hypotheses; `recC`/`rlvls` are the
recursor's name and its level parameters as levels). -/
def directRecRhsR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
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
    (Expr.pisToLamsPw pw nF (q.2.liftLooseBVars (n + 1) 0)
        (directRuleBodyR recC rlvls pw nP n nF j recIdx (directFieldTeleOf cty nP nF)
          (directFieldIdxOf cty nP nF))).bind
      fun inner =>
    (directMinorsLamsR lps nP pw ctors 1 inner).bind fun minors =>
    Expr.pisToLamsPw pw nP tty
      (.lam motiveTy minors ⟨pw⟩)

/-- The constructors zipped with their recursive positions, as the
generators take them. -/
def directFixCtors4 (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) :
    List (Name × Nat × Expr × List Nat) :=
  List.zipWith (fun cA ks => (cA.1.name, cA.2, cA.1.type, recIdxOf ks)) ctorsA kinds

/-- **The stream's rules against the generated ones** (task #210 Part
D, at install): rule `j` fires constructor `j` with its field count,
and its body is the canonical right-hand side with the inductive
hypotheses — generated from the STORED constructors (their field
domains normalised by official's positivity walk, which is what the
elaborator generated the stream's rules from), at the parse
placeholder's binder data (`resetMeta`).  Official's replay compares an
exported recursor structurally with the one it generates; this is that
comparison, on the bodies (the type is `isDefEq`'d at
`checkDirectFixRec`). -/
def directFixRulesOk (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n : Nat)
    (cs : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) (rhss : List Expr) :
    Bool :=
  rhss.length == n && kinds.length == n &&
  (List.range n).all fun j =>
    match rhss[j]?, cs[j]?, kinds[j]? with
    | some rhs, some (cA, nF), some ks =>
      ks.length == nF &&
      (match rhs.stripLams (nP + 1 + n + nF) with
       | some (_, rbody) =>
         rbody == Expr.resetMeta (directRuleBodyR recC rlvls pw nP n nF j (recIdxOf ks)
           (directFieldTeleOf cA.type nP nF) (directFieldIdxOf cA.type nP nF))
       | none => false)
    | _, _, _ => false

/-! ## Recognition -/

/-- The block's shape at a recursive block: `directSumPartsCore?`
without its one-constructor exclusion and without the rule bodies
(which need the field kinds); the index count is read off the
recursor as there.  The rules' names and field counts are pinned
here; their bodies by `directFixRulesOk`. -/
def directFixShape? (block : List ConstantInfo) : Option DirectSumParts :=
  match block with
  | .indInfo cvT _ :: rest =>
    match directSumSplit rest with
    | some (cs, cvR, mI, rP, rules) =>
      let T := cvT.name
      let lps := cvT.levelParams
      let n := cs.length
      if rP < n + 1 || mI < rP then none else
      let nP := rP - (n + 1)
      let nIdx := mI - rP
      if cvR.name == T.str "rec" &&
          reservedBasisNames.contains T == false &&
          reservedBasisNames.contains cvR.name == false &&
          cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
            reservedBasisNames.contains c.1.name == false &&
            (match c.1.type.stripPis (nP + c.2.2) with
             | some (_, cbody) => directCtorResidOk T lps nP c.2.2 nIdx cbody
             | none => false)) &&
          rules.length == n &&
          (List.range n).all (fun j =>
            match rules[j]?, cs[j]? with
            | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
            | _, _ => false) then
        -- the result sort: read off the declared type when it is a
        -- syntactic telescope ending in a sort; otherwise (task #195, a
        -- former declared AT A DEFINITION that only unfolds to its
        -- telescope) a PLACEHOLDER that the install's whnf loop replaces
        -- (`checkDirectSumInd`, `DirectSumParts.withSort`; task #210
        -- Part B lifts the fix route's syntactic reading, the sum route's
        -- former stage being the one it runs)
        let s : Level := match cvT.type.stripPis (nP + nIdx) with
          | some (_, .sort s) => s
          | _ => .zero
        let isProp := Level.isEquiv s .zero == some true
        let ctors := cs.map fun c => (c.1, c.2.2)
        let rhss := rules.map (·.rhs)
        let large? : Option Name :=
          match cvR.levelParams with
          | elim :: relps =>
            if relps == lps && !lps.contains elim then some elim else none
          | [] => none
        match large? with
        | some elim => some ⟨cvT, ctors, nP, nIdx, cvR, elim, s, rhss, true, isProp⟩
        | none =>
          if cvR.levelParams == lps then
            some ⟨cvT, ctors, nP, nIdx, cvR, .anonymous, s, rhss, false, isProp⟩
          else none
      else none
    | none => none
  | _ => none

/-- The record completed with the fields' kinds (task #210 Part D):
the install classifies them on the constructors it stored — their
field domains normalised by official's positivity walk
(`normCtorVal`) — and every later stage runs on this record. -/
def DirectFixParts.withKinds (p : DirectFixParts) (ks : List (List RecFieldKind)) :
    DirectFixParts :=
  { p with kinds := ks }

@[simp] theorem DirectFixParts.withKinds_kinds (p : DirectFixParts)
    (ks : List (List RecFieldKind)) : (p.withKinds ks).kinds = ks := rfl
@[simp] theorem DirectFixParts.withKinds_toDirectSumParts (p : DirectFixParts)
    (ks : List (List RecFieldKind)) : (p.withKinds ks).toDirectSumParts = p.toDirectSumParts := rfl

/-- Recognise a direct block — ONE ROUTE (task #210): its SHAPE
(`directFixShape?`); the fields' kinds are a PLACEHOLDER the install
fills (`DirectFixParts.withKinds`) after normalising every field
domain by official's positivity walk — a syntactic reading here
would refuse a recursive occurrence hidden under a definition, which
official whnf's away (audit #206-A5, Part D).  A block with a
NON-POSITIVE occurrence is admitted so that the install rejects it
exactly as official's positivity check would, before anything else is
looked at.  A nested block is never this route's: it carries an
in-process `_model` family, and the dispatch reads that first.  A
reflexive field is taken at every sort (task #202); a block with no
constructor is this route's too (`FixKI₀.hsq` at most one). -/
def directFixParts? (block : List ConstantInfo) : Option DirectFixParts :=
  (directFixShape? block).map fun p => ⟨p, []⟩

/-- The one route's reading of a block's RAW constructors: does the
syntactic classification (`recCtorKinds`) find no occurrence the route
does not model?  On the raw stream a nested occurrence (`List T`) and
a definition redex over one (`Id' T`) look alike — both `.unsupported`
— and only the install, whnf'ing, tells them apart; here the reading
decides the DISPATCH together with the presence of a model
(`blockIsModeled`). -/
def rawKindsOk (p : DirectSumParts) : Bool :=
  match p.ctors.mapM (recCtorKinds p.cvT.name p.cvT.levelParams p.nP p.nIdx) with
  | some ks => ks.all fun k => k.all (· != .unsupported)
  | none => false

/-- Is the block the modeled path's (task #210 Part D)?  It carries an
in-process `_model` family (the mutual and nested blocks, task #200)
AND the one route's raw reading refuses it (`rawKindsOk`, or the shape
is not the route's at all).  The first conjunct keeps a redex-hidden
occurrence (`Id' T`, arena 053) where no model exists on the route,
which whnf's it; the second keeps a block the route takes with a stale
model beside it (the preprocessor-era fixture streams' `PProd'._model`)
on the route, its projection table with it. -/
def blockIsModeled (find? : Name → Option ConstantInfo) (block : List ConstantInfo) : Bool :=
  match block with
  | .indInfo cvT _ :: _ =>
    (find? (cvT.name.str "_model")).isSome &&
    (match directFixShape? block with
     | some p => !rawKindsOk p
     | none => true)
  | _ => false

end ConLeche
