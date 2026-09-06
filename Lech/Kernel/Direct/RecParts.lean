import Lech.Kernel.Direct.SumParts

/-!
# The direct recursive class: recognition and the generated recursor
(task #188)

A **direct recursive** block is a non-indexed, non-nested inductive
with any number of constructors in which the type former occurs in
some constructor field, every such occurrence being **finitary and
strictly positive**: the field's domain is exactly the family at the
block's parameters, `T p⃗` (`Nat`, `List`, binary trees, `Lean.Level`,
`Lean.Expr`, `Lean.Name`, …; a structure with a recursive field is the
one-constructor instance).  The model is the Knaster–Tarski least
pre-fixed point of the constructor-tower functor
(`Lech/SetTheory/Derive/Lfp.lean`), and the recursor the fixed point of
its own one-step unfolding (`Lech/Semantics/Tower/FixRec.lean`).

**Positivity** mirrors the official `check_positivity`
(`inductive.cpp`; lean4lean `Inductive/Add.lean:184-199`) syntactically
on each field's domain: a domain that does not mention the block is
ordinary (`.ordinary`); one that is literally `T p⃗` is a finitary
recursive field (`.recursive`); one whose own `∀`-telescope binds a domain
mentioning the block is a NON-POSITIVE occurrence, rejected as the
official kernel rejects it (`.negative`, `.invalid` at install); a
family application at the head with other arguments or levels is the
official "non valid occurrence", also rejected; anything else the
official kernel accepts or handles by nested elimination — a
reflexive field `∀ y⃗, T p⃗`, a nested occurrence `List (T p⃗)`, an
occurrence under a redex — is positively declined (`.unsupported`,
`.notImplemented`): the ω-iterate is a closed member only for finitary
constructors, and the nested translation is a later task.  The
recogniser classifies the raw types; the install re-checks the
classification on the annotated types (`directFixFieldsOk`), so the
proof reads it off the stored constants.

**The recursor** is generated and compared (task #175 S2): each
minor premise binds the constructor's fields, then one **inductive
hypothesis** `f_i_ih : motive f_i` per recursive field in field
order, and concludes `motive (C p⃗ f⃗)` (official `mk_rec_infos`:
`mkForall bu (mkForall v motiveApp)`); rule `j`'s right-hand side is
`λ p⃗ motive m⃗ f⃗, minor_j f⃗ (T.rec p⃗ motive m⃗ f_i)…` (official
`mk_rec_rules`: the minor at the fields, then the recursor at every
recursive field).  The generators below are the index-free ones of
`Lech/Kernel/Direct/Parts.lean` with the `ih` binders threaded.
-/

namespace Lech

/-- Does the constant `T` occur in `e`?  A syntactic walk (`fvar`
annotations included; a `.proj` node names its structure). -/
def Expr.mentionsConst (T : Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => n == T
  | .fvar _ _ ty => ty.mentionsConst T
  | .app f a => f.mentionsConst T || a.mentionsConst T
  | .lam _ ty b _ | .forallE _ ty b _ => ty.mentionsConst T || b.mentionsConst T
  | .letE _ ty v b => ty.mentionsConst T || v.mentionsConst T || b.mentionsConst T
  | .proj s _ e => s == T || e.mentionsConst T

/-- The kind of a constructor field of a recursive block (see the
module docstring). -/
inductive RecFieldKind where
  /-- the domain does not mention the block -/
  | ordinary
  /-- the domain is exactly `T p⃗`: a finitary recursive field -/
  | recursive
  /-- a non-positive (or non-valid) occurrence: the official kernel
  rejects the block -/
  | negative
  /-- an occurrence the official kernel accepts (reflexive, nested,
  under a redex) that this route does not model yet -/
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- Official `check_positivity`'s telescope walk on a field domain that
mentions the block, syntactically: `k` binders of the field's own
telescope have been peeled (the parameters sit `o + k` binders up). -/
def recPositivity (T : Name) (lps : List Name) (nP o : Nat) : Expr → Nat → RecFieldKind
  | .forallE _ dom body _, k =>
    if dom.mentionsConst T then .negative else recPositivity T lps nP o body (k + 1)
  | e, k =>
    if !e.mentionsConst T then .ordinary
    else if e.getAppFn == Expr.const T (lps.map .param) then
      if e.getAppArgs == directPsAt (o + k) nP then
        (if k == 0 then .recursive else .unsupported)
      else .negative
    else
      match e.getAppFn with
      | .const T' _ => if T' == T then .negative else .unsupported
      | _ => .unsupported

/-- The kind of a field whose domain is `dom`, `o` fields into the
constructor's telescope. -/
def recFieldKind (T : Name) (lps : List Name) (nP o : Nat) (dom : Expr) : RecFieldKind :=
  if dom.mentionsConst T then recPositivity T lps nP o dom 0 else .ordinary

/-- The kinds of one constructor's fields, off its (raw or annotated)
type. -/
def recCtorKinds (T : Name) (lps : List Name) (nP : Nat) (c : ConstantVal × Nat) :
    Option (List RecFieldKind) :=
  match c.1.type.stripPis (nP + c.2) with
  | some (cbs, _) =>
    some ((List.range c.2).map fun i => recFieldKind T lps nP i (cbs.getD (nP + i) default).2.1)
  | none => none

/-- The positions of the recursive fields. -/
def recIdxOf (ks : List RecFieldKind) : List Nat :=
  (List.range ks.length).filter fun i => ks.getD i .ordinary == .recursive

/-- The pieces of a recognised direct recursive block: the sum parts
(at `nIdx = 0`) and the per-constructor field kinds. -/
structure DirectFixParts extends DirectSumParts where
  /-- per constructor, per field: its kind -/
  kinds : List (List RecFieldKind)
  deriving Repr

/-! ## The generated recursor with inductive hypotheses -/

/-- The parameter, motive and minor variables as seen from under the
`nF` fields (and `e` further binders): the recursor's leading spine
`p⃗ motive m⃗` at that frame. -/
def directRecPrefixAt (nP n nF e : Nat) : List Expr :=
  directPsAt (e + nF + n + 1) nP ++ [Expr.bvar (e + nF + n)] ++
    (List.range n).map fun l => Expr.bvar (e + nF + n - 1 - l)

/-- The inductive hypothesis' value for recursive field `i`, spelled
under the fields: the recursor at the prefix and the field. -/
def directIhApp (recC : Name) (rlvls : List Level) (nP n nF i : Nat) : Expr :=
  Expr.mkAppN (.const recC rlvls) (directRecPrefixAt nP n nF 0 ++ [Expr.bvar (nF - 1 - i)])

/-- The right-hand side body of rule `j` at a recursive block: minor
`j` at the fields, then at the inductive hypotheses of the recursive
fields (`directRuleBodyAt` with the `ih` arguments). -/
def directRuleBodyR (recC : Name) (rlvls : List Level) (nP n nF j : Nat) (recIdx : List Nat) :
    Expr :=
  Expr.mkAppN (.bvar (nF + n - 1 - j))
    (((List.range nF).map fun k => Expr.bvar (nF - 1 - k)) ++
      recIdx.map fun i => directIhApp recC rlvls nP n nF i)

/-- The `ih` binders of a minor premise: for each recursive field
position (in order), `motive f_i` under the `l` earlier `ih` binders,
the motive sitting `nF + o - 1` binders above the fields. -/
def directIhPis (nF o : Nat) (pw : PropWhen) : List Nat → Nat → Expr → Expr
  | [], _, body => body
  | i :: is, l, body =>
    .forallE (.str .anonymous "ih")
      (.app (.bvar (nF + o - 1 + l)) (.bvar (nF - 1 - i + l)))
      (directIhPis nF o pw is (l + 1) body) ⟨.default, pw⟩

/-- A constructor's minor premise at a recursive block: its field
telescope lifted under the `o` extras, every binder's datum reset to
the elimination datum, then the `ih` binders, ending in
`motive (C p⃗ f⃗)` lifted above the `ih`s. -/
def directMinorTyR (C : Name) (lps : List Name) (nP nF o : Nat) (pw : PropWhen)
    (cty : Expr) (recIdx : List Nat) : Option Expr :=
  (cty.stripPis nP).bind fun q =>
    Expr.replacePisPw pw nF (q.2.liftLooseBVars o 0)
      (directIhPis nF o pw recIdx 0
        (.app (.bvar (nF + o - 1 + recIdx.length))
          ((directCtorSpineAt C lps o nP nF).liftLooseBVars recIdx.length 0)))

/-- The minor premises' `∀`-telescope at a recursive block, one per
constructor `(C, nF, cty, recIdx)`. -/
def directMinorsPisR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (directMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (directMinorsPisR lps nP pw cs (o + 1) body).map fun rest =>
        .forallE (Name.lastStr C) mty rest ⟨.default, pw⟩

/-- The `λ` twin of `directMinorsPisR`. -/
def directMinorsLamsR (lps : List Name) (nP : Nat) (pw : PropWhen) :
    List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (directMinorTyR C lps nP nF o pw cty recIdx).bind fun mty =>
      (directMinorsLamsR lps nP pw cs (o + 1) body).map fun rest =>
        .lam (Name.lastStr C) mty rest ⟨.default, pw⟩

/-- **The generated recursor type at a recursive block**

    ∀ p⃗ {motive : ∀ (t : T p⃗), Sort ℓ}
      (minor_C : ∀ f⃗ (ih⃗ : motive f_i)…, motive (C p⃗ f⃗))…
      (t : T p⃗), motive t

(`directRecTy` with `ih` binders in the minors). -/
def directRecTyR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) : Option Expr :=
  let ℓ := directElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  (directMinorsPisR lps nP pw ctors 1
      (.forallE (.str .anonymous "t") (directFam T lps nP (n + 1))
        (.app (.bvar (n + 1)) (.bvar 0)) ⟨.default, pw⟩)).bind fun minors =>
    Expr.replacePisPw pw nP tty
      (.forallE (.str .anonymous "motive") (directMotiveTy T lps nP ℓ) minors
        ⟨.default, pw⟩)

/-- **The generated rule** for constructor `j` at a recursive block:
`λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j (T.rec p⃗ motive minor⃗ f_i)…`
(`directRecRhs` with the inductive hypotheses; `recC`/`rlvls` are the
recursor's name and its level parameters as levels). -/
def directRecRhsR (T : Name) (lps : List Name) (elim : Name) (large : Bool)
    (nP : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat))
    (recC : Name) (rlvls : List Level) (j : Nat) : Option Expr :=
  let ℓ := directElimLevel elim large
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  match ctors[j]? with
  | none => none
  | some (_, nF, cty, recIdx) =>
    (cty.stripPis nP).bind fun q =>
    (Expr.pisToLamsPw pw nF (q.2.liftLooseBVars (n + 1) 0)
        (directRuleBodyR recC rlvls nP n nF j recIdx)).bind fun inner =>
    (directMinorsLamsR lps nP pw ctors 1 inner).bind fun minors =>
    Expr.pisToLamsPw pw nP tty
      (.lam (.str .anonymous "motive") (directMotiveTy T lps nP ℓ) minors
        ⟨.default, pw⟩)

/-- The constructors zipped with their recursive positions, as the
generators take them. -/
def directFixCtors4 (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) :
    List (Name × Nat × Expr × List Nat) :=
  (List.range ctorsA.length).filterMap fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks => some (cA.1.name, cA.2, cA.1.type, recIdxOf ks)
    | _, _ => none

/-! ## Recognition -/

/-- The stream's rules at a recursive block, in constructor order:
rule `j` fires constructor `j` with its field count and the canonical
right-hand side with the inductive hypotheses. -/
def directFixRulesOk (recC : Name) (rlvls : List Level) (nP n : Nat)
    (cs : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) (rhss : List Expr) :
    Bool :=
  rhss.length == n && kinds.length == n &&
  (List.range n).all fun j =>
    match rhss[j]?, cs[j]?, kinds[j]? with
    | some rhs, some (_, nF), some ks =>
      ks.length == nF &&
      (match rhs.stripLams (nP + 1 + n + nF) with
       | some (_, rbody) => rbody == directRuleBodyR recC rlvls nP n nF j (recIdxOf ks)
       | none => false)
    | _, _, _ => false

/-- The block's shape at a recursive block: `directSumPartsCore?`
without its one-constructor exclusion and without the rule bodies
(which need the field kinds), at `nIdx = 0`.  The rules' names and
field counts are pinned here; their bodies by `directFixRulesOk`. -/
def directFixShape? (block : List ConstantInfo) : Option DirectSumParts :=
  match block with
  | .indInfo cvT _ :: rest =>
    match directSumSplit rest with
    | some (cs, cvR, mI, rP, rules) =>
      let T := cvT.name
      let lps := cvT.levelParams
      let n := cs.length
      if rP < n + 1 || mI != rP then none else
      let nP := rP - (n + 1)
      if cvR.name == T.str "rec" &&
          reservedBasisNames.contains T == false &&
          reservedBasisNames.contains cvR.name == false &&
          cs.all (fun c => c.2.1 == nP && c.1.levelParams == lps &&
            reservedBasisNames.contains c.1.name == false &&
            (match c.1.type.stripPis (nP + c.2.2) with
             | some (_, cbody) => directCtorResidOk T lps nP c.2.2 0 cbody
             | none => false)) &&
          rules.length == n &&
          (List.range n).all (fun j =>
            match rules[j]?, cs[j]? with
            | some rule, some (cvC, _, nF) => rule.ctor == cvC.name && rule.nfields == nF
            | _, _ => false) then
        match cvT.type.stripPis nP with
        | some (_, .sort s) =>
          let isProp := Level.isEquiv s .zero == some true
          let ctors := cs.map fun c => (c.1, c.2.2)
          let rhss := rules.map (·.rhs)
          let large? : Option Name :=
            match cvR.levelParams with
            | elim :: relps =>
              if relps == lps && !lps.contains elim then some elim else none
            | [] => none
          match large? with
          | some elim => some ⟨cvT, ctors, nP, 0, cvR, elim, s, rhss, true, isProp⟩
          | none =>
            if cvR.levelParams == lps then
              some ⟨cvT, ctors, nP, 0, cvR, .anonymous, s, rhss, false, isProp⟩
            else none
        | _ => none
      else none
    | none => none
  | _ => none

/-- The field kinds of every constructor. -/
def directFixKinds? (p : DirectSumParts) : Option (List (List RecFieldKind)) :=
  p.ctors.mapM (recCtorKinds p.cvT.name p.cvT.levelParams p.nP)

/-- Recognise a direct recursive block: the shape, some field
mentioning the block (else it is not this route: a non-recursive block
is the structure's or the sum's), and — when every field is ordinary
or a finitary recursive one — the rules' bodies.  A block with a
non-positive or unsupported occurrence is admitted WITHOUT the rule
check so that the install diagnoses it (reject, resp. decline) exactly
as the official kernel's positivity check would, before anything else
is looked at. -/
def directFixParts? (block : List ConstantInfo) : Option DirectFixParts :=
  match directFixShape? block with
  | some p =>
    match directFixKinds? p with
    | some kinds =>
      if kinds.any (fun ks => ks.any (· != .ordinary)) then
        if kinds.all (fun ks => ks.all fun k => k == .ordinary || k == .recursive) then
          if directFixRulesOk p.cvR.name (p.cvR.levelParams.map .param) p.nP p.ctors.length
              p.ctors kinds p.rhss then
            some ⟨p, kinds⟩
          else none
        else some ⟨p, kinds⟩
      else none
    | none => none
  | none => none

end Lech
