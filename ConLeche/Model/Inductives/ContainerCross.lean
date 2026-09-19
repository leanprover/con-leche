module

public import ConLeche.Model.Inductives.NestedPremise
public import ConLeche.Model.Inductives.BlockRepCross
import ConLeche.Model.Install
import ConLeche.Verify.Inductives.ContainerFrame
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedCopyInstU
import ConLeche.Verify.Inductives.NestedCopyKinds
import ConLeche.Verify.Inductives.NestedCopyGlue
public section

/-!
# A container's block model across an environment extension (task #315, M7-3)

`EnvModelB` (`NestedPremise.lean`) carries `EnvBlockModels`: every
stored container's block model, at the carrier.  The fold extends the
environment one declaration at a time, so the field's MAINTENANCE is
two questions per stage, and this module answers both generically:

* **does the reading move?** — `containerInfo?` consults the
  environment only through inductive-kind lookups, so a non-inductive
  extension leaves every container's block exactly as it was
  (`containerInfo?_cons_nonInd`, `Verify/Inductives/ContainerFrame.lean`),
  and an inductive one leaves every OLD container's alone
  (`containerInfo?_ext_ind`);
* **does the block model move?** — no: `ContainerModeled`'s
  model-facing clauses are the block's representation and its typing,
  and those cross an extension by `BlockRepCross.lean`'s four
  hypotheses (`hF`, `hres`, `hag`, `hde`).  `ContainerModeled.crossEnv`
  is that transport; its remaining clauses (`k`, `nP`, `inj`, `frame`,
  `ordFree`, `pinsNotMembers`, `pinNP`) name no model at all — `pinNP`
  reads `containerInfo?` at the block's OWN pre-block environment
  `d.env₀`, which no later extension touches.

`EnvModelB.ofNonIndStep` puts the two together at the shape every
VALUE kind of the fold installs (`NonIndStep`): nothing at all, or one
fresh cons of a kind that is neither inductive nor a projection table.
Its one model-facing input is `AcvalAgrees` — the new carrier values
every old constant as the old one did — which the cons-level steps
always proved (their `acvalWith` equation, `exists_agrees_of_cons`)
and the stage theorems used to drop.  The lifts themselves are
`EnvModelBStages.lean`.

An INDUCTIVE extension keeps `EnvBlockModels` only modulo the new
block's own containers, which is the installing route's obligation:
`EnvBlockModels.crossInd` takes it as its last argument.

**The reading hypothesis `hde` is too strong for the INDUCTIVE routes**
(task #315 M7-3 session 2, DESIGN §U.40): every inductive route ends by
consing the projection tables of its structure-like members, and a
table cons MOVES a successful reading — `denoteMeta` reads `.proj sn i`
through the table when there is one and through the pair decoder when
there is none.  `denoteMeta_not_mono_of_newTable` and
`hde_not_of_newTable` are that refutation, in the tree, with the shape
of the weaker hypothesis that replaces it (the readings guarded by the
subjects' proj-freedom at the newly tabled structures, which the block
model's own `BlockOpened` clauses already record).  The VALUE kinds are
unaffected: `crossCons` excludes a projection table by `hntc`.

`ContainerModeled.of_readBack` is the other half the routes need —
K.34's Bool, inverted: the block just installed reads back as its own
`ContainerInfo`, so the record's four data clauses are the block's own
data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecRule ContainerInfo
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The group is never empty -/

/-- **A container's group has a member**: `containerInfo?` returns only
a group whose name list CONTAINS the container it was asked about
(`names.contains I`), and the members are that list, read one by one. -/
theorem containerInfo?_members_pos {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) : 0 < ci.members.length := by
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ := ConLeche.containerInfo?_inv h
  cases hc : ci.members with
  | nil => rw [hc] at hmem; exact nomatch hmem
  | cons M Ms => simp

/-! ## The own-pin table across an inductive install -/

/-- **A STORED RECURSOR'S MAJOR PREMISE IS HEADED BY A STORED
CONSTANT** (task #315 M7-3 session 17) — the one premise
`ContainerOwnPinsSyn.crossInd` needs beyond the frame's, and the reason
it needs one.

`containerOwnPinsAt` reads a container's own pins off its MIMIC
recursors: it instantiates `T₁.rec_j`'s `mI` binders at the caller's
components `Ds` (padded with sorts), takes the next domain — the major
premise — and keeps it when its head is a stored container.  Every
other ingredient of that computation is the recursor's STORED type, so
an environment extension cannot move it; the head is the one place
where the CALLER's components can enter, because `Expr.instPis`
substitutes them and a domain headed by a loose `bvar` comes back
headed by whatever the substitution put there.  A head that comes from
the stored type is a constant that `constsResolve` guarantees is
stored (`EnvWF`), hence old; a head that comes from `Ds` need not be,
and a NEW container there is exactly an own pin the extended
environment reads and the old one does not.

This premise excludes that: the major premise's head is a constant the
environment has.  It is the unguarded form of the shape `EnvWF` already
records for a recursor with a NESTED rule (`ConstWF`'s
`nestedRuleShape` clause: `cv.type.stripPis mI = some (pre, .forallE dom body bm)`
with `dom.getAppFn = .const D lvls`, `D` resolving in the environment),
which is why every real mimic satisfies it — a mimic recursor exists
only to carry the nested rules whose shape that clause pins down.  The
`args.length = mI` side condition is what makes this the MAJOR PREMISE
and not an arbitrary binder's domain: an index binder's domain may
perfectly well be a parameter. -/
@[expose] def RecMajorHeadStored (env : Env) : Prop :=
  ∀ (n : Name) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule)
    (lps : List Name) (lvls : List Level) (args : List Expr)
    (dom body : Expr) (bm : ConLeche.BinderMeta) (K : Name) (us : List Level),
    env.find? n = some (.recInfo cvR mI rP rules) →
    args.length = mI →
    Expr.instPis (cvR.type.instantiateLevelParams lps lvls) args = some (.forallE dom body bm) →
    dom.getAppFn = .const K us →
    (env.find? K).isSome = true

/-! ### `RecMajorHeadStored` from the stored major-premise shape

`EnvWF` records the shape unconditionally at every stored recursor —
`cv.type` strips `mI` `∀`s onto a `∀` whose domain is headed by a
CONSTANT (the kernel's `Expr.recMajorHeadOk`, checked once at install).
`RecMajorHeadStored` asks for the head of the domain the READER sees,
which is that domain level-instantiated and substituted at the caller's
`mI` arguments.  Neither operation can move a constant head — level
instantiation rewrites a `.const`'s level arguments and nothing else,
and `Expr.instPis`' substitution can only replace a head that is a
loose `bvar` — so the two are the same name, and `constsResolve` (the
GENERIC `ConstWF` conjunct) then puts it in the environment.

The head-preservation half is `instPis_ilp_major_head`
(`Verify/Inductives/NestedCopyInstU.lean`, beside `instPis_ilp`): it is
stated there, in the Verify tier, so that a route PRODUCING the stored
shape cites it instead of re-deriving it.  What is left here is the
occurrence half, `mentionsConst_of_stripPis_body`. -/

/-- A `∀`-telescope's stripped residual is MENTIONED by the whole:
`Expr.stripPis` peels a binder without instantiating, so the residual
stands where it was.  (`stripPis_binder_leaves`' `mentionsConst` twin,
at the residual rather than at a binder.) -/
private theorem mentionsConst_of_stripPis_body {C : Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr},
      e.stripPis k = some (bs, body) → body.mentionsConst C = true →
      e.mentionsConst C = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h hb
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hb
  | succ k ih =>
    intro e bs body h hb
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        obtain ⟨pbs, pbody⟩ := p
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp [Expr.mentionsConst, ih hs hb]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- **THE STORED SHAPE DISCHARGES `RecMajorHeadStored`** (task #315 M7-3
session 18): the premise's environment-level content is exactly
`EnvWF`'s — a recursor's stored type strips its `mI` major binders onto
a `∀` with a constant-headed domain, and every constant the stored type
mentions is stored (`constsResolve`).

`hmaj` is that shape written out: the kernel's `Expr.recMajorHeadOk`
conjunct of `ConstWF` unfolded, so that this bridge does not wait on the
integration that brings the name into the tree — when it arrives, the
field's discharge is this lemma and one `exact`.

The reader's domain is the stored one after `Expr.instantiateLevelParams`
and after `Expr.instPis` at the caller's `mI` arguments;
`ConLeche.instPis_ilp_major_head` carries the constant head across both. -/
theorem recMajorHeadStored_of_stripPis {env : Env}
    (hmaj : ∀ (n : Name) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env.find? n = some (.recInfo cvR mI rP rules) →
      ∃ (pre : List (Expr × ConLeche.BinderMeta)) (dom body : Expr)
        (bm : ConLeche.BinderMeta) (D : Name) (us : List Level),
        cvR.type.stripPis mI = some (pre, .forallE dom body bm) ∧
        dom.getAppFn = .const D us)
    (hwf : ConLeche.EnvWF env) :
    RecMajorHeadStored env := by
  intro n cvR mI rP rules lps lvls args dom body bm K us hf hlen hinst hK
  obtain ⟨pre, dom₀, body₀, bm₀, D, us₀, hstrip, hD⟩ := hmaj n cvR mI rP rules hf
  -- (1)+(2) the head the reader saw is the stored one, level arguments aside
  obtain ⟨us', hD'⟩ := ConLeche.instPis_ilp_major_head hstrip hD hlen hinst
  obtain rfl : K = D := by
    rw [hD'] at hK
    injection hK with hname _
    exact hname.symm
  -- (3) `D` occurs in the stored type, which resolves
  refine ConLeche.mentionsConst_of_constsResolve cvR.type
    (hwf _ (List.mem_of_find?_eq_some hf)).2.2.1 ?_
  refine mentionsConst_of_stripPis_body mI hstrip ?_
  simp [Expr.mentionsConst, Expr.mentionsConst_of_getAppFn hD]

omit [SetTheory V] in
/-- **`EnvWF` GIVES THE OWN-PIN WALK ITS ONE NON-FRAME PREMISE** (task
#315 M7-3): `recMajorHeadStored_of_stripPis` at the environment
invariant's own unconditional recursor clause (`Expr.recMajorHeadOk`,
K.55), inverted on the spot — the Bool says the strip succeeds at a
`∀`-binder whose domain's head is a constant, which is the shape the
bridge asks for.

Every crossing of `ContainerOwnPinsSyn` reads the premise here rather
than as a hypothesis: an install route holds `EnvWF` of the environment
it extends by construction. -/
theorem recMajorHeadStored_of_envWF {env : Env} (hwf : ConLeche.EnvWF env) :
    RecMajorHeadStored env := by
  refine recMajorHeadStored_of_stripPis (fun n cvR mI rP rules hf => ?_) hwf
  have h := (hwf _ (List.mem_of_find?_eq_some hf)).2.2.2.2.2.1 cvR mI rP rules rfl
  unfold ConLeche.Expr.recMajorHeadOk at h
  split at h
  · next bs dom body bm hs =>
    split at h
    · next D us hd => exact ⟨bs, dom, body, bm, D, us, hs, hd⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `containerOwnPinsAt`, inverted: a successful read is the mimic walk
at the group's own first member, from the container's stored level
parameters and the group's parameter count.

Public since task #315 M7-3 session 18: the nested route's own
discharge of the clause (`nestedOwnPins_of`) reduces BOTH tables — the
one the reader asks for and the one K.47 records — to the walk through
this, and the three walk lemmas here are shared rather than
duplicated. -/
theorem containerOwnPinsAt_inv {env : Env} {C : Name} {lvls : List Level}
    {Ds ps : List Expr} (h : ConLeche.containerOwnPinsAt env C lvls Ds = some ps) :
    ∃ (cv : ConstantVal) (caps : IndCaps) (ci : ContainerInfo) (M : ConLeche.ContainerMember),
      env.find? C = some (.indInfo cv caps) ∧ ConLeche.containerInfo? env C = some ci ∧
      ci.members.head? = some M ∧
      ps = ConLeche.containerOwnPinsAtGo env (M.name.str "rec") cv.levelParams lvls Ds
        ci.nP 64 0 := by
  unfold ConLeche.containerOwnPinsAt at h
  cases hf : env.find? C with
  | none => rw [hf] at h; exact nomatch h
  | some c =>
    rw [hf] at h
    cases c with
    | indInfo cv caps =>
      cases hci : ConLeche.containerInfo? env C with
      | none => simp [hci, bind, Option.bind] at h
      | some ci =>
        cases hM : ci.members.head? with
        | none => simp [hci, hM, bind, Option.bind] at h
        | some M =>
          refine ⟨cv, caps, ci, M, rfl, rfl, hM, ?_⟩
          simp [hci, hM, bind, Option.bind, pure] at h
          exact h.symm
    | _ => simp [bind, Option.bind] at h

/-- `containerOwnPinsAt_inv`, read forwards (public with it). -/
theorem containerOwnPinsAt_eq {env : Env} {C : Name} {cv : ConstantVal} {caps : IndCaps}
    {ci : ContainerInfo} {M : ConLeche.ContainerMember} {lvls : List Level} {Ds : List Expr}
    (hf : env.find? C = some (.indInfo cv caps))
    (hci : ConLeche.containerInfo? env C = some ci) (hM : ci.members.head? = some M) :
    ConLeche.containerOwnPinsAt env C lvls Ds =
      some (ConLeche.containerOwnPinsAtGo env (M.name.str "rec") cv.levelParams lvls Ds
        ci.nP 64 0) := by
  unfold ConLeche.containerOwnPinsAt
  rw [hf]
  simp only [bind, Option.bind, hci, hM, pure]

/-- **THE MIMIC WALK DOES NOT MOVE** (task #315 M7-3 session 17): the
table `containerOwnPinsAtGo` reads is the same at both environments.

The walk stops at the first name under `base` that is not a stored
recursor, and reads each one it finds.  An extension cannot SHORTEN it
(`hext` keeps every stored recursor, with its very type) and cannot
LENGTHEN it either: a mimic name that is a recursor at `env₂` and not
at `env₁` is one of the new names, and `hmimOld` excludes exactly that
for this container's mimics.  What each step reads is then a function
of the SAME stored type, save for the container lookup at the major
premise's head, which `hhead` places in the old environment and
`hciEq` therefore leaves alone.

Public with `containerOwnPinsAt_inv` above (task #315 M7-3
session 18). -/
theorem containerOwnPinsAtGo_ext {env₁ env₂ : Env} {N : List Name} {base : Name}
    {lps : List Name} {lvls : List Level} {Ds : List Expr} {nPr : Nat}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hmimOld : ∀ (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter base j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter base j ∉ N)
    (hciEq : ∀ K : Name, (env₁.find? K).isSome = true →
      ConLeche.containerInfo? env₂ K = ConLeche.containerInfo? env₁ K)
    (hhead : RecMajorHeadStored env₁) :
    ∀ (fuel j : Nat),
      ConLeche.containerOwnPinsAtGo env₂ base lps lvls Ds nPr fuel j
        = ConLeche.containerOwnPinsAtGo env₁ base lps lvls Ds nPr fuel j := by
  intro fuel
  induction fuel with
  | zero => intro j; rfl
  | succ fuel ih =>
    intro j
    cases h₁ : env₁.find? (Name.appendIndexAfter base (j + 1)) with
    | none =>
      cases h₂ : env₂.find? (Name.appendIndexAfter base (j + 1)) with
      | none => simp only [ConLeche.containerOwnPinsAtGo, h₁, h₂]
      | some c =>
        cases c with
        | recInfo cvR mI rP rules =>
          refine absurd ((hnewN _ _ h₂).resolve_left ?_) (hmimOld (j + 1) cvR mI rP rules h₂)
          rw [h₁]; exact fun hh => nomatch hh
        | _ => simp only [ConLeche.containerOwnPinsAtGo, h₁, h₂]
    | some c =>
      have h₂ := hext _ _ h₁
      cases c with
      | recInfo cvR mI rP rules =>
        simp only [ConLeche.containerOwnPinsAtGo, h₁, h₂]
        rw [ih (j + 1)]
        refine congrArg (· ++ _) ?_
        by_cases hcond : (decide (nPr ≤ mI) && (Ds.length == nPr)) = true
        · rw [if_pos hcond, if_pos hcond]
          have hlen : (Ds ++ (List.range (mI - nPr)).map fun _ => Expr.sort Level.zero).length
              = mI := by
            simp only [List.length_append, List.length_map, List.length_range]
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
            rw [hcond.2]
            exact Nat.add_sub_cancel' hcond.1
          cases hI : Expr.instPis (cvR.type.instantiateLevelParams lps lvls)
              (Ds ++ (List.range (mI - nPr)).map fun _ => Expr.sort Level.zero) with
          | none => simp only
          | some ty =>
            cases ty with
            | forallE dom body bm =>
              cases hfn : dom.getAppFn with
              | const K us =>
                simp only [hfn]
                rw [hciEq K (hhead _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ hlen hI hfn)]
              | _ => simp only [hfn]
            | _ => simp only
        · rw [if_neg hcond, if_neg hcond]
      | _ => simp only [ConLeche.containerOwnPinsAtGo, h₁, h₂]

omit [SetTheory V] in
/-- **A BLOCK'S OWN-PIN CLAUSE CROSSES AN INDUCTIVE INSTALL** (task
#315 M7-3 session 17): `ContainerOwnPinsSyn` is a statement about the
environment's own-pin TABLE at the block's members, and an install that
touches none of them leaves that table where it was.

The frame hypotheses are `EnvBlocksOf.crossIndP`'s, plus `hmimN` — the
mimic twin of `hrecN`: a NEW recursor named `T₁.rec_j` belongs to a NEW
`T₁`.  With it, the walk cannot grow at an OLD container (the members
are old by `hold`, and the group's first member — where the walk starts
— is stored, hence old too), and `containerInfo?_ext_ind_eq` keeps both
the group's reading and the per-step container lookups fixed.

`RecMajorHeadStored` is the one premise that is NOT frame, and it is
not cosmetic: the components `DsE` the clause quantifies over are the
CALLER's, a major-premise domain headed by a loose `bvar` reads back
headed by whatever the substitution put there, and a NEW container
there is an own pin `env₂`'s table carries and `env₁`'s does not —
which no fact about the OLD block can match, so the crossing is
genuinely unavailable without it.  (No countermodel is built here: an
environment exhibiting the gap needs a stored group whose mimic's
major premise is headed by one of the recursor's own PARAMETERS, which
no install writes — which is also why every route can discharge the
premise.)  See its docstring. -/
theorem ContainerOwnPinsSyn.crossInd {env₁ env₂ : Env} {N : List Name} {d : BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hold : ∀ i, i < d.k → (d.memberName i) ∉ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hhead : RecMajorHeadStored env₁)
    (h : ContainerOwnPinsSyn (V := V) env₁ d) :
    ContainerOwnPinsSyn (V := V) env₂ d := by
  -- a name stored at the old environment is not a new one
  have hstored : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ N := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  have hciEq : ∀ K : Name, (env₁.find? K).isSome = true →
      ConLeche.containerInfo? env₂ K = ConLeche.containerInfo? env₁ K := fun K hK =>
    ConLeche.containerInfo?_ext_ind_eq hext hnewN hfreshN hrecN hwf hrc (hstored K hK)
  intro i cvC caps lvls DsE ps hi hf₂ hcl hps
  -- the member is old, so it is stored as it was
  have hf₁ : env₁.find? (d.memberName i) = some (.indInfo cvC caps) :=
    (hnewN _ _ hf₂).resolve_right (hold i hi)
  obtain ⟨cv, caps', ci, M, hfc, hci₂, hM, rfl⟩ := containerOwnPinsAt_inv hps
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfc.symm.trans hf₂))
  have hci₁ : ConLeche.containerInfo? env₁ (d.memberName i) = some ci := by
    rw [← hciEq _ (by rw [hf₁]; rfl)]; exact hci₂
  -- the group's first member is stored, hence old, hence so are its mimics
  have hMmem : M ∈ ci.members := List.mem_of_mem_head? (by rw [hM]; exact rfl)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hall⟩ := ConLeche.containerInfo?_inv hci₁
  obtain ⟨_, _, _, _, _, hfM, _⟩ := hall M hMmem
  have hMold : M.name ∉ N := hstored _ (by rw [hfM]; rfl)
  rw [containerOwnPinsAtGo_ext hext hnewN
    (fun j cv' mI rP rules h2 hmem => hMold (hmimN M.name j cv' mI rP rules h2 hmem))
    hciEq hhead 64 0]
  exact h i _ _ lvls DsE _ hi hf₁ hcl (containerOwnPinsAt_eq hf₁ hci₁ hM)

/-- **THE CROSSING, AT `EnvBlocksOf.crossIndP`'s OWN HYPOTHESES** (task
#315 M7-3 session 21): `ContainerOwnPinsSyn.crossInd` with `hold` —
"the block's members are not new" — DISCHARGED, so that the clause
`ContainerModeled.ownPins` costs its call site nothing beyond the two
inputs that are genuinely extra.

Every hypothesis here is one the crossing's own site already has: the
first six are `EnvBlocksOf.crossIndP`'s (the install's conses and the
old environment's well-formedness), and the remaining two are the
crossing's residue — `hmimN`, the mimic twin of `hrecN`, which each
install route reads off its own `new` list
(`BlockInstallExt.mimN` / `nestedMimN`, `EnvModelBStages.lean`), and
`RecMajorHeadStored`, the kernel record the walk cannot do without
(see its docstring).

`hold` is not an assumption because the block is a container the OLD
environment STORES: `ContainerModeled`'s representation says every
member below `d.k` is a stored inductive there
(`IsBlockModel.memsFound` off `reps`), and a name `env₁` answers is not
one of the install's fresh names (`hfreshN`).  This is exactly the
`hstored` dance `EnvBlocksOf.crossIndP` does for the pins' containers,
at the members. -/
theorem ContainerOwnPinsSyn.crossIndOf {env₁ env₂ : Env} {m₁ : EnvModel V env₁}
    {N : List Name} {ci : ContainerInfo} {d : BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hhead : RecMajorHeadStored env₁)
    (C : ContainerModeled m₁ ci d)
    (h : ContainerOwnPinsSyn (V := V) env₁ d) :
    ContainerOwnPinsSyn (V := V) env₂ d :=
  h.crossInd hext hnewN hfreshN hrecN hmimN
    (fun i hi hmem => by
      obtain ⟨_, _, _, _, _, hb⟩ := C.reps i hi
      obtain ⟨_, _, hf⟩ := hb.memsFound i hi
      rw [hfreshN _ hmem] at hf
      exact nomatch hf)
    hwf hrc hhead

/-! ## The block model across the change -/

/-- **A container's block model crosses an environment change**: its
representation (`IsBlockModels`), the per-member `IsBlockModel` of the
`member` clause and the three typing clauses travel by
`BlockRepCross.lean`'s four hypotheses; every other clause is
model-free (`pinNP` reads `containerInfo?` at `d.env₀`, the block's own
pre-block environment, not at the model's).  `pinConts` is the one
clause that names BOTH environments, and `hci` — the pins' containers'
groups read the same at the new one, which every caller already holds
for the pins' shapes — is what carries it. -/
theorem ContainerModeled.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ci : ContainerInfo} {d : BlockModel V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hnpMem : ∀ M ∈ ci.members, ProjFree Ts M.type)
    (hk : 0 < d.k)
    (hci : ∀ q, q < d.nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ (d.pinAt q).J = some ci')
    (hownCross : ContainerOwnPinsSyn (V := V) env₁ d → ContainerOwnPinsSyn (V := V) env₂ d)
    (C : ContainerModeled m₁ ci d) : ContainerModeled m₂ ci d := by
  -- the member clause crosses at the STORED constant, whose type is
  -- guarded; `IsBlockModels` is then READ OFF it (the `member` clause
  -- is the stronger one — DESIGN §U.31 (e) 2)
  have hmemCross : ∀ (i : Nat) (M : ConLeche.ContainerMember), ci.members[i]? = some M →
      d.memberName i = M.name ∧ (d.ctorsM i).map (·.1.name) = M.ctors.map (·.name) ∧
      ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        IsBlockModel m₂ M.name ⟨M.name, M.lps, M.type⟩ cvR mI rP rules d i := by
    intro i M hM
    obtain ⟨hname, hctors, cvR, mI, rP, rules, hI⟩ := C.member i M hM
    exact ⟨hname, hctors, cvR, mI, rP, rules,
      hI.crossEnvP hF hres hag hde hfresh (hnpMem M (List.mem_of_getElem? hM))⟩
  have hreps₂ : IsBlockModels m₂ d := by
    intro mm hmm
    obtain ⟨M, hM⟩ : ∃ M, ci.members[mm]? = some M :=
      ⟨_, List.getElem?_eq_getElem (by rw [← C.k]; exact hmm)⟩
    obtain ⟨hname, -, cvR, mI, rP, rules, hI⟩ := hmemCross mm M hM
    exact ⟨⟨M.name, M.lps, M.type⟩, cvR, mI, rP, rules, by rw [hname]; exact hI⟩
  exact
    { k := C.k
      namesLen := C.namesLen
      nP := C.nP
      reps := hreps₂
      typed := fun ψ =>
        ⟨(C.typed ψ).1.crossEnv hag C.reps, (C.typed ψ).2.1.crossEnv hag C.reps,
          (C.typed ψ).2.2.crossEnv hag C.reps hk⟩
      inj := C.inj
      member := hmemCross
      frame := C.frame
      ordFree := C.ordFree
      nestMention := C.nestMention
      pinsDistinct := C.pinsDistinct
      pinsDistinctAt := C.pinsDistinctAt
      nestArgsMention := C.nestArgsMention
      nestArgsMentionAbs := C.nestArgsMentionAbs
      nestArgsMentionAbsRefl := C.nestArgsMentionAbsRefl
      nestPinSpineAbs := C.nestPinSpineAbs
      nestPinSpineAbsRefl := C.nestPinSpineAbsRefl
      ctorProjFree := C.ctorProjFree
      pinsNotMembers := C.pinsNotMembers
      pinNP := C.pinNP
      pinConts := fun q hq ci' h => hci q hq ci' (C.pinConts q hq ci' h)
      ownPins := hownCross C.ownPins
      pinParams := C.pinParams
      pinDsScoped := C.pinDsScoped
      pinDsRes := fun q hq x hx => hres _ (C.pinDsRes q hq x hx)
      -- the READING clause is the one the guard exists for: `hde` is
      -- refutable across a projection-table cons, and the guard comes
      -- from the components' own resolution at the OLD environment
      -- (K.64's first conjunct), exactly as the member types' does
      pinDsRead := fun q hq φ =>
        DenoteMetaSpine.crossEnvP (fun e he => hde φ d.nP e he)
          (fun e he => ProjFree.of_constsResolve hfresh (C.pinDsRes q hq e he))
          (C.pinDsRead q hq φ)
      pinψ := fun q hq cvT caps hf => by
        obtain ⟨cvT', cvR', mI', rP', rules', h0⟩ := C.reps 0 hk
        obtain ⟨cv, caps', hf₁⟩ := h0.pinsFound q hq
        have hf₂ := hF _ (.indInfo cv caps') (fun _ _ _ _ h => nomatch h) hf₁
        have he := ConLeche.ConstantInfo.indInfo.inj (Option.some.inj (hf.symm.trans hf₂))
        rw [he.1]
        exact C.pinψ q hq cv caps' hf₁ }

/-- **A container's block model crosses an environment change**: the
unguarded crossing (`Ts := []`), for an extension that installs no
projection table — the value kinds' shape.  An INDUCTIVE extension
takes `crossEnvP`. -/
theorem ContainerModeled.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ci : ContainerInfo} {d : BlockModel V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hk : 0 < d.k)
    (hci : ∀ q, q < d.nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ (d.pinAt q).J = some ci')
    (hownCross : ContainerOwnPinsSyn (V := V) env₁ d → ContainerOwnPinsSyn (V := V) env₂ d)
    (C : ContainerModeled m₁ ci d) : ContainerModeled m₂ ci d :=
  C.crossEnvP (Ts := []) hF hres hag (fun ψ dp e _ {_ea} hr => hde ψ dp e hr)
    (fun _ hT => nomatch hT) (fun M _ => ProjFree.nil M.type) hk hci hownCross

/-- **A stored container's member types are guarded at names the
environment does not carry**: `containerInfo?` returns the members'
STORED types (`containerInfo?_inv`), those resolve (`EnvWF`), and a
resolving expression has no projection at an unstored structure
(`ProjFree.of_constsResolve`).  This is what lets an OLD container's
block model cross an INDUCTIVE extension: the block being installed is
fresh, so its projection tables are at structures no old subject
mentions. -/
theorem projFree_members {Ts : List Name} {env : Env} (m : EnvModel V env)
    (hfresh : ∀ T ∈ Ts, env.find? T = none) {J : Name} {ci : ContainerInfo}
    (hci : ConLeche.containerInfo? env J = some ci) :
    ∀ M ∈ ci.members, ProjFree Ts M.type := by
  intro M hM
  obtain ⟨cvT, caps, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfind, -, -, htype, -⟩ := H.2.2.2.2 M hM
  rw [htype]
  exact ProjFree.of_constsResolve hfresh
    (m.wf _ (ConLeche.Semantics.Env.find?_mem hfind)).2.2.1

/-! ## The pins' laws and shapes across the change -/

/-- **A stored block's pins' shapes cross an environment change**: the
shapes read the carrier only at the block's members, its pins'
containers and the containers' own pins' containers — all stored at
the old environment — and the pins' containers' groups are read the
same at the new one (`hci`). -/
theorem PinShapes.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {d : BlockModel V} {pc : Nat → PinCtors V}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hk : 0 < d.k) (hd : IsBlockModels m₁ d)
    (hB : ∀ q, q < d.nPins → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci → IsBlockModels m₁ (B ci))
    (hci : ∀ q, q < d.nPins → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₁ (d.pinAt q).J = some ci →
      ConLeche.containerInfo? env₂ (d.pinAt q).J = some ci)
    (h : PinShapes m₁ B d pc) : PinShapes m₂ B d pc := by
  intro q hq
  obtain ⟨q₀, kJ, i, ci, hqe, hi, hcont, hgv, hct, hsh⟩ := h q hq
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci q hq ci hcont, hgv, hct,
    fun ψ ρp hρp i' j hi' hj cvT₂ caps₂ hf₂ => ?_⟩
  obtain ⟨cvT, cvR, mI, rP, rules, h0⟩ := hd 0 hk
  -- the pin's container at the new environment is the one at the old
  obtain ⟨cv₁, caps₁, hf₁⟩ := h0.pinsFound (q₀ + i') (by
    have := hgv.seg; omega)
  have he := ConLeche.ConstantInfo.indInfo.inj
    (Option.some.inj (hf₂.symm.trans (hF _ (.indInfo cv₁ caps₁) (fun _ _ _ _ h => nomatch h) hf₁)))
  rw [he.1]
  have hmem : ∀ t, t < d.k →
      m₂.acval (d.memberNames.getD t .anonymous) ψ = m₁.acval (d.memberNames.getD t .anonymous) ψ := by
    intro t ht
    obtain ⟨cv, caps, hf⟩ := h0.memsFound t ht
    exact congrFun (hag (d.memberNames.getD t .anonymous)
      (by rw [show d.memberNames.getD t .anonymous = d.memberName t from rfl, hf]; rfl)) ψ
  have hpin : ∀ q', q' < d.pins.length →
      m₂.acval (d.pins.getD q' default).J ((d.pins.getD q' default).ψJ ψ)
        = m₁.acval (d.pins.getD q' default).J ((d.pins.getD q' default).ψJ ψ) := by
    intro q' hq'
    obtain ⟨cv, caps, hf⟩ := h0.pinsFound q' hq'
    exact congrFun (hag (d.pins.getD q' default).J
      (by rw [show d.pins.getD q' default = d.pinAt q' from rfl, hf]; rfl)) _
  have hBci := hB q hq ci hcont
  have hac : ∀ qK, qK < (B ci).nPins →
      m₂.acval ((B ci).pinAt qK).J (((B ci).pinAt qK).ψJ ((d.pinAt q₀).ψJ ψ))
        = m₁.acval ((B ci).pinAt qK).J (((B ci).pinAt qK).ψJ ((d.pinAt q₀).ψJ ψ)) := by
    intro qK hqK
    obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hBci i' (hgv.kEq ▸ hi')
    obtain ⟨cv, caps, hf⟩ := hI'.pinsFound qK hqK
    exact congrFun (hag _ (by rw [hf]; rfl)) _
  exact CopyCtorShape.of_EA (TV := d.targetView m₁.acval ψ)
    (targetRead m₂.acval d.memberNames d.pins d.nP d.k ψ) (targetRead_congr hmem hpin) hac
    (hBci.tgt_pin_lt (hgv.kEq ▸ hi') (List.getElem?_eq_getElem hj))
    (hsh ψ ρp hρp i' j hi' hj cv₁ caps₁ hf₁)

/-- **A container group's obligation crosses an INDUCTIVE extension**
(task #315 M7-3 session 3): `ContainerModeled.crossEnvP` for the block
model, the pins' laws model-free, `PinShapes.crossEnv` for the shapes —
with the readings guarded at the structures the extension tables
(`hde`, `hfresh`) rather than asked of every expression. -/
theorem BlockAt.crossEnvP {Ts : List Name} {env₁ env₂ : Env}
    {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {ci : ContainerInfo}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hnpMem : ∀ M ∈ ci.members, ProjFree Ts M.type)
    (hk : 0 < (B ci).k)
    (hB : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' → IsBlockModels m₁ (B ci'))
    (hci : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci')
    (hownCross : ContainerOwnPinsSyn (V := V) env₁ (B ci) →
      ContainerOwnPinsSyn (V := V) env₂ (B ci))
    (h : BlockAt m₁ B ci) : BlockAt m₂ B ci := by
  obtain ⟨C, pc, hL, hS⟩ := h
  exact ⟨C.crossEnvP hF hres hag hde hfresh hnpMem hk hci hownCross, pc, hL.cross,
    hS.crossEnv hF hag hk C.reps hB hci⟩

/-- **A container group's obligation crosses an environment change**
(the block model by `ContainerModeled.crossEnv`, the pins' laws
model-free, the shapes by `PinShapes.crossEnv`), given the pins'
containers' groups at the old environment and their reading at the
new one. -/
theorem BlockAt.crossEnv {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V} {ci : ContainerInfo}
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hk : 0 < (B ci).k)
    (hB : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' → IsBlockModels m₁ (B ci'))
    (hci : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
      ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci')
    (hownCross : ContainerOwnPinsSyn (V := V) env₁ (B ci) →
      ContainerOwnPinsSyn (V := V) env₂ (B ci))
    (h : BlockAt m₁ B ci) : BlockAt m₂ B ci := by
  obtain ⟨C, pc, hL, hS⟩ := h
  exact ⟨C.crossEnv hF hres hag hde hk hci hownCross, pc, hL.cross,
    hS.crossEnv hF hag hk C.reps hB hci⟩

/-! ## The field across an extension -/

/-- **The pins' containers' groups of a stored block are stored**: at
an assignment carrying every group, a container's pin's container reads
a group whose model is `IsBlockModels`. -/
theorem EnvBlocksOf.pinGroups {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    (hb : EnvBlocksOf m B) {ci : ContainerInfo} :
    ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? env ((B ci).pinAt q).J = some ci' → IsBlockModels m (B ci') :=
  fun _ _ ci' hci' => (hb _ ci' hci').1.reps

/-- **The blocks survive a change of carrier at the SAME environment**:
the reading does not move at all, and every obligation crosses on the
agreement alone. -/
theorem EnvBlocksOf.crossSame {env : Env} {m₁ m₂ : EnvModel V env}
    {B : ContainerInfo → BlockModel V} (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ B := by
  intro J ci hci
  refine (hb J ci hci).crossEnv (fun _ _ _ hf => hf) (fun _ h => h) hag ?_
    ((hb J ci hci).1.k ▸ containerInfo?_members_pos hci) hb.pinGroups (fun _ _ _ h => h)
    (fun h => h)
  intro ψ dp e ea hd
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

theorem EnvBlockModels.crossSame {env : Env} {m₁ m₂ : EnvModel V env}
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, hB.crossSame hag⟩

/-- **The blocks survive a non-inductive fresh cons**: the reading does
not move (`containerInfo?_cons_nonInd`) and every obligation crosses.
The only model-facing input is the carriers' AGREEMENT at the stored
names: `denoteMeta` consults the valuation only at names it found, so
the reading transport `hde` follows from it
(`denoteMeta_acval_congr` then `denoteMeta_env_mono`). -/
theorem EnvBlocksOf.crossCons {env : Env} {m₁ : EnvModel V env} {c₀ : ConstantInfo}
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩} {B : ContainerInfo → BlockModel V}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlocksOf m₁ B) : EnvBlocksOf m₂ B := by
  intro J ci hci
  rw [ConLeche.containerInfo?_cons_nonInd hfresh hkind] at hci
  -- the own-pin clause crosses the cons as an INDUCTIVE extension whose
  -- one new name is `c₀`'s: that name is neither a recursor's nor a
  -- mimic's, so the walk cannot grow (`hkind`'s recursor clause)
  have hnewN : ∀ (n : Name) (c : ConstantInfo),
      (⟨c₀ :: env.consts⟩ : Env).find? n = some c →
      env.find? n = some c ∨ n ∈ [c₀.name] := by
    intro n c hf
    rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · next heq => exact Or.inr (List.mem_singleton.mpr heq.symm)
    · exact Or.inl hf
  have hnotRec : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      c₀.name = n → (⟨c₀ :: env.consts⟩ : Env).find? n ≠ some (.recInfo cv mI rP rules) := by
    intro n cv mI rP rules heq hrec
    rw [ConLeche.Env.find?_cons, if_pos heq] at hrec
    exact hkind.2.1 cv mI rP rules (Option.some.inj hrec)
  refine (hb J ci hci).crossEnv (fun n c _ hf => Env.find?_cons_of_fresh hfresh hf)
    (constsResolve_of_findPreserved (findPreserved_cons hfresh)) hag ?_
    ((hb J ci hci).1.k ▸ containerInfo?_members_pos hci) hb.pinGroups
    (fun q _ ci' h => by rw [ConLeche.containerInfo?_cons_nonInd hfresh hkind]; exact h)
    (fun h => ContainerOwnPinsSyn.crossIndOf (N := [c₀.name])
      (fun n c hf => Env.find?_cons_of_fresh hfresh hf) hnewN
      (fun n hn => by rw [List.mem_singleton.mp hn]; exact hfresh)
      (fun n cv mI rP rules hf hmem =>
        absurd hf (hnotRec _ cv mI rP rules (List.mem_singleton.mp hmem).symm))
      (fun n j cv mI rP rules hf hmem =>
        absurd hf (hnotRec _ cv mI rP rules (List.mem_singleton.mp hmem).symm))
      m₁.wf m₁.rec_ctors
      (recMajorHeadStored_of_envWF m₁.wf)
      (hb J ci hci).1 h)
  intro ψ dp e ea hd
  refine denoteMeta_env_mono (findPreserved_cons hfresh) (litGuardsMono_cons hfresh)
    (findProj?_cons_of_base_none hntc) dp e ?_
  rw [denoteMeta_acval_congr (acval₁ := m₂.acval) (acval₂ := m₁.acval) hag dp e]
  exact hd

theorem EnvBlockModels.crossCons {env : Env} {m₁ : EnvModel V env} {c₀ : ConstantInfo}
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩}
    (hfresh : env.find? c₀.name = none)
    (hkind : (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF))
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlockModels m₁) : EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, hB.crossCons hfresh hkind hntc hag⟩

/-- **The blocks survive an inductive extension, modulo the new block's
own containers**: an OLD container's block is read the same at the
extended environment (`containerInfo?_ext_ind_eq`) and its obligation
crosses at an assignment `B'` agreeing with the old one at the old
groups (`hold`); the containers the extension itself creates are the
installing route's obligation at `B'`, `hnew`.  The readings cross
under the GUARD (task #315 M7-3 session 3): the extension's new
projection tables are at structures fresh in `env₁` (`hfresh`), and an
old container's subjects are its members' STORED types, which resolve
there (`projFree_members`). -/
theorem EnvBlocksOf.crossIndP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name} {B B' : ContainerInfo → BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hold : ∀ (J : Name) (ci : ContainerInfo), J ∉ N →
      ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci)
    (hb : EnvBlocksOf m₁ B)
    (hnew : ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
      BlockAt m₂ B' ci) :
    EnvBlocksOf m₂ B' := by
  -- a name stored at the old environment is not a new one
  have hstored : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ N := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  -- the own-pin table's crossing needs one fact beyond the frame: a
  -- stored recursor's major premise is headed by a STORED constant,
  -- which `EnvWF` records unconditionally (`Expr.recMajorHeadOk`)
  have hhead : RecMajorHeadStored env₁ := recMajorHeadStored_of_envWF hwf
  intro J ci hci
  by_cases hJ : J ∈ N
  · exact hnew J hJ ci hci
  · have h₁ := ConLeche.containerInfo?_ext_ind hext hnewN hfreshN hrecN hwf hrc hJ hci
    have hB := hb J ci h₁
    -- the pins' containers of an old block are old, and read the same
    have hpc : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
        ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
        ((B ci).pinAt q).J ∉ N ∧ ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci' := by
      intro q hq ci' hci'
      obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci'
      have hnot : ((B ci).pinAt q).J ∉ N := hstored _ (by rw [hf]; rfl)
      refine ⟨hnot, ?_⟩
      rw [ConLeche.containerInfo?_ext_ind_eq hext hnewN hfreshN hrecN hwf hrc hnot]
      exact hci'
    obtain ⟨C, pc, hL, hS⟩ := hB.crossEnvP hF hres hag hde hfresh
      (projFree_members m₁ hfresh h₁) (hB.1.k ▸ containerInfo?_members_pos h₁)
      hb.pinGroups (fun q hq ci' hci' => (hpc q hq ci' hci').2)
      (fun h => ContainerOwnPinsSyn.crossIndOf hext hnewN hfreshN hrecN hmimN hwf hrc hhead
        hB.1 h)
    have hBci : B' ci = B ci := hold J ci hJ h₁
    refine ⟨by rw [hBci]; exact C, pc, by rw [hBci]; exact hL, ?_⟩
    rw [hBci]
    refine hS.congrB fun q hq ci' hci' => ?_
    -- `ci'` is the old reading of the pin's container
    obtain ⟨q₀, kJ, i, ci₁, -, -, hci₁, -, -⟩ := hB.2.choose_spec.2 q hq
    obtain ⟨hnot, hci₂⟩ := hpc q hq ci₁ hci₁
    obtain rfl : ci' = ci₁ := Option.some.inj (hci'.symm.trans hci₂)
    exact hold _ ci' hnot hci₁

/-- `EnvBlocksOf.crossIndP` at an extension that installs NO projection
table (`Ts := []`), where the readings cross unguarded. -/
theorem EnvBlocksOf.crossInd {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name} {B B' : ContainerInfo → BlockModel V}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hold : ∀ (J : Name) (ci : ContainerInfo), J ∉ N →
      ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci)
    (hb : EnvBlocksOf m₁ B)
    (hnew : ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
      BlockAt m₂ B' ci) :
    EnvBlocksOf m₂ B' := by
  -- a name stored at the old environment is not a new one
  have hstored : ∀ n : Name, (env₁.find? n).isSome = true → n ∉ N := by
    intro n hn hmem
    rw [hfreshN n hmem] at hn
    exact nomatch hn
  -- the own-pin table's crossing needs one fact beyond the frame: a
  -- stored recursor's major premise is headed by a STORED constant,
  -- which `EnvWF` records unconditionally (`Expr.recMajorHeadOk`)
  have hhead : RecMajorHeadStored env₁ := recMajorHeadStored_of_envWF hwf
  intro J ci hci
  by_cases hJ : J ∈ N
  · exact hnew J hJ ci hci
  · have h₁ := ConLeche.containerInfo?_ext_ind hext hnewN hfreshN hrecN hwf hrc hJ hci
    have hB := hb J ci h₁
    -- the pins' containers of an old block are old, and read the same
    have hpc : ∀ q, q < (B ci).nPins → ∀ ci' : ContainerInfo,
        ConLeche.containerInfo? env₁ ((B ci).pinAt q).J = some ci' →
        ((B ci).pinAt q).J ∉ N ∧ ConLeche.containerInfo? env₂ ((B ci).pinAt q).J = some ci' := by
      intro q hq ci' hci'
      obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci'
      have hnot : ((B ci).pinAt q).J ∉ N := hstored _ (by rw [hf]; rfl)
      refine ⟨hnot, ?_⟩
      rw [ConLeche.containerInfo?_ext_ind_eq hext hnewN hfreshN hrecN hwf hrc hnot]
      exact hci'
    obtain ⟨C, pc, hL, hS⟩ := hB.crossEnv hF hres hag hde (hB.1.k ▸ containerInfo?_members_pos h₁)
      hb.pinGroups (fun q hq ci' hci' => (hpc q hq ci' hci').2)
      (fun h => ContainerOwnPinsSyn.crossIndOf hext hnewN hfreshN hrecN hmimN hwf hrc hhead
        hB.1 h)
    have hBci : B' ci = B ci := hold J ci hJ h₁
    refine ⟨by rw [hBci]; exact C, pc, by rw [hBci]; exact hL, ?_⟩
    rw [hBci]
    refine hS.congrB fun q hq ci' hci' => ?_
    -- `ci'` is the old reading of the pin's container
    obtain ⟨q₀, kJ, i, ci₁, -, -, hci₁, -, -⟩ := hB.2.choose_spec.2 q hq
    obtain ⟨hnot, hci₂⟩ := hpc q hq ci₁ hci₁
    obtain rfl : ci' = ci₁ := Option.some.inj (hci'.symm.trans hci₂)
    exact hold _ ci' hnot hci₁

/-- **The field survives an inductive extension** (the guarded form):
`EnvBlocksOf.crossIndP` with the assignment quantified. -/
theorem EnvBlockModels.crossIndP {Ts : List Name} {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree Ts e → ∀ {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hfresh : ∀ T ∈ Ts, env₁.find? T = none)
    (hb : EnvBlockModels m₁)
    (hnew : ∀ B : ContainerInfo → BlockModel V, EnvBlocksOf m₁ B →
      ∃ B' : ContainerInfo → BlockModel V,
        (∀ (J : Name) (ci : ContainerInfo), J ∉ N →
          ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci) ∧
        ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
          BlockAt m₂ B' ci) :
    EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨B', hold, hnew'⟩ := hnew B hB
  exact ⟨B', hB.crossIndP hext hnewN hfreshN hrecN hmimN hwf hrc hF hres hag hde hfresh hold
    hnew'⟩

/-- `EnvBlockModels.crossIndP` at `Ts := []`. -/
theorem EnvBlockModels.crossInd {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {N : List Name}
    (hext : ∀ (n : Name) (c : ConstantInfo), env₁.find? n = some c → env₂.find? n = some c)
    (hnewN : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      env₁.find? n = some c ∨ n ∈ N)
    (hfreshN : ∀ n ∈ N, env₁.find? n = none)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) → n.str "rec" ∈ N → n ∈ N)
    (hmimN : ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N)
    (hwf : ConLeche.EnvWF env₁) (hrc : ConLeche.RecCtorsStored env₁)
    (hF : ∀ (n : Name) (c : ConstantInfo),
      (∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules) →
      env₁.find? n = some c → env₂.find? n = some c)
    (hres : ∀ e : Expr, e.constsResolve env₁ = true → e.constsResolve env₂ = true)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → m₂.acval n = m₁.acval n)
    (hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta m₁.acval env₁ ψ dp e = some ea → denoteMeta m₂.acval env₂ ψ dp e = some ea)
    (hb : EnvBlockModels m₁)
    (hnew : ∀ B : ContainerInfo → BlockModel V, EnvBlocksOf m₁ B →
      ∃ B' : ContainerInfo → BlockModel V,
        (∀ (J : Name) (ci : ContainerInfo), J ∉ N →
          ConLeche.containerInfo? env₁ J = some ci → B' ci = B ci) ∧
        ∀ J ∈ N, ∀ ci : ContainerInfo, ConLeche.containerInfo? env₂ J = some ci →
          BlockAt m₂ B' ci) :
    EnvBlockModels m₂ := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨B', hold, hnew'⟩ := hnew B hB
  exact ⟨B', hB.crossInd hext hnewN hfreshN hrecN hmimN hwf hrc hF hres hag hde hold hnew'⟩

/-! ## The own-pin table at ANOTHER instantiation (task #315 M7-3
session 18, DESIGN §U.104)

`containerOwnPinsAt` reads a container's own pins AT AN INSTANTIATION —
the level arguments and the components the caller asks for — and K.47
records the answer at ONE of them: the block's own levels
(`p.lps.map Level.param`, the identity substitution) and its parameter
OPENERS.  `ContainerOwnPinsSyn` is quantified over all of them, so the
recorded answer has to be TRANSPORTED, and that is what this section
does: one step of the walk (`ownPinsStep_subst`, on lane L-B's
`instPis_openers_subst` and the two level-instantiation commutations),
the walk's LENGTH (`containerOwnPinsAtGo_length_le`, which is what K.43
pins down), and the walk itself (`containerOwnPinsAtGo_subst`).

**Why the length is needed at all.**  The transport carries a step that
SUCCEEDS at the openers to the same step at the components; it says
nothing about a step that fails there, and such a step can succeed at
other components — a major premise headed by one of the recursor's own
PARAMETERS reads back headed by whatever the substitution put there
(`RecMajorHeadStored`'s discussion above).  K.43 makes the walk visit
exactly `numNested` names and K.47 makes it read exactly the
`st.pins.length` recorded pins; with one entry per step at most, the
two counts force EVERY step to succeed at the openers, and the
pathology is excluded rather than assumed.

**The components must be closed** (`hDcl`) — the clause's new
hypothesis, and not a convenience: the pad the reader instantiates the
mimic's motives, minors and indices at runs AFTER the components, so a
component carrying a loose bound variable is eaten by it.  See
`ContainerOwnPinsSyn`'s own docstring for the two real-run
counterexamples. -/

/-- **A TABLE ENTRY, RE-SPELLED AT ANOTHER INSTANTIATION**: the head's
level arguments substituted, and each component closed at the block's
parameter openers, level-instantiated and re-opened at the components
the reader was asked for.

At a constant-headed spine — which every entry of the table is, the
reader keeps no other — this IS `PinSyn.ownAt` of the pin the entry
records (`nestedOwnPins_of`); it is spelled here without a `PinSyn` so
that the walk's lemmas stay about `Expr`s. -/
@[expose] def ownSubst (nP : Nat) (lps : List Name) (lvls : List Level) (DsE : List Expr)
    (e : Expr) : Expr :=
  Expr.mkAppN (Expr.instantiateLevelParams lps lvls e.getAppFn)
    (e.getAppArgs.map fun x =>
      Expr.instSeq DsE (DsE.length - 1)
        ((x.abstractRange 0 nP 0).instantiateLevelParams lps lvls))

/-- **ONE STEP OF THE OWN-PIN WALK**: what the mimic recursor whose
stored type is `ty` contributes to the table — `containerOwnPinsAtGo`'s
own `here`, named so that the step and the walk can be reasoned about
apart. -/
@[expose] def ownPinsStep (env : Env) (lps : List Name) (lvls : List Level) (Ds : List Expr)
    (nPr mI : Nat) (ty : Expr) : List Expr :=
  if nPr ≤ mI && Ds.length == nPr then
    match Expr.instPis (ty.instantiateLevelParams lps lvls)
        (Ds ++ (List.range (mI - nPr)).map fun _ => Expr.sort Level.zero) with
    | some (.forallE dom _ _) =>
      match dom.getAppFn with
      | .const K _ =>
        match ConLeche.containerInfo? env K with
        | some ciK => [Expr.mkAppN dom.getAppFn (dom.getAppArgs.take ciK.nP)]
        | none => []
      | _ => []
    | _ => []
  else []

/-- A step reads at most one pin: every branch of the walk's `here` is
empty or a singleton. -/
theorem ownPinsStep_length_le_one (env : Env) (lps : List Name) (lvls : List Level)
    (Ds : List Expr) (nPr mI : Nat) (ty : Expr) :
    (ownPinsStep env lps lvls Ds nPr mI ty).length ≤ 1 := by
  unfold ownPinsStep
  repeat' split
  all_goals simp

/-- The walk, unfolded at a name that IS a stored recursor: this step's
entry, then the walk from the next name. -/
theorem containerOwnPinsAtGo_cons {env : Env} {base : Name} {lps : List Name}
    {lvls : List Level} {Ds : List Expr} {nPr : Nat} {cvR : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (fuel j : Nat)
    (h : env.find? (Name.appendIndexAfter base (j + 1)) = some (.recInfo cvR mI rP rules)) :
    ConLeche.containerOwnPinsAtGo env base lps lvls Ds nPr (fuel + 1) j
      = ownPinsStep env lps lvls Ds nPr mI cvR.type
        ++ ConLeche.containerOwnPinsAtGo env base lps lvls Ds nPr fuel (j + 1) := by
  simp only [ConLeche.containerOwnPinsAtGo, h]
  rfl

/-- The walk, at a name that is NOT a stored recursor: it stops, at any
fuel. -/
theorem containerOwnPinsAtGo_stop {env : Env} {base : Name} {lps : List Name}
    {lvls : List Level} {Ds : List Expr} {nPr : Nat} (fuel j : Nat)
    (h : ConLeche.isRecInfoAt env (Name.appendIndexAfter base (j + 1)) = false) :
    ConLeche.containerOwnPinsAtGo env base lps lvls Ds nPr fuel j = [] := by
  cases fuel with
  | zero => rfl
  | succ f =>
    unfold ConLeche.isRecInfoAt at h
    unfold ConLeche.containerOwnPinsAtGo
    split
    · rename_i cvR mI rP rules hfind
      rw [hfind] at h
      exact nomatch h
    · rfl

/-- **THE WALK'S LENGTH IS THE NUMBER OF MIMICS** (the half K.43
records): a walk that reaches a name which is not a stored recursor
after `n` steps reads at most `n` entries, since a step reads at most
one. -/
theorem containerOwnPinsAtGo_length_le {env : Env} {base : Name} {lps : List Name}
    {lvls : List Level} {Ds : List Expr} {nPr : Nat} :
    ∀ (fuel n j : Nat),
      ConLeche.isRecInfoAt env (Name.appendIndexAfter base (j + n + 1)) = false →
      (ConLeche.containerOwnPinsAtGo env base lps lvls Ds nPr fuel j).length ≤ n := by
  intro fuel
  induction fuel with
  | zero => intro n j _; simp [ConLeche.containerOwnPinsAtGo]
  | succ f ih =>
    intro n j hstop
    cases hfind : env.find? (Name.appendIndexAfter base (j + 1)) with
    | none =>
      rw [containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])]
      simp
    | some c =>
      cases c with
      | recInfo cvR mI rP rules =>
        cases n with
        | zero =>
          exfalso
          unfold ConLeche.isRecInfoAt at hstop
          rw [show j + 0 + 1 = j + 1 from rfl, hfind] at hstop
          exact nomatch hstop
        | succ n' =>
          rw [containerOwnPinsAtGo_cons f j hfind, List.length_append]
          have h1 := ownPinsStep_length_le_one env lps lvls Ds nPr mI cvR.type
          have h2 := ih n' (j + 1)
            (by rw [show j + 1 + n' + 1 = j + (n' + 1) + 1 from by omega]; exact hstop)
          omega
      | _ =>
        rw [containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])]
        simp

/-- **A STEP THAT READ A PIN, INVERTED**: the guard held, the mimic's
telescope instantiated to a `∀`, its domain is a constant-headed spine
and the head is a stored container — the data the transport moves. -/
theorem ownPinsStep_inv {env : Env} {lps : List Name} {lvls : List Level} {Ds : List Expr}
    {nPr mI : Nat} {ty e₀ : Expr}
    (h : ownPinsStep env lps lvls Ds nPr mI ty = [e₀]) :
    ∃ (dom body : Expr) (bm : ConLeche.BinderMeta) (K : Name) (us : List Level)
      (ciK : ContainerInfo),
      nPr ≤ mI ∧ Ds.length = nPr ∧
      Expr.instPis (ty.instantiateLevelParams lps lvls)
          (Ds ++ (List.range (mI - nPr)).map fun _ => Expr.sort Level.zero)
        = some (.forallE dom body bm) ∧
      dom.getAppFn = Expr.const K us ∧
      ConLeche.containerInfo? env K = some ciK ∧
      e₀ = Expr.mkAppN (Expr.const K us) (dom.getAppArgs.take ciK.nP) := by
  unfold ownPinsStep at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
    split at h
    · rename_i dom body bm heq
      split at h
      · rename_i K us hfn
        split at h
        · rename_i ciK hK
          refine ⟨dom, body, bm, K, us, ciK, hg.1, hg.2, heq, hfn, hK, ?_⟩
          rw [← hfn]
          simpa using h.symm
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **ONE STEP, TRANSPORTED** (task #315 M7-3 session 18, DESIGN §U.104
(b)): a step that reads a pin at the block's own levels and parameter
OPENERS reads the SAME pin, re-spelled (`ownSubst`), at any level
arguments and any CLOSED components of the same number.

The stored type is closed (`hf`, `hb`: it is a stored recursor's), so
lane L-B's `instPis_openers_subst` carries the whole telescope
instantiation from the openers to the components; the level arguments
move first, by `instPis_ilp` at the IDENTITY substitution K.47 records
(`Expr.instantiateLevelParams_self`); and the entry is a
constant-headed spine, which the two transports pass through component
by component (`ilp_mkAppN`, `abstractRange_mkAppN`,
`instSeq_mkAppN_const`). -/
theorem ownPinsStep_subst {env : Env} {lps : List Name} {lvls : List Level}
    {params DsE : List Expr} {nP mI : Nat} {ty e₀ : Expr}
    (hf : ty.hasFvar = false) (hb : ty.looseBVarsBounded 0 = true)
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ t, params[j]? = some (Expr.fvar j t))
    (hDlen : DsE.length = nP) (hDcl : ∀ a ∈ DsE, a.looseBVarsBounded 0 = true)
    (hbase : ownPinsStep env lps (lps.map Level.param) params nP mI ty = [e₀]) :
    ownPinsStep env lps lvls DsE nP mI ty = [ownSubst nP lps lvls DsE e₀] := by
  obtain ⟨dom, body, bm, K, us, ciK, hle, -, h0, hfn, hK, he₀⟩ := ownPinsStep_inv hbase
  rw [Expr.instantiateLevelParams_self] at h0
  -- the pad is closed and carries no free variable
  have hpadMem : ∀ a ∈ (List.range (mI - nP)).map (fun _ => Expr.sort Level.zero),
      a = Expr.sort Level.zero := by
    intro a ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    rfl
  have hpadb : ∀ a ∈ (List.range (mI - nP)).map (fun _ => Expr.sort Level.zero),
      a.looseBVarsBounded 0 = true := fun a ha => by rw [hpadMem a ha]; rfl
  have hpadf : ∀ a ∈ (List.range (mI - nP)).map (fun _ => Expr.sort Level.zero),
      a.hasFvar = false := fun a ha => by rw [hpadMem a ha]; rfl
  -- the run at the components: the levels first (K.47 records the identity
  -- substitution), then the openers
  have hilp := ConLeche.instPis_ilp lps lvls
    (params ++ (List.range (mI - nP)).map fun _ => Expr.sort Level.zero) ty
    (.forallE dom body bm) h0
  have hmap : (params ++ (List.range (mI - nP)).map fun _ => Expr.sort Level.zero).map
        (Expr.instantiateLevelParams lps lvls)
      = params.map (Expr.instantiateLevelParams lps lvls)
        ++ (List.range (mI - nP)).map fun _ => Expr.sort Level.zero := by
    rw [List.map_append]
    refine congrArg _ (List.ext_getElem (by simp) (fun n _ h2 => ?_))
    rw [List.getElem_map, hpadMem _ (List.getElem_mem h2)]
    rfl
  rw [hmap] at hilp
  have hgen := ConLeche.instPis_openers_subst
    (T := ty.instantiateLevelParams lps lvls) (nP := nP)
    (params := params.map (Expr.instantiateLevelParams lps lvls))
    (pad := (List.range (mI - nP)).map fun _ => Expr.sort Level.zero) (Ds := DsE)
    (R₀ := (Expr.forallE dom body bm).instantiateLevelParams lps lvls)
    (by rw [Expr.hasFvar_instantiateLevelParams]; exact hf)
    (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb)
    (by rw [List.length_map]; exact hplen)
    (fun j hj => by
      obtain ⟨t, ht⟩ := hidx j hj
      exact ⟨t.instantiateLevelParams lps lvls, by rw [List.getElem?_map, ht]; rfl⟩)
    hDlen hDcl hpadb hpadf hilp
  -- the residual is a `∀` whose domain is the pin, re-spelled
  have hshape : Expr.instSeq DsE (nP - 1)
        (((Expr.forallE dom body bm).instantiateLevelParams lps lvls).abstractRange 0 nP 0)
      = Expr.forallE
          (Expr.instSeq DsE (nP - 1)
            ((dom.instantiateLevelParams lps lvls).abstractRange 0 nP 0))
          (Expr.instSeq DsE (nP - 1 + 1)
            ((body.instantiateLevelParams lps lvls).abstractRange 0 nP 1))
          ⟨Level.substPW lps lvls bm.pw⟩ := by
    show Expr.instSeq DsE (nP - 1) (Expr.forallE _ _ _) = _
    exact Expr.instSeq_forallE DsE (nP - 1) _ _ _ (by rw [hDlen]; omega)
  -- the domain's spine, component by component
  have hdomEq : dom = Expr.mkAppN (Expr.const K us) dom.getAppArgs := by
    conv => lhs; rw [← Expr.mkAppN_getApp dom]
    rw [hfn]
  have hDgen : Expr.instSeq DsE (nP - 1)
        ((dom.instantiateLevelParams lps lvls).abstractRange 0 nP 0)
      = Expr.mkAppN (Expr.const K (us.map (Level.subst lps lvls)))
          (dom.getAppArgs.map fun x => Expr.instSeq DsE (DsE.length - 1)
            ((x.abstractRange 0 nP 0).instantiateLevelParams lps lvls)) := by
    conv => lhs; rw [hdomEq]
    rw [ConLeche.ilp_mkAppN]
    show Expr.instSeq DsE (nP - 1)
      ((Expr.mkAppN (Expr.const K (us.map (Level.subst lps lvls)))
        (dom.getAppArgs.map (Expr.instantiateLevelParams lps lvls))).abstractRange 0 nP 0) = _
    rw [ConLeche.abstractRange_mkAppN, ConLeche.abstractRange_const,
      ConLeche.instSeq_mkAppN_const, hDlen]
    simp only [List.map_map, Function.comp_def]
    refine congrArg _ (List.map_congr_left (fun x _ => ?_))
    rw [ConLeche.abstractRange_ilp]
  -- and the step at the components reads exactly that
  unfold ownPinsStep
  rw [if_pos (by simp only [hDlen, beq_self_eq_true, Bool.and_true, decide_eq_true_eq]; exact hle)]
  simp only [hgen, hshape, hDgen, Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN, Expr.getAppFn,
    Expr.getAppArgs, List.nil_append, hK, he₀, ownSubst, List.map_take]
  simp only [Expr.instantiateLevelParams]

/-- A step at the WRONG NUMBER of components reads nothing: the
reader's guard compares the components' length with the group's
parameter count. -/
theorem ownPinsStep_nil_of_len {env : Env} {lps : List Name} {lvls : List Level} {Ds : List Expr}
    {nPr mI : Nat} {ty : Expr} (h : Ds.length ≠ nPr) :
    ownPinsStep env lps lvls Ds nPr mI ty = [] := by
  unfold ownPinsStep
  rw [if_neg (by simp [h])]

/-- …and so does the whole walk, at every name and every fuel. -/
theorem containerOwnPinsAtGo_nil_of_len {env : Env} {base : Name} {lps : List Name}
    {lvls : List Level} {Ds : List Expr} {nPr : Nat} (h : Ds.length ≠ nPr) :
    ∀ (fuel j : Nat), ConLeche.containerOwnPinsAtGo env base lps lvls Ds nPr fuel j = [] := by
  intro fuel
  induction fuel with
  | zero => intro j; rfl
  | succ f ih =>
    intro j
    cases hfind : env.find? (Name.appendIndexAfter base (j + 1)) with
    | none =>
      exact containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])
    | some c =>
      cases c with
      | recInfo cvR mI rP rules =>
        rw [containerOwnPinsAtGo_cons f j hfind, ownPinsStep_nil_of_len h, ih (j + 1)]
        rfl
      | _ =>
        exact containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])

/-- **THE TABLE, TRANSPORTED** (task #315 M7-3 session 18, DESIGN §U.104
(b)): the own-pin table at any level arguments and any CLOSED
components of the right number is the table at the block's own levels
and parameter openers, entry by entry re-spelled.

`hstop` is K.43's second half — the walk reaches a name that is not a
stored recursor after `n` steps — and `hlen` is K.47's: the table read
there has one entry per step.  Together they make every step of the
walk succeed AT THE OPENERS, which is what lets the step transport
apply to all of them (see the section's preamble). -/
theorem containerOwnPinsAtGo_subst {env : Env} {base : Name} {lps : List Name}
    {lvls : List Level} {params DsE : List Expr} {nP : Nat}
    (hwf : ConLeche.EnvWF env)
    (hplen : params.length = nP)
    (hidx : ∀ j, j < nP → ∃ t, params[j]? = some (Expr.fvar j t))
    (hDlen : DsE.length = nP) (hDcl : ∀ a ∈ DsE, a.looseBVarsBounded 0 = true) :
    ∀ (n fuel j : Nat),
      ConLeche.isRecInfoAt env (Name.appendIndexAfter base (j + n + 1)) = false →
      (ConLeche.containerOwnPinsAtGo env base lps (lps.map Level.param) params nP
        fuel j).length = n →
      ConLeche.containerOwnPinsAtGo env base lps lvls DsE nP fuel j
        = (ConLeche.containerOwnPinsAtGo env base lps (lps.map Level.param) params nP
            fuel j).map (ownSubst nP lps lvls DsE) := by
  intro n
  induction n with
  | zero =>
    intro fuel j hstop _
    have hstop0 : ConLeche.isRecInfoAt env (Name.appendIndexAfter base (j + 1)) = false := by
      rw [show j + 1 = j + 0 + 1 from rfl]
      exact hstop
    simp only [containerOwnPinsAtGo_stop fuel j hstop0, List.map_nil]
  | succ n ih =>
    intro fuel j hstop hlen
    cases fuel with
    | zero => simp [ConLeche.containerOwnPinsAtGo] at hlen
    | succ f =>
      cases hfind : env.find? (Name.appendIndexAfter base (j + 1)) with
      | none =>
        rw [containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])]
          at hlen
        exact nomatch hlen
      | some c =>
        cases c with
        | recInfo cvR mI rP rules =>
          rw [containerOwnPinsAtGo_cons f j hfind] at hlen ⊢
          rw [containerOwnPinsAtGo_cons f j hfind]
          -- one entry per step: the step reads at most one and the tail at most `n`
          have h1 := ownPinsStep_length_le_one env lps (lps.map Level.param) params nP mI cvR.type
          have hstop' : ConLeche.isRecInfoAt env
              (Name.appendIndexAfter base (j + 1 + n + 1)) = false := by
            rw [show j + 1 + n + 1 = j + (n + 1) + 1 from by omega]; exact hstop
          have h2 := containerOwnPinsAtGo_length_le (env := env) (base := base) (lps := lps)
            (lvls := lps.map Level.param) (Ds := params) (nPr := nP) f n (j + 1) hstop'
          rw [List.length_append] at hlen
          have hstep : (ownPinsStep env lps (lps.map Level.param) params nP mI cvR.type).length
              = 1 := by omega
          have htail : (ConLeche.containerOwnPinsAtGo env base lps (lps.map Level.param) params
              nP f (j + 1)).length = n := by omega
          obtain ⟨e₀, he₀⟩ := List.length_eq_one_iff.mp hstep
          have hclosed := hwf _ (List.mem_of_find?_eq_some hfind)
          rw [he₀, ownPinsStep_subst (env := env) (lps := lps) (lvls := lvls) (params := params)
            (DsE := DsE) (nP := nP) (mI := mI) (ty := cvR.type) (e₀ := e₀)
            hclosed.1 hclosed.2.2.2.1 hplen hidx hDlen hDcl he₀,
            ih f (j + 1) hstop' htail, List.map_append]
          rfl
        | _ =>
          rw [containerOwnPinsAtGo_stop (f + 1) j (by unfold ConLeche.isRecInfoAt; rw [hfind])]
            at hlen
          exact nomatch hlen

/-! ## What the crossing cannot be asked across a projection table -/

/-- Every TOWER reading of a field is headed by `fst`
(`projAV k e = .fst (.snd^[k] e)`). -/
theorem projAV_head_fst : ∀ (k : Nat) (e : AnnotTerm), ∃ x, projAV k e = .fst x
  | 0, e => ⟨e, rfl⟩
  | k + 1, e => projAV_head_fst k (.snd e)

/-- **A NEW PROJECTION TABLE MOVES THE READING** (task #315 M7-3
session 2, DESIGN §U.40).  `denoteMeta` reads `.proj sn i e` through
the environment's table when there is one (`projAV`, headed by `fst`)
and through the PAIR decoder when there is none (`projPair?`, which at
`i = 1` is `snd`).  So an extension that adds a table at a structure
whose slot `1` was untabled changes a SUCCESSFUL reading — the two
readings of `.proj sn 1 (.sort .zero)` differ in their head former.

This is the exact hypothesis `ContainerModeled.crossEnv` and
`EnvBlocksOf.crossInd` take as `hde`, and it is why no install route
can discharge it as it stands: every route ends by consing the
projection tables of its structure-like members
(`checkNativeTable`/`mutualTables`/`nestedTables`), and a structure
with two or more fields has a slot `1`. -/
theorem denoteMeta_not_mono_of_newTable {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {ψ : Name → Nat} {dp : Nat} {sn : Name} {entry : ConLeche.ProjEntry}
    (h₁ : env₁.findProj? sn 1 = none) (h₂ : env₂.findProj? sn 1 = some entry) :
    ∃ (e : Expr) (ea : AnnotTerm),
      denoteMeta acval₁ env₁ ψ dp e = some ea ∧ denoteMeta acval₂ env₂ ψ dp e ≠ some ea := by
  refine ⟨.proj sn 1 (.sort .zero), .snd (.sort (Level.zero.eval ψ)), ?_, ?_⟩
  · simp only [denoteMeta, h₁, bind, Option.bind]
    rfl
  · simp only [denoteMeta, h₂, bind, Option.bind]
    intro hh
    obtain ⟨x, hx⟩ := projAV_head_fst (1 + entry.off) (.sort (Level.zero.eval ψ))
    rw [hx] at hh
    exact nomatch (Option.some.inj hh)

/-- **The crossing's reading hypothesis is REFUTABLE across a table
cons**: `ContainerModeled.crossEnv`'s `hde` (and with it
`BlockAt.crossEnv`, `EnvBlocksOf.crossInd`) asks for EVERY expression's
reading to survive, which an extension installing a projection table
does not grant.  The fix is not a stronger route fact but a WEAKER
hypothesis — the readings guarded by the subjects' resolution at the
block's own pre-block environment (`BlockOpened`'s `ord`/`recF`/
`reflF`/`nestF` clauses already record it, and a block's members are
fresh there, so `noProjAt_of_constsResolve` applies) — DESIGN §U.40. -/
theorem hde_not_of_newTable {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {sn : Name} {entry : ConLeche.ProjEntry}
    (h₁ : env₁.findProj? sn 1 = none) (h₂ : env₂.findProj? sn 1 = some entry) :
    ¬ (∀ (ψ : Name → Nat) (dp : Nat) (e : Expr) {ea : AnnotTerm},
        denoteMeta m₁.acval env₁ ψ dp e = some ea →
        denoteMeta m₂.acval env₂ ψ dp e = some ea) := by
  intro h
  obtain ⟨e, ea, h1, h2⟩ :=
    denoteMeta_not_mono_of_newTable (acval₁ := m₁.acval) (acval₂ := m₂.acval)
      (ψ := fun _ => 0) (dp := 0) h₁ h₂
  exact h2 (h _ _ e h1)

/-! ## The route's own read-back (task #315 K.34) -/

/-- Structural equality on the container data is an equality: every
field is a `Name`, an `Expr`, a `Nat` or a list of those, and all of
those are `LawfulBEq`.  The three instances are what makes K.34's
Bool — `containerInfo? envOut M.name == some want` — readable as the
EQUATION `EnvBlocksOf` is quantified over. -/
instance : LawfulBEq ConLeche.ContainerCtor where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerCtor.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [ConLeche.ContainerCtor.mk.injEq]
    exact ⟨eq_of_beq h1, eq_of_beq h2, of_decide_eq_true h3⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerCtor.beq, Bool.and_eq_true]
    exact ⟨beq_self_eq_true (α := Name) _, beq_self_eq_true (α := Expr) _, by simp⟩

@[inherit_doc instLawfulBEqContainerCtor]
instance : LawfulBEq ConLeche.ContainerMember where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerMember.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [ConLeche.ContainerMember.mk.injEq]
    exact ⟨eq_of_beq h1, eq_of_beq h2, eq_of_beq h3, eq_of_beq h4⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerMember.beq, Bool.and_eq_true]
    exact ⟨beq_self_eq_true (α := Name) _, beq_self_eq_true (α := List Name) _,
      beq_self_eq_true (α := Expr) _,
      beq_self_eq_true (α := List ConLeche.ContainerCtor) _⟩

@[inherit_doc instLawfulBEqContainerCtor]
instance : LawfulBEq ContainerInfo where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, ConLeche.instBEqContainerInfo.beq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [ConLeche.ContainerInfo.mk.injEq]
    exact ⟨of_decide_eq_true h1, eq_of_beq h2⟩
  rfl {a} := by
    cases a
    simp only [BEq.beq, ConLeche.instBEqContainerInfo.beq, Bool.and_eq_true]
    exact ⟨by simp, beq_self_eq_true (α := List ConLeche.ContainerMember) _⟩

/-- **THE READ-BACK, INVERTED** (task #315 K.34, DESIGN §U.31 (d)): the
route's own Bool says that `containerInfo?` of the environment it
produced reads, AT EVERY MEMBER of the block it installed, exactly the
block's own data — so at member `i` the reading is
`blockContainerInfo`, which is the `ContainerInfo` the field
`EnvBlocksOf` is quantified over asks about. -/
theorem containerInfo?_of_readBack {envOut : Env} {nP : Nat}
    {members : List (ConstantVal × List (ConstantVal × Nat))}
    (h : ConLeche.blockReadBackOk envOut nP members = true)
    {i : Nat} {c : ConstantVal × List (ConstantVal × Nat)} (hi : members[i]? = some c) :
    ConLeche.containerInfo? envOut c.1.name
      = some (ConLeche.blockContainerInfo nP members) := by
  unfold ConLeche.blockReadBackOk at h
  rw [List.all_eq_true] at h
  have hM : (⟨c.1.name, c.1.levelParams, c.1.type,
      c.2.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember)
      ∈ (ConLeche.blockContainerInfo nP members).members :=
    List.mem_map_of_mem (List.mem_of_getElem? hi)
  exact eq_of_beq (h _ hM)

/-- **The block just installed IS its own container group** (task #315
K.34's inversion at the model tier): at the reading the route
certifies, `ContainerModeled`'s four DATA clauses — the member count,
the parameter count, the member names and the constructors' names —
are the block's own, so the record is the block model's ties to the
route's data (`hk`, `hnP`, `hnames`, `hctorNames`) together with the
model-facing facts the route already proves.  The member clause's
constant is the stored one on the nose: `blockContainerInfo` copies
the member's `ConstantVal` field by field.

What every route must still bring is the LAST argument, `hmember`:
`IsBlockModel` at the OUTPUT model.  Every route builds it at the
model of its RECURSORS' environment and then conses its projection
tables, and the block model does not cross that cons — DESIGN §U.40. -/
theorem ContainerModeled.of_readBack {env : Env} {m : EnvModel V env} {nP : Nat}
    {members : List (ConstantVal × List (ConstantVal × Nat))} {d : BlockModel V}
    (hk : d.k = members.length) (hnP : d.nP = nP)
    (hnamesLen : d.memberNames.length = d.k)
    (hnames : ∀ i, i < d.k → d.memberName i = (members.getD i default).1.name)
    (hctorNames : ∀ i, i < d.k →
      (d.ctorsM i).map (·.1.name) = (members.getD i default).2.map (·.1.name))
    (hreps : IsBlockModels m d)
    (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ ∧ PinsTyped m d ψ)
    (hinj : ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
      d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt])))
    (hframe : ∀ i, i < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM i ψ).take d.nP).map (·.2.2)).reverse ρ)
    (hordFree : ∀ (i j l : Nat) (x : Expr), i < d.k → j < (d.ctorsM i).length →
      (d.xFvsF i j)[l]? = some x → (d.ksF i j).getD l .ordinary = .ordinary →
      ConLeche.mentionsMember d.memberNames x.fvarTypeD = false)
    (hnestMention : ∀ q, q < d.nPins →
      ∃ e ∈ (d.pinAt q).DsE.take (d.pinAt q).nPJ,
        ConLeche.mentionsMember d.memberNames e = true)
    (hnestArgsMention : ∀ (i j l : Nat) (x : Expr) (q : Nat), i < d.k →
      j < (d.ctorsM i).length → (d.xFvsF i j)[l]? = some x → d.nestOf i j l = some q →
      q < d.nPins →
      (d.ksF i j).getD l .ordinary = .recursive →
      ∃ e ∈ x.fvarTypeD.getAppArgs.take (d.pinAt q).nPJ,
        ConLeche.mentionsMember d.memberNames e = true)
    (hnestArgsMentionAbs : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat), i < d.k →
      (d.ctorsM i)[j]? = some cA →
      cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
      d.nestOf i j l = some q → q < d.nPins →
      (d.ksF i j).getD l .ordinary = .recursive →
      ∃ e ∈ dom.1.getAppArgs.take (d.pinAt q).nPJ,
        ConLeche.mentionsMember d.memberNames e = true)
    (hnestArgsMentionAbsRefl : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat), i < d.k →
      (d.ctorsM i)[j]? = some cA →
      cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
      d.nestOf i j l = some q → q < d.nPins →
      (d.ksF i j).getD l .ordinary = .reflexive →
      ∃ e ∈ (ConLeche.stripDomPis dom.1).getAppArgs.take (d.pinAt q).nPJ,
        ConLeche.mentionsMember d.memberNames e = true)
    (hnestPinSpineAbs : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat) (lps : List Name), i < d.k →
      (d.ctorsM i)[j]? = some cA →
      cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
      d.nestOf i j l = some q → q < d.nPins →
      (d.ksF i j).getD l .ordinary = .recursive →
      Expr.instantiateList
          (Expr.mkAppN dom.1.getAppFn (dom.1.getAppArgs.take (d.pinAt q).nPJ))
          (ConLeche.containerParamOpeners d.nP).reverse l
        = (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
            (ConLeche.containerParamOpeners d.nP))
    (hnestPinSpineAbsRefl : ∀ (i j l : Nat) (cA : ConstantVal × Nat)
      (bs : List (Expr × ConLeche.BinderMeta)) (r : Expr)
      (dom : Expr × ConLeche.BinderMeta) (q : Nat) (lps : List Name), i < d.k →
      (d.ctorsM i)[j]? = some cA →
      cA.1.type.stripPis (d.nP + cA.2) = some (bs, r) → bs[d.nP + l]? = some dom →
      d.nestOf i j l = some q → q < d.nPins →
      (d.ksF i j).getD l .ordinary = .reflexive →
      Expr.instantiateList
          (Expr.mkAppN (ConLeche.stripDomPis dom.1).getAppFn
            ((ConLeche.stripDomPis dom.1).getAppArgs.take (d.pinAt q).nPJ))
          (ConLeche.containerParamOpeners d.nP).reverse (l + ConLeche.domPiDepth dom.1)
        = (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
            (ConLeche.containerParamOpeners d.nP))
    (hctorProjFree : ∀ (i j : Nat) (cA : ConstantVal × Nat), i < d.k →
      (d.ctorsM i)[j]? = some cA →
      ∀ T ∈ d.memberNames, ∀ n : Nat, ConLeche.Expr.NoProjAt T n cA.1.type)
    (hpinsNotMembers : ∀ q, q < d.nPins → (d.pinAt q).J ∉ d.memberNames)
    (hpinNP : ∀ q, q < d.nPins → ∃ ci' : ContainerInfo,
      ConLeche.containerInfo? d.env₀ (d.pinAt q).J = some ci' ∧ (d.pinAt q).nPJ = ci'.nP)
    (hpinConts : ∀ q, q < d.nPins → ∀ ci' : ContainerInfo,
      ConLeche.containerInfo? d.env₀ (d.pinAt q).J = some ci' →
      ConLeche.containerInfo? env (d.pinAt q).J = some ci')
    (hownPins : ContainerOwnPinsSyn (V := V) env d)
    (hpinψ : ∀ q, q < d.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (d.pinAt q).J = some (.indInfo cvT caps) →
      (d.pinAt q).lvls.length = cvT.levelParams.length ∧
      ∀ ψ : Name → Nat, (d.pinAt q).ψJ ψ = Level.substFn ψ cvT.levelParams (d.pinAt q).lvls)
    (hpinParams : ∀ (i : Nat), i < members.length →
      ContainerPinParams (V := V) (members.getD i default).1 d)
    (hmember : ∀ i, i < d.k → ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel m (members.getD i default).1.name (members.getD i default).1 cvR mI rP rules
        d i)
    (hpinsDistinct : ∀ q q', q < d.nPins → q' < d.nPins →
      Expr.mkAppN (.const (d.pinAt q).J (d.pinAt q).lvls) (d.pinAt q).DsE
        = Expr.mkAppN (.const (d.pinAt q').J (d.pinAt q').lvls) (d.pinAt q').DsE → q = q')
    (hpinsDistinctAt : ∀ q q' (lps : List Name), q < d.nPins → q' < d.nPins →
      (d.pinAt q).ownAt d.nP lps (lps.map Level.param)
          (ConLeche.containerParamOpeners d.nP)
        = (d.pinAt q').ownAt d.nP lps (lps.map Level.param)
            (ConLeche.containerParamOpeners d.nP) → q = q')
    (hpinDsScoped : ∀ q, q < d.nPins →
      ∃ params : List Expr, params.length = d.nP ∧
        (∀ j, j < d.nP → ∃ ty, params[j]? = some (Expr.fvar j ty)) ∧
        ∀ x ∈ (d.pinAt q).DsE, x.looseBVarsBounded 0 = true ∧
          ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ params)
    (hpinDsRes : ∀ q, q < d.nPins → ∀ x ∈ (d.pinAt q).DsE,
      x.constsResolve env = true)
    (hpinDsRead : ∀ q, q < d.nPins → ∀ φ : Name → Nat,
      DenoteMetaSpine m.acval env φ d.nP (d.pinAt q).DsE ((d.pinAt q).Ds φ)) :
    ContainerModeled m (ConLeche.blockContainerInfo nP members) d where
  k := by rw [hk]; show _ = (members.map _).length; rw [List.length_map]
  namesLen := hnamesLen
  nP := hnP
  reps := hreps
  typed := htyped
  inj := fun _ => hinj
  frame := hframe
  ordFree := hordFree
  nestMention := hnestMention
  pinsDistinct := hpinsDistinct
  pinsDistinctAt := hpinsDistinctAt
  pinDsScoped := hpinDsScoped
  pinDsRes := hpinDsRes
  pinDsRead := hpinDsRead
  nestArgsMention := hnestArgsMention
  nestArgsMentionAbs := hnestArgsMentionAbs
  nestArgsMentionAbsRefl := hnestArgsMentionAbsRefl
  nestPinSpineAbs := hnestPinSpineAbs
  nestPinSpineAbsRefl := hnestPinSpineAbsRefl
  ctorProjFree := hctorProjFree
  pinsNotMembers := hpinsNotMembers
  pinNP := hpinNP
  pinConts := hpinConts
  ownPins := hownPins
  pinψ := hpinψ
  pinParams := by
    -- the group's member `i` IS the route's `i`-th member
    -- (`blockContainerInfo` copies the stored `ConstantVal` field by
    -- field), so the clause at `⟨M.name, M.lps, M.type⟩` IS the clause
    -- at that member's own constant
    intro i M hM
    have hMl : (members.map fun (cvT, cs) =>
        (⟨cvT.name, cvT.levelParams, cvT.type,
          cs.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember))[i]?
        = some M := hM
    rw [List.getElem?_map] at hMl
    cases hc : members[i]? with
    | none => rw [hc] at hMl; exact nomatch hMl
    | some c =>
      rw [hc] at hMl
      obtain rfl : M = ⟨c.1.name, c.1.levelParams, c.1.type,
          c.2.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := (Option.some.inj hMl).symm
      have hcD : members.getD i default = c := by
        rw [List.getD_eq_getElem?_getD, hc]; rfl
      have h := hpinParams i (List.getElem?_eq_some_iff.mp hc).1
      rw [hcD] at h
      exact h
  member := fun i M hM => by
    -- the `i`-th entry is the `i`-th member of the route's list
    have hMl : (members.map fun (cvT, cs) =>
        (⟨cvT.name, cvT.levelParams, cvT.type,
          cs.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember))[i]?
        = some M := hM
    rw [List.getElem?_map] at hMl
    cases hc : members[i]? with
    | none => rw [hc] at hMl; exact nomatch hMl
    | some c =>
      rw [hc] at hMl
      obtain rfl : M = ⟨c.1.name, c.1.levelParams, c.1.type,
          c.2.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := (Option.some.inj hMl).symm
      have hik : i < d.k := by
        rw [hk]; exact (List.getElem?_eq_some_iff.mp hc).1
      have hcD : members.getD i default = c := by
        rw [List.getD_eq_getElem?_getD, hc]; rfl
      refine ⟨by rw [hnames i hik, hcD], ?_, ?_⟩
      · rw [hctorNames i hik, hcD]
        show _ = (c.2.map _).map _
        rw [List.map_map]; rfl
      · obtain ⟨cvR, mI, rP, rules, hI⟩ := hmember i hik
        rw [hcD] at hI
        exact ⟨cvR, mI, rP, rules, hI⟩

/-! ## A block with no pins -/

/-- **A block with NO PINS carries its group's obligation as soon as
its `ContainerModeled` holds** (task #315 M7-3 session 6): at
`d.pins = []` every clause of `PinRecLaws` but `mkZero` is quantified
`q < d.nPins` and so vacuous, `mkZero` is the `Inhabited (PinCtors V)`
witness's own injection (`fun _ _ _ => pt`, which is `mkZero`), and
`PinShapes` is vacuous.  The mutual and native routes' blocks are of
this shape (`MutualBlockModelOf.pins`). -/
theorem BlockAt.of_noPins {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    {ci : ContainerInfo} (hc : ContainerModeled m ci (B ci)) (hp : (B ci).pins = []) :
    BlockAt m B ci := by
  have h0 : (B ci).nPins = 0 := by show (B ci).pins.length = 0; rw [hp]; rfl
  refine ⟨hc, fun _ => default, ?_, fun q hq => absurd hq (by rw [h0]; omega)⟩
  exact
    { tgtsLt := fun _ q _ _ hq => absurd hq (by rw [h0]; omega)
      idxOk := fun _ _ _ q hq => absurd hq (by rw [h0]; omega)
      fibre := fun _ _ _ _ _ _ q hq => absurd hq (by rw [h0]; omega)
      mkZero := fun _ _ _ _ _ => rfl
      mkInj := fun _ _ q hq => absurd hq (by rw [h0]; omega)
      injW := fun _ q hq => absurd hq (by rw [h0]; omega)
      ind := fun _ _ _ _ _ _ _ q hq => absurd hq (by rw [h0]; omega) }

/-! ## The non-inductive stages of the fold -/

/-- **A stage that installs NOTHING, or conses ONE fresh constant of a
non-inductive kind** — the shape of every value-kind stage of the P
fold (definitions, theorems, opaques, axioms; the tolerated axiom skip
is the left arm): the new environment is the old one or one cons whose
name is fresh and whose head is neither of the three inductive kinds
`containerInfo?` reads nor a projection table. -/
@[expose] def NonIndStep (env env₂ : Env) : Prop :=
  env₂ = env ∨
    ∃ c₀ : ConstantInfo, env₂ = ⟨c₀ :: env.consts⟩ ∧ env.find? c₀.name = none ∧
      (∀ cv caps, c₀ ≠ .indInfo cv caps) ∧
      (∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) ∧
      (∀ cv nP nF, c₀ ≠ .ctorInfo cv nP nF) ∧ (∀ tbl, c₀ ≠ .projInfo tbl)

/-- **The model WITH ITS BLOCKS survives a non-inductive stage** — the
maintenance shape of every value-kind stage of the fold: the
`EnvModelM` the stage already produces, plus the agreement of its
carrier with the old one at the stored names, give the `blocks` field
back. -/
noncomputable def EnvModelB.ofNonIndStep {env env₂ : Env}
    (mb : EnvModelB V μ env) (m' : EnvModelM V μ env₂)
    (hstep : NonIndStep env env₂)
    (hag : AcvalAgrees mb.base2 m'.base2) :
    EnvModelB V μ env₂ where
  toEnvModelM := m'
  blocks := by
    rcases hstep with rfl | ⟨c₀, rfl, hfresh, hi, hr, hc, ht⟩
    · exact EnvBlockModels.crossSame hag mb.blocks
    · exact EnvBlockModels.crossCons hfresh ⟨hi, hr, hc⟩ ht hag mb.blocks

/-- **A block model's members are determined by their NAMES** (task
#315 L-E, DESIGN §U.71 — the alignment's second half): a group's
member-name list is `Nodup` (`containerInfo?_inv`) and
`ContainerModeled.member` reads the block model's members off it
positionally, so two classes of one block model with one name are one
class.  What identifies the root's class with the block's pin group's
member once the two sides' containers are known to be the same. -/
theorem ContainerModeled.memberName_inj {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {d : BlockModel V} (h : ContainerModeled m ci d) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci) {a b : Nat} (ha : a < d.k) (hb : b < d.k)
    (hab : d.memberName a = d.memberName b) : a = b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hnodup, -⟩ := ConLeche.containerInfo?_inv hci
  have ha' : a < ci.members.length := by rw [← h.k]; exact ha
  have hb' : b < ci.members.length := by rw [← h.k]; exact hb
  have hA := (h.member a ci.members[a] (by rw [List.getElem?_eq_getElem ha'])).1
  have hB := (h.member b ci.members[b] (by rw [List.getElem?_eq_getElem hb'])).1
  have hlenA : a < (ci.members.map (·.name)).length := by rw [List.length_map]; exact ha'
  have hlenB : b < (ci.members.map (·.name)).length := by rw [List.length_map]; exact hb'
  refine (List.getElem_inj (h₀ := hlenA) (h₁ := hlenB) hnodup).mp ?_
  rw [List.getElem_map, List.getElem_map, ← hA, ← hB]
  exact hab


/-- **A group's members share their level parameters, so its data are a
congruence in the level assignment** (task #315 L-E, DESIGN §U.71 —
`classPin_of_views`' `hparK`): at a stored group, two assignments
agreeing on the group's OWN constant's level parameters give one index
universe (`IsBlockModel.uParams`) and one parameter-and-index telescope
(`FormerData.params`) at EVERY member — because `containerInfo?`
records every member's level parameters as the group's
(`containerInfo?_inv`) and `ContainerModeled.member` asserts the
member's `IsBlockModel` at exactly that record. -/
theorem ContainerModeled.params_congr {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {dK : BlockModel V} (h : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {cvI : ConstantVal} {capsI : IndCaps} (hfI : env.find? I = some (.indInfo cvI capsI))
    {ψ₁ ψ₂ : Name → Nat} (hψ : ∀ p ∈ cvI.levelParams, ψ₁ p = ψ₂ p) {a : Nat} (ha : a < dK.k) :
    dK.uM a ψ₁ = dK.uM a ψ₂ ∧ dK.ppsM a ψ₁ = dK.ppsM a ψ₂ ∧ dK.w ψ₁ = dK.w ψ₂ := by
  obtain ⟨cvT, _caps, _cvR0, _mI0, _rP0, _rules0, hfind, _hfr0, _hmem0, _hnd0, hall⟩ :=
    ConLeche.containerInfo?_inv hci
  have hcvT : cvT = cvI := (ConstantInfo.indInfo.inj (Option.some.inj (hfind.symm.trans hfI))).1
  have ha' : a < ci.members.length := by rw [← h.k]; exact ha
  have hmem : ci.members[a]? = some ci.members[a] := by rw [List.getElem?_eq_getElem ha']
  obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := h.member a ci.members[a] hmem
  obtain ⟨_cvC, _capsC, _cvRc, _mIc, _rulesC, _hf1, _hf2, hlps, _hf4, hshare, _hf6, _hf7⟩ :=
    hall ci.members[a] (List.getElem_mem ha')
  have hψ' : ∀ p ∈ (⟨ci.members[a].name, ci.members[a].lps, ci.members[a].type⟩
      : ConstantVal).levelParams, ψ₁ p = ψ₂ p := by
    intro p hp
    exact hψ p (by rw [← hcvT, ← hshare, ← hlps]; exact hp)
  exact ⟨hI.uParams a ha ψ₁ ψ₂ hψ', (hI.former.params ψ₁ ψ₂ hψ').1,
    (hI.former.params ψ₁ ψ₂ hψ').2⟩


/-- **A member's level parameters ARE the group's** (task #315 L-E,
DESIGN §U.77): `containerInfo?_inv` records every member's as the
group's own constant's, and `ContainerModeled.member` asserts the
member's `IsBlockModel` at that record. -/
theorem ContainerModeled.memberLpsI {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {dK : BlockModel V} (h : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {cvI : ConstantVal} {capsI : IndCaps} (hfI : env.find? I = some (.indInfo cvI capsI))
    {a : Nat} (ha : a < dK.k) {cvA : ConstantVal} {capsA : IndCaps}
    (hA : env.find? (dK.memberName a) = some (.indInfo cvA capsA)) :
    cvA.levelParams = cvI.levelParams := by
  obtain ⟨cvT, _caps, _cvR0, _mI0, _rP0, _rules0, hfind, _hfr0, _hmem0, _hnd0, hall⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain rfl : cvT = cvI := (ConstantInfo.indInfo.inj (Option.some.inj (hfind.symm.trans hfI))).1
  have ha' : a < ci.members.length := by rw [← h.k]; exact ha
  have hmem : ci.members[a]? = some ci.members[a] := by rw [List.getElem?_eq_getElem ha']
  have hname := (h.member a ci.members[a] hmem).1
  obtain ⟨cvC, _capsC, _cvRc, _mIc, _rulesC, hf1, _hf2, _hlps, _hf4, hshare, _hf6, _hf7⟩ :=
    hall ci.members[a] (List.getElem_mem ha')
  rw [hname] at hA
  obtain rfl : cvA = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (hA.symm.trans hf1))).1
  exact hshare

/-- **A group's members share their level parameters** — so a level
agreement taken at ONE member's constant is an agreement at EVERY
member's.  What the WALK needs when it steps from the pair's member to
the field's target member (task #315 L-E, DESIGN §U.77). -/
theorem ContainerModeled.memberLps {env : Env} {m : EnvModel V env} {ci : ContainerInfo}
    {dK : BlockModel V} (h : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {cvI : ConstantVal} {capsI : IndCaps} (hfI : env.find? I = some (.indInfo cvI capsI))
    {a b : Nat} (ha : a < dK.k) (hb : b < dK.k)
    {cvA cvB : ConstantVal} {capsA capsB : IndCaps}
    (hA : env.find? (dK.memberName a) = some (.indInfo cvA capsA))
    (hB : env.find? (dK.memberName b) = some (.indInfo cvB capsB)) :
    cvA.levelParams = cvB.levelParams := by
  rw [h.memberLpsI hci hfI ha hA, h.memberLpsI hci hfI hb hB]


end ConLeche.Model
