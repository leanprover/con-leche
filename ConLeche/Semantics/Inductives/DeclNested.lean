module

public import ConLeche.Verify.Inductives.NestedOrderK

@[expose] public section

/-!
# `DeclNestedRun`: the nested declaration relation (task #279)

The nested arm of the `.indDecl` clause (`checkNested`,
`ConLeche/Kernel/Inductives/NestedInstall.lean`), recorded as a run
relation exactly as `DeclMutualRun` records the mutual route's: the two
syntactic front guards (official's `check_no_nested_aux` and
`check_uniform_ind_occs`), the PURE elimination with its mimic count,
the auxiliary mutual block checked by task #278's installer in a
SCRATCH environment, the read-back, the restored constructors, recursor
types and rules at the rule-less provision, the projection tables of
the structure-like members, and official's two remaining post-checks —
the pins typed at the parameter context (leanprover/lean4#14577) and
the stream's recursor records against the restored generated ones.

**`order`** is the copies' TOPOLOGICAL ORDER along their reference
relation (DESIGN §M.22, the maintainer's decision that the KERNEL
computes it): `nestedTopoOrder (ElimState.grp st) p.k st = .ok order`,
where `ElimState.grp` is the mint-group assignment the elimination now
records on every pin (`NestedPin.grpBase`/`grpSize` — it is not
recoverable from the pin list afterwards).  `copyRefB` is the model
lane's `CopyRef` clause for clause, as a `Bool`; `nestedTopoOrder`
checks its own result against `topoOrderOk`, whose four conjuncts ARE
`TopoOrder`'s four fields, so the fields are facts about the result and
not about the algorithm (`Verify/Inductives/NestedOrderK.lean`).  A
CYCLE is a positive DECLINE, and it cannot fire on a stream official
accepts — §M.22 records that kinding excludes the cycles.

**`st` is the RE-MINTED state** (§M.21 (A), K.8): `elimNested` produces
`st₀`, whose copies' types are the container's stored types at RAW pin
components — the export carries no binder datum, so every stream binder
arrives as the parse placeholder and the annotation pass rewrites the
data inside them.  `nestedRemint` annotates the components first, at the
pre-block environment plus the block's formers, and re-mints every
copy's type from the container's stored ANNOTATED type at the ANNOTATED
components with the first former's ANNOTATED parameter binders (premise
B).  A copy's type is therefore annotated throughout, and every later
conjunct is about `st`, the re-minted state; the pins, their order and
the copies' constructors are `st₀`'s untouched.

**`pinsClosed`** is the pins' SCOPE, the pair of Bool tests `ConstWF`
demands of a nested RULE's stored pins: abstracted over the block's
parameters, every pin is free of free variables and has its loose bound
variables within the parameter telescope.  Nothing else certifies it —
`annotateBody` certifies only that each `.fvar` it REACHES carries an
index below the depth, it never descends into an fvar's type annotation
and never compares it with the opener's, and it passes `.bvar`
through — and a pin's components appear in no other term the route
checks.  It narrows only where official rejects too: the elimination's
local-variable rule already refuses a pin holding a field variable, the
stream's own terms carry no free variable, and `abstractRange`
introduces a loose bound variable only at an abstracted parameter.

**`pinsOkAux`** is one of the two conjuncts the model lane asked for:
post-check (a) is run a SECOND time, at the SCRATCH environment
`envAux` where the auxiliary block is installed, because both fold
spellings need the pins `Ds` to fit the container's parameter telescope
THERE, and the run at the restored environment is about an environment
whose model is what is being built.  It is ADDED, never substituted, so
the accept set can only narrow; and the two runs agree on everything a
pin can MENTION — a pin is a sub-term of a constructor's field domain,
and `checkMutualCtor` resolves those at the environment holding the
pre-block constants and the block's FORMERS (never its constructors),
which both environments hold identically.  The one thing the restore
respells that a pin could reach is a projection TABLE's bodies, through
a `.proj T i` node; running both is what makes that case checked rather
than assumed.

**`copiesFresh`** is the other conjunct the model lane asked for: every name
the elimination MINTS — each copy's type, its constructors and its
recursor — is free in the PRE-BLOCK environment, so the scratch
environment's cons shadows nothing and every constant the restore
stores is the block's own.  The copies' TYPE names cannot collide in
the first place (`mkUniqueName` is official's `mk_unique_name` and
skips a taken one); what the check catches is a constructor or a
recursor name, which official refuses at `declare_inductive_types`'
`check_name`.

**What the model tier consumes.**  Every intermediate environment is
written out as an application of the pure cons/store functions
(`consNestedFormers`, `consNestedCtors`, `provisionNestedRecs`,
`storeNestedRecs`), so the lane can compute with them; the auxiliary
half is `checkMutualCore … = .ok envAux`, from which #278's
`checkMutualCore_inv` gives the whole mutual chain and hence the
simultaneous least fixed point the copies and the members share.  The
restore is the constant replacement `restoreNested` and nothing else:
the stored VALUES are the auxiliary block's, only their TYPES (and the
rule right-hand sides and the projection bodies) are respelled.

**Not on the dispatch yet.**  The fold still sends a nested block to
the modelled route; this relation is the interface the model lane's
`declNested` will be stated over, and the dispatch gains its fourth arm
when that lands.  Two things are owed at that point and are NOT here:
the η half (`declNestedRun_etaClosed` — the formers carry the
capability record the AUXILIARY install stored, which
`consMutualFormers` sets to `{}`, so the lemma is a fact about
`checkMutualCore`'s output environment and belongs with the wiring),
and the `FEnv` twins with their cached mirror.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo RecRule
  NestedParts MutualBlock AuxType AuxStored ElimState fueledOps)

/-! ## The run relation -/

/-- **The nested declaration, as checked**: the stage runs of
`checkNested`.  `env` is the pre-block environment. -/
def DeclNestedRun (μ : CheckMode) (F : Nat) (env : Env)
    (p : NestedParts) (envOut : Env) : Prop :=

  (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
    (p.ctors.map (fun c => c.cv.type)).all
      (fun t => !t.mentionsNestedAux)) = true ∧
  uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
    (p.ctors.map (fun c => c.cv.type)) = true ∧
  ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
    (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (cvRms cvRns : List ConstantVal)
    (rulesM rulesN : List (List RecRule))
    (st₀ : ElimState) (a₀ : AuxStored) (fvsA : List Expr × Expr) (order : List Nat),
    -- the elimination, and the mimic count against the stream's records
    elimNested env p.nP p.lps
      (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun c => c.member == mIdx)).map
            fun c => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st₀ ∧
    -- the copies' types RE-MINTED at annotated pin components (§M.21 (A))
    nestedRemint (m := CheckM) (fueledOps μ F) env p st₀ = .ok st ∧
    st.pins.length = p.numNested ∧
    -- every MINTED name is free in the pre-block environment
    ConLeche.copiesFresh env p.k st = true ∧
    -- the copies' REFERENCE RELATION, topologically sorted: the order
    -- the model's forward fold recurses along (DESIGN §M.22)
    nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
    -- the auxiliary mutual block, checked in a SCRATCH environment
    auxBlock p st = some b ∧
    checkMutualCore (m := CheckM) (fueledOps μ F) env b none = .ok envAux ∧
    auxStoredAll envAux b b.k = some stored ∧
    -- `pinsOkAux`: the pins typed at the SCRATCH environment
    (stored.take p.k).head? = some a₀ ∧
    openPisAtFvars p.nP a₀.cvTa.type 0 = some fvsA ∧
    -- `pinsClosed`: every pin, abstracted over the parameters, is
    -- fvar-free with its loose bvars inside the telescope
    pinsClosed p.nP st.pins = true ∧
    nestedPinsOk (m := CheckM) (fueledOps μ F) envAux p.nP fvsA.1 st.pins = .ok () ∧
    -- the restored constructors, at the environment holding the formers
    (stored.take p.k).mapM (fun a =>
        restoreCtors (m := CheckM) (fueledOps μ F)
          (consNestedFormers (stored.take p.k) env) (restoreTbl p st) p.lps a.ctors)
      = .ok ctorsR ∧
    -- the restored recursor types
    restoreRecTys (m := CheckM) (fueledOps μ F)
        (consNestedCtors ctorsR.flatten
          (consNestedFormers (stored.take p.k) env))
        (restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms ∧
    restoreRecTys (m := CheckM) (fueledOps μ F)
        (consNestedCtors ctorsR.flatten
          (consNestedFormers (stored.take p.k) env))
        (restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName)
        (stored.drop p.k) = .ok cvRns ∧
    -- the restored rules, at the rule-less provision
    (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        restoreRules (m := CheckM) (fueledOps μ F)
          (provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env)))
          (restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
      = .ok rulesM ∧
    (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        restoreRules (m := CheckM) (fueledOps μ F)
          (provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env)))
          (restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
      = .ok rulesN ∧
    -- the projection tables, on the stored recursors
    nestedTables (m := CheckM)
        (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
          ((p.formers.getD mIdx default).1.name, a.tbl, cs))
        (storeNestedRecs
          ((cvRms.zip ((stored.take p.k).zip rulesM)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
            ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))) = .ok envOut ∧
    -- POST-CHECK (a): the same pins at the RESTORED environment
    nestedPinsOk (m := CheckM) (fueledOps μ F) envOut p.nP fvsA.1 st.pins = .ok () ∧
    -- POST-CHECK (c): the stream's records against the generated ones
    (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true ∧
    nestedRecsOk (m := CheckM) (fueledOps μ F)
        (consNestedCtors ctorsR.flatten
          (consNestedFormers (stored.take p.k) env))
        p.nP b.k b.n
        ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
            (fun (((sr, cv), rs), mIdx) =>
              (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
          ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
            (fun (((sr, cv), rs), j) =>
              (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
      = .ok ()

/-- **The copies' order, as the four `TopoOrder` fields in one place**
(DESIGN K.6): what the run relation's `nestedTopoOrder … = .ok order`
conjunct gives the model tier's fold.  The relation is the kernel's
`Bool` one; the model lane turns it into its own `CopyRef` with one
decidability lemma (`Verify/Inductives/NestedOrderK.lean`'s header). -/
theorem topoFields_of {st : ConLeche.ElimState} {order : List Nat} {k : Nat}
    (h : ConLeche.nestedTopoOrder (ConLeche.ElimState.grp st) k st = .ok order) :
    order.Nodup ∧
    (∀ j, j < st.pins.length → j ∈ order) ∧
    (∀ j ∈ order, j < st.pins.length) ∧
    (∀ j j', j < st.pins.length → j' < st.pins.length →
      ConLeche.copyRefB (ConLeche.ElimState.grp st) k st j j' = true →
      j' ∈ order ∧ order.idxOf j' < order.idxOf j) :=
  ⟨ConLeche.nestedTopoOrder_nodup h, ConLeche.nestedTopoOrder_complete h,
    ConLeche.nestedTopoOrder_bounded h,
    fun _ _ hj hj' hR => ConLeche.nestedTopoOrder_ref h hj hj' hR⟩

/-- The bridge inversion: a successful nested install is a run. -/
theorem declNestedRun_of {μ : CheckMode} {F : Nat} {env envOut : Env} {p : NestedParts}
    (h : ConLeche.checkNested (m := ConLeche.CheckM) (fueledOps μ F) env p = .ok envOut) :
    DeclNestedRun μ F env p envOut :=
  ConLeche.checkNested_inv h

end ConLeche.Semantics
