module

public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedOrderK

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

**THE ELIMINATION'S INPUTS ARE ANNOTATED** (K.12), which is why there is
ONE state here and no re-mint.  `nestedAnnotFormers` puts every former
through `checkConstantVal` and `checkSumTele` at the pre-block
environment — the constant the scratch install will store — and
`nestedAnnotCtors` puts every constructor through `checkConstantVal` at
`nestedFormerEnv fmsA env`, the environment holding those formers, which
is where `checkMutualCtor`'s front door runs.  `elimNested` is run on
those (`nestedTypes0 p fmsA ctorsA`), so it reads its parameter openers
and binders off the FIRST FORMER'S STORED type, instantiates the
containers' stored (annotated) types at ANNOTATED components, and
rewrites `J Ds is ↦ auxJ p⃗ is` — an application with no binders of its
own.  Every copy's TYPE and every copy's CONSTRUCTORS are therefore
annotated by construction, the pins are annotated, and nothing is
re-annotated afterwards: `nestedRemint`, the `st₀`/`st` pair and the
`pinsA` list are gone.

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

**The pins the two passes check are ONE object** (K.10, simplified by
K.12).  Both `nestedPinsOk` runs take `st.pins` itself: a pin is the
elimination's own term — annotated, and already opened at the block's
parameter variables — so neither pass annotates or instantiates
anything.  They VALIDATE the term by inference, the way
`checkConstantValPre` validates a pre-annotated declaration, and the
pin in the recorded equation and the pin the checks type are literally
the same term.

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

**The stored types are the MINTED types, by construction** (K.10,
widened by K.12).  `Verify/Inductives/NestedInv.lean`'s
`nestedCopyFormerType_eq` takes this relation's `auxBlock p st = some b`
and `checkMutualCore … b none true = .ok envAux` conjuncts and returns,
for EVERY member of the block — no `_nested`-prefix side condition — the
formers stage's own `f.cvTa.type = t.type` at that position, with
`env₁ = consMutualFormers fms env`, so the STORED former type is the
minted one, syntactically.  The `auxRoute` grade is what makes this a
definitional chain rather than an annotation-stability hypothesis:
`checkConstantValPre` runs every check and returns its input, and
`checkSumTele` keeps a telescope that already ends in a sort.

The CONSTRUCTOR side has its twin, `nestedCopyCtorType_eq`: the
constructors' stage stores `normCtorValM`'s output ON THE MINTED
CONSTANT — the positivity normalisation, no annotation walk — which is
the minted constant itself wherever that normalisation changes nothing.
The `whnf` behind it stays: at a λ-pin (`DMap α (fun _ => PT α)`) the
copied field is the redex `(fun _ => PT α) k`, whose head is a `.lam`,
and `mutualPositivity` reads no member application there; official
`whnf`s in the same place.

**`.proj` nodes on the graded path** (K.13).  The annotation walk is
what validates a `.proj` node's structure-name slot (task #271), and the
graded path skips the walk — so `checkConstantValPre` asks the same
condition itself: every `.proj sn i e` in the checked type has a
projection-table entry AT ITS OWN NAME and index
(`Expr.projTablesOk`).  It narrows nothing (a node the walk accepted
satisfies it), and `checkConstantValPre_projOk` hands the fact to the
model tier — `nestedCopyCtorType_eq` carries it for every STORED
constructor of the block, which is what discharges a `CtorsNoProj`-style
hypothesis at grade `true`.

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
    (fmsA ctorsA : List ConstantVal) (order : List Nat),
    -- THE INPUTS, ANNOTATED (K.12): the formers as the install will store
    -- them, the constructors at the environment holding those formers
    ConLeche.nestedAnnotFormers (m := CheckM) (fueledOps μ F) env p.nP p.formers = .ok fmsA ∧
    ConLeche.nestedAnnotCtors (m := CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA ∧
    -- the elimination on those, and the mimic count against the stream's
    -- records
    elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st ∧
    st.pins.length = p.numNested ∧
    -- every MINTED name is free in the pre-block environment
    ConLeche.copiesFresh env p.k st = true ∧
    -- the CONTAINERS' facts (K.14): uniform occurrences of the group in
    -- the stored constructors, and the two recursor facts at every member
    ConLeche.nestedContainersOk env st.pins = true ∧
    -- the copies' REFERENCE RELATION, topologically sorted: the order
    -- the model's forward fold recurses along (DESIGN §M.22)
    nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
    -- the auxiliary mutual block, checked in a SCRATCH environment
    auxBlock p st = some b ∧
    checkMutualCore (m := CheckM) (fueledOps μ F) env b none true = .ok envAux ∧
    auxStoredAll envAux b b.k = some stored ∧
    -- `pinsClosed`: every pin, abstracted over the parameters, is
    -- fvar-free with its loose bvars inside the telescope
    pinsClosed p.nP st.pins = true ∧
    -- `pinsOkAux`: the pins — the elimination's own, annotated terms
    -- opened at the block's parameter variables — typed at the SCRATCH
    -- environment
    nestedPinsOk (m := CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () ∧
    -- THE WHNF WITNESS (K.17): at every constructor of the auxiliary
    -- block, the STORED field is the weak head normal form of the
    -- PROCESSED one wherever the stage's normalisation changed it
    ConLeche.nestedCtorsWhnfOk (m := CheckM) (fueledOps μ F)
        (consNestedFormers (stored.take p.k) env) (restoreTbl p st) p.nP
        (ConLeche.nestedCtorPairs b stored) = .ok () ∧
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
    nestedPinsOk (m := CheckM) (fueledOps μ F) envOut p.nP st.pins = .ok () ∧
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
