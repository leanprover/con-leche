module

public import ConLeche.Verify.Inductives.NestedInv

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

**`copiesFresh`** is the conjunct the model lane asked for: every name
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
    (a₀ : AuxStored) (fvsA : List Expr × Expr),
    -- the elimination, and the mimic count against the stream's records
    elimNested env p.nP p.lps
      (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
        (⟨cv.name, cv.type,
          (p.ctors.filter (fun c => c.member == mIdx)).map
            fun c => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st ∧
    st.pins.length = p.numNested ∧
    -- every MINTED name is free in the pre-block environment
    ConLeche.copiesFresh env p.k st = true ∧
    -- the auxiliary mutual block, checked in a SCRATCH environment
    auxBlock p st = some b ∧
    checkMutualCore (m := CheckM) (fueledOps μ F) env b none = .ok envAux ∧
    auxStoredAll envAux b b.k = some stored ∧
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
    -- POST-CHECK (a): the pins, typed at the parameter context
    (stored.take p.k).head? = some a₀ ∧
    openPisAtFvars p.nP a₀.cvTa.type 0 = some fvsA ∧
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

/-- The bridge inversion: a successful nested install is a run. -/
theorem declNestedRun_of {μ : CheckMode} {F : Nat} {env envOut : Env} {p : NestedParts}
    (h : ConLeche.checkNested (m := ConLeche.CheckM) (fueledOps μ F) env p = .ok envOut) :
    DeclNestedRun μ F env p envOut :=
  ConLeche.checkNested_inv h

end ConLeche.Semantics
