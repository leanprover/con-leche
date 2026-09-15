module

public import ConLeche.Semantics.DeclIndRun
public import ConLeche.Verify.Inductives.MutualWF
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.Extend.Inversions

@[expose] public section

/-!
# `DeclMutualRun`: the mutual declaration relation (task #278)

The mutual arm of `checkDecl`'s `.indDecl` clause (`checkMutual`,
`ConLeche/Kernel/Inductives/MutualInstall.lean`), recorded as a run
relation exactly as `DeclNativeRun` records the fixpoint route's: the
recursor records' structural pin, the block's shape guards, the
formers' loop, the cross-member checks and the eliminator's level
shape, the constructors with their kinds, the constructors' conses,
the `k` recursor types, the rules at the rule-less provision, the
group store, and the structure-like members' projection tables.

The η half closes the file: every constant the mutual install stores
is fresh at the environment it is stored on, and the only FORMERS it
stores carry the block's capability record `{}` — whose `eta` is a
literal `false` — so no stored family claims η and the η-families
stay closed across the whole install (`declMutualRun_etaClosed`).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo RecRule
  MutualParts MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4
  RecFieldKind fueledOps EtaFamiliesClosed)

/-! ## The run relation -/

/-- **The mutual declaration, as checked**: the stage runs of
`checkMutual`.  `env` is the pre-block environment; `b` is the block
record the recogniser hands the install and `streamRecs` the stream's
recursor records in member order, compared with the generated ones at
the two recursor stages. -/
def DeclMutualRun (μ : CheckMode) (F : Nat) (env : Env)
    (p : MutualParts) (env₂ : Env) : Prop :=
  -- the recursor records' structural pin (thrown at the install: an
  -- exported recursor that is not the generated one is official's
  -- reject)
  p.recPinned = true ∧
  ∃ (b : MutualBlock) (streamRecs : Option (List (ConstantVal × List RecRule)))
    (env₁ : Env) (fms : List MutualFormerA) (f₀ : MutualFormerA)
    (tq₀ : List Expr × Expr) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (cvRas : List ConstantVal) (rulesOf : List (List (MutualCtor × Expr))),
    b = p.toBlock ∧
    streamRecs = some (p.members.map fun mb => (mb.cvR, mb.rules)) ∧
    -- stage 0: the block's shape, official's rejects
    b.blockNames.Nodup ∧
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true ∧
    b.ctors.all (fun c => c.member < b.k) = true ∧
    ConLeche.mutualCtorsGrouped b.ctors = true ∧
    -- stage 1: the formers at official's telescope, consed with `{}`
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (env₁, fms) ∧
    fms[0]? = some f₀ ∧
    -- stage 2: official's cross-member checks and the eliminator
    ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀ ∧
    ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (fueledOps μ F) env₁ b.nP f₀
      (tq₀.1.map Expr.fvarTypeD) fms = .ok () ∧
    b.large = f₀.s.isNeverZero ∧
    -- stage 3: the constructors, their kinds, and the conses
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ b fms
      (Level.isEquiv f₀.s .zero == some true) b.ctors = .ok (ctorsA, sortss) ∧
    ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds ∧
    ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true ∧
    -- stage 4: the recursor types, the rules at the rule-less
    -- provision, the group store
    ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4) ∧
    ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA env₁) b formers4 ctors4 streamRecs b.k
      = .ok cvRas ∧
    ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA env₁))
      b formers4 ctors4 streamRecs b.k = .ok rulesOf ∧
    -- stage 5: the projection tables of the structure-like members
    ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss fms.zipIdx
      (ConLeche.storeMutualRecs (ConLeche.consMutualCtors b.nP ctorsA env₁) b fms rulesOf
        cvRas.zipIdx (ConLeche.consMutualCtors b.nP ctorsA env₁)) = .ok env₂

/-- The bridge inversion: a successful mutual install is a run. -/
theorem declMutualRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env} {p : MutualParts}
    (h : ConLeche.checkMutual (m := ConLeche.CheckM) (fueledOps μ F) env p = .ok env₂) :
    DeclMutualRun μ F env p env₂ := by
  obtain ⟨hpin, hcore⟩ := ConLeche.checkMutual_inv h
  obtain ⟨h0, h1, h2, h3, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, hformers, hf₀, htq₀, hcross, hL, hctors, hkinds, hfo, hgd, hrectys,
    hrules, htbl⟩ := ConLeche.checkMutualCore_inv hcore
  exact ⟨hpin, p.toBlock, _, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, rfl, rfl, h0, h1, h2, h3, hformers, hf₀, htq₀, hcross, hL, hctors,
    hkinds, hfo, hgd, hrectys, hrules, htbl⟩

/-! ## The η half: a fresh extension by non-formers -/

/-- **A fresh extension of `env` by no η-capable former**: the
environment grows by constants whose names `env` does not carry, none
of which is a type former claiming η.  Every stage of the mutual
install performs one — the formers carry the block's capability record
`{}`, and constructors, recursors and projection tables are not
formers at all — and closure of the η families travels along it
(`EtaFamiliesClosed.ofFreshExt`). -/
def FreshEtaExt (env envOut : Env) : Prop :=
  ∃ new : List ConstantInfo, envOut.consts = new ++ env.consts ∧
    (∀ c ∈ new, env.find? c.name = none) ∧
    (∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → caps.eta = false)

/-- A name the extension does not find is not found below it either. -/
theorem find?_none_of_append {new : List ConstantInfo} {env envOut : Env} {n : Name}
    (hc : envOut.consts = new ++ env.consts) (h : envOut.find? n = none) :
    env.find? n = none := by
  rw [Env.find?, hc, List.find?_append] at h
  cases hn : List.find? (fun c => c.name == n) new with
  | none => rw [hn] at h; simpa [Env.find?] using h
  | some c => rw [hn] at h; exact nomatch h

/-- A lookup the extension does not answer from its own constants is
the base's. -/
theorem find?_append_of_new_none {new : List ConstantInfo} {env envOut : Env} {n : Name}
    (hc : envOut.consts = new ++ env.consts)
    (hn : List.find? (fun c => c.name == n) new = none) :
    envOut.find? n = env.find? n := by
  rw [Env.find?, hc, List.find?_append, hn]
  rfl

theorem FreshEtaExt.rfl' (env : Env) : FreshEtaExt env env :=
  ⟨[], by simp, by simp, by simp⟩

/-- One fresh cons of a non-η-former. -/
theorem FreshEtaExt.cons {env : Env} {c : ConstantInfo}
    (hfresh : env.find? c.name = none)
    (hnd : ∀ cv caps, c = .indInfo cv caps → caps.eta = false) :
    FreshEtaExt env ⟨c :: env.consts⟩ :=
  ⟨[c], rfl, by
    intro c' hc'
    obtain rfl := List.mem_singleton.mp hc'
    exact hfresh, by
    intro c' hc'
    obtain rfl := List.mem_singleton.mp hc'
    exact hnd⟩

theorem FreshEtaExt.trans {env env₁ env₂ : Env}
    (h₁ : FreshEtaExt env env₁) (h₂ : FreshEtaExt env₁ env₂) : FreshEtaExt env env₂ := by
  obtain ⟨new₁, hc₁, hf₁, hi₁⟩ := h₁
  obtain ⟨new₂, hc₂, hf₂, hi₂⟩ := h₂
  refine ⟨new₂ ++ new₁, by rw [hc₂, hc₁, List.append_assoc], ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact find?_none_of_append hc₁ (hf₂ c hc')
    · exact hf₁ c hc'
  · intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact hi₂ c hc'
    · exact hi₁ c hc'

/-- One fresh cons in front of a fresh extension. -/
theorem FreshEtaExt.consChain {env envOut : Env} {c : ConstantInfo}
    (hfresh : env.find? c.name = none)
    (hnd : ∀ cv caps, c = .indInfo cv caps → caps.eta = false)
    (hrest : FreshEtaExt ⟨c :: env.consts⟩ envOut) : FreshEtaExt env envOut :=
  (FreshEtaExt.cons hfresh hnd).trans hrest

/-- **Closure of the η families travels along a fresh extension**: a
family found in the extension is an old one (the new constants are
never η-capable formers), and its constructor is still found where the
old environment found it (the new names are fresh). -/
theorem EtaFamiliesClosed.ofFreshExt {env envOut : Env}
    (hE : EtaFamiliesClosed env) (hx : FreshEtaExt env envOut) :
    EtaFamiliesClosed envOut := by
  obtain ⟨new, hc, hf, hi⟩ := hx
  intro T cvT caps hfind he hr
  -- the family is an old one
  have hnew : List.find? (fun c => c.name == T) new = none := by
    cases hn : List.find? (fun c => c.name == T) new with
    | none => rfl
    | some c =>
      exfalso
      have hmem : c ∈ new := List.mem_of_find?_eq_some hn
      have hT : envOut.find? T = some c := by
        rw [Env.find?, hc, List.find?_append, hn]; rfl
      rw [hT] at hfind
      obtain rfl := Option.some.inj hfind
      rw [hi _ hmem cvT caps rfl] at he
      exact nomatch he
  rw [find?_append_of_new_none hc hnew] at hfind
  obtain ⟨cvC, hfC⟩ := hE T cvT caps hfind he hr
  refine ⟨cvC, ?_⟩
  have hnewC : List.find? (fun c => c.name == caps.etaCtor) new = none := by
    cases hn : List.find? (fun c => c.name == caps.etaCtor) new with
    | none => rfl
    | some c =>
      exfalso
      have hmem : c ∈ new := List.mem_of_find?_eq_some hn
      have hname : c.name = caps.etaCtor := by
        have hh := List.find?_eq_some_iff_getElem.mp hn
        simpa using hh.1
      have hfn := hf c hmem
      rw [hname, hfC] at hfn
      exact nomatch hfn
  rw [find?_append_of_new_none hc hnewC]
  exact hfC

/-! ## The stages are fresh extensions -/

variable {μ : CheckMode}

/-- The formers' conses, read off. -/
theorem consMutualFormers_consts :
    ∀ {fms : List MutualFormerA} {env : Env},
      (ConLeche.consMutualFormers fms env).consts
        = (fms.map (fun f => ConstantInfo.indInfo f.cvTa {})).reverse ++ env.consts
  | [], env => by simp [ConLeche.consMutualFormers]
  | f :: fs, env => by
    simp only [ConLeche.consMutualFormers, List.map_cons, List.reverse_cons]
    rw [consMutualFormers_consts]
    simp

/-- Stage 1: the formers' conses, all of names fresh at the PRE-BLOCK
environment (where each was checked) and all carrying the block's
capability record `{}`. -/
theorem consMutualFormers_freshExt {fms : List MutualFormerA} {env : Env}
    (hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none) :
    FreshEtaExt env (ConLeche.consMutualFormers fms env) := by
  refine ⟨_, consMutualFormers_consts, ?_, ?_⟩
  · intro ci hci
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨f, hf, rfl⟩ := hci
    exact hfresh f hf
  · intro ci hci cv caps heq
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨f, hf, rfl⟩ := hci
    obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
    rfl

/-- Stage 1: the formers, each checked at the pre-block environment
and consed with `{}`. -/
theorem mutualFormers_freshExt {F nP : Nat} {l : List (ConstantVal × Nat)}
    {env env' : Env} {fms : List MutualFormerA}
    (h : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) nP l env
      = .ok (env', fms)) :
    FreshEtaExt env env' := by
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv h
  refine consMutualFormers_freshExt (fun f hf => ?_)
  obtain ⟨cv', hccv'⟩ := ConLeche.mutualFormerChecks_checked hchecks f hf
  obtain ⟨hfresh, -, -, -, -, -, _, _, _, -, -, -, -, -, hTeq⟩ :=
    ConLeche.checkConstantVal_inv hccv'
  show env.find? f.cvTa.name = none
  rw [hTeq]; exact hfresh

/-- Stage 3: the constructors' conses. -/
theorem consMutualCtors_consts {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (ConLeche.consMutualCtors nP ctorsA env).consts
        = (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 nP c.2)).reverse ++ env.consts
  | [], env => by simp [ConLeche.consMutualCtors]
  | c :: cs, env => by
    simp only [ConLeche.consMutualCtors, List.map_cons, List.reverse_cons]
    rw [consMutualCtors_consts]
    simp

theorem consMutualCtors_freshExt {nP : Nat} {ctorsA : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ c ∈ ctorsA, env.find? c.1.name = none) :
    FreshEtaExt env (ConLeche.consMutualCtors nP ctorsA env) := by
  refine ⟨_, consMutualCtors_consts, ?_, ?_⟩
  · intro ci hci
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨c, hc, rfl⟩ := hci
    exact hfresh c hc
  · intro ci hci cv caps heq
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨c, hc, rfl⟩ := hci
    exact nomatch heq

/-- Stage 4: the recursors' group store. -/
theorem storeMutualRecs_consts {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env},
      (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).consts
        = (l.map (fun q => ConstantInfo.recInfo q.1
            (b.rulePrefix + (fms.getD q.2 default).nIdx) b.rulePrefix
            (ConLeche.mutualRules env₂.find? q.1.name b.nP
              (b.rulePrefix + (fms.getD q.2 default).nIdx) b.rulePrefix q.1.type
              (rulesOf.getD q.2 [])))).reverse ++ env.consts
  | [], env => by simp [ConLeche.storeMutualRecs]
  | (cvRa, mIdx) :: rest, env => by
    simp only [ConLeche.storeMutualRecs, List.map_cons, List.reverse_cons]
    rw [storeMutualRecs_consts]
    simp

theorem storeMutualRecs_freshExt {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {l : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ q ∈ l, env.find? (Prod.fst q).name = none) :
    FreshEtaExt env (ConLeche.storeMutualRecs env₂ b fms rulesOf l env) := by
  refine ⟨_, storeMutualRecs_consts, ?_, ?_⟩
  · intro ci hci
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨q, hq, rfl⟩ := hci
    exact hfresh q hq
  · intro ci hci cv caps heq
    simp only [List.mem_reverse, List.mem_map] at hci
    obtain ⟨q, hq, rfl⟩ := hci
    exact nomatch heq

/-- Stage 5: one member's projection table. -/
theorem mutualMemberTable_freshExt {b : MutualBlock} {f : MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {mIdx : Nat}
    {env env' : Env}
    (h : ConLeche.mutualMemberTable (m := ConLeche.CheckM) b f ctorsA sortss mIdx env
      = .ok env') : FreshEtaExt env env' := by
  rcases ConLeche.mutualMemberTable_inv h with rfl | ⟨J, c, -, -, htbl⟩
  · exact FreshEtaExt.rfl' _
  · obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
    exact FreshEtaExt.cons hfresh (fun _ _ heq => nomatch heq)

/-- Stage 5 over the members. -/
theorem mutualTables_freshExt {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ {l : List (MutualFormerA × Nat)} {env env' : Env},
      ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss l env = .ok env' →
      FreshEtaExt env env'
  | [], env, env', h => by
    obtain rfl := ConLeche.mutualTables_nil_inv h
    exact FreshEtaExt.rfl' _
  | (f, mIdx) :: rest, env, env', h => by
    obtain ⟨envI, hI, hrest⟩ := ConLeche.mutualTables_inv h
    exact (mutualMemberTable_freshExt hI).trans (mutualTables_freshExt hrest)

/-! ## The freshness facts the stages leave -/

/-- Every annotated constructor's name is fresh at the formers'
environment (its own constant check's duplicate guard). -/
theorem checkMutualCtors_fresh {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp : Bool} {F : Nat} {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (h : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) env b fms isProp cs
      = .ok (ctorsA, sortss)) :
    ∀ c ∈ ctorsA, env.find? c.1.name = none := by
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkMutualCtors_inv h
  intro c hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hj' : j < cs.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, _, -, hrun⟩ := hall j cs[j] c (List.getElem?_eq_getElem hj') hj
  obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
  obtain ⟨hfresh, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
    ConLeche.checkConstantVal_inv hccv
  rw [hCeq]
  exact hfresh

/-- Every generated recursor's name is fresh at the constructors'
environment: the stream's record carries that very name (the
structural pin, thrown at the install) and its own constant check
found nothing there. -/
theorem checkMutualRecTys_fresh {env : Env} {p : MutualParts} {F : Nat}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {cvRas : List ConstantVal}
    (hpin : ConLeche.mutualRecPinOk p = true)
    (h : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F) env p.toBlock
      formers4 ctors4 (some (p.members.map fun mb => (mb.cvR, mb.rules))) p.toBlock.k
      = .ok cvRas) :
    ∀ q ∈ cvRas.zipIdx, env.find? (Prod.fst q).name = none := by
  obtain ⟨hlen, hall⟩ := ConLeche.checkMutualRecTys_inv h
  intro q hq
  obtain ⟨cvRa, mIdx⟩ := q
  have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hq
  have hlt : mIdx < p.toBlock.k := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    omega
  have hltk : mIdx < p.k := by
    simpa [MutualBlock.k, MutualParts.toBlock, MutualParts.k] using hlt
  obtain ⟨cvRa', hget', hrec⟩ := hall mIdx hlt
  obtain rfl := Option.some.inj (hget.symm.trans hget')
  -- the stream's record at this member
  obtain ⟨mb, hmb⟩ : ∃ mb, p.members[mIdx]? = some mb := by
    have : mIdx < p.members.length := by simpa [MutualParts.k] using hltk
    exact ⟨p.members[mIdx], List.getElem?_eq_getElem this⟩
  have hsr : (some (p.members.map fun mb => (mb.cvR, mb.rules))).bind
      (fun rs => (rs[mIdx]?).map (·.1)) = some mb.cvR := by
    simp only [Option.bind_some]
    rw [List.getElem?_map, hmb]
    rfl
  rw [hsr] at hrec
  obtain ⟨recTy, sty, u, -, -, -, -, -, -, -, hcmp, rfl⟩ :=
    ConLeche.checkMutualRecTy_shape hrec
  obtain ⟨cvRi, hccv, -⟩ := hcmp mb.cvR rfl
  obtain ⟨hfresh, -, -, -, -, -, _, _, _, -, -, -, -, -, -⟩ :=
    ConLeche.checkConstantVal_inv hccv
  show env.find? (p.toBlock.recName mIdx) = none
  rw [ConLeche.MutualParts.toBlock_recName hmb,
    ← ConLeche.mutualRecPinOk_name (p := p) hpin hltk hmb]
  exact hfresh

/-! ## The mutual arm keeps the η-families closed -/

/-- **The mutual arm keeps the η-families closed**: every stored
former carries the block's capability record `{}` — whose `eta` is a
literal `false` — and the constructors, recursors and projection
tables are not formers, so the whole install is a fresh extension by
non-formers. -/
theorem declMutualRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : MutualParts} (hpinOk : ConLeche.mutualRecPinOk p = true)
    (hE : EtaFamiliesClosed env)
    (h : DeclMutualRun μ F env p env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨-, b, streamRecs, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, rfl, rfl, -, -, -, -, hformers, -, -, -, -, hctors, -, -, -, hrectys,
    -, htbl⟩ := h
  have hx1 : FreshEtaExt env env₁ := mutualFormers_freshExt hformers
  have hx2 : FreshEtaExt env₁ (ConLeche.consMutualCtors p.toBlock.nP ctorsA env₁) :=
    consMutualCtors_freshExt (nP := p.toBlock.nP) (checkMutualCtors_fresh hctors)
  have hx3 := storeMutualRecs_freshExt (env₂ := ConLeche.consMutualCtors p.toBlock.nP ctorsA env₁)
    (b := p.toBlock) (fms := fms) (rulesOf := rulesOf)
    (checkMutualRecTys_fresh hpinOk hrectys)
  exact EtaFamiliesClosed.ofFreshExt hE
    (hx1.trans (hx2.trans (hx3.trans (mutualTables_freshExt htbl))))

end ConLeche.Semantics
