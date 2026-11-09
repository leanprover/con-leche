module

public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Semantics.Inductives.DeclBlockWF
public import ConLeche.Cached.Decls
import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.InstLevels
import ConLeche.Verify.PinRen

@[expose] public section

/-!
# The declaration fold keeps the environment well formed, model-free

`EnvWF` (`Verify/EnvWF.lean`) of every environment the checker accepts, off the run record alone
(task #521): every stored constant is closed, its level parameters are declared, the constants it
mentions are stored, and every stored projection table is well formed.  The step is
`declWFStepRun`, which reads the kinds' guards (`ConstantValRun`, `ValueFrontRun`, the quotient
record's predecessors) and, at an inductive block, `blockRun_envWF`
(`Semantics/Inductives/DeclBlockWF.lean`).

The letters: one accepted declaration (`checkDecl_envWF`), the pure fold (`checkDeclsPure_envWF`)
and the fold the binary returns the accept of (`checkDecls_envWF`).

This module is model-free by construction: no `V`, no `SetTheory`, nothing of `Model/*`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify ConLeche.Cached

/-! ## The constants a value kind stores -/

/-- **A constant stored by its checked type alone** (an axiom, an opaque constant, a theorem): its
type's guards are `ConstantValRun`'s. -/
theorem ConstantValRun.envWF_cons {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (henv : EnvWF env) (hcv : ConstantValRun F env cv type') {c : ConstantInfo}
    (hc : c.toConstantVal = ⟨cv.name, cv.levelParams, type'⟩)
    (hnd : ∀ cv' v h, c ≠ .defnInfo cv' v h) (hnr : ∀ cv' mI rP isK rules, c ≠ .recInfo cv' mI rP isK rules) :
    EnvWF ⟨c :: env.consts, env.tables⟩ := by
  obtain ⟨-, -, hlbt, hitf, hann, htp, htr, -, hshape⟩ := hcv
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  refine EnvWF.cons (hshape _ (by rw [hc, hann])) henv ?_
  refine ⟨?_, ?_, ?_, ?_, fun cv' v h heq => absurd heq (hnd cv' v h),
    fun cv' mI rP isK rules heq => absurd heq (hnr cv' mI rP isK rules)⟩ <;> rw [hc]
  · exact htf'
  · exact htp
  · exact Expr.constsResolve_mono htr
  · exact hbt'

/-- **An axiom's or an opaque constant's record**, stored as an axiom. -/
theorem ConstantValRun.envWF_axiom {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (henv : EnvWF env) (hcv : ConstantValRun F env cv type') :
    EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ :=
  hcv.envWF_cons henv rfl (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq)

/-- **A theorem's record**, stored by its statement. -/
theorem ConstantValRun.envWF_thm {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (henv : EnvWF env) (hcv : ConstantValRun F env cv type') :
    EnvWF ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ :=
  hcv.envWF_cons henv rfl (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq)

/-- **A definition's record**: its type's guards are `ConstantValRun`'s, its value's
`ValueFrontRun`'s. -/
theorem ConstantValRun.envWF_defn {F : Nat} {env : Env} {cv : ConstantVal} {value : Expr}
    {type' value' : Expr} (hint : ReducibilityHint)
    (henv : EnvWF env) (hcv : ConstantValRun F env cv type')
    (hv : ValueFrontRun F env cv value type' value') :
    EnvWF ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint :: env.consts, env.tables⟩ := by
  obtain ⟨-, -, hlbt, hitf, hann, htp, htr, -, hshape⟩ := hcv
  obtain ⟨htf', hbt'⟩ := stored_syntax hann hitf hlbt
  obtain ⟨hlbv, hivf, hvann, hvp, hvr, -⟩ := hv
  obtain ⟨hvf', hbv'⟩ := stored_syntax hvann hivf hlbv
  refine EnvWF.cons (hshape _ (by rw [hann]; rfl)) henv ⟨htf', htp,
    Expr.constsResolve_mono htr, hbt', fun _ _ _ heq => ?_, fun _ _ _ _ _ heq => nomatch heq⟩
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
  exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩

/-! ## The quotient package's records

A quotient record stores its slot's pin at the record's level-parameter names (`quotAt`).  The
pin's own facts are computed (`decide`); what its type and its rules mention is stored before it
(`quotPredsOk`) or is the record itself.  Resolution reads only which names are stored, so the pin's
is decided at a stub environment holding exactly those names (`quotStub`) and carried over. -/

/-- The names a quotient slot's pin mentions, its own among them. -/
def quotNeeds (k : QuotKind) : List Name :=
  (quotPin k).name :: match k with
    | .type => [eqName]
    | .ctor => [quotName]
    | .lift | .sound => [eqName, quotName, quotMkName]
    | .ind => [quotName, quotMkName]

/-- A stub environment storing exactly `quotNeeds k`. -/
def quotStub (k : QuotKind) : Env :=
  ⟨(quotNeeds k).map fun n => .axiomInfo ⟨n, [], .sort .zero⟩, []⟩

/-- The stub stores only the needed names. -/
theorem quotStub_find {k : QuotKind} {n : Name} (h : ((quotStub k).find? n).isSome = true) :
    n ∈ quotNeeds k := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have hn := Env.find?_name hc
  have hm := Env.find?_mem hc
  simp only [quotStub, List.mem_map] at hm
  obtain ⟨n', hn', rfl⟩ := hm
  rw [← hn]
  exact hn'

/-- A constant that is not a definition, as a test. -/
def notDefnB : ConstantInfo → Bool
  | .defnInfo .. => false
  | _ => true

/-- A firing that is not `.nested`, as a test. -/
def fireNotNestedB : RecRuleFire → Bool
  | .nested _ _ => false
  | _ => true

/-- A recursor's rules' right-hand sides closed, at its level parameters, resolving at `E₀`,
bounded, and none firing `.nested`, as a test (true at any other kind of constant). -/
def recRulesOkB (E₀ : Env) : ConstantInfo → Bool
  | .recInfo cv _ _ _ rules => rules.all fun r =>
    !r.rhs.hasFvar && r.rhs.allLevelParamsDefined cv.levelParams && r.rhs.constsResolve E₀ &&
      r.rhs.looseBVarsBounded 0 && fireNotNestedB r.fire
  | _ => true

/-- **A copy of a constant at other level-parameter names keeps its well-formedness**, read at
any environment storing what the original's resolution needs (`hdom`). -/
theorem constWF_atLps {E E₀ : Env}
    (hdom : ∀ n, (E₀.find? n).isSome = true → (E.find? n).isSome = true)
    {pin : ConstantInfo} {ps : List Name}
    (hl : pin.toConstantVal.levelParams.length = ps.length)
    (h1 : pin.toConstantVal.type.hasFvar = false)
    (h2 : pin.toConstantVal.type.allLevelParamsDefined pin.toConstantVal.levelParams = true)
    (h3 : pin.toConstantVal.type.constsResolve E₀ = true)
    (h4 : pin.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : notDefnB pin = true) (h6 : recRulesOkB E₀ pin = true) :
    ConstWF E (pin.atLps ps) := by
  have htype : (pin.atLps ps).toConstantVal.type = pin.toConstantVal.type.instantiateLevelParams
      pin.toConstantVal.levelParams (ps.map Level.param) := by rw [atLps_cv]; rfl
  have hlps : (pin.atLps ps).toConstantVal.levelParams = ps := by rw [atLps_cv]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htype, Expr.hasFvar_instantiateLevelParams]; exact h1
  · rw [htype, hlps]; exact expr_defined_ren hl _ h2
  · rw [htype, Expr.constsResolve_instantiateLevelParams]; exact Expr.constsResolve_of_find hdom h3
  · rw [htype, Expr.looseBVarsBounded_instantiateLevelParams]; exact h4
  · intro cv v h heq
    cases pin with
    | defnInfo cvp vp hp => exact nomatch h5
    | _ => exact nomatch heq
  · intro cv mI rP isK rules heq r hr
    cases pin with
    | recInfo cvp a b c rs =>
      simp only [ConstantInfo.atLps] at heq
      injection heq with e0 e1 e2 e3 e4
      subst e0 e1 e2 e3 e4
      obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hr
      have hg := (List.all_eq_true.mp h6) rp hrp
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg
      obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := hg
      refine ⟨?_, expr_defined_ren hl _ g2, ?_, ?_, fun lvls pins hf => ?_⟩
      · show (rp.rhs.instantiateLevelParams _ _).hasFvar = false
        rw [Expr.hasFvar_instantiateLevelParams]; exact g1
      · show (rp.rhs.instantiateLevelParams _ _).constsResolve E = true
        rw [Expr.constsResolve_instantiateLevelParams]; exact Expr.constsResolve_of_find hdom g3
      · show (rp.rhs.instantiateLevelParams _ _).looseBVarsBounded 0 = true
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact g4
      · change RecRuleFire.atLps _ _ rp.fire = _ at hf
        cases hrf : rp.fire with
        | nested _ _ => rw [hrf] at g5; exact nomatch g5
        | _ => rw [hrf] at hf; exact nomatch hf
    | _ => exact nomatch heq

/-- **The pin's computed facts**: closed, bounded, resolving at the stub, not a definition, and
every rule's right-hand side alike, firing other than `.nested`. -/
theorem quotPin_facts (k : QuotKind) :
    (quotPin k).toConstantVal.type.hasFvar = false ∧
    (quotPin k).toConstantVal.type.allLevelParamsDefined
      (quotPin k).toConstantVal.levelParams = true ∧
    (quotPin k).toConstantVal.type.constsResolve (quotStub k) = true ∧
    (quotPin k).toConstantVal.type.looseBVarsBounded 0 = true ∧
    notDefnB (quotPin k) = true ∧ recRulesOkB (quotStub k) (quotPin k) = true := by
  cases k <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **A quotient record's install keeps well-formedness.** -/
theorem declQuotRun_envWF {env env₂ : Env} {k : QuotKind} {cv : ConstantVal}
    (henv : EnvWF env) (h : DeclQuotRun env k cv env₂) : EnvWF env₂ := by
  obtain ⟨hhit, hp, -, rfl⟩ := h
  simp only [quotPinHit, Bool.and_eq_true, beq_iff_eq] at hhit
  obtain ⟨⟨-, hlen⟩, -⟩ := hhit
  have hname : (quotAt k cv).name = (quotPin k).name := atLps_name _ _
  -- what the pin mentions is stored before it (`quotPredsOk`), or is the record itself
  have hpred : ∀ n ∈ quotNeeds k, n ≠ (quotPin k).name → (env.find? n).isSome = true := by
    intro n hn hne
    cases k <;> simp only [quotNeeds, List.mem_cons, List.not_mem_nil, or_false] at hn <;>
      simp only [quotPredsOk, Bool.and_eq_true] at hp <;>
      rcases hn with rfl | rfl | rfl | rfl <;> simp_all
  have hdom : ∀ n, ((quotStub k).find? n).isSome = true →
      (Env.find? ⟨quotAt k cv :: env.consts, env.tables⟩ n).isSome = true := by
    intro n hn
    rw [Env.find?_cons]
    by_cases hs : (quotAt k cv).name = n
    · rw [ite_eq_left hs]; rfl
    · rw [ite_eq_right hs]
      exact hpred n (quotStub_find hn) fun he => hs (hname.trans he.symm)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := quotPin_facts k
  have hshape : litShapeOk (quotAt k cv) = true :=
    litShapeOk_of_not_lit (by rw [hname]; cases k <;> decide)
  exact EnvWF.cons hshape henv
    (constWF_atLps hdom (by rw [hlen]) f1 f2 f3 f4 f5 f6)

/-! ## The step and the folds -/

/-- **The declaration fold's well-formedness step, on the run record.**  The inductive kind is
`DeclKindRun`'s `Ind` parameter, so its one premise is at whatever payload the caller instantiates
(`declRun_envWF` discharges it at `DeclIndRunDispatchK`). -/
theorem declWFStepRun {F : Nat}
    {Ind : List ConstantInfo → Nat → Env → Prop}
    {env : Env} {d : Declaration} {env₂ : Env}
    (hind : ∀ {block : List ConstantInfo} {nP : Nat} {envI : Env}, Ind block nP envI → EnvWF envI)
    (henv : EnvWF env)
    (h : DeclKindRun F Ind env d env₂) : EnvWF env₂ := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hv, rfl, -, -⟩ := h
    exact hcv.envWF_defn hint henv hv
  | thmDecl cv value =>
    obtain ⟨-, type', value', hcv, -, -, rfl⟩ := h
    exact hcv.envWF_thm henv
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', hcv, -, rfl, -⟩ := h
    exact hcv.envWF_axiom henv
  | axiomDecl cv =>
    rcases h with ⟨-, hq⟩ | ⟨-, type', -, hcv, harm⟩
    · exact declQuotRun_envWF henv hq
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
    · exact hcv.envWF_axiom henv
    · exact hcv.envWF_axiom henv
    · exact hcv.envWF_axiom henv
    · exact henv
  | quotDecl k cv => exact declQuotRun_envWF henv h
  | indDecl block nP => exact hind h

/-- **One declaration's run keeps well-formedness**, at the fold's dispatch. -/
theorem declRun_envWF {F : Nat} {env env₂ : Env} {d : Declaration} (henv : EnvWF env)
    (h : DeclRun F (DeclIndRunDispatchK F env) env d env₂) : EnvWF env₂ :=
  declWFStepRun (fun {block nP _} hI => by
    unfold DeclIndRunDispatchK at hI
    split at hI
    · exact blockRun_envWF henv hI
    · exact hI.elim) henv h.2

variable {pins : List NatOpPinSet}

/-- **An accepted declaration keeps the environment well formed.** -/
theorem checkDecl_envWF {F : Nat} {env env₂ : Env} {d : Declaration} (henv : EnvWF env)
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env₂) : EnvWF env₂ :=
  declRun_envWF henv (checkDeclRun_ofEnvFactsK h)

/-- The empty environment is well formed. -/
theorem EnvWF.empty : EnvWF Env.empty :=
  ⟨fun _ hc => (nomatch hc), fun _ hc => (nomatch hc), fun _ ht => (nomatch ht)⟩

/-- **The pure fold keeps the environment well formed**, from any well-formed start. -/
theorem foldlM_checkDecl_envWF {F : Nat} :
    ∀ (ds : List Declaration) {env env' : Env}, EnvWF env →
      ds.foldlM (checkDecl .verified (fueledOps .verified F) pins) env = .ok env' → EnvWF env'
  | [], _, _, henv, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ henv
  | d :: ds, env, _, henv, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl .verified (fueledOps .verified F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      exact foldlM_checkDecl_envWF ds (checkDecl_envWF henv hd) h

/-- **What the pure fold accepts is well formed.** -/
theorem checkDeclsPure_envWF {F : Nat} {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure .verified (fueledOps .verified F) pins ds = .ok env') : EnvWF env' :=
  foldlM_checkDecl_envWF ds EnvWF.empty h

/-- **The fold's run keeps the environment well formed**: each record's cached check is a pure
`checkDecl` run (`checkDeclStepC_run`, which itself reads the environment's well-formedness). -/
theorem declsRun_envWF {maxNatSize : Nat} {ds : List Declaration} {p q : Nat × FEnv}
    (hrun : DeclsRun .verified pins maxNatSize ds p q) :
    p.2 = mkFEnv p.2.env → EnvWF p.2.env → EnvWF q.2.env := by
  induction hrun with
  | nil p => exact fun _ hw => hw
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hw
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    rw [hfe] at hstepC
    obtain ⟨-, hfe₁, F, hF⟩ := checkDeclStepC_run hw (CSOKF.fresh _) hstepC
    exact ih hfe₁ (checkDecl_envWF hw hF)

/-- **What the fold the binary runs accepts is well formed** (`checkDecls`, the subject of the
main theorem), model-free. -/
theorem checkDecls_envWF {maxNatSize : Nat} {ds : Array Declaration} {env' : Env}
    (h : checkDecls .verified pins maxNatSize ds = .ok env') : EnvWF env' := by
  obtain ⟨n, fe, r, rfl⟩ := checkDecls_run .verified h
  exact declsRun_envWF r rfl EnvWF.empty

end ConLeche.Semantics
