module

public import Fragment.NestRead
public import Fragment.InstallScope

@[expose] public section

/-!
# Scope of an installed nested block

The syntactic half of installing a nested block, the twin of
`InstallScope.lean`: what the installed environment (`IndSpec.installN`,
`Decl.lean`) stores under each name, and that every stored term of it
is in scope of it (`Env.Scoped`, `InstallDef.lean`).

* **Lookups.**  `T.rec_1` is found under its name, then `T.rec`, the
  rest as in `envCtors` (`installN_find?`, `InstallScope.lean`); every
  stored name is found as before, the block's names being fresh.
* **Scope of the generated terms.**  The two recursors' types and the
  rules' right-hand sides use only the recursor's level parameters:
  the extras (two motives, the block's minors, the class's minors) are
  built from the block's specification, the class (over the block's
  parameters, `NestScoped`) and the container's constructors read in
  the block's terms (`classCtor`) — whose fields are in the block's
  scope because the container's are in the container's (`NestScoped`,
  last clauses) and the class's arguments in the block's.  A rule's
  right-hand side is closed and mentions only stored constants: its
  context is the rule type's, inferred in the empty context; its body
  mentions `T.rec` and `T.rec_1` (stored in `installN`), the
  specification's expressions and variables.
* **The installed environment is closed** (`Env.Scoped.installN`): the
  former and the constructors as for a plain block
  (`Env.Scoped.foldl_ctors`); then by cases on where a name is found —
  `T.rec_1`, `T.rec` (each rule's right-hand side in scope of the whole
  installed environment, since `T.rec`'s rules mention `T.rec_1` at a
  container field; a rule of `T.rec_1` fires on a constructor of the
  container, stored by `NestScoped`), or a constant stored before.
-/

namespace Fragment

namespace IndSpec

variable (S : IndSpec)

/-! ## Lookups in the installed nested environment -/

/-- The nested block's fresh names include the plain block's. -/
theorem fresh_of_freshN {env : Env} {N : NestInfo}
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none) :
    ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none := by
  intro m hm
  refine hfresh m ?_
  simp only [List.mem_cons] at hm ⊢
  rcases hm with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

/-- A stored name is found as before in the installed nested
environment, when the block's names are fresh. -/
theorem find?_mono_installN (N : NestInfo) (env : Env)
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none)
    {n : Name} {ci : ConstInfo} (h : env.find? n = some ci) :
    (S.installN N env).find? n = some ci := by
  have haux : n ≠ N.aux := by
    rintro rfl
    rw [hfresh N.aux (by simp)] at h
    cases h
  have hrec : n ≠ S.recName := by
    rintro rfl
    rw [hfresh S.recName (by simp)] at h
    cases h
  rw [installN_find?, if_neg haux, if_neg hrec]
  exact S.find?_mono_envCtors env (S.fresh_of_freshN hfresh) h

/-- A name stored with the former and the constructors stays stored in
the installed nested environment. -/
theorem isSome_find?_installN (N : NestInfo) (env : Env) {n : Name}
    (h : ((S.envCtors env).find? n).isSome) : ((S.installN N env).find? n).isSome := by
  unfold installN
  exact Env.isSome_find?_add (Env.isSome_find?_add h _ _) _ _

/-! ## The nested recursors' contexts -/

theorem oN_eq (N : NestInfo) : S.oN N = 2 + S.n + N.nK := rfl

/-- A nested rule's context holds the fields, the extras and the
parameters. -/
theorem length_ruleCtxN (N : NestInfo) (c : CtorSpec) :
    (S.ruleCtxN N c).length = c.fields.length + S.oN N + S.nP := by
  simp only [ruleCtxN, List.length_append, length_fieldCtxAt, length_extrasN]
  rfl

/-- An entry of the inductive hypotheses' context under `o` binders is
a hypothesis' type at a recursive position. -/
theorem mem_ihCtxAt {c : CtorSpec} {o : Nat} {A : Expr} (h : A ∈ S.ihCtxAt c o) :
    ∃ kf ∈ c.recFields, ∃ l, A = S.ihTy c.fields.length kf.1 l o kf.2 := by
  rw [ihCtxAt, List.mem_reverse, List.mem_mapIdx] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨_, List.getElem_mem hl, l, rfl⟩

/-- An entry of the block's minors' context (nested block) is a minor
premise of one of the block's constructors. -/
theorem mem_minorsCtxN {A : Expr} (h : A ∈ S.minorsCtxN) :
    ∃ j c, S.ctors[j]? = some c ∧ A = S.minorTyN c j := by
  rw [minorsCtxN, List.mem_reverse, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, S.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- An entry of the class's minors' context is a minor premise of one
of the container's constructors. -/
theorem mem_minorsCtxK (N : NestInfo) {A : Expr} (h : A ∈ S.minorsCtxK N) :
    ∃ j c, N.K.ctors[j]? = some c ∧ A = S.minorTyK N c j := by
  rw [minorsCtxK, List.mem_reverse, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, N.K.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- A rule of `T.rec` is one of the block's constructors'. -/
theorem mem_rulesN (N : NestInfo) {rl : RecRule} (h : rl ∈ S.rulesN N) :
    ∃ j c, S.ctors[j]? = some c ∧ rl = ⟨c.name, c.fields.length, S.ruleRhsN N c j, none⟩ := by
  rw [rulesN, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, S.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- A rule of `T.rec_1` is one of the container's constructors', with
its stored instantiation. -/
theorem mem_rules1 (N : NestInfo) {rl : RecRule} (h : rl ∈ S.rules1 N) :
    ∃ j c, N.K.ctors[j]? = some c ∧
      rl = ⟨c.name, c.fields.length, S.rule1Rhs N c j, some (N.lsK, S.classArgs N 0)⟩ := by
  rw [rules1, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, N.K.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-! ## Scope of the translated constructors -/

section Generated

variable {env : Env}

/-- **A recursive position of a translated constructor is in the
block's scope**: a member field became a recursive field (reflexive
with an empty telescope) at the member's index expressions (lifted
over the earlier fields), a recursive field of the container a
container field; an ordinary
field carries no hypothesis.  Needs nothing of the container's own
scope. -/
theorem classCtor_recField_scoped (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) {kf : Nat × Field}
    (h : kf ∈ (S.classCtor N c).recFields) :
    S.fieldScoped env kf.1 kf.2 ∧ kf.1 < (S.classCtor N c).fields.length := by
  have hNS := hS.2.2.2.2.2.2 N hN
  have hpos := hNS.2.2.2.2.2.2.2.2.1
  obtain ⟨k, f⟩ := kf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields h
  dsimp only at hf hk hrec ⊢
  refine ⟨?_, hk⟩
  simp only [classCtor] at hf hk
  rw [S.length_classFields] at hf hk
  rw [S.classFields_getElem?, Option.map_eq_some_iff] at hf
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  have hpf := positive_field N hpos hc (List.drop_zero (l := c.fields)) hf₀
  have hk' : c.fields.length - 1 - (c.fields.length - 1 - k) = k := by omega
  rw [hk'] at hpf hrec ⊢
  cases f₀ with
  | ordinary A =>
    rcases hpf with rfl | ⟨hu, -⟩
    · simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, fieldScoped]
      refine ⟨fun _ _ hT => by simp at hT, by simpa using hNS.2.2.2.2.2.1, fun e he => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      have hb' := hNS.2.2.2.2.2.2.2.1 b hb
      exact ⟨Expr.closedAt_liftN (n := k) (k := 0) hb'.1, by rw [Expr.consts_liftN]; exact hb'.2.1,
        by rw [Expr.lparamsIn_liftN]; exact hb'.2.2⟩
    · rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)]
        at hrec
      simp [Field.isRec] at hrec
  | reflexive _ _ => simp [classField, fieldScoped, hN]
  | container => exact hpf.elim

/-- **A translated field's domain uses the block's level
parameters**: the container's field is in the container's scope
(`NestScoped`), the class's levels, arguments and the member's index
expressions in the block's. -/
theorem lparamsIn_classField_dom (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) {i : Nat} {f : Field} (hi : c.fields[i]? = some f)
    (k' : Nat) :
    (S.fieldDom k' (S.classField N (c.fields.length - 1 - i) f)).lparamsIn S.lparams = true := by
  have hNS := hS.2.2.2.2.2.2 N hN
  have hpos := hNS.2.2.2.2.2.2.2.2.1
  have hpf := positive_field N hpos hc (List.drop_zero (l := c.fields)) hi
  have hsc0 := hNS.2.2.2.2.2.2.2.2.2.1 c hc i f hi
  obtain ⟨k, hk⟩ : ∃ k, c.fields.length - 1 - i = k := ⟨_, rfl⟩
  rw [hk] at hsc0 hpf ⊢
  cases f with
  | ordinary A =>
    rcases hpf with rfl | ⟨hu, -⟩
    · simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, fieldDom]
      refine S.lparamsIn_famAt _ fun e he => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      rw [Expr.lparamsIn_liftN]
      exact (hNS.2.2.2.2.2.2.2.1 b hb).2.2
    · rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)]
      have hsc : Expr.Scoped env N.KS.lparams (N.KS.nP + k) A := hsc0
      simp only [fieldDom]
      refine Expr.lparamsIn_instChainAt _ _ _ ?_ (S.classArgs_lparamsIn' N hS hN 0)
      exact Expr.lparamsIn_instL hNS.2.2.2.1 hNS.2.2.1 hsc.2.2
  | reflexive _ _ =>
    simp only [classField, fieldDom, hN]
    exact S.lparamsIn_classTy hS hN k'
  | container => exact hpf.elim

/-- A translated constructor's field context is over the block's
parameters. -/
theorem lparamsIn_fieldCtx_classCtor (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) :
    ∀ A ∈ S.fieldCtx (S.classCtor N c).fields, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨i, f, hi, rfl⟩ := S.mem_fieldCtx hA
  simp only [classCtor] at hi ⊢
  rw [S.classFields_getElem?, Option.map_eq_some_iff] at hi
  obtain ⟨f₀, hf₀, rfl⟩ := hi
  rw [S.length_classFields]
  exact S.lparamsIn_classField_dom hS hN hc hf₀ _

/-- A translated constructor's field context, moved under `o`
binders, is over the block's parameters. -/
theorem lparamsIn_fieldCtxAt_classCtor (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (o : Nat) :
    ∀ A ∈ S.fieldCtxAt (S.classCtor N c) o, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨i, A', hi, rfl⟩ := Expr.mem_liftCtx hA
  rw [Expr.lparamsIn_liftN]
  exact S.lparamsIn_fieldCtx_classCtor hS hN hc A' (List.mem_of_getElem? hi)

/-! ## Scope of the generated terms -/

/-- The inductive hypotheses' context under `o` binders uses the
recursor's level parameters, when the recursive positions are in
scope. -/
theorem lparamsIn_ihCtxAt {c : CtorSpec} (hrf : ∀ kf ∈ c.recFields, S.fieldScoped env kf.1 kf.2)
    (o : Nat) : ∀ A ∈ S.ihCtxAt c o, A.lparamsIn S.recLparams = true := by
  intro A hA
  obtain ⟨kf, hkf, l, rfl⟩ := S.mem_ihCtxAt hA
  exact S.lparamsIn_ihTy (hrf kf hkf) _ _ _ _

/-- A minor premise of one of the block's constructors (nested block)
uses the recursor's level parameters. -/
theorem lparamsIn_minorTyN (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) (j : Nat) :
    (S.minorTyN c j).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  simp only [minorTyN]
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · rcases List.mem_append.mp hA with hA | hA
    · exact S.lparamsIn_ihCtxAt (fun kf hkf => (S.fieldScoped_of_mem_recFields hS hc hkf).1) _ A hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_fieldCtxAt hS hc _ A hA)
  · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (S.lparamsIn_idx hS hc e he)
    · rw [List.mem_singleton] at ha
      subst ha
      refine Expr.lparamsIn_mkAppN (Expr.lparamsIn_mono hR (S.lparamsIn_const_lvls _))
        fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact Expr.lparamsIn_varsAt _ _ _ a ha
      · exact Expr.lparamsIn_varsAt _ _ _ a ha

/-- A minor premise of one of the container's constructors uses the
recursor's level parameters: the translated fields and their
hypotheses are over the block's, the container's levels at the
instantiation are (`NestScoped`), and so are the class's arguments. -/
theorem lparamsIn_minorTyK (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (j : Nat) :
    (S.minorTyK N c j).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  have hNS := hS.2.2.2.2.2.2 N hN
  simp only [minorTyK]
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · rcases List.mem_append.mp hA with hA | hA
    · exact S.lparamsIn_ihCtxAt (fun kf hkf => (S.classCtor_recField_scoped hS hN hc hkf).1) _ A hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_fieldCtxAt_classCtor hS hN hc _ A hA)
  · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rw [List.mem_singleton] at ha
    subst ha
    refine Expr.lparamsIn_mkAppN ?_ fun a ha => ?_
    · simp only [Expr.lparamsIn_const, List.all_eq_true]
      exact fun l hl => Level.paramsIn_mono hR (hNS.2.2.2.1 l hl)
    · rcases List.mem_append.mp ha with ha | ha
      · exact Expr.lparamsIn_mono hR (S.lparamsIn_classArgs hS hN _ a ha)
      · exact Expr.lparamsIn_varsAt _ _ _ a ha

/-- The class's motive's type uses the recursor's level parameters. -/
theorem lparamsIn_motiveTy1 (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) :
    (S.motiveTy1 N).lparamsIn S.recLparams = true := by
  unfold motiveTy1
  refine Expr.lparamsIn_mkPis rfl (fun A hA => ?_) ?_
  · rw [List.mem_singleton] at hA
    subst hA
    exact Expr.lparamsIn_mono S.lparams_sub_recLparams (S.lparamsIn_classTy hS hN 1)
  · rw [Expr.lparamsIn_sort]
    exact S.ℓ_paramsIn

/-- The extras use the recursor's level parameters. -/
theorem lparamsIn_extrasN (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) :
    ∀ A ∈ S.extrasN N, A.lparamsIn S.recLparams = true := by
  intro A hA
  simp only [extrasN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with (hA | hA) | rfl | rfl
  · obtain ⟨j, c, hj, rfl⟩ := S.mem_minorsCtxK N hA
    exact S.lparamsIn_minorTyK hS hN (List.mem_of_getElem? hj) j
  · obtain ⟨j, c, hj, rfl⟩ := S.mem_minorsCtxN hA
    exact S.lparamsIn_minorTyN hS (List.mem_of_getElem? hj) j
  · exact S.lparamsIn_motiveTy1 hS hN
  · exact S.lparamsIn_motiveTy hS

/-- **`T.rec`'s type uses the recursor's level parameters.** -/
theorem lparamsIn_recTypeN (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) :
    (S.recTypeN N).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  unfold recTypeN recCtxN
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · simp only [List.mem_cons, List.mem_append] at hA
    rcases hA with ((rfl | hA) | hA) | hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_famVars _)
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_indicesAt hS _ A hA)
    · exact S.lparamsIn_extrasN hS hN A hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_params hS A hA)
  · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · rw [List.mem_singleton] at ha
      subst ha
      rfl

/-- **`T.rec_1`'s type uses the recursor's level parameters.** -/
theorem lparamsIn_rec1Type (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) :
    (S.rec1Type N).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  unfold rec1Type rec1Ctx
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · simp only [List.mem_cons, List.mem_append] at hA
    rcases hA with (rfl | hA) | hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_classTy hS hN _)
    · exact S.lparamsIn_extrasN hS hN A hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_params hS A hA)
  · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rw [List.mem_singleton] at ha
    subst ha
    rfl

/-- A nested rule's context uses the recursor's level parameters, when
the constructor's field context does. -/
theorem lparamsIn_ruleCtxN (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hfc : ∀ A ∈ S.fieldCtxAt c (S.oN N), A.lparamsIn S.lparams = true) :
    ∀ A ∈ S.ruleCtxN N c, A.lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  intro A hA
  simp only [ruleCtxN, List.mem_append] at hA
  rcases hA with (hA | hA) | hA
  · exact Expr.lparamsIn_mono hR (hfc A hA)
  · exact S.lparamsIn_extrasN hS hN A hA
  · exact Expr.lparamsIn_mono hR (S.lparamsIn_params hS A hA)

/-- An inductive hypothesis' value in a nested rule uses the
recursor's level parameters. -/
theorem lparamsIn_ihValN (N : NestInfo) {k : Nat} {f : Field} (hf : S.fieldScoped env k f)
    (nF k' : Nat) : (S.ihValN N nF k' f).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  cases f with
  | ordinary A => rfl
  | container =>
    simp only [ihValN]
    refine Expr.lparamsIn_mkAppN (S.lparamsIn_const_recLvls _) fun a ha => ?_
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · rfl
  | reflexive tele es =>
    simp only [ihValN]
    refine Expr.lparamsIn_mkLams S.q_paramsIn (fun T hT => ?_) ?_
    · obtain ⟨t, T', ht, rfl⟩ := Expr.mem_liftCtx hT
      rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (hf.1 t T' ht).2.2
    · refine Expr.lparamsIn_mkAppN (S.lparamsIn_const_recLvls _) fun a ha => ?_
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with ((ha | ha) | ⟨e, he, rfl⟩) | rfl
      · exact Expr.lparamsIn_varsAt _ _ _ a ha
      · exact Expr.lparamsIn_varsAt _ _ _ a ha
      · rw [Expr.lparamsIn_atCtx]
        exact Expr.lparamsIn_mono hR (hf.2.2 e he).2.2
      · exact Expr.lparamsIn_mkAppN rfl (Expr.lparamsIn_varsAt _ _ _)

/-- The common shape of the two rules' right-hand sides — the minor
at the fields and the inductive hypotheses' values, under the rule's
context — uses the recursor's level parameters. -/
theorem lparamsIn_ruleLamN (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (i : Nat)
    (hfc : ∀ A ∈ S.fieldCtxAt c (S.oN N), A.lparamsIn S.lparams = true)
    (hrf : ∀ kf ∈ c.recFields, S.fieldScoped env kf.1 kf.2) :
    (Expr.mkLams S.q (S.ruleCtxN N c)
      (Expr.mkAppN (.bvar i) (Expr.varsAt 0 c.fields.length ++
        c.recFields.map fun kf => S.ihValN N c.fields.length kf.1 kf.2))).lparamsIn
      S.recLparams = true := by
  refine Expr.lparamsIn_mkLams S.q_paramsIn (S.lparamsIn_ruleCtxN hS hN hfc) ?_
  refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha
  · exact Expr.lparamsIn_varsAt _ _ _ a ha
  · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
    exact S.lparamsIn_ihValN N (hrf kf hkf) _ _

/-- **A `T.rec` rule's right-hand side uses the recursor's level
parameters.** -/
theorem lparamsIn_ruleRhsN (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ S.ctors) (j : Nat) :
    (S.ruleRhsN N c j).lparamsIn S.recLparams = true := by
  simp only [ruleRhsN]
  exact S.lparamsIn_ruleLamN hS hN _ (S.lparamsIn_fieldCtxAt hS hc _)
    fun kf hkf => (S.fieldScoped_of_mem_recFields hS hc hkf).1

/-- **A `T.rec_1` rule's right-hand side uses the recursor's level
parameters.** -/
theorem lparamsIn_rule1Rhs (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (j : Nat) :
    (S.rule1Rhs N c j).lparamsIn S.recLparams = true := by
  simp only [rule1Rhs]
  exact S.lparamsIn_ruleLamN hS hN _ (S.lparamsIn_fieldCtxAt_classCtor hS hN hc _)
    fun kf hkf => (S.classCtor_recField_scoped hS hN hc hkf).1

/-! ### A rule's right-hand side is closed and mentions stored constants -/

/-- An inductive hypothesis' value is closed under a nested rule's
context. -/
theorem closedAt_ihValN (N : NestInfo) {k : Nat} {f : Field} (hf : S.fieldScoped env k f)
    {nF : Nat} (hk : k ≤ nF) :
    (S.ihValN N nF k f).closedAt (nF + S.oN N + S.nP) = true := by
  have hoN := S.oN_eq N
  cases f with
  | ordinary A => rfl
  | container =>
    simp only [ihValN]
    refine Expr.closedAt_mkAppN rfl fun a ha => ?_
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Expr.closedAt_varsAt (by omega) a ha
    · exact Expr.closedAt_varsAt (by omega) a ha
    · rw [Expr.closedAt_bvar, decide_eq_true_eq]
      omega
  | reflexive tele es =>
    simp only [ihValN]
    refine Expr.closedAt_mkLams (fun t T hT => ?_) ?_
    · rw [Expr.liftCtx_getElem?, Option.map_eq_some_iff] at hT
      obtain ⟨T', hT', rfl⟩ := hT
      rw [Expr.length_liftCtx]
      exact Expr.closedAt_mono (by omega)
        (Expr.closedAt_atCtx (j := S.nP + k) (d := tele.length - 1 - t) (hf.1 t T' hT').1)
    · rw [Expr.length_liftCtx]
      refine Expr.closedAt_mkAppN rfl fun a ha => ?_
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with ((ha | ha) | ⟨e, he, rfl⟩) | rfl
      · exact Expr.closedAt_varsAt (by omega) a ha
      · exact Expr.closedAt_varsAt (by omega) a ha
      · exact Expr.closedAt_mono (by omega)
          (Expr.closedAt_atCtx (j := S.nP + k) (d := tele.length) (hf.2.2 e he).1)
      · refine Expr.closedAt_mkAppN ?_ (Expr.closedAt_varsAt (by omega))
        rw [Expr.closedAt_bvar, decide_eq_true_eq]
        omega

/-- A nested rule type's context is closed, the type having been
inferred in the empty context. -/
theorem ctxClosedAt_ruleCtxN [LevelOracle] {env' : Env} {N : NestInfo} {c : CtorSpec} {b T : Expr}
    (hT : Infer env' [] (Expr.mkPis S.q (S.ruleCtxN N c) b) T) :
    Expr.CtxClosedAt 0 (S.ruleCtxN N c) :=
  (Expr.closedAt_mkPis_iff.mp (Infer.closedAt hT)).1

/-- The common shape of the two rules' right-hand sides is closed:
the context is, and the body is a variable applied to variables and
inductive hypotheses' values. -/
theorem closedAt_ruleLamN (N : NestInfo) {c : CtorSpec} {i : Nat}
    (hi : i < c.fields.length + S.oN N + S.nP)
    (hrf : ∀ kf ∈ c.recFields, S.fieldScoped env kf.1 kf.2 ∧ kf.1 < c.fields.length)
    (hctx : Expr.CtxClosedAt 0 (S.ruleCtxN N c)) :
    (Expr.mkLams S.q (S.ruleCtxN N c)
      (Expr.mkAppN (.bvar i) (Expr.varsAt 0 c.fields.length ++
        c.recFields.map fun kf => S.ihValN N c.fields.length kf.1 kf.2))).closedAt 0 = true := by
  refine Expr.closedAt_mkLams hctx ?_
  rw [Nat.zero_add, length_ruleCtxN]
  refine Expr.closedAt_mkAppN ?_ fun a ha => ?_
  · rw [Expr.closedAt_bvar, decide_eq_true_eq]
    exact hi
  · rcases List.mem_append.mp ha with ha | ha
    · exact Expr.closedAt_varsAt (by omega) a ha
    · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hf, hk⟩ := hrf kf hkf
      exact S.closedAt_ihValN N hf (Nat.le_of_lt hk)

/-- **A `T.rec` rule's right-hand side is closed.** -/
theorem closedAt_ruleRhsN (hS : S.Scoped env) (N : NestInfo) {c : CtorSpec} (hc : c ∈ S.ctors)
    (j : Nat) (hctx : Expr.CtxClosedAt 0 (S.ruleCtxN N c)) :
    (S.ruleRhsN N c j).closedAt 0 = true := by
  simp only [ruleRhsN]
  refine S.closedAt_ruleLamN N ?_ (fun kf hkf => S.fieldScoped_of_mem_recFields hS hc hkf) hctx
  have := S.oN_eq N
  omega

/-- **A `T.rec_1` rule's right-hand side is closed.** -/
theorem closedAt_rule1Rhs (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (j : Nat)
    (hctx : Expr.CtxClosedAt 0 (S.ruleCtxN N (S.classCtor N c))) :
    (S.rule1Rhs N c j).closedAt 0 = true := by
  simp only [rule1Rhs]
  refine S.closedAt_ruleLamN N ?_ (fun kf hkf => S.classCtor_recField_scoped hS hN hc hkf) hctx
  have := S.oN_eq N
  omega

/-- An inductive hypothesis' value in a nested rule mentions the two
recursors and the specification's constants, all stored in the
installed environment. -/
theorem consts_ihValN (N : NestInfo) (env : Env)
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none)
    {k : Nat} {f : Field} (hf : S.fieldScoped env k f) (nF k' : Nat) :
    ∀ d ∈ (S.ihValN N nF k' f).consts, ((S.installN N env).find? d).isSome := by
  have hrec : ∀ d ∈ (Expr.const S.recName S.recLvls).consts,
      ((S.installN N env).find? d).isSome := by
    intro d hd
    rw [Expr.consts_const, List.mem_singleton] at hd
    subst hd
    rw [installN_find?]
    split
    · rfl
    · rw [if_pos rfl]
      rfl
  have haux : ∀ d ∈ (Expr.const N.aux S.recLvls).consts, ((S.installN N env).find? d).isSome := by
    intro d hd
    rw [Expr.consts_const, List.mem_singleton] at hd
    subst hd
    rw [installN_find?, if_pos rfl]
    rfl
  have hspec : ∀ {e : Expr} {k'' : Nat}, Expr.Scoped env S.lparams k'' e →
      ∀ d ∈ e.consts, ((S.installN N env).find? d).isSome := by
    intro e k'' he d hd
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (he.2.1 d hd)
    rw [S.find?_mono_installN N env hfresh hci]
    rfl
  cases f with
  | ordinary A => intro d hd; simp [ihValN] at hd
  | container =>
    intro d hd
    simp only [ihValN] at hd
    rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
    rcases hd with hd | ⟨a, ha, hd⟩
    · exact haux d hd
    · simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · simp at hd
  | reflexive tele es =>
    intro d hd
    simp only [ihValN] at hd
    rcases Expr.consts_mkLams _ _ _ d hd with hd | ⟨T, hT, hd⟩
    · rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
      rcases hd with hd | ⟨a, ha, hd⟩
      · exact hrec d hd
      · simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
        rcases ha with ((ha | ha) | ⟨e, he, rfl⟩) | rfl
        · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
        · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
        · rw [Expr.consts_atCtx] at hd
          exact hspec (hf.2.2 e he) d hd
        · rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
          rcases hd with hd | ⟨a, ha, hd⟩
          · simp at hd
          · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
    · obtain ⟨t, T', hT', rfl⟩ := Expr.mem_liftCtx hT
      rw [Expr.consts_atCtx] at hd
      exact hspec (hf.1 t T' hT') d hd

/-- The common shape of the two rules' right-hand sides mentions only
stored constants: its context's are the rule type's (inferred with
the former and the constructors), its body's are the recursors' and
the specification's. -/
theorem consts_ruleLamN [LevelOracle] (N : NestInfo) (env : Env)
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none)
    {c : CtorSpec} (i : Nat) (hrf : ∀ kf ∈ c.recFields, S.fieldScoped env kf.1 kf.2)
    {b T : Expr} (hT : Infer (S.envCtors env) [] (Expr.mkPis S.q (S.ruleCtxN N c) b) T) :
    ∀ d ∈ (Expr.mkLams S.q (S.ruleCtxN N c)
      (Expr.mkAppN (.bvar i) (Expr.varsAt 0 c.fields.length ++
        c.recFields.map fun kf => S.ihValN N c.fields.length kf.1 kf.2))).consts,
      ((S.installN N env).find? d).isSome := by
  intro d hd
  rcases Expr.consts_mkLams _ _ _ d hd with hd | ⟨A, hA, hd⟩
  · rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
    rcases hd with hd | ⟨a, ha, hd⟩
    · simp at hd
    · rcases List.mem_append.mp ha with ha | ha
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
        exact S.consts_ihValN N env hfresh (hrf kf hkf) _ _ d hd
  · exact S.isSome_find?_installN N env (Infer.consts hT d (Expr.consts_mkPis_of _ _ _ hA hd))

/-- **A `T.rec` rule's right-hand side mentions only stored
constants.** -/
theorem consts_ruleRhsN [LevelOracle] (hS : S.Scoped env) (N : NestInfo)
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none)
    {c : CtorSpec} (hc : c ∈ S.ctors) (j : Nat)
    {T : Expr} (hT : Infer (S.envCtors env) [] (S.ruleTypeN N c) T) :
    ∀ d ∈ (S.ruleRhsN N c j).consts, ((S.installN N env).find? d).isSome := by
  simp only [ruleRhsN]
  exact S.consts_ruleLamN N env hfresh _
    (fun kf hkf => (S.fieldScoped_of_mem_recFields hS hc hkf).1) hT

/-- **A `T.rec_1` rule's right-hand side mentions only stored
constants.** -/
theorem consts_rule1Rhs [LevelOracle] (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N)
    (hfresh : ∀ m ∈ S.name :: S.recName :: N.aux :: S.ctors.map (·.name), env.find? m = none)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (j : Nat)
    {T : Expr} (hT : Infer (S.envCtors env) [] (S.rule1Type N c) T) :
    ∀ d ∈ (S.rule1Rhs N c j).consts, ((S.installN N env).find? d).isSome := by
  simp only [rule1Rhs]
  exact S.consts_ruleLamN N env hfresh _
    (fun kf hkf => (S.classCtor_recField_scoped hS hN hc hkf).1) hT

end Generated

/-! ## The installed nested environment is closed -/

/-- **The installed nested environment is closed.**  The former and
the constructors as for a plain block; then, by where a name is found:
`T.rec_1` and `T.rec` have the types the checker inferred (closed,
stored constants) over the recursor's level parameters, and rules
that are closed, mention stored constants, use the recursor's
parameters and fire on stored constructors — the block's own for
`T.rec`, the container's (stored, `NestScoped`) for `T.rec_1`; a
constant stored before keeps its scope. -/
theorem _root_.Fragment.Env.Scoped.installN [LevelOracle] {env : Env} {S : IndSpec} {N : NestInfo}
    (hs : Env.Scoped env) (hok : S.OkN N env) : Env.Scoped (S.install env) := by
  have hN : S.nest = some N := hok.1
  simp only [IndSpec.install, hN]
  obtain ⟨-, hnodup, hfresh, hS, ⟨T₀, hind⟩, hctors, -, -, -, -, -, hrules1, ⟨T₁, hrec⟩,
    ⟨T₂, hrec1⟩⟩ := hok
  rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
  obtain ⟨hname, hrecName, haux, hcnodup⟩ := hnodup
  have hNS := hS.2.2.2.2.2.2 N hN
  -- The former.
  have h₁ : Env.Scoped (S.envInd env) := by
    refine hs.add (c := S.name) (ci := S.indInfo) (hfresh S.name List.mem_cons_self)
      ⟨Infer.closedAt hind, Infer.consts hind, S.lparamsIn_indType hS⟩ ?_ ?_
    · intro v hv
      simp [ConstInfo.value?, indInfo, ConstKind.value?] at hv
    · intro _ _ _ _ _ hk
      simp [indInfo] at hk
  -- The constructors.
  have h₂ : Env.Scoped (S.envCtors env) := by
    refine Env.Scoped.foldl_ctors S h₁ hcnodup ?_ ?_
    · intro c hc
      rw [envInd_find?, if_neg, hfresh c.name (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))))]
      intro h
      exact hname (by
        rw [← h]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)))
    · intro c hc
      obtain ⟨T, hT⟩ := (hctors c hc).1
      exact ⟨Infer.closedAt hT, Infer.consts hT, S.lparamsIn_ctorType hS hc⟩
  -- The two recursors' types, in scope of the installed environment.
  have hty_rec : Expr.Scoped (S.installN N env) S.recLparams 0 (S.recTypeN N) :=
    ⟨Infer.closedAt hrec, fun d hd => S.isSome_find?_installN N env (Infer.consts hrec d hd),
      S.lparamsIn_recTypeN hS hN⟩
  have hty_rec1 : Expr.Scoped (S.installN N env) S.recLparams 0 (S.rec1Type N) :=
    ⟨Infer.closedAt hrec1, fun d hd => S.isSome_find?_installN N env (Infer.consts hrec1 d hd),
      S.lparamsIn_rec1Type hS hN⟩
  intro n ci hfind
  rw [installN_find?] at hfind
  split at hfind
  · -- `T.rec_1`
    rename_i hn
    subst hn
    cases hfind
    refine ⟨hty_rec1, ?_, ?_⟩
    · intro v hv
      simp [ConstInfo.value?, rec1Info, ConstKind.value?] at hv
    · intro nP nM nMin nI rules hk rl hrl
      simp only [rec1Info, ConstKind.recursor.injEq] at hk
      obtain ⟨_, _, _, _, rfl⟩ := hk
      obtain ⟨j, c, hj, rfl⟩ := S.mem_rules1 N hrl
      have hcj := List.mem_of_getElem? hj
      obtain ⟨T, hT⟩ := hrules1 c hcj
      refine ⟨⟨S.closedAt_rule1Rhs hS hN hcj j (S.ctxClosedAt_ruleCtxN (by rw [rule1Type] at hT; exact hT)),
        S.consts_rule1Rhs hS hN hfresh hcj j hT, S.lparamsIn_rule1Rhs hS hN hcj j⟩, ?_⟩
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hNS.2.2.2.2.2.2.2.2.2.2 c hcj)
      rw [S.find?_mono_installN N env hfresh hci]
      rfl
  · split at hfind
    · -- `T.rec`
      rename_i hn
      subst hn
      cases hfind
      refine ⟨hty_rec, ?_, ?_⟩
      · intro v hv
        simp [ConstInfo.value?, recInfoN, ConstKind.value?] at hv
      · intro nP nM nMin nI rules hk rl hrl
        simp only [recInfoN, ConstKind.recursor.injEq] at hk
        obtain ⟨_, _, _, _, rfl⟩ := hk
        obtain ⟨j, c, hj, rfl⟩ := S.mem_rulesN N hrl
        have hcj := List.mem_of_getElem? hj
        obtain ⟨T, hT⟩ := (hctors c hcj).2.2.2
        refine ⟨⟨S.closedAt_ruleRhsN hS N hcj j (S.ctxClosedAt_ruleCtxN (by rw [ruleTypeN] at hT; exact hT)),
          S.consts_ruleRhsN hS N hfresh hcj j hT, S.lparamsIn_ruleRhsN hS hN hcj j⟩, ?_⟩
        rw [installN_find?,
          if_neg (fun h => haux (by rw [← h]; exact List.mem_map_of_mem hcj)),
          if_neg (fun h => hrecName (by
            rw [← h]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hcj))),
          envCtors_find? S env hcnodup, S.ctorOf?_of_getElem? hcnodup hj]
        rfl
    · -- A constant stored before.
      have h := h₂ n ci hfind
      unfold IndSpec.installN
      refine ⟨(h.1.add _ _).add _ _, fun v hv => ((h.2.1 v hv).add _ _).add _ _, ?_⟩
      intro nP nM nMin nI rules hk rl hrl
      have h' := h.2.2 nP nM nMin nI rules hk rl hrl
      exact ⟨(h'.1.add _ _).add _ _, Env.isSome_find?_add (Env.isSome_find?_add h'.2 _ _) _ _⟩

end IndSpec

end Fragment
