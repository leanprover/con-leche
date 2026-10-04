module

public import Fragment.Install
public import Fragment.NestSem

@[expose] public section

/-!
# The model remembers its blocks

A nested block reads its container's **family** — not just the
container's set in the model, but the fact that this set is the graph
of the least fixed point of the container's operator, whose leastness
and accessibility are what make the container's clause monotone and
accessible (`NestSem.lean`).  So the model of an environment carries,
besides the three laws of `EnvModel`, one law per stored plain block
(`BlockLaw`): the block is in scope, its former's and constructors'
sets are the family's graph and the constructors' graphs of the
block's own installation, and the universe bound on its fields holds
at every fitting parameter list — exactly the facts a later nesting
consumes (`NestFacts`).  A nested block stores no such law: nesting is
at depth one, so it is never a container (the law is conditional on
the block being plain).

The law is stated at the model's own assignment, and survives every
later installation because the block's syntax mentions only constants
stored before it (`EnvModel.transport`'s argument again:
`famSet_congr`, `ctorSet_congr`, `DomsBounded_congr`).

Con-leche: the `lfpBlocks` of `EnvModelM`
(`ConLeche/Model/Annot/EnvModelM.lean`), the datum of every installed
block kept with the model.
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) {env : Env}

/-- **The block's law** in a model: for a plain block, its scope, its
constants stored, its former's set the family's graph, its
constructors' sets their graphs, and the universe bound on its fields
at fitting parameters.  Vacuous for a nested block. -/
def BlockLaw (env : Env) (M : Name → List Nat → V) : Prop :=
  S.nest = none →
    S.Scoped env ∧ S.NoCont ∧
    env.find? S.name = some S.indInfo ∧
    (∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → env.find? c.name = some (S.ctorInfo c)) ∧
    (∀ ls, M S.name ls = S.famSet M ls) ∧
    (∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → ∀ ls, M c.name ls = S.ctorSet M ls j c) ∧
    (∀ ls ps, FitsVals M (S.ψ ls) base S.params ps → S.DomsBounded M ls ps)

end IndSpec

/-- **A model of an environment that remembers its blocks**: an
`EnvModel` with the block law of every stored block. -/
structure BlockModel (V : Type u) [IndLib V] (env : Env) extends EnvModel V env where
  /-- Every stored block's law. -/
  blocks : ∀ (K : Name) (ci : ConstInfo) (nP nI : Nat) (cs : List Name) (spec : IndSpec),
    env.find? K = some ci → ci.kind = .induct nP nI cs spec → spec.BlockLaw env M

/-- The empty environment's model remembers nothing. -/
def BlockModel.empty (M : Name → List Nat → V) : BlockModel V Env.empty where
  toEnvModel := EnvModel.empty M
  blocks := fun _ _ _ _ _ _ h => by simp at h

/-! ## Hygiene: a block's semantic objects read the model at its stored constants only

Every reading of the block's syntax goes through `interp M (S.ψ ls) ρ e`
with `e` an expression of the specification, in scope of `env`
(`S.Scoped env`) — so it mentions only stored constants, on which two
assignments agreeing on `env` agree (`interp_consts`) — and depends on
the levels `ls` only through the valuation `S.ψ ls`.  A nested block's
container field reads the container's set, a stored constant, so it
agrees too.  The two agreements are carried together (`Agree`) and
pushed bottom-up through the definitions of `IndSem.lean`: the
fields, the fitting lists, the operator, the family. -/

namespace IndSpec

variable (S : IndSpec) {env : Env} {M M' : Name → List Nat → V} {ls ls' : List Nat}

/-- The container's specification is in scope (vacuous for a plain
block): what a later reading of the container's constructors needs. -/
def ContScoped (env : Env) : Prop := ∀ N, S.nest = some N → N.KS.Scoped env

theorem contScoped_of_plain (hpl : S.nest = none) : S.ContScoped env := fun N hN => by
  rw [hpl] at hN
  cases hN

/-- **Two readings of the block's syntax that agree**: the block and
its container in scope, the assignments agreeing on the stored
constants, the two level lists valuing the block's parameters alike. -/
structure Agree (env : Env) (M M' : Name → List Nat → V) (ls ls' : List Nat) : Prop where
  /-- The block is in scope. -/
  block : S.Scoped env
  /-- Its container is in scope. -/
  cont : S.ContScoped env
  /-- The assignments agree on the stored constants. -/
  agree : AgreeOn env M M'
  /-- The valuations agree. -/
  ψ : S.ψ ls = S.ψ ls'

variable {S}

omit [IndLib V] in
theorem Agree.symm (h : S.Agree env M M' ls ls') : S.Agree env M' M ls' ls :=
  ⟨h.block, h.cont, fun c hc l => (h.agree c hc l).symm, h.ψ.symm⟩

omit [IndLib V] in
/-- The same agreement at any other levels (the valuations identical). -/
theorem Agree.same (h : S.Agree env M M' ls ls') (l : List Nat) : S.Agree env M M' l l :=
  ⟨h.block, h.cont, h.agree, rfl⟩

/-! ### Scope, in membership form -/

theorem Scoped.params_in (hS : S.Scoped env) :
    ∀ A ∈ S.params, ∃ k, Expr.Scoped env S.lparams k A := fun A hA => by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hA
  exact ⟨_, hS.1 i A hi⟩

theorem Scoped.indices_in (hS : S.Scoped env) :
    ∀ T ∈ S.indices, ∃ k, Expr.Scoped env S.lparams k T := fun T hT => by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hT
  exact ⟨_, hS.2.1 t T ht⟩

theorem Scoped.fields_in (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ f ∈ c.fields, ∃ k, S.fieldScoped env k f := fun f hf => by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  exact ⟨_, (hS.2.2.2.1 c hc).1 i f hi⟩

theorem Scoped.fields_rev_in (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ f ∈ c.fields.reverse, ∃ k, S.fieldScoped env k f :=
  fun f hf => hS.fields_in hc f (List.mem_reverse.mp hf)

theorem Scoped.idx_in (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ e ∈ c.idx, Expr.Scoped env S.lparams (S.nP + c.fields.length) e :=
  (hS.2.2.2.1 c hc).2.2.2

/-- A reflexive field's telescope entries, in membership form. -/
theorem tele_in {k : Nat} {tele es : List Expr} (hf : S.fieldScoped env k (.reflexive tele es)) :
    ∀ T ∈ tele.reverse, ∃ k, Expr.Scoped env S.lparams k T := fun T hT => by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp (List.mem_reverse.mp hT)
  exact ⟨_, hf.1 t T ht⟩

/-! ### Scope survives growing the environment -/

theorem _root_.Fragment.Expr.Scoped.mono {env env' : Env} {ps : List Name} {k : Nat} {e : Expr}
    (h : Expr.Scoped env ps k e) (hm : ∀ n, (env.find? n).isSome → (env'.find? n).isSome) :
    Expr.Scoped env' ps k e :=
  ⟨h.1, fun d hd => hm d (h.2.1 d hd), h.2.2⟩

theorem fieldScoped.mono {env env' : Env} {k : Nat} {f : Field} (h : S.fieldScoped env k f)
    (hm : ∀ n, (env.find? n).isSome → (env'.find? n).isSome) : S.fieldScoped env' k f := by
  cases f with
  | ordinary A => exact Expr.Scoped.mono h hm
  | reflexive tele es =>
    exact ⟨fun t T hT => (h.1 t T hT).mono hm, h.2.1, fun e he => (h.2.2 e he).mono hm⟩
  | container => exact h

theorem NestScoped.mono {env env' : Env} (h : S.NestScoped env)
    (hm : ∀ n, (env.find? n).isSome → (env'.find? n).isSome) : S.NestScoped env' := by
  intro N hN
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h N hN
  exact ⟨hm _ h1, h2, h3, h4, h5, h6, fun e he => (h7 e he).mono hm,
    fun e he => (h8 e he).mono hm, h9, fun c hc i f hf => fieldScoped.mono (h10 c hc i f hf) hm,
    fun c hc => hm _ (h11 c hc)⟩

/-- A specification in scope stays in scope when the environment
grows. -/
theorem Scoped.mono {env env' : Env} (h : S.Scoped env)
    (hm : ∀ n, (env.find? n).isSome → (env'.find? n).isSome) : S.Scoped env' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨fun i A hA => (h1 i A hA).mono hm, fun t T hT => (h2 t T hT).mono hm, h3,
    fun c hc => ⟨fun i f hf => fieldScoped.mono ((h4 c hc).1 i f hf) hm, (h4 c hc).2.1, (h4 c hc).2.2.1,
      fun e he => ((h4 c hc).2.2.2 e he).mono hm⟩,
    h5, h6, NestScoped.mono h7 hm⟩

/-! ### Reading an expression -/

/-- An expression in scope reads alike under agreeing assignments, at
any valuation. -/
theorem Agree.read' (h : S.Agree env M M' ls ls') {ps : List Name} {k : Nat} {e : Expr}
    (he : Expr.Scoped env ps k e) (φ : Name → Nat) (ρ : Nat → V) :
    interp M φ ρ e = interp M' φ ρ e :=
  interp_consts fun c hc l => h.agree c (he.2.1 c hc) l

/-- An expression of the specification reads alike in the two
readings. -/
theorem Agree.read (h : S.Agree env M M' ls ls') {ps : List Name} {k : Nat} {e : Expr}
    (he : Expr.Scoped env ps k e) (ρ : Nat → V) :
    interp M (S.ψ ls) ρ e = interp M' (S.ψ ls') ρ e := by
  rw [h.ψ]
  exact h.read' he _ ρ

theorem Agree.ctxAgree (h : S.Agree env M M' ls ls') {Γ : List Expr}
    (hΓ : ∀ A ∈ Γ, ∃ k, Expr.Scoped env S.lparams k A) (ρ : Nat → V) :
    CtxAgree M M' (S.ψ ls) (S.ψ ls') ρ ρ Γ := by
  intro i A hA vs _
  obtain ⟨k, hk⟩ := hΓ A (List.mem_of_getElem? hA)
  exact h.read hk _

theorem Agree.fitsParams_iff (h : S.Agree env M M' ls ls') (ps : List V) :
    FitsVals M (S.ψ ls) base S.params ps ↔ FitsVals M' (S.ψ ls') base S.params ps :=
  FitsVals_congr₂ (h.ctxAgree h.block.params_in base)

/-! ### The regime, the class -/

omit [IndLib V] in
theorem Agree.z_eq (h : S.Agree env M M' ls ls') : S.z ls = S.z ls' := by
  unfold z
  rw [h.ψ]

omit [IndLib V] in
theorem Agree.u₀_eq (h : S.Agree env M M' ls ls') : S.u₀ ls = S.u₀ ls' := by
  unfold u₀
  rw [h.ψ]

omit [IndLib V] in
theorem Agree.lsK_eq (h : S.Agree env M M' ls ls') (N : NestInfo) : S.lsK ls N = S.lsK ls' N := by
  unfold lsK
  rw [h.ψ]

theorem Agree.ctorVal_eq (h : S.Agree env M M' ls ls') :
    S.ctorVal (V := V) ls = S.ctorVal (V := V) ls' := by
  funext j fs
  unfold ctorVal
  rw [h.z_eq]

theorem Agree.idxVals_eq (h : S.Agree env M M' ls ls') {k : Nat} {es : List Expr}
    (hes : ∀ e ∈ es, Expr.Scoped env S.lparams k e) (ρ : Nat → V) :
    S.idxVals M ls ρ es = S.idxVals M' ls' ρ es := by
  unfold idxVals
  congr 1
  exact List.map_congr_left fun e he => h.read (hes e he) ρ

theorem Agree.classArgsV_eq (h : S.Agree env M M' ls ls') {N : NestInfo} (hN : S.nest = some N)
    (ps : List V) (X : V) : S.classArgsV M ls N ps X = S.classArgsV M' ls' N ps X := by
  have hNS := h.block.2.2.2.2.2.2 N hN
  unfold classArgsV
  congr 1
  · congr 1
    exact List.map_congr_left fun e he =>
      h.read (hNS.2.2.2.2.2.2.1 e (List.mem_of_mem_take he)) _
  · exact List.map_congr_left fun e he =>
      h.read (hNS.2.2.2.2.2.2.1 e (List.mem_of_mem_drop he)) _

theorem Agree.classSet_eq (h : S.Agree env M M' ls ls') {N : NestInfo} (hN : S.nest = some N) :
    S.classSet M ls N = S.classSet M' ls' N := by
  funext ps X
  unfold classSet
  rw [h.lsK_eq N, h.agree N.K.name (h.block.2.2.2.2.2.2 N hN).1, h.classArgsV_eq hN ps X]

theorem Agree.memberIdx_eq (h : S.Agree env M M' ls ls') {N : NestInfo} (hN : S.nest = some N) :
    S.memberIdx M ls N = S.memberIdx M' ls' N := by
  funext ps
  unfold memberIdx
  exact h.idxVals_eq (h.block.2.2.2.2.2.2 N hN).2.2.2.2.2.2.2.1 _

theorem Agree.psK_eq (h : S.Agree env M M' ls ls') {N : NestInfo} (hN : S.nest = some N) :
    S.psK M ls N = S.psK M' ls' N := by
  funext ps X
  unfold psK
  rw [h.classArgsV_eq hN ps X]

/-! ### Fields, fitting lists, the operator, the family -/

theorem Agree.fieldSet_eq (h : S.Agree env M M' ls ls') (W : List V → V)
    (ps fs : List V) {k : Nat} {f : Field} (hf : S.fieldScoped env k f) :
    S.fieldSet M ls W ps fs f = S.fieldSet M' ls' W ps fs f := by
  cases f with
  | ordinary A => exact h.read hf _
  | reflexive tele es =>
    simp only [fieldSet]
    rw [h.z_eq]
    refine piCtx_congr₂ (h.ctxAgree (fun T hT => ?_) _) fun ys _ => ?_
    · obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hT
      exact ⟨_, hf.1 t T ht⟩
    · simp only [h.idxVals_eq hf.2.2]
  | container =>
    cases hN : S.nest with
    | none => rw [S.fieldSet_container_none M ls hN, S.fieldSet_container_none M' ls' hN]
    | some N =>
      rw [S.fieldSet_container M ls hN, S.fieldSet_container M' ls' hN, h.memberIdx_eq hN,
        h.classSet_eq hN]

theorem Agree.fitsFields_iff (h : S.Agree env M M' ls ls') (W : List V → V)
    (ps : List V) : ∀ {fields : List Field}, (∀ f ∈ fields, ∃ k, S.fieldScoped env k f) →
      ∀ vs : List V, S.FitsFields M ls W ps fields vs ↔ S.FitsFields M' ls' W ps fields vs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | f :: fields, hsc, v :: vs => by
    obtain ⟨k, hk⟩ := hsc f List.mem_cons_self
    simp only [FitsFields]
    rw [h.fieldSet_eq W ps vs hk,
      Agree.fitsFields_iff h W ps (fun f' hf' => hsc f' (List.mem_cons_of_mem f hf')) vs]

theorem Agree.fitsSet_eq (h : S.Agree env M M' ls ls') (W : List V → V) (ps : List V) :
    ∀ {fields : List Field}, (∀ f ∈ fields, ∃ k, S.fieldScoped env k f) →
      S.fitsSet M ls W ps fields = S.fitsSet M' ls' W ps fields
  | [], _ => rfl
  | f :: fields, hsc => by
    obtain ⟨k, hk⟩ := hsc f List.mem_cons_self
    simp only [fitsSet]
    rw [Agree.fitsSet_eq h W ps (fun f' hf' => hsc f' (List.mem_cons_of_mem f hf'))]
    refine famUnion_congr fun t _ => ?_
    rw [h.fieldSet_eq W ps _ hk]

/-- **The operator reads the model at the block's constants only.** -/
theorem Agree.famOp_eq (h : S.Agree env M M' ls ls') (ps : List V) :
    S.famOp M ls ps = S.famOp M' ls' ps := by
  funext W is
  unfold famOp
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hc := S.getD_mem (List.mem_range.mp hj)
  unfold ctorFibre
  rw [h.ctorVal_eq, h.fitsSet_eq W ps (h.block.fields_in hc)]
  congr 1
  apply ext
  intro t
  rw [mem_sep, mem_sep, h.idxVals_eq (h.block.idx_in hc)]

/-- **The family reads the model at the block's constants only.** -/
theorem Agree.Fam_eq (h : S.Agree env M M' ls ls') : S.Fam M ls = S.Fam M' ls' := by
  funext ps is
  unfold Fam
  rw [h.u₀_eq, h.famOp_eq ps]

theorem Agree.famSet_eq (h : S.Agree env M M' ls ls') : S.famSet M ls = S.famSet M' ls' := by
  unfold famSet famSetF
  refine lamCtx_congr₂ (h.ctxAgree (fun A hA => ?_) base) fun _ _ => ?_
  · rcases List.mem_append.mp hA with hA | hA
    · exact h.block.indices_in A hA
    · exact h.block.params_in A hA
  · rw [h.Fam_eq]

/-! ### The constructors' sets: the model with the former -/

/-- The model with the former added: the two readings agree at the
former and at the stored constants. -/
theorem Agree.M₁_agree (h : S.Agree env M M' ls ls') (c : Name)
    (hc : c = S.name ∨ (env.find? c).isSome) (l : List Nat) : S.M₁ M c l = S.M₁ M' c l := by
  simp only [M₁, M₁F]
  by_cases hc' : c = S.name
  · rw [ite_eq_left hc', ite_eq_left hc']
    exact (h.same l).famSet_eq
  · rw [ite_eq_right hc', ite_eq_right hc']
    exact h.agree c (hc.resolve_left hc') l

theorem Agree.M₁_read (h : S.Agree env M M' ls ls') {e : Expr}
    (he : ∀ c ∈ e.consts, c = S.name ∨ (env.find? c).isSome) (ρ : Nat → V) :
    interp (S.M₁ M) (S.ψ ls) ρ e = interp (S.M₁ M') (S.ψ ls') ρ e := by
  rw [h.ψ]
  exact interp_consts fun c hc l => h.M₁_agree c (he c hc) l

variable (S)

/-- The family applied mentions the former and the constants of its
index expressions. -/
theorem consts_famAt {k : Nat} {es : List Expr}
    (hes : ∀ e ∈ es, ∀ c ∈ e.consts, (env.find? c).isSome) :
    ∀ c ∈ (S.famAt k es).consts, c = S.name ∨ (env.find? c).isSome := by
  intro c hc
  unfold famAt at hc
  rw [Expr.consts_mkAppN, List.mem_append, Expr.consts_const, List.mem_singleton,
    List.mem_flatMap] at hc
  rcases hc with rfl | ⟨e, he, hce⟩
  · exact Or.inl rfl
  · rcases List.mem_append.mp he with he | he
    · rw [Expr.consts_varsAt _ _ e he] at hce
      exact absurd hce List.not_mem_nil
    · exact Or.inr (hes e he c hce)

/-- The class mentions the container, the former and the constants
of the class's arguments. -/
theorem consts_classTy (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) (o : Nat) :
    ∀ c ∈ (S.classTy N o).consts, c = S.name ∨ (env.find? c).isSome := by
  have hNS := hS.2.2.2.2.2.2 N hN
  intro c hc
  unfold classTy at hc
  rw [Expr.consts_mkAppN, List.mem_append, Expr.consts_const, List.mem_singleton,
    List.mem_flatMap] at hc
  rcases hc with rfl | ⟨e, he, hce⟩
  · exact Or.inr hNS.1
  · unfold classArgs at he
    rw [List.mem_append, List.mem_append, List.mem_singleton] at he
    rcases he with (he | rfl) | he
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rw [Expr.consts_liftN] at hce
      exact Or.inr ((hNS.2.2.2.2.2.2.1 a (List.mem_of_mem_take ha)).2.1 c hce)
    · refine S.consts_famAt (fun e he d hd => ?_) c hce
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rw [Expr.consts_liftN] at hd
      exact (hNS.2.2.2.2.2.2.2.1 a ha).2.1 d hd
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rw [Expr.consts_liftN] at hce
      exact Or.inr ((hNS.2.2.2.2.2.2.1 a (List.mem_of_mem_drop ha)).2.1 c hce)

/-- A field's domain mentions the former and stored constants only. -/
theorem consts_fieldDom (hS : S.Scoped env) {k : Nat} {f : Field} (hf : S.fieldScoped env k f) :
    ∀ c ∈ (S.fieldDom k f).consts, c = S.name ∨ (env.find? c).isSome := by
  cases f with
  | ordinary A => exact fun c hc => Or.inr (hf.2.1 c hc)
  | reflexive tele es =>
    intro c hc
    simp only [fieldDom] at hc
    rcases Expr.consts_mkPis _ _ _ c hc with hc | ⟨A, hA, hc⟩
    · exact S.consts_famAt (fun e he => (hf.2.2 e he).2.1) c hc
    · obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hA
      exact Or.inr ((hf.1 t A ht).2.1 c hc)
  | container =>
    intro c hc
    simp only [fieldDom] at hc
    cases hN : S.nest with
    | none =>
      rw [hN] at hc
      exact absurd hc List.not_mem_nil
    | some N =>
      rw [hN] at hc
      exact S.consts_classTy hS hN k c hc

variable {S}

theorem Agree.ctorSet_eq (h : S.Agree env M M' ls ls') (j : Nat) {c : CtorSpec}
    (hc : c ∈ S.ctors) : S.ctorSet M ls j c = S.ctorSet M' ls' j c := by
  unfold ctorSet
  rw [h.z_eq, h.ctorVal_eq]
  refine lamCtx_congr₂ ?_ fun _ _ => rfl
  intro i A hA vs _
  rcases List.mem_append.mp (List.mem_of_getElem? hA) with hA | hA
  · obtain ⟨i', f, hf, rfl⟩ := S.mem_fieldCtx hA
    exact h.M₁_read (S.consts_fieldDom h.block ((h.block.2.2.2.1 c hc).1 i' f hf)) _
  · obtain ⟨k, hk⟩ := h.block.params_in A hA
    exact h.M₁_read (fun d hd => Or.inr (hk.2.1 d hd)) _

/-! ### The domains' bound -/

theorem Agree.domsBounded_imp (h : S.Agree env M M' ls ls') (ps : List V) :
    S.DomsBounded M ls ps → S.DomsBounded M' ls' ps := by
  intro hd hz W hW c hc k f hf hk fs hfs
  rw [← h.z_eq] at hz
  rw [← h.u₀_eq] at hW
  have hfs' := (h.fitsFields_iff W ps (fun f' hf' => h.block.fields_in hc f'
    (List.mem_of_mem_drop hf')) fs).mpr hfs
  have := hd hz W hW c hc k f hf hk fs hfs'
  have hsc := (h.block.2.2.2.1 c hc).1 _ f hf
  cases f with
  | ordinary A =>
    dsimp only at this ⊢
    rwa [h.read hsc, h.u₀_eq] at this
  | reflexive tele es =>
    dsimp only at this ⊢
    intro t T hT ys hys
    have hys' := (FitsVals_congr₂ (h.ctxAgree (fun T' hT' => ?_) _)).mpr hys
    · have := this t T hT ys hys'
      rwa [h.read (hsc.1 t T hT), h.u₀_eq] at this
    · obtain ⟨t', ht'⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_drop hT')
      exact ⟨_, hsc.1 t' T' ht'⟩
  | container => trivial

/-! ### The hygiene lemmas, at one assignment change -/

variable (S)

/-- The family reads the model at the block's constants only. -/
theorem Fam_congr (hS : S.Scoped env) (hK : S.ContScoped env) (hM : AgreeOn env M M')
    (ls : List Nat) : S.Fam M ls = S.Fam M' ls :=
  (Agree.mk hS hK hM rfl : S.Agree env M M' ls ls).Fam_eq

theorem famSet_congr (hS : S.Scoped env) (hK : S.ContScoped env) (hM : AgreeOn env M M')
    (ls : List Nat) : S.famSet M ls = S.famSet M' ls :=
  (Agree.mk hS hK hM rfl : S.Agree env M M' ls ls).famSet_eq

theorem ctorSet_congr (hS : S.Scoped env) (hK : S.ContScoped env) (hM : AgreeOn env M M')
    (ls : List Nat) (j : Nat) {c : CtorSpec} (hc : c ∈ S.ctors) :
    S.ctorSet M ls j c = S.ctorSet M' ls j c :=
  (Agree.mk hS hK hM rfl : S.Agree env M M' ls ls).ctorSet_eq j hc

theorem DomsBounded_congr (hS : S.Scoped env) (hK : S.ContScoped env) (hM : AgreeOn env M M')
    (ls : List Nat) (ps : List V) : S.DomsBounded M ls ps ↔ S.DomsBounded M' ls ps :=
  ⟨(Agree.mk hS hK hM rfl : S.Agree env M M' ls ls).domsBounded_imp ps,
    (Agree.mk hS hK hM rfl : S.Agree env M M' ls ls).symm.domsBounded_imp ps⟩

theorem FitsVals_params_congr (hS : S.Scoped env) (hM : AgreeOn env M M') (ls : List Nat)
    (ps : List V) :
    FitsVals M (S.ψ ls) base S.params ps ↔ FitsVals M' (S.ψ ls) base S.params ps :=
  FitsVals_congr₂ (M := M) (M' := M') (φ := S.ψ ls) (φ' := S.ψ ls) (ρ := base) (ρ' := base)
    fun i A hA _ _ => interp_consts fun c hc l => hM c ((hS.1 i A hA).2.1 c hc) l

/-! ### The block law survives -/

/-- **The block law survives a change of assignment away from the
stored constants.** -/
theorem BlockLaw_transport (hM : AgreeOn env M M') (h : S.BlockLaw env M) : S.BlockLaw env M' := by
  intro hpl
  obtain ⟨hS, hnc, hfind, hctors, hfam, hcs, hdoms⟩ := h hpl
  have hA : ∀ ls, S.Agree env M M' ls ls :=
    fun ls => ⟨hS, S.contScoped_of_plain hpl, hM, rfl⟩
  refine ⟨hS, hnc, hfind, hctors, fun ls => ?_, fun j c hc ls => ?_, fun ls ps hp => ?_⟩
  · rw [← hM S.name (by rw [hfind]; rfl) ls, hfam ls, (hA ls).famSet_eq]
  · rw [← hM c.name (by rw [hctors j c hc]; rfl) ls, hcs j c hc ls,
      (hA ls).ctorSet_eq j (List.mem_of_getElem? hc)]
  · exact (hA ls).domsBounded_imp ps (hdoms ls ps (((hA ls).fitsParams_iff ps).mpr hp))

/-- **The block law survives growing the environment** under fresh
names. -/
theorem BlockLaw_add (h : S.BlockLaw env M) (c : Name) (ci : ConstInfo) (hfresh : env.find? c = none) :
    S.BlockLaw (env.add c ci) M := by
  intro hpl
  obtain ⟨hS, hnc, hfind, hctors, hfam, hcs, hdoms⟩ := h hpl
  refine ⟨hS.mono fun n hn => Env.isSome_find?_add hn c ci, hnc, ?_, fun j c' hc' => ?_,
    hfam, hcs, hdoms⟩
  · rw [Env.find?_add_of_ne env ci (Env.ne_of_isSome_find? (by rw [hfind]; rfl) hfresh), hfind]
  · rw [Env.find?_add_of_ne env ci (Env.ne_of_isSome_find? (by rw [hctors j c' hc']; rfl) hfresh),
      hctors j c' hc']

/-- The block law survives adding constants in order under fresh,
distinct names. -/
theorem BlockLaw_foldl (val : CtorSpec → ConstInfo) :
    ∀ {cs : List CtorSpec} {env : Env}, S.BlockLaw env M → (∀ c ∈ cs, env.find? c.name = none) →
      (cs.map (·.name)).Nodup → S.BlockLaw (cs.foldl (fun e c => e.add c.name (val c)) env) M
  | [], _, h, _, _ => h
  | c :: cs, env, h, hfresh, hnodup => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rw [List.foldl_cons]
    refine BlockLaw_foldl val (S.BlockLaw_add h c.name (val c) (hfresh c List.mem_cons_self)) ?_
      hnodup.2
    intro c' hc'
    rw [Env.find?_add_of_ne _ _ (fun h' => hnodup.1 (by rw [← h']; exact List.mem_map_of_mem hc'))]
    exact hfresh c' (List.mem_cons_of_mem c hc')

end IndSpec

/-! ## The two installations keep the block laws -/

variable [LevelOracle]

/-- **Installing a definition preserves having a block model.** -/
theorem install_def' {env : Env} {c : Name} {ci : ConstInfo} (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : DefOk env c ci) :
    ∃ m' : BlockModel V (env.add c ci), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  obtain ⟨m', hm'⟩ := install_def hs m.toEnvModel hok
  refine ⟨{ toEnvModel := m', blocks := ?_ }, hm'⟩
  intro K ci' nP nI cs spec hfind hkind
  rw [Env.find?_add] at hfind
  split at hfind
  · cases hfind
    obtain ⟨v, T, hk, -⟩ := hok.2.2.1
    rw [hk] at hkind
    cases hkind
  · exact spec.BlockLaw_add
      (spec.BlockLaw_transport (fun n hn ls => (hm' n hn ls).symm)
        (m.blocks K ci' nP nI cs spec hfind hkind)) c ci hok.1

/-- **Installing a plain inductive block preserves having a block
model**, and the new block satisfies its law (the model of
`Install.lean`). -/
theorem install_ind' {env : Env} {S : IndSpec} (hpl : S.nest = none) (hs : Env.Scoped env)
    (m : BlockModel V env) (hok : S.Ok env) :
    ∃ m' : BlockModel V (S.install env), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  have hagree : AgreeOn env m.M (S.M₃ m.M) := IndSpec.agree_M₃ hok m.M
  have hS := hok.scoped
  have hK := S.contScoped_of_plain (env := env) hpl
  have hA : ∀ ls, S.Agree env m.M (S.M₃ m.M) ls ls := fun ls => ⟨hS, hK, hagree, rfl⟩
  have hmono : ∀ n, (env.find? n).isSome → ((S.install env).find? n).isSome := by
    intro n hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [S.find?_mono_install hpl env hok.fresh hci]
    rfl
  have hinst : S.install env = (S.envCtors env).add S.recName S.recInfo := by
    simp only [IndSpec.install, hpl]
  -- the block's names are fresh along the way
  have hfreshC : ∀ c ∈ S.ctors, (S.envInd env).find? c.name = none := by
    intro c hc
    rw [S.envInd_find?, ite_eq_right fun h => hok.name_not_mem (by
      rw [← h]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hc))]
    exact hok.fresh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)))
  have hfreshR : (S.envCtors env).find? S.recName = none := by
    rw [S.envCtors_find? env hok.nodup_ctors, hok.ctorOf?_rec, S.envInd_find?,
      ite_eq_right hok.name_ne_rec.symm]
    exact hok.fresh _ (List.mem_cons_of_mem _ List.mem_cons_self)
  -- the universe bound on the fields at every level list and fitting parameters, in the old model
  have hnc : S.NoCont := S.noCont_of_plain hpl hS
  have hbO : ∀ ls ps, FitsVals m.M (S.ψ ls) base S.params ps → S.DomsBounded m.M ls ps := by
    intro ls ps hp
    have hB : S.Agree env m.M m.M ls (S.lparams.map (S.ψ ls)) :=
      ⟨hS, hK, fun _ _ _ => rfl, (valOf_map_valOf S.lparams ls).symm⟩
    have hps : ps.length = S.nP := FitsVals_length m.M (S.ψ ls) hp
    exact hB.symm.domsBounded_imp ps
      (IndSpec.domsBounded_of hpl hs m.toEnvModel hok (S.ψ ls) base hps ((hB.fitsParams_iff ps).mp hp))
  refine ⟨{ toEnvModel := IndSpec.mInstall hpl hs m.toEnvModel hok, blocks := ?_ },
    fun n hn ls => (hagree n hn ls).symm⟩
  intro K ci nP nI cs spec hfind hkind
  show spec.BlockLaw (S.install env) (S.M₃ m.M)
  rw [S.install_find? hpl] at hfind
  split at hfind
  · -- the new recursor is not a block
    cases hfind
    simp [IndSpec.recInfo] at hkind
  · rw [S.envCtors_find? env hok.nodup_ctors] at hfind
    split at hfind
    · -- a new constructor is not a block
      cases hfind
      simp [IndSpec.ctorInfo] at hkind
    · rw [S.envInd_find?] at hfind
      split at hfind
      · -- the new block: its law
        rename_i hKn
        subst hKn
        cases hfind
        simp only [IndSpec.indInfo, ConstKind.induct.injEq] at hkind
        obtain ⟨-, -, -, rfl⟩ := hkind
        intro _
        refine ⟨hS.mono hmono, hnc, ?_, fun j c hc => ?_, fun ls => ?_,
          fun j c hc ls => ?_, fun ls ps hp => ?_⟩
        · rw [S.install_find? hpl, ite_eq_right hok.name_ne_rec, S.envCtors_find? env hok.nodup_ctors,
            hok.ctorOf?_name, S.envInd_find?, ite_eq_left rfl]
        · rw [S.install_find? hpl, ite_eq_right (hok.ctor_ne_rec hc),
            S.envCtors_find? env hok.nodup_ctors, S.ctorOf?_of_getElem? hok.nodup_ctors hc]
        · rw [(IndSpec.reader₃ hok m.M fun _ => 0).R.fam ls, ← S.famSet_eq_famSetF, (hA ls).famSet_eq]
        · rw [(IndSpec.reader₃ hok m.M fun _ => 0).ctor j c hc ls,
            (hA ls).ctorSet_eq j (List.mem_of_getElem? hc)]
        · -- the domains' bound: the checker's, at the block's own valuation
          exact (hA ls).domsBounded_imp ps (hbO ls ps (((hA ls).fitsParams_iff ps).mpr hp))
      · -- an old block: its law, transported and grown
        have h₁ := spec.BlockLaw_transport hagree (m.blocks K ci nP nI cs spec hfind hkind)
        have h₂ := spec.BlockLaw_add h₁ S.name S.indInfo hok.freshI
        have h₃ := spec.BlockLaw_foldl S.ctorInfo h₂ hfreshC hok.nodup_ctors
        rw [hinst]
        exact spec.BlockLaw_add h₃ S.recName S.recInfo hfreshR

end Fragment
