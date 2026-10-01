module

public import Fragment.InstallDef
public import Fragment.Read

@[expose] public section

/-!
# Scope of an installed block

The syntactic half of installing an inductive block: what the
installed environment (`IndSpec.install`, `Decl.lean`) stores under
each name, and that every stored term of it is in scope of it
(`Env.Scoped`, `InstallDef.lean`).

* **Lookups.**  The former is found in `envInd`, a constructor in
  `envCtors` (by name, through `ctorOf?`, `IndSem.lean`), the recursor
  in `install`; every other name is found as before.  The block's
  names are distinct and fresh (`IndSpec.Ok`), so a fold of `Env.add`s
  over the constructors reads like a lookup table.
* **Scope of the generated terms.**  The generated types use only the
  block's level parameters (the recursor's type and rules the
  recursor's, which hold the elimination parameter too); a rule's
  right-hand side is closed and mentions only stored constants — its
  context is the rule type's, which the checker infers in the empty
  context, and its body mentions the recursor, the specification's
  expressions and variables.
* **The installed environment is closed** (`Env.Scoped.install`):
  three `Env.Scoped.add`s — the former, the constructors in order, the
  recursor — each fed by the `Infer` facts of `IndSpec.Ok` at the
  environment the checker inferred in.
-/

namespace Fragment

/-! ## Level parameters are monotone -/

namespace Level

/-- A level over `ps` is a level over any `qs ⊇ ps`. -/
theorem paramsIn_mono {ps qs : List Name} (h : ps ⊆ qs) :
    ∀ {l : Level}, paramsIn ps l = true → paramsIn qs l = true
  | zero, _ => rfl
  | succ l, hl => paramsIn_mono h (l := l) hl
  | max a b, hl => by
    simp only [paramsIn_max, Bool.and_eq_true] at hl ⊢
    exact ⟨paramsIn_mono h hl.1, paramsIn_mono h hl.2⟩
  | imax a b, hl => by
    simp only [paramsIn_imax, Bool.and_eq_true] at hl ⊢
    exact ⟨paramsIn_mono h hl.1, paramsIn_mono h hl.2⟩
  | param n, hl => by
    rw [paramsIn_param, List.contains_iff_mem] at hl ⊢
    exact h hl

end Level

namespace PropWhen

/-- A datum over `ps` is a datum over any `qs ⊇ ps`. -/
theorem paramsIn_mono {ps qs : List Name} (h : ps ⊆ qs) :
    ∀ {pw : PropWhen}, paramsIn ps pw = true → paramsIn qs pw = true
  | never, _ => rfl
  | whenZero s, hs => by
    simp only [paramsIn_whenZero, List.all_eq_true, List.contains_iff_mem] at hs ⊢
    exact fun n hn => h (hs n hn)

end PropWhen

namespace Expr

/-- A term over `ps` is a term over any `qs ⊇ ps`. -/
theorem lparamsIn_mono {ps qs : List Name} (h : ps ⊆ qs) :
    ∀ {e : Expr}, lparamsIn ps e = true → lparamsIn qs e = true
  | bvar _, _ => rfl
  | sort u, hu => by
    rw [lparamsIn_sort] at hu ⊢
    exact Level.paramsIn_mono h hu
  | const _ ls, hl => by
    simp only [lparamsIn_const, List.all_eq_true] at hl ⊢
    exact fun l hl' => Level.paramsIn_mono h (hl l hl')
  | app f a, he => by
    simp only [lparamsIn_app, Bool.and_eq_true] at he ⊢
    exact ⟨lparamsIn_mono h he.1, lparamsIn_mono h he.2⟩
  | lam A pw b, he => by
    simp only [lparamsIn_lam, Bool.and_eq_true] at he ⊢
    exact ⟨⟨lparamsIn_mono h he.1.1, PropWhen.paramsIn_mono h he.1.2⟩, lparamsIn_mono h he.2⟩
  | pi A pw B, he => by
    simp only [lparamsIn_pi, Bool.and_eq_true] at he ⊢
    exact ⟨⟨lparamsIn_mono h he.1.1, PropWhen.paramsIn_mono h he.1.2⟩, lparamsIn_mono h he.2⟩

/-- The parameters of `ps`, as levels, are levels over `ps`. -/
theorem lparamsIn_const_params (ps : List Name) (c : Name) :
    lparamsIn ps (const c (ps.map .param)) = true := by
  simp only [lparamsIn_const, List.all_eq_true, List.mem_map]
  rintro l ⟨n, hn, rfl⟩
  rw [Level.paramsIn_param, List.contains_iff_mem]
  exact hn

/-- The body's constants are among its `∀`-telescope's. -/
theorem consts_mkPis_body (pw : PropWhen) :
    ∀ (Γ : List Expr) (b : Expr) {c : Name}, c ∈ consts b → c ∈ consts (mkPis pw Γ b)
  | [], _, _, hc => hc
  | B :: Γ, b, c, hc => by
    rw [mkPis_cons]
    exact consts_mkPis_body pw Γ (pi B pw b) (by rw [consts_pi]; exact List.mem_append_right _ hc)

/-- A context entry's constants are among its `∀`-telescope's. -/
theorem consts_mkPis_of (pw : PropWhen) :
    ∀ (Γ : List Expr) (b : Expr) {A : Expr} {c : Name}, A ∈ Γ → c ∈ consts A →
      c ∈ consts (mkPis pw Γ b)
  | [], _, _, _, hA, _ => absurd hA List.not_mem_nil
  | B :: Γ, b, A, c, hA, hc => by
    rw [mkPis_cons]
    rcases List.mem_cons.mp hA with rfl | hA
    · exact consts_mkPis_body pw Γ (pi A pw b)
        (by rw [consts_pi]; exact List.mem_append_left _ hc)
    · exact consts_mkPis_of pw Γ (pi B pw b) hA hc

end Expr

/-! ## Lookups after a fold of adds -/

namespace Env

/-- After adding constants under names none of which is `n`, `n` is
found as before. -/
theorem find?_foldl_add_of_not_mem (val : CtorSpec → ConstInfo) {n : Name} :
    ∀ {cs : List CtorSpec} (env : Env), (∀ c ∈ cs, c.name ≠ n) →
      (cs.foldl (fun e c => e.add c.name (val c)) env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, h => by
    rw [List.foldl_cons,
      find?_foldl_add_of_not_mem val (env.add c.name (val c))
        (fun c' hc' => h c' (List.mem_cons_of_mem c hc')),
      find?_add_of_ne env _ (h c List.mem_cons_self).symm]

/-- After adding constants under distinct names, a name among them is
found with its constant. -/
theorem find?_foldl_add_of_mem (val : CtorSpec → ConstInfo) {c : CtorSpec} :
    ∀ {cs : List CtorSpec} (env : Env), (cs.map (·.name)).Nodup → c ∈ cs →
      (cs.foldl (fun e c => e.add c.name (val c)) env).find? c.name = some (val c)
  | [], _, _, hc => absurd hc List.not_mem_nil
  | c' :: cs, env, hnodup, hc => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [find?_foldl_add_of_not_mem val _ (fun d hd h => hnodup.1 (by
          rw [← h]; exact List.mem_map_of_mem hd)),
        find?_add_self]
    · exact find?_foldl_add_of_mem val _ hnodup.2 hc

end Env

/-! ## Lookups in the installed environment -/

namespace IndSpec

variable (S : IndSpec)

/-- The environment with the former: the former under its name, the
rest as before. -/
theorem envInd_find? (env : Env) (n : Name) :
    (S.envInd env).find? n = if n = S.name then some S.indInfo else env.find? n :=
  Env.find?_add env S.name n S.indInfo

/-- `ctorOf?` (`IndSem.lean`) finds a constructor by name, with its
number. -/
theorem ctorOf?_some {n : Name} {j : Nat} {c : CtorSpec} (h : S.ctorOf? n = some (j, c)) :
    S.ctors[j]? = some c ∧ c.name = n := by
  obtain ⟨j', _, hj'⟩ := List.exists_of_findSome?_eq_some h
  revert hj'
  split
  · rename_i c' hc'
    split
    · rename_i hn
      intro hj'
      simp only [Option.some.injEq, Prod.mk.injEq] at hj'
      obtain ⟨rfl, rfl⟩ := hj'
      exact ⟨hc', hn⟩
    · intro h; simp at h
  · intro h; simp at h

/-- With distinct constructor names, `ctorOf?` finds constructor `j`
under its name. -/
theorem ctorOf?_of_getElem? {j : Nat} {c : CtorSpec} (hnodup : (S.ctors.map (·.name)).Nodup)
    (h : S.ctors[j]? = some c) : S.ctorOf? c.name = some (j, c) := by
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp h).1
  -- The search finds `j`: any earlier hit would be a second constructor of the same name.
  have key : ∀ (js : List Nat), j ∈ js →
      (js.findSome? fun j' => match S.ctors[j']? with
        | some c' => if c'.name = c.name then some (j', c') else none
        | none => none) = some (j, c) := by
    intro js
    induction js with
    | nil => intro h; simp at h
    | cons j' js ih =>
      intro hj'
      rw [List.findSome?_cons]
      by_cases hjj : j' = j
      · subst hjj
        simp [h]
      · rcases List.mem_cons.mp hj' with h' | h'
        · exact absurd h'.symm hjj
        · have hnone : (match S.ctors[j']? with
              | some c' => if c'.name = c.name then some (j', c') else none
              | none => none) = none := by
            split
            · rename_i c' hc'
              rw [if_neg]
              intro hn
              apply hjj
              rw [← List.getElem?_inj (l := S.ctors.map (·.name)) (i := j') (j := j)
                (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hc').1) hnodup]
              rw [List.getElem?_map, List.getElem?_map, hc', h, Option.map_some, Option.map_some,
                hn]
            · rfl
          rw [hnone]
          exact ih h'
  exact key _ (List.mem_range.mpr hj)

/-- A name that is no constructor's is not found by `ctorOf?`. -/
theorem ctorOf?_none {n : Name} (h : ∀ c ∈ S.ctors, c.name ≠ n) : S.ctorOf? n = none := by
  rw [ctorOf?, List.findSome?_eq_none_iff]
  intro j _
  split
  · rename_i c hc
    rw [if_neg (h c (List.mem_of_getElem? hc))]
  · rfl

/-- `ctorOf?` finds nothing exactly when no constructor has the name. -/
theorem ctorOf?_eq_none_iff {n : Name} : S.ctorOf? n = none ↔ ∀ c ∈ S.ctors, c.name ≠ n := by
  refine ⟨fun h c hc hn => ?_, S.ctorOf?_none⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
  rw [ctorOf?, List.findSome?_eq_none_iff] at h
  have := h j (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1)
  simp [hj, hn] at this

/-- The environment with the former and the constructors: a
constructor under its name, the rest as in `envInd`. -/
theorem envCtors_find? (env : Env) (hnodup : (S.ctors.map (·.name)).Nodup) (n : Name) :
    (S.envCtors env).find? n =
      match S.ctorOf? n with
      | some (_, c) => some (S.ctorInfo c)
      | none => (S.envInd env).find? n := by
  unfold envCtors
  split
  · rename_i j c hjc
    obtain ⟨hj, rfl⟩ := S.ctorOf?_some hjc
    exact Env.find?_foldl_add_of_mem S.ctorInfo _ hnodup (List.mem_of_getElem? hj)
  · rename_i hnone
    exact Env.find?_foldl_add_of_not_mem S.ctorInfo _ (S.ctorOf?_eq_none_iff.mp hnone)

/-- The installed environment: the recursor under its name, the rest
as in `envCtors`. -/
theorem install_find? (hpl : S.nest = none) (env : Env) (n : Name) :
    (S.install env).find? n =
      if n = S.recName then some S.recInfo else (S.envCtors env).find? n := by
  simp only [install, hpl]
  exact Env.find?_add _ S.recName n S.recInfo

/-- The installed nested environment: the auxiliary recursor, the
recursor, the rest as in `envCtors`. -/
theorem installN_find? (N : NestInfo) (env : Env) (n : Name) :
    (S.installN N env).find? n =
      if n = N.aux then some (S.rec1Info N)
      else if n = S.recName then some (S.recInfoN N) else (S.envCtors env).find? n := by
  unfold installN
  rw [Env.find?_add, Env.find?_add]

/-- A stored name is found as before in `envInd`, when the block's
names are fresh. -/
theorem find?_mono_envInd (env : Env) (hfresh : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none)
    {n : Name} {ci : ConstInfo} (h : env.find? n = some ci) : (S.envInd env).find? n = some ci := by
  rw [envInd_find?, if_neg, h]
  rintro rfl
  rw [hfresh S.name List.mem_cons_self] at h
  cases h

/-- A stored name is found as before in `envCtors`, when the block's
names are fresh. -/
theorem find?_mono_envCtors (env : Env) (hfresh : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none)
    {n : Name} {ci : ConstInfo} (h : env.find? n = some ci) :
    (S.envCtors env).find? n = some ci := by
  unfold envCtors
  rw [Env.find?_foldl_add_of_not_mem S.ctorInfo _ fun c hc hn => ?_]
  · exact S.find?_mono_envInd env hfresh h
  · rw [hfresh n (by
      rw [← hn]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)))] at h
    cases h

/-- A stored name is found as before in the installed environment,
when the block's names are fresh. -/
theorem find?_mono_install (hpl : S.nest = none) (env : Env)
    (hfresh : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none)
    {n : Name} {ci : ConstInfo} (h : env.find? n = some ci) :
    (S.install env).find? n = some ci := by
  rw [install_find? S hpl, if_neg, S.find?_mono_envCtors env hfresh h]
  rintro rfl
  rw [hfresh S.recName (List.mem_cons_of_mem _ List.mem_cons_self)] at h
  cases h

/-! ## Scope of the generated terms -/

section Generated

variable {env : Env}

/-- The block's level parameters are among the recursor's. -/
theorem lparams_sub_recLparams : S.lparams ⊆ S.recLparams := by
  unfold recLparams
  split
  · exact List.subset_cons_of_subset _ (List.Subset.refl _)
  · exact List.Subset.refl _

/-- The elimination level is over the recursor's parameters. -/
theorem ℓ_paramsIn : S.ℓ.paramsIn S.recLparams = true := by
  unfold ℓ recLparams
  split
  · simp
  · rfl

/-- The recursor's annotation is over the recursor's parameters. -/
theorem q_paramsIn : S.q.paramsIn S.recLparams = true := Level.zeroness_paramsIn S.ℓ_paramsIn

/-- The family's annotation is over the block's parameters. -/
theorem pw_paramsIn (hS : S.Scoped env) : S.pw.paramsIn S.lparams = true :=
  Level.zeroness_paramsIn hS.2.2.1

/-- A constant at the block's levels is over the block's parameters. -/
theorem lparamsIn_const_lvls (c : Name) : (Expr.const c S.lvls).lparamsIn S.lparams = true :=
  Expr.lparamsIn_const_params _ _

/-- A constant at the recursor's levels is over the recursor's
parameters. -/
theorem lparamsIn_const_recLvls (c : Name) :
    (Expr.const c S.recLvls).lparamsIn S.recLparams = true :=
  Expr.lparamsIn_const_params _ _

/-- The family at the parameter variables and index expressions over
the block's parameters. -/
theorem lparamsIn_famAt (o : Nat) {es : List Expr} (hes : ∀ e ∈ es, e.lparamsIn S.lparams = true) :
    (S.famAt o es).lparamsIn S.lparams = true := by
  unfold famAt
  refine Expr.lparamsIn_mkAppN (S.lparamsIn_const_lvls _) fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha
  · exact Expr.lparamsIn_varsAt _ _ _ a ha
  · exact hes a ha

/-- The family at variables. -/
theorem lparamsIn_famVars (e : Nat) : (S.famVars e).lparamsIn S.lparams = true :=
  S.lparamsIn_famAt _ (Expr.lparamsIn_varsAt _ _ _)

/-- Every parameter's domain is over the block's parameters. -/
theorem lparamsIn_params (hS : S.Scoped env) : ∀ A ∈ S.params, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hA
  exact (hS.1 i A hi).2.2

/-- Every index's domain is over the block's parameters. -/
theorem lparamsIn_indices (hS : S.Scoped env) : ∀ T ∈ S.indices, T.lparamsIn S.lparams = true := by
  intro T hT
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hT
  exact (hS.2.1 t T ht).2.2

/-- The class's arguments are over the block's parameters. -/
theorem lparamsIn_classArgs (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) (o : Nat) :
    ∀ e ∈ S.classArgs N o, e.lparamsIn S.lparams = true := by
  have hNS := hS.2.2.2.2.2.2 N hN
  intro e he
  simp only [classArgs, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with (⟨a, ha, rfl⟩ | rfl) | ⟨a, ha, rfl⟩
  · rw [Expr.lparamsIn_liftN]; exact (hNS.2.2.2.2.2.2.1 a (List.mem_of_mem_take ha)).2.2
  · refine S.lparamsIn_famAt _ fun e he => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    rw [Expr.lparamsIn_liftN]; exact (hNS.2.2.2.2.2.2.2.1 a ha).2.2
  · rw [Expr.lparamsIn_liftN]; exact (hNS.2.2.2.2.2.2.1 a (List.mem_of_mem_drop ha)).2.2

/-- The class is over the block's parameters. -/
theorem lparamsIn_classTy (hS : S.Scoped env) {N : NestInfo} (hN : S.nest = some N) (o : Nat) :
    (S.classTy N o).lparamsIn S.lparams = true := by
  have hNS := hS.2.2.2.2.2.2 N hN
  refine Expr.lparamsIn_mkAppN ?_ (S.lparamsIn_classArgs hS hN o)
  simp only [Expr.lparamsIn_const, List.all_eq_true]
  exact hNS.2.2.2.1

/-- A field's domain, at any number of earlier fields, is over the
block's parameters. -/
theorem lparamsIn_fieldDom (hS : S.Scoped env) {k : Nat} {f : Field} (hf : S.fieldScoped env k f)
    (k' : Nat) : (S.fieldDom k' f).lparamsIn S.lparams = true := by
  cases f with
  | container =>
    obtain ⟨N, hN⟩ := Option.isSome_iff_exists.mp hf
    simp only [fieldDom, hN]
    exact S.lparamsIn_classTy hS hN k'
  | ordinary A => exact hf.2.2
  | recursive es => exact S.lparamsIn_famAt _ fun e he => (hf.2 e he).2.2
  | reflexive tele es =>
    refine Expr.lparamsIn_mkPis (S.pw_paramsIn hS) (fun T hT => ?_)
      (S.lparamsIn_famAt _ fun e he => (hf.2.2 e he).2.2)
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hT
    exact (hf.1 t T ht).2.2

/-- An entry of a field context is a field's domain under the fields
below it. -/
theorem mem_fieldCtx {fs : List Field} {A : Expr} (h : A ∈ S.fieldCtx fs) :
    ∃ i f, fs[i]? = some f ∧ A = S.fieldDom (fs.length - 1 - i) f := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [fieldCtx_getElem?, Option.map_eq_some_iff] at hi
  obtain ⟨f, hf, rfl⟩ := hi
  exact ⟨i, f, hf, rfl⟩

/-- The scope of a constructor's field at position `i`. -/
theorem fieldScoped_of_getElem? (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) {i : Nat}
    {f : Field} (hi : c.fields[i]? = some f) : S.fieldScoped env (c.fields.length - 1 - i) f :=
  (hS.2.2.2.1 c hc).1 i f hi

/-- The scope of a recursive position's field: `kf.1` earlier fields. -/
theorem fieldScoped_of_mem_recFields (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors)
    {kf : Nat × Field} (h : kf ∈ c.recFields) :
    S.fieldScoped env kf.1 kf.2 ∧ kf.1 < c.fields.length := by
  obtain ⟨hf, hk, _⟩ := mem_recFields h
  have := S.fieldScoped_of_getElem? hS hc hf
  rw [show c.fields.length - 1 - (c.fields.length - 1 - kf.1) = kf.1 by omega] at this
  exact ⟨this, hk⟩

/-- A constructor's field context is over the block's parameters. -/
theorem lparamsIn_fieldCtx (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ A ∈ S.fieldCtx c.fields, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨i, f, hi, rfl⟩ := S.mem_fieldCtx hA
  exact S.lparamsIn_fieldDom hS (S.fieldScoped_of_getElem? hS hc hi) _

/-- A constructor's index expressions are over the block's
parameters. -/
theorem lparamsIn_idx (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ e ∈ c.idx, e.lparamsIn S.lparams = true :=
  fun e he => ((hS.2.2.2.1 c hc).2.2.2 e he).2.2

/-- **The former's type uses the block's level parameters.** -/
theorem lparamsIn_indType (hS : S.Scoped env) : S.indType.lparamsIn S.lparams = true := by
  unfold indType
  refine Expr.lparamsIn_mkPis rfl (fun A hA => ?_) ?_
  · rcases List.mem_append.mp hA with hA | hA
    · exact S.lparamsIn_indices hS A hA
    · exact S.lparamsIn_params hS A hA
  · rw [Expr.lparamsIn_sort]
    exact hS.2.2.1

/-- **A constructor's type uses the block's level parameters.** -/
theorem lparamsIn_ctorType (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    (S.ctorType c).lparamsIn S.lparams = true := by
  unfold ctorType
  refine Expr.lparamsIn_mkPis (S.pw_paramsIn hS) (fun A hA => ?_)
    (S.lparamsIn_famAt _ (S.lparamsIn_idx hS hc))
  rcases List.mem_append.mp hA with hA | hA
  · exact S.lparamsIn_fieldCtx hS hc A hA
  · exact S.lparamsIn_params hS A hA

/-- The motive's type uses the recursor's level parameters (the
elimination level is one of them). -/
theorem lparamsIn_motiveTy (hS : S.Scoped env) : S.motiveTy.lparamsIn S.recLparams = true := by
  unfold motiveTy
  refine Expr.lparamsIn_mkPis rfl (fun A hA => ?_) ?_
  · rcases List.mem_cons.mp hA with rfl | hA
    · exact Expr.lparamsIn_mono S.lparams_sub_recLparams (S.lparamsIn_famVars 0)
    · exact Expr.lparamsIn_mono S.lparams_sub_recLparams (S.lparamsIn_indices hS A hA)
  · rw [Expr.lparamsIn_sort]
    exact S.ℓ_paramsIn

/-- An inductive hypothesis' type uses the recursor's level
parameters. -/
theorem lparamsIn_ihTy {k : Nat} {f : Field} (hf : S.fieldScoped env k f) (nF k' l o : Nat) :
    (S.ihTy nF k' l o f).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  cases f with
  | ordinary A => rfl
  | container => rfl
  | recursive es =>
    refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (hf.2 e he).2.2
    · rw [List.mem_singleton] at ha
      subst ha
      rfl
  | reflexive tele es =>
    simp only [ihTy]
    refine Expr.lparamsIn_mkPis S.q_paramsIn (fun T hT => ?_) ?_
    · obtain ⟨t, T', ht, rfl⟩ := Expr.mem_liftCtx hT
      rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (hf.1 t T' ht).2.2
    · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        rw [Expr.lparamsIn_atCtx]
        exact Expr.lparamsIn_mono hR (hf.2.2 e he).2.2
      · rw [List.mem_singleton] at ha
        subst ha
        exact Expr.lparamsIn_mkAppN rfl (Expr.lparamsIn_varsAt _ _ _)

/-- An entry of the inductive hypotheses' context is a hypothesis' type
at a recursive position. -/
theorem mem_ihCtx {c : CtorSpec} {j : Nat} {A : Expr} (h : A ∈ S.ihCtx c j) :
    ∃ kf ∈ c.recFields, ∃ l, A = S.ihTy c.fields.length kf.1 l (j + 1) kf.2 := by
  rw [ihCtx, List.mem_reverse, List.mem_mapIdx] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨_, List.getElem_mem hl, l, rfl⟩

/-- A constructor's field context, moved under `o` binders, is over
the block's parameters. -/
theorem lparamsIn_fieldCtxAt (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) (o : Nat) :
    ∀ A ∈ S.fieldCtxAt c o, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨i, A', hi, rfl⟩ := Expr.mem_liftCtx hA
  rw [Expr.lparamsIn_liftN]
  exact S.lparamsIn_fieldCtx hS hc A' (List.mem_of_getElem? hi)

/-- A minor premise uses the recursor's level parameters. -/
theorem lparamsIn_minorTy (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) (j : Nat) :
    (S.minorTy c j).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  simp only [minorTy]
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨kf, hkf, l, rfl⟩ := S.mem_ihCtx hA
      exact S.lparamsIn_ihTy (S.fieldScoped_of_mem_recFields hS hc hkf).1 _ _ _ _
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

/-- An entry of the minors' context is a minor premise of a
constructor. -/
theorem mem_minorsCtx {A : Expr} (h : A ∈ S.minorsCtx) :
    ∃ j c, S.ctors[j]? = some c ∧ A = S.minorTy c j := by
  rw [minorsCtx, List.mem_reverse, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, S.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- The minors' context uses the recursor's level parameters. -/
theorem lparamsIn_minorsCtx (hS : S.Scoped env) :
    ∀ A ∈ S.minorsCtx, A.lparamsIn S.recLparams = true := by
  intro A hA
  obtain ⟨j, c, hj, rfl⟩ := S.mem_minorsCtx hA
  exact S.lparamsIn_minorTy hS (List.mem_of_getElem? hj) j

/-- The index context, moved under `o` binders, is over the block's
parameters. -/
theorem lparamsIn_indicesAt (hS : S.Scoped env) (o : Nat) :
    ∀ A ∈ S.indicesAt o, A.lparamsIn S.lparams = true := by
  intro A hA
  obtain ⟨t, T, ht, rfl⟩ := Expr.mem_liftCtx hA
  rw [Expr.lparamsIn_liftN]
  exact S.lparamsIn_indices hS T (List.mem_of_getElem? ht)

/-- **The recursor's type uses the recursor's level parameters.** -/
theorem lparamsIn_recType (hS : S.Scoped env) : S.recType.lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  unfold recType
  refine Expr.lparamsIn_mkPis S.q_paramsIn (fun A hA => ?_) ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with (((rfl | hA) | hA) | rfl) | hA
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_famVars _)
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_indicesAt hS _ A hA)
    · exact S.lparamsIn_minorsCtx hS A hA
    · exact S.lparamsIn_motiveTy hS
    · exact Expr.lparamsIn_mono hR (S.lparamsIn_params hS A hA)
  · refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · rw [List.mem_singleton] at ha
      subst ha
      rfl

/-- A rule's context uses the recursor's level parameters. -/
theorem lparamsIn_ruleCtx (hS : S.Scoped env) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ A ∈ S.ruleCtx c, A.lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  intro A hA
  simp only [ruleCtx, List.mem_append, List.mem_singleton] at hA
  rcases hA with ((hA | hA) | rfl) | hA
  · exact Expr.lparamsIn_mono hR (S.lparamsIn_fieldCtxAt hS hc _ A hA)
  · exact S.lparamsIn_minorsCtx hS A hA
  · exact S.lparamsIn_motiveTy hS
  · exact Expr.lparamsIn_mono hR (S.lparamsIn_params hS A hA)

/-- An inductive hypothesis' value uses the recursor's level
parameters. -/
theorem lparamsIn_ihVal {k : Nat} {f : Field} (hf : S.fieldScoped env k f) (nF k' : Nat) :
    (S.ihVal nF k' f).lparamsIn S.recLparams = true := by
  have hR := S.lparams_sub_recLparams
  cases f with
  | ordinary A => rfl
  | container => rfl
  | recursive es =>
    simp only [ihVal]
    refine Expr.lparamsIn_mkAppN (S.lparamsIn_const_recLvls _) fun a ha => ?_
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
    rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · rfl
    · exact Expr.lparamsIn_varsAt _ _ _ a ha
    · rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (hf.2 e he).2.2
    · rfl
  | reflexive tele es =>
    simp only [ihVal]
    refine Expr.lparamsIn_mkLams S.q_paramsIn (fun T hT => ?_) ?_
    · obtain ⟨t, T', ht, rfl⟩ := Expr.mem_liftCtx hT
      rw [Expr.lparamsIn_atCtx]
      exact Expr.lparamsIn_mono hR (hf.1 t T' ht).2.2
    · refine Expr.lparamsIn_mkAppN (S.lparamsIn_const_recLvls _) fun a ha => ?_
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
      · exact Expr.lparamsIn_varsAt _ _ _ a ha
      · rfl
      · exact Expr.lparamsIn_varsAt _ _ _ a ha
      · rw [Expr.lparamsIn_atCtx]
        exact Expr.lparamsIn_mono hR (hf.2.2 e he).2.2
      · exact Expr.lparamsIn_mkAppN rfl (Expr.lparamsIn_varsAt _ _ _)

/-- **A rule's right-hand side uses the recursor's level parameters.** -/
theorem lparamsIn_ruleRhs (hS : S.Scoped env) {c : CtorSpec} {j : Nat} (hc : S.ctors[j]? = some c) :
    (S.ruleRhs c j).lparamsIn S.recLparams = true := by
  have hc' := List.mem_of_getElem? hc
  simp only [ruleRhs]
  refine Expr.lparamsIn_mkLams S.q_paramsIn (S.lparamsIn_ruleCtx hS hc') ?_
  refine Expr.lparamsIn_mkAppN rfl fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha
  · exact Expr.lparamsIn_varsAt _ _ _ a ha
  · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
    exact S.lparamsIn_ihVal (S.fieldScoped_of_mem_recFields hS hc' hkf).1 _ _

/-! ### A rule's right-hand side is closed and mentions stored constants -/

/-- Moving a field context under binders keeps its length. -/
theorem length_fieldCtxAt (c : CtorSpec) (o : Nat) : (S.fieldCtxAt c o).length = c.fields.length := by
  rw [fieldCtxAt, Expr.length_liftCtx, length_fieldCtx]

/-- A rule's context holds the fields, the minors, the motive and the
parameters. -/
theorem length_ruleCtx (c : CtorSpec) : (S.ruleCtx c).length = c.fields.length + S.n + 1 + S.nP := by
  simp [ruleCtx, length_fieldCtxAt, length_minorsCtx, nP]
  omega

/-- An inductive hypothesis' value is closed under a rule's context. -/
theorem closedAt_ihVal {k : Nat} {f : Field} (hf : S.fieldScoped env k f) {nF : Nat} (hk : k ≤ nF) :
    (S.ihVal nF k f).closedAt (nF + S.n + 1 + S.nP) = true := by
  cases f with
  | ordinary A => rfl
  | container => rfl
  | recursive es =>
    simp only [ihVal]
    refine Expr.closedAt_mkAppN rfl fun a ha => ?_
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
    rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
    · exact Expr.closedAt_varsAt (by omega) a ha
    · rw [Expr.closedAt_bvar, decide_eq_true_eq]
      omega
    · exact Expr.closedAt_varsAt (by omega) a ha
    · exact Expr.closedAt_mono (by omega)
        (Expr.closedAt_atCtx (j := S.nP + k) (d := 0) (hf.2 e he).1)
    · rw [Expr.closedAt_bvar, decide_eq_true_eq]
      omega
  | reflexive tele es =>
    simp only [ihVal]
    refine Expr.closedAt_mkLams (fun t T hT => ?_) ?_
    · rw [Expr.liftCtx_getElem?, Option.map_eq_some_iff] at hT
      obtain ⟨T', hT', rfl⟩ := hT
      rw [Expr.length_liftCtx]
      exact Expr.closedAt_mono (by omega)
        (Expr.closedAt_atCtx (j := S.nP + k) (d := tele.length - 1 - t) (hf.1 t T' hT').1)
    · rw [Expr.length_liftCtx]
      refine Expr.closedAt_mkAppN rfl fun a ha => ?_
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
      · exact Expr.closedAt_varsAt (by omega) a ha
      · rw [Expr.closedAt_bvar, decide_eq_true_eq]
        omega
      · exact Expr.closedAt_varsAt (by omega) a ha
      · exact Expr.closedAt_mono (by omega)
          (Expr.closedAt_atCtx (j := S.nP + k) (d := tele.length) (hf.2.2 e he).1)
      · refine Expr.closedAt_mkAppN ?_ (Expr.closedAt_varsAt (by omega))
        rw [Expr.closedAt_bvar, decide_eq_true_eq]
        omega

/-- **A rule's right-hand side is closed**: its context is the rule
type's, inferred in the empty context, and its body is a variable
applied to variables and inductive hypotheses' values. -/
theorem closedAt_ruleRhs [LevelOracle] (hS : S.Scoped env) {c : CtorSpec} {j : Nat}
    (hc : S.ctors[j]? = some c) (hty : ∃ T, Infer (S.envCtors env) [] (S.ruleType c) T) :
    (S.ruleRhs c j).closedAt 0 = true := by
  obtain ⟨T, hT⟩ := hty
  have h0 : (S.ruleType c).closedAt 0 = true := Infer.closedAt hT
  rw [ruleType] at h0
  have hctx := (Expr.closedAt_mkPis_iff.mp h0).1
  have hc' := List.mem_of_getElem? hc
  simp only [ruleRhs]
  refine Expr.closedAt_mkLams hctx ?_
  rw [Nat.zero_add, length_ruleCtx]
  refine Expr.closedAt_mkAppN ?_ fun a ha => ?_
  · rw [Expr.closedAt_bvar, decide_eq_true_eq]
    omega
  · rcases List.mem_append.mp ha with ha | ha
    · exact Expr.closedAt_varsAt (by omega) a ha
    · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hf, hk⟩ := S.fieldScoped_of_mem_recFields hS hc' hkf
      exact S.closedAt_ihVal hf (Nat.le_of_lt hk)

/-- An inductive hypothesis' value mentions the recursor and the
specification's constants, all stored in the installed environment. -/
theorem consts_ihVal (hpl : S.nest = none)
    (hfresh : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none)
    {k : Nat} {f : Field} (hf : S.fieldScoped env k f) (nF k' : Nat) :
    ∀ d ∈ (S.ihVal nF k' f).consts, ((S.install env).find? d).isSome := by
  have hrec : ∀ d ∈ (Expr.const S.recName S.recLvls).consts, ((S.install env).find? d).isSome := by
    intro d hd
    rw [Expr.consts_const, List.mem_singleton] at hd
    subst hd
    rw [install_find? S hpl, if_pos rfl]
    rfl
  have hspec : ∀ {e : Expr} {k'' : Nat}, Expr.Scoped env S.lparams k'' e →
      ∀ d ∈ e.consts, ((S.install env).find? d).isSome := by
    intro e k'' he d hd
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (he.2.1 d hd)
    rw [S.find?_mono_install hpl env hfresh hci]
    rfl
  cases f with
  | ordinary A => intro d hd; simp [ihVal] at hd
  | container => intro d hd; simp [ihVal] at hd
  | recursive es =>
    intro d hd
    simp only [ihVal] at hd
    rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
    rcases hd with hd | ⟨a, ha, hd⟩
    · exact hrec d hd
    · simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
      rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · simp at hd
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · rw [Expr.consts_atCtx] at hd
        exact hspec (hf.2 e he) d hd
      · simp at hd
  | reflexive tele es =>
    intro d hd
    simp only [ihVal] at hd
    rcases Expr.consts_mkLams _ _ _ d hd with hd | ⟨T, hT, hd⟩
    · rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
      rcases hd with hd | ⟨a, ha, hd⟩
      · exact hrec d hd
      · simp only [List.mem_append, List.mem_singleton, List.mem_map] at ha
        rcases ha with (((ha | rfl) | ha) | ⟨e, he, rfl⟩) | rfl
        · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
        · simp at hd
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

/-- **A rule's right-hand side mentions only stored constants**: its
context's are the rule type's (inferred), its body's are the
recursor's and the specification's. -/
theorem consts_ruleRhs [LevelOracle] (hpl : S.nest = none) (hS : S.Scoped env)
    (hfresh : ∀ m ∈ S.name :: S.recName :: S.ctors.map (·.name), env.find? m = none)
    {c : CtorSpec} {j : Nat} (hc : S.ctors[j]? = some c)
    (hty : ∃ T, Infer (S.envCtors env) [] (S.ruleType c) T) :
    ∀ d ∈ (S.ruleRhs c j).consts, ((S.install env).find? d).isSome := by
  obtain ⟨T, hT⟩ := hty
  have hc' := List.mem_of_getElem? hc
  intro d hd
  simp only [ruleRhs] at hd
  rcases Expr.consts_mkLams _ _ _ d hd with hd | ⟨A, hA, hd⟩
  · rw [Expr.consts_mkAppN, List.mem_append, List.mem_flatMap] at hd
    rcases hd with hd | ⟨a, ha, hd⟩
    · simp at hd
    · rcases List.mem_append.mp ha with ha | ha
      · rw [Expr.consts_varsAt _ _ a ha] at hd; simp at hd
      · obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp ha
        exact S.consts_ihVal hpl hfresh (S.fieldScoped_of_mem_recFields hS hc' hkf).1 _ _ d hd
  · have := Infer.consts hT d (by rw [ruleType]; exact Expr.consts_mkPis_of _ _ _ hA hd)
    simp only [install, hpl]
    exact Env.isSome_find?_add this _ _

end Generated

/-! ## The installed environment is closed -/

/-- A rule of the recursor is constructor `j`'s. -/
theorem mem_rules {rl : RecRule} (h : rl ∈ S.rules) :
    ∃ j c, S.ctors[j]? = some c ∧ rl = ⟨c.name, c.fields.length, S.ruleRhs c j, none⟩ := by
  rw [rules, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  rw [List.mem_range] at hj
  refine ⟨j, S.ctors.getD j ⟨"", [], []⟩, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- Adding constructors, in order, to a closed environment in which
their names are fresh and their types in scope keeps it closed. -/
theorem _root_.Fragment.Env.Scoped.foldl_ctors :
    ∀ {cs : List CtorSpec} {env : Env}, Env.Scoped env → (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, env.find? c.name = none) → (∀ c ∈ cs, Expr.Scoped env S.lparams 0 (S.ctorType c)) →
      Env.Scoped (cs.foldl (fun e c => e.add c.name (S.ctorInfo c)) env)
  | [], _, hs, _, _, _ => hs
  | c :: cs, env, hs, hnodup, hfresh, hty => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rw [List.foldl_cons]
    refine Env.Scoped.foldl_ctors
      (hs.add (c := c.name) (ci := S.ctorInfo c) (hfresh c List.mem_cons_self)
        (hty c List.mem_cons_self) ?_ ?_) hnodup.2 ?_ ?_
    · intro v hv
      simp [ConstInfo.value?, ctorInfo, ConstKind.value?] at hv
    · intro _ _ _ _ _ hk
      simp [ctorInfo] at hk
    · intro c' hc'
      rw [Env.find?_add_of_ne _ _ (fun h => hnodup.1 (by rw [← h]; exact List.mem_map_of_mem hc'))]
      exact hfresh c' (List.mem_cons_of_mem c hc')
    · intro c' hc'
      exact (hty c' (List.mem_cons_of_mem c hc')).add _ _

/-- **The installed environment is closed.**  The former, the
constructors in order, and the recursor are each added under a fresh
name with a type the checker inferred (closed, stored constants) over
the constant's own level parameters; the recursor's rules are closed,
mention stored constants, use the recursor's parameters and fire on
stored constructors. -/
theorem _root_.Fragment.Env.Scoped.install [LevelOracle] {env : Env} (hpl : S.nest = none)
    (hs : Env.Scoped env) (hok : S.Ok env) : Env.Scoped (S.install env) := by
  simp only [IndSpec.install, hpl]
  obtain ⟨hnodup, hfresh, hS, ⟨T₀, hind⟩, hctors, _, ⟨T₁, hrec⟩⟩ := hok
  rw [List.nodup_cons, List.nodup_cons] at hnodup
  obtain ⟨hname, hrecName, hcnodup⟩ := hnodup
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
      rw [envInd_find?, if_neg, hfresh c.name
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)))]
      intro h
      exact hname (by rw [← h]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
    · intro c hc
      obtain ⟨T, hT⟩ := (hctors c hc).1
      exact ⟨Infer.closedAt hT, Infer.consts hT, S.lparamsIn_ctorType hS hc⟩
  -- The recursor.
  refine h₂.add (c := S.recName) (ci := S.recInfo) ?_
    ⟨Infer.closedAt hrec, Infer.consts hrec, S.lparamsIn_recType hS⟩ ?_ ?_
  · rw [envCtors_find? S env hcnodup,
      ctorOf?_none S (fun c hc h => hrecName (by rw [← h]; exact List.mem_map_of_mem hc)),
      envInd_find?, if_neg (fun h => hname (by rw [← h]; exact List.mem_cons_self))]
    exact hfresh S.recName (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro v hv
    simp [ConstInfo.value?, recInfo, ConstKind.value?] at hv
  · intro nP nM nMin nI rules hk rl hrl
    simp only [recInfo, ConstKind.recursor.injEq] at hk
    obtain ⟨_, _, _, _, rfl⟩ := hk
    obtain ⟨j, c, hj, rfl⟩ := S.mem_rules hrl
    have hcj := List.mem_of_getElem? hj
    have hinst : (S.envCtors env).add S.recName S.recInfo = S.install env := by
      simp only [IndSpec.install, hpl]
    refine ⟨⟨S.closedAt_ruleRhs hS hj (hctors c hcj).2.2.2,
      hinst ▸ S.consts_ruleRhs hpl hS hfresh hj (hctors c hcj).2.2.2, S.lparamsIn_ruleRhs hS hj⟩, ?_⟩
    rw [Env.find?_add, if_neg (fun h => hrecName (by rw [← h]; exact List.mem_map_of_mem hcj)),
      envCtors_find? S env hcnodup, S.ctorOf?_of_getElem? hcnodup hj]
    rfl

end IndSpec

end Fragment
