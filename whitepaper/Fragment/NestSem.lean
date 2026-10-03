module

public import Fragment.IndSem

@[expose] public section

/-!
# The class of a nested block: monotone, bounded

What the installation of a nested block proves about its class from
the container's own model — the **one new idea** of nested blocks:

* the class at a member set `X` is the container's family at the
  instantiation with `X` at the member's position
  (`classSet_eq_Fam`: the container's set in the model is the graph
  over its parameters of its fibre, applied by β);
* **the class grows with the member set** (`contGood_of`): by
  **leastness** of the container's fixed point at the smaller member
  set — every member of the container's family at `X` is a member at
  `Y ⊇ X`, by induction over the family at `X`, because the
  container is **positive** in the member's position: a field of the
  container is the member field (its value is in `X`, hence in `Y`),
  a recursive field (the induction hypothesis), or an ordinary field
  mentioning neither (the same set at `X` and at `Y`); the member at
  `Y` is in the container's bound at `Y` because that bound is closed
  under the container's constructors;
* **the class is inside the class's bound** (`contInBound_of`): the
  closure the block's bound comes from lists the container's
  constructors at the instantiation with the member field at the
  family's bound, so, again by induction over the container's family,
  every member of the class at the family's fibre is in it.

The facts about the container these need (`NestFacts`) are what the
container's own installation left in the model (`BlockModel.lean`)
and what the nested block's checks add (the class's arguments fit,
the sorts agree, N3).

Con-leche: `Model/Inductives/ContLeaf.lean` (`monoOn_of_famLe`: a
container instance grows along a relation as soon as the carrier
does at the two key frames), `ContAcc.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLibCompat V]

/-! ## Small list and environment facts -/

omit [IndLibCompat V] in
/-- The value at the seam of a pushed list `l₁ ++ x :: l₂` is `x`. -/
theorem consList_append_cons_self (l₁ : List V) (x : V) (l₂ : List V) (ρ : Nat → V) :
    consList (l₁ ++ x :: l₂) ρ l₁.length = x := by
  rw [consList_append, ← Nat.zero_add l₁.length, consList_ge]; rfl

omit [IndLibCompat V] in
/-- Two pushed lists differing at one position read alike elsewhere. -/
theorem consList_append_cons_ne {l₁ : List V} {x y : V} {l₂ : List V} {ρ : Nat → V} {i : Nat}
    (h : i ≠ l₁.length) : consList (l₁ ++ x :: l₂) ρ i = consList (l₁ ++ y :: l₂) ρ i := by
  induction l₁ generalizing i with
  | nil =>
    cases i with
    | zero => exact absurd rfl h
    | succ j => rfl
  | cons a l₁ ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih fun e => h (by simp [e])

section Beta

variable (M : Name → List Nat → V) (φ : Name → Nat)

/-- β over a context in the graph regime needs no bound on the body
(`Read.lean` proves it again as `appList_lamCtx_false`; it comes
later in the import order). -/
theorem appList_lamCtx_false_fits :
    ∀ {Γ : List Expr} {ρ : Nat → V} {F : (Nat → V) → V} {vs : List V},
      FitsVals M φ ρ Γ vs → appList (lamCtx M φ false ρ Γ F) vs.reverse = F (consList vs ρ)
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
  | A :: Γ, ρ, F, v :: vs, h => by
    rw [FitsVals_cons] at h
    simp only [lamCtx_cons, List.reverse_cons, appList_append, appList_cons, appList_nil]
    rw [appList_lamCtx_false_fits h.1, app_lamR_false h.2]
    rfl

end Beta

namespace NestInfo

variable (N : NestInfo)

/-- **Positivity's clause for one field** at position `i` (innermost
first) of a field list: the member field, a recursive field (an empty
telescope) with no index expressions, or an ordinary field mentioning neither the member
parameter nor a later-listed (earlier) member field — `Positive`'s
match, with the constructor's field list abstracted so that it passes
to the tails. -/
def FieldPos (fields : List Field) (i : Nat) : Field → Prop
  | .ordinary A => A = Expr.bvar (N.memberVar (fields.length - 1 - i)) ∨
      (A.usesVar (N.memberVar (fields.length - 1 - i)) = false ∧
        ∀ i' f', fields[i']? = some f' → i < i' →
          N.isMember (fields.length - 1 - i') f' = true → A.usesVar (i' - i - 1) = false)
  | .reflexive tele es => tele = [] ∧ es = []
  | .container => False

theorem FieldPos_of_positive (hpos : N.Positive) {c : CtorSpec} (hc : c ∈ N.K.ctors) :
    ∀ i f, c.fields[i]? = some f → N.FieldPos c.fields i f := by
  intro i f hf
  have := (hpos.2.2.2.2 c hc).2 i f hf
  cases f <;> exact this

/-- The clause passes to the tail of the field list. -/
theorem FieldPos_tail {f : Field} {rest : List Field}
    (h : ∀ i f', (f :: rest)[i]? = some f' → N.FieldPos (f :: rest) i f') :
    ∀ i f', rest[i]? = some f' → N.FieldPos rest i f' := by
  intro i f' hf'
  have hlen : (f :: rest).length - 1 - (i + 1) = rest.length - 1 - i := by
    simp only [List.length_cons]; omega
  have := h (i + 1) f' (by simpa using hf')
  cases f' with
  | ordinary A =>
    simp only [FieldPos] at this ⊢
    rw [hlen] at this
    rcases this with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, fun i' f'' hf'' hlt hm => ?_⟩
      have := h2 (i' + 1) f'' (by simpa using hf'') (by omega)
        (by rw [show (f :: rest).length - 1 - (i' + 1) = rest.length - 1 - i' by
              simp only [List.length_cons]; omega]; exact hm)
      rwa [show i' + 1 - (i + 1) - 1 = i' - i - 1 by omega] at this
  | reflexive tele es => exact this
  | container => exact this

theorem isMember_self (k : Nat) : N.isMember k (.ordinary (.bvar (N.memberVar k))) = true := by
  simp [isMember]

/-- An ordinary field not mentioning the member parameter is not the
member field. -/
theorem isMember_eq_false_of_usesVar {k : Nat} {A : Expr} (h : A.usesVar (N.memberVar k) = false) :
    N.isMember k (.ordinary A) = false := by
  cases A with
  | bvar i =>
    simp only [Expr.usesVar_bvar, decide_eq_false_iff_not] at h
    simp [isMember, h]
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ => rfl

/-- Replace the values at the recursive positions and at the member
field by the point — the values `toTeleXK` accumulates. -/
def junkK : List Field → List V → List V
  | f :: fields, v :: vs => (if f.isRec || N.isMember fields.length f then pt else v) :: junkK fields vs
  | _, vs => vs

theorem junkK_length : ∀ (fields : List Field) (fs : List V), (N.junkK fields fs).length = fs.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: fields, _ :: fs => by simp [junkK, junkK_length fields fs]

theorem junkK_cons (f : Field) (fields : List Field) (v : V) (fs : List V) :
    N.junkK (f :: fields) (v :: fs) =
      (if f.isRec || N.isMember fields.length f then pt else v) :: N.junkK fields fs := rfl

/-- The junked values agree with the values at every position that is
neither recursive nor the member field. -/
theorem consList_junkK_eq (ρ : Nat → V) :
    ∀ (fields : List Field) (fs : List V) (i : Nat),
      (∀ f, fields[i]? = some f → (f.isRec || N.isMember (fields.length - 1 - i) f) = false) →
      consList (N.junkK fields fs) ρ i = consList fs ρ i
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | f :: fields, _ :: _, 0, h => by
    have := h f rfl
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at this
    simp [junkK_cons, this]
  | f :: fields, _ :: fs, i + 1, h => by
    simp only [junkK_cons, consList_cons, cons_succ]
    exact consList_junkK_eq ρ fields fs i fun f' hf' => by
      have := h f' (by simpa using hf')
      rwa [show (f :: fields).length - 1 - (i + 1) = fields.length - 1 - i by
        simp only [List.length_cons]; omega] at this

end NestInfo

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-- **What is known about the container** when a block nests through
it: its set in the model is its family's graph (its installation's
law), it is plain, positive in the member's position, no field reads
an earlier recursive field, the domains met along a fitting instance
are bounded at every fitting parameter list (its own checks), the
class's arguments fit its parameters at every member set in the result
universe (the nested block's check), and its result universe at the
instantiation is the block's (N3). -/
structure NestFacts : Prop where
  /-- The container's set is its family's graph. -/
  fam : ∀ ls', M N.K.name ls' = N.KS.famSet M ls'
  /-- The container has no container field (depth one). -/
  noCont : N.KS.NoCont
  /-- The container is positive in the member's position. -/
  positive : N.Positive
  /-- No field of the container reads an earlier recursive field. -/
  noRecDep : N.KS.NoRecDep
  /-- The container's domains are bounded at fitting parameters. -/
  domsBounded : ∀ ps', FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params ps' →
    N.KS.DomsBounded M (S.lsK ls N) ps'
  /-- The class's arguments fit the container's parameters at every
  member set in the result universe. -/
  argsFit : ∀ ps, FitsVals M (S.ψ ls) base S.params ps → ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) →
    FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params (S.psK M ls N ps X)
  /-- The container's result universe at the instantiation is the
  block's. -/
  u₀_eq : N.KS.u₀ (S.lsK ls N) = S.u₀ ls
  /-- The class's arguments fill all but the member's position of the
  container's parameters (`NestScoped`). -/
  args_len : N.args.length + 1 = N.nPK

variable {S M ls N}

/-- The container's regime at the instantiation is the block's. -/
theorem NestFacts.z_eq (hf : S.NestFacts M ls N) : N.KS.z (S.lsK ls N) = S.z ls := by
  apply Bool.eq_iff_iff.mpr
  rw [z_iff, z_iff, hf.u₀_eq]

/-! ## The member's position among the container's parameter values -/

/-- The container's parameter values, split at the member. -/
theorem psK_eq (ps : List V) (X : V) :
    S.psK M ls N ps X = ((N.args.drop N.p).map (interp M (S.ψ ls) (envP ps))).reverse ++
      X :: ((N.args.take N.p).map (interp M (S.ψ ls) (envP ps))).reverse := by
  simp [psK, classArgsV]

theorem length_dropK (hf : S.NestFacts M ls N) {ps : List V} :
    (((N.args.drop N.p).map (interp M (S.ψ ls) (envP ps))).reverse).length = N.nPK - 1 - N.p := by
  have := hf.args_len
  have := hf.positive.2.1
  simp only [List.length_reverse, List.length_map, List.length_drop]
  omega

/-- The member's parameter value is the member set. -/
theorem envP_psK_member (hf : S.NestFacts M ls N) {ps : List V} {X : V} :
    envP (S.psK M ls N ps X) (N.nPK - 1 - N.p) = X := by
  rw [envP, psK_eq, ← S.length_dropK hf]
  exact consList_append_cons_self _ _ _ _

/-- The other parameter values do not depend on the member set. -/
theorem envP_psK_ne (hf : S.NestFacts M ls N) {ps : List V} {X Y : V} {i : Nat}
    (hi : i ≠ N.nPK - 1 - N.p) :
    envP (S.psK M ls N ps X) i = envP (S.psK M ls N ps Y) i := by
  show consList (S.psK M ls N ps X) base i = consList (S.psK M ls N ps Y) base i
  rw [S.psK_eq, S.psK_eq]
  exact consList_append_cons_ne (by rw [S.length_dropK hf]; exact hi)

/-- The member variable under `k` field values reads the member set. -/
theorem interp_memberVar (hf : S.NestFacts M ls N) (φ : Name → Nat) {ps : List V} {X : V}
    {vs : List V} {k : Nat} (hv : vs.length = k) :
    interp M φ (consList vs (envP (S.psK M ls N ps X))) (.bvar (N.memberVar k)) = X := by
  have := hf.positive.2.1
  rw [interp_bvar, NestInfo.memberVar,
    show k + N.nPK - 1 - N.p = (N.nPK - 1 - N.p) + vs.length by omega, consList_ge]
  exact S.envP_psK_member hf

/-- **Reading alike at two member sets**: an expression not mentioning
the member variable reads alike under two field-value lists agreeing
at the variables it uses, over the container's parameters at two
member sets. -/
theorem interp_psK_env_congr (hf : S.NestFacts M ls N) (φ : Name → Nat) {ps : List V} (X Y : V)
    (A : Expr) {vs ws : List V} {k : Nat} (hv : vs.length = k) (hw : ws.length = k)
    (hmem : A.usesVar (N.memberVar k) = false)
    (hlo : ∀ i, i < k → A.usesVar i = true → consList vs base i = consList ws base i) :
    interp M φ (consList vs (envP (S.psK M ls N ps X))) A =
      interp M φ (consList ws (envP (S.psK M ls N ps Y))) A := by
  subst hv
  apply interp_usesVar
  intro i hi
  by_cases hlt : i < vs.length
  · have := hlo i hlt hi
    rw [consList_lt hlt, consList_lt (by omega)] at this
    rw [consList_lt hlt, consList_lt (by omega), this]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + vs.length := ⟨i - vs.length, by omega⟩
    rw [consList_ge, ← hw, consList_ge]
    apply S.envP_psK_ne hf
    intro e
    have hp := hf.positive.2.1
    have : i' + vs.length = N.memberVar vs.length := by rw [NestInfo.memberVar]; omega
    rw [this, hmem] at hi
    exact Bool.false_ne_true hi

/-! ## The class is the container's family -/

/-- **The class is the container's family** at the instantiation
(the container's set applied by β to fitting parameter values). -/
theorem classSet_eq_Fam (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) :
    S.classSet M ls N ps X = N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] := by
  have hfit := hf.argsFit ps hp X hX
  have hI : N.KS.indices = [] := hf.positive.1
  have hlen : (S.psK M ls N ps X).length = N.KS.nP := FitsVals_length M _ hfit
  rw [classSet, hf.fam, famSet, hI, List.nil_append,
    show S.classArgsV M ls N ps X = (S.psK M ls N ps X).reverse by simp [psK],
    appList_lamCtx_false_fits M _ hfit]
  simp only [nI, hI, List.length_nil, shiftE_zero_zero, readEnv_consList hlen, readEnv_zero]

/-! ## The class grows with the member set -/

/-- **Fitting fields at a smaller member set fit at a larger one**,
relative to the family at the larger set: by positivity each field is
the member field (its value is in the smaller set, hence in the
larger), a recursive field (reflexive with an empty telescope: the
induction hypothesis `hP`), or an ordinary field not mentioning the member (the same set). -/
theorem FitsFields_psK_mono (hf : S.NestFacts M ls N) {X Y : V} (hXY : X ⊆ˢ Y) {ps : List V}
    {P : FamP V}
    (hP : ∀ x, P (S.psK M ls N ps X) [] x →
      N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps Y) [] x ∧
        (N.KS.z (S.lsK ls N) = false → x ∈ˢ N.KS.bound M (S.lsK ls N) (S.psK M ls N ps Y) [])) :
    ∀ {fields : List Field} {fs : List V},
      (∀ i f, fields[i]? = some f → N.FieldPos fields i f) →
      N.KS.FitsFields M (S.lsK ls N) (N.KS.bound M (S.lsK ls N))
        (fun ps' is' x => N.KS.Mem M (S.lsK ls N) ps' is' x ∧ P ps' is' x)
        (S.psK M ls N ps X) fields fs →
      N.KS.FitsFields M (S.lsK ls N) (N.KS.bound M (S.lsK ls N)) (N.KS.Mem M (S.lsK ls N))
        (S.psK M ls N ps Y) fields fs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | f :: rest, v :: vs, hpos, hfit => by
    have hv : vs.length = rest.length := N.KS.FitsFields_length M _ hfit.1
    refine ⟨FitsFields_psK_mono hf hXY hP (N.FieldPos_tail hpos) hfit.1, ?_⟩
    have hfv := hfit.2
    have hFP := hpos 0 f rfl
    cases f with
    | ordinary A =>
      simp only [NestInfo.FieldPos, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hFP
      rcases hFP with hA | ⟨hA, -⟩
      · subst hA
        simp only [fieldSet] at hfv ⊢
        rw [S.interp_memberVar hf _ hv] at hfv ⊢
        exact hXY v hfv
      · simp only [fieldSet] at hfv ⊢
        rw [S.interp_psK_env_congr hf _ X Y A hv hv hA (fun _ _ _ => rfl)] at hfv
        exact hfv
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hFP
      simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil] at hfv ⊢
      cases hz : N.KS.z (S.lsK ls N)
      · rw [hz] at hfv
        rw [mem_fibreR_false] at hfv ⊢
        exact ⟨(hP v hfv.2.2).2 hz, (hP v hfv.2.2).1⟩
      · rw [hz] at hfv
        rw [mem_fibreR_true] at hfv ⊢
        obtain ⟨rfl, y, hy⟩ := hfv
        exact ⟨rfl, y, (hP y hy.2).1⟩
    | container => simp only [NestInfo.FieldPos] at hFP

/-- **Every member of the container's family at a smaller member set
is a member at a larger one**, and is in the container's bound there
(above a proposition): induction over the family at the smaller set,
the step by `FitsFields_psK_mono` and the closure of the bound under
the container's constructors. -/
theorem Mem_psK_mono (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X Y : V} (hXY : X ⊆ˢ Y)
    (hY : Y ∈ˢ (univ (S.u₀ ls) : V)) {x : V}
    (hx : N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps X) [] x) :
    N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps Y) [] x ∧
      (N.KS.z (S.lsK ls N) = false → x ∈ˢ N.KS.bound M (S.lsK ls N) (S.psK M ls N ps Y) []) := by
  refine N.KS.Mem_ind M (S.lsK ls N)
    (P := fun ps' _ x => ps' = S.psK M ls N ps X →
      N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps Y) [] x ∧
        (N.KS.z (S.lsK ls N) = false → x ∈ˢ N.KS.bound M (S.lsK ls N) (S.psK M ls N ps Y) []))
    ?_ hx rfl
  intro ps' _ x hs hps
  subst hps
  obtain ⟨j, c, fs, hc, hfit, -, rfl⟩ := hs
  have hcm : c ∈ N.KS.ctors := List.mem_of_getElem? hc
  have hidx : c.idx = [] := (hf.positive.2.2.2.2 c hcm).1
  have hfit' : N.KS.FitsFields M (S.lsK ls N) (N.KS.bound M (S.lsK ls N)) (N.KS.Mem M (S.lsK ls N))
      (S.psK M ls N ps Y) c.fields fs :=
    S.FitsFields_psK_mono hf hXY (fun x h => h rfl) (N.FieldPos_of_positive hf.positive hcm) hfit
  have hmem : N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps Y) [] (tag (N.KS.tagOf j) (tuple fs.reverse)) :=
    N.KS.Mem_intro M (S.lsK ls N) ⟨j, c, fs, hc, hfit', by simp [hidx, idxVals], rfl⟩
  refine ⟨hmem, fun hz => ?_⟩
  have hn : N.KS.u₀ (S.lsK ls N) ≠ 0 := fun h0 => by simp [(N.KS.z_iff (S.lsK ls N)).mpr h0] at hz
  have hcx := N.KS.ctorsX_tagOf M (S.lsK ls N) (S.psK M ls N ps Y) hc
  have hB := N.KS.FitsB_of_FitsFields M (S.lsK ls N) hz hfit' (hf.noRecDep c hcm)
    (hf.domsBounded _ (hf.argsFit ps hp Y hY) hz c hcm fs hfit')
    (fun _ h _ => (N.KS.noCont_absurd hf.noCont hcm h).elim)
    c.fields.reverse [] fs.reverse [] (by simp [N.KS.FitsFields_length M _ hfit']) (by simp) (by simp)
  dsimp only [junkRec] at hB
  have := (N.KS.boundJ_spec M (S.lsK ls N) _ hn).2 _ _ fs.reverse hcx hB
  simpa [bound, hidx, idxVals] using this

/-- **The class grows with the member set, and stays in the
universe** (`ContGood`), by the leastness of the container's fixed
point and its positivity. -/
theorem contGood_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) : S.ContGood M ls := by
  intro N' hN' ps hp
  rw [hN, Option.some.injEq] at hN'
  subst hN'
  refine ⟨fun X Y hXY hX hY => ?_, fun X hX => ?_⟩
  · rw [S.classSet_eq_Fam hf hp hX, S.classSet_eq_Fam hf hp hY]
    intro x hx
    cases hz : N.KS.z (S.lsK ls N)
    · simp only [Fam, hz] at hx ⊢
      rw [mem_fibreR_false] at hx ⊢
      exact ⟨(S.Mem_psK_mono hf hp hXY hY hx.2).2 hz, (S.Mem_psK_mono hf hp hXY hY hx.2).1⟩
    · simp only [Fam, hz] at hx ⊢
      rw [mem_fibreR_true] at hx ⊢
      obtain ⟨rfl, y, hy⟩ := hx
      exact ⟨rfl, y, (S.Mem_psK_mono hf hp hXY hY hy).1⟩
  · rw [S.classSet_eq_Fam hf hp hX, ← hf.u₀_eq]
    exact N.KS.Fam_mem_univ M _ _ _

/-! ## The class is inside the class's bound -/

/-- The container's constructor `j` in the joint closure list, at
position `j`. -/
theorem ctorsX_K (ps : List V) (hN : S.nest = some N) {j : Nat} {c : CtorSpec}
    (hc : N.K.ctors[j]? = some c) :
    (S.ctorsX M ls ps)[j]? =
      some (S.toTeleXK M ls N ps c.fields.reverse [], fun _ => (true, [])) := by
  have hj : j < N.K.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  simp only [ctorsX, hN]
  rw [List.getElem?_append_left (by simp [ctorsXK, hj]), ctorsXK, List.getElem?_map, hc]
  rfl

/-- **A fitting instance of a container constructor at the
instantiation is a bounded instance of its telescope in the joint
closure** (above a proposition), given a member set `F` in the
universe whose members are in the block's bound at the member's
indices and a property `P` of the recursive fields placing them in the
class's bound: the mirror of `FitsB_of_FitsFields`, the member and
recursive positions junked. -/
theorem FitsB_of_FitsFieldsK (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hz : S.z ls = false) {F : V}
    (hFu : F ∈ˢ (univ (S.u₀ ls) : V))
    (hFb : ∀ v, v ∈ˢ F → v ∈ˢ S.boundJ M ls ps (false, S.memberIdx M ls N ps))
    {c : CtorSpec} (hcm : c ∈ N.KS.ctors) {P : FamP V} {fs : List V}
    (hfit : N.KS.FitsFields M (S.lsK ls N) (N.KS.bound M (S.lsK ls N))
      (fun ps' is' x => N.KS.Mem M (S.lsK ls N) ps' is' x ∧ P ps' is' x)
      (S.psK M ls N ps F) c.fields fs)
    (hP : ∀ x, P (S.psK M ls N ps F) [] x → x ∈ˢ S.classBound M ls ps) :
    ∀ (L done : List Field) (vsO fsDone : List V), vsO.length = L.length →
      c.fields = L.reverse ++ done → fs = vsO.reverse ++ fsDone →
      TeleX.FitsB (S.u₀ ls) (S.boundJ M ls ps) (S.toTeleXK M ls N ps L (N.junkK done fsDone)) vsO
  | [], done, [], fsDone, _, hc, hfs => by simp [toTeleXK, TeleX.FitsB]
  | f :: L, done, v :: vs, fsDone, hl, hc, hfs => by
    have hl' : vs.length = L.length := by simpa using hl
    have hc' : c.fields = L.reverse ++ f :: done := by simpa [List.append_assoc] using hc
    have hfs' : fs = vs.reverse ++ v :: fsDone := by simpa [List.append_assoc] using hfs
    have hzK : N.KS.z (S.lsK ls N) = false := by rw [hf.z_eq]; exact hz
    have hlen := N.KS.FitsFields_length M _ hfit
    have hfv : v ∈ˢ N.KS.fieldSet M (S.lsK ls N) (N.KS.bound M (S.lsK ls N))
        (fun ps' is' x => N.KS.Mem M (S.lsK ls N) ps' is' x ∧ P ps' is' x)
        (S.psK M ls N ps F) fsDone f := by
      rw [hc', hfs'] at hfit
      exact N.KS.FitsFields_middle M _ (by simpa using hl') hfit
    -- the field's position and its earlier fields
    have hpos : c.fields[c.fields.length - 1 - done.length]? = some f := by
      rw [hc']
      have : (L.reverse ++ f :: done).length - 1 - done.length = L.reverse.length := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hklt : done.length < c.fields.length := by
      rw [hc']; simp only [List.length_append, List.length_reverse, List.length_cons]; omega
    have hdl : fsDone.length = done.length := by
      rw [hfs', hc'] at hlen; simp at hlen; omega
    have hearlier : earlier fs done.length = fsDone := by
      rw [hfs', earlier]
      have : (vs.reverse ++ v :: fsDone).length - done.length = vs.reverse.length + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, ← List.drop_drop, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      rfl
    have hdrop : c.fields.drop (c.fields.length - 1 - done.length + 1) = done := by
      rw [hc']
      have : (L.reverse ++ f :: done).length - 1 - done.length + 1 = L.reverse.length + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_cons]; omega
      rw [this, ← List.drop_drop, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      rfl
    have hidx : c.fields.length - 1 - (c.fields.length - 1 - done.length) = done.length := by omega
    have hnr' := hf.noRecDep c hcm _ f hpos
    rw [hdrop] at hnr'
    have hFP := N.FieldPos_of_positive hf.positive hcm _ f hpos
    have hfitM : N.KS.FitsFields M (S.lsK ls N) (N.KS.bound M (S.lsK ls N))
        (N.KS.Mem M (S.lsK ls N)) (S.psK M ls N ps F) c.fields fs :=
      N.KS.FitsFields_mono M (S.lsK ls N) (N.KS.boundOk_bound M (S.lsK ls N))
        (fun _ _ _ h => h.1) _ hfit
    have hb' := hf.domsBounded _ (hf.argsFit ps hp F hFu) hzK c hcm fs hfitM done.length f hpos hklt
    rw [hearlier] at hb'
    have ih := FitsB_of_FitsFieldsK hf hp hz hFu hFb hcm hfit hP L (f :: done) vs (v :: fsDone)
      hl' hc' hfs'
    have hjl : (N.junkK done fsDone).length = done.length := by rw [N.junkK_length, hdl]
    cases f with
    | ordinary A =>
      simp only [NestInfo.FieldPos, hidx] at hFP
      rcases hFP with hA | ⟨hA, hA'⟩
      · subst hA
        simp only [toTeleXK, hjl, N.isMember_self, if_true, TeleX.FitsB]
        refine ⟨?_, ?_⟩
        · simp only [fieldSet] at hfv
          rw [S.interp_memberVar hf _ hdl] at hfv
          exact hFb v hfv
        · simpa [N.junkK_cons, N.isMember_self] using ih
      · have hnm : N.isMember done.length (.ordinary A) = false := N.isMember_eq_false_of_usesVar hA
        simp only [toTeleXK, hjl, hnm, Bool.false_eq_true, if_false, TeleX.FitsB]
        have hdom : interp M (N.KS.ψ (S.lsK ls N)) (consList (N.junkK done fsDone) (envP (S.psK M ls N ps pt))) A
            = interp M (N.KS.ψ (S.lsK ls N)) (consList fsDone (envP (S.psK M ls N ps F))) A := by
          apply S.interp_psK_env_congr hf _ pt F A hjl hdl hA
          intro i _ hiA
          apply N.consList_junkK_eq base done fsDone i
          intro f' hf'
          have hnr'' : f'.isRec = false := by
            cases hr : f'.isRec
            · rfl
            · exfalso
              have := hnr' i f' hf' hr
              rw [this] at hiA
              exact Bool.false_ne_true hiA
          have hnm'' : N.isMember (done.length - 1 - i) f' = false := by
            cases hm : N.isMember (done.length - 1 - i) f'
            · rfl
            · exfalso
              have hidx' : c.fields[c.fields.length - 1 - done.length + 1 + i]? = some f' := by
                rw [← hdrop, List.getElem?_drop] at hf'; exact hf'
              have := hA' _ f' hidx' (by omega)
                (by rw [show c.fields.length - 1 - (c.fields.length - 1 - done.length + 1 + i)
                    = done.length - 1 - i by omega]; exact hm)
              rw [show c.fields.length - 1 - done.length + 1 + i - (c.fields.length - 1 - done.length) - 1
                = i by omega] at this
              rw [this] at hiA
              exact Bool.false_ne_true hiA
          simp [hnr'', hnm'']
        rw [hdom]
        refine ⟨by rw [← hf.u₀_eq]; exact hb', hfv, ?_⟩
        simpa [N.junkK_cons, Field.isRec, hnm] using ih
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hFP
      simp only [toTeleXK, NestInfo.isMember, Bool.false_eq_true, if_false, TeleX.FitsB]
      refine ⟨?_, ?_⟩
      · simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil, hzK] at hfv
        exact hP v (mem_fibreR_false.mp hfv).2.2
      · simpa [N.junkK_cons, Field.isRec] using ih
    | container => simp only [NestInfo.FieldPos] at hFP
  | [], _, _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, _, [], _, hl, _, _ => by simp at hl

/-- **Every member of the container's family at a member set inside
the block's bound is in the class's bound**: induction over the
container's family, the step by the closure of the joint bound under
the container's constructors (`FitsB_of_FitsFieldsK`). -/
theorem classBound_of_Mem (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hz : S.z ls = false) {F : V}
    (hFu : F ∈ˢ (univ (S.u₀ ls) : V))
    (hFb : ∀ v, v ∈ˢ F → v ∈ˢ S.boundJ M ls ps (false, S.memberIdx M ls N ps)) {x : V}
    (hx : N.KS.Mem M (S.lsK ls N) (S.psK M ls N ps F) [] x) : x ∈ˢ S.classBound M ls ps := by
  have hn : S.u₀ ls ≠ 0 := fun h0 => by simp [(S.z_iff ls).mpr h0] at hz
  refine N.KS.Mem_ind M (S.lsK ls N)
    (P := fun ps' _ x => ps' = S.psK M ls N ps F → x ∈ˢ S.classBound M ls ps) ?_ hx rfl
  intro ps' _ x hs hps
  subst hps
  obtain ⟨j, c, fs', hc, hfit, -, rfl⟩ := hs
  have hcm : c ∈ N.KS.ctors := List.mem_of_getElem? hc
  have hB := S.FitsB_of_FitsFieldsK hf hp hz hFu hFb hcm hfit (fun x h => h rfl)
    c.fields.reverse [] fs'.reverse [] (by simp [N.KS.FitsFields_length M _ hfit]) (by simp) (by simp)
  dsimp only [NestInfo.junkK] at hB
  have := (S.boundJ_spec M ls ps hn).2 j _ fs'.reverse (S.ctorsX_K ps hN hc) hB
  rw [show N.KS.tagOf j = j from Nat.zero_add j]
  exact this

/-- **The class is inside the class's bound** (`ContInBound`), by
induction over the container's family at the instantiation: the
closure lists the container's constructors with the member field at
the family's bound. -/
theorem contInBound_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) : S.ContInBound M ls ps := by
  intro hz c hc fs hfit k hk hklt
  have hzK : N.KS.z (S.lsK ls N) = false := by rw [hf.z_eq]; exact hz
  have hget := S.FitsFields_get M ls hfit hk hklt
  simp only [fieldSet, hN] at hget
  have h1 : fieldVal fs k ∈ˢ S.classSet M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps)) :=
    (mem_sep.mp hget).1
  rw [S.classSet_eq_Fam hf hp (S.Fam_mem_univ M ls ps _)] at h1
  exact S.classBound_of_Mem hf hN hp hz (S.Fam_mem_univ M ls ps _)
    (fun v hv => ((S.mem_Fam_false M ls hz).mp hv).1)
    (N.KS.Mem_of_mem_Fam_false M (S.lsK ls N) hzK h1)

end IndSpec

end Fragment
