module

public import Fragment.IndSem

@[expose] public section

/-!
# The container's clause: accessible by positivity

What the installation of a nested block proves about its container
from the container's own model — the **one new idea** of nested
blocks, the content of the paper's nested section:

* **the class is the container's family** at the instantiation
  (`classSet_eq_Fam`: the container's set in the model is the graph
  over its parameters of its fibre, applied by β to the class's
  arguments with the parameter set in the nested position);
* **the class is accessible in the parameter set** (`Fam_psK_acc`), by
  **positivity plus the nested case of accessibility**: the
  container's operator is accessible jointly in the parameter set and
  its own family — a constructor value depends on its parameter fields
  (occurrences in the parameter set) and its recursive fields
  (occurrences in the family), one code per field position, and fits
  at every pair holding them (`FitsFields_psK_repl`: a field is the
  parameter field, whose value is in the new parameter set; a
  recursive field, whose value is in the new family; or an ordinary
  field mentioning neither the nested parameter nor an earlier
  parameter or recursive field, the same set at both) — so the least
  family as a function of the parameter set is accessible with the
  bound `accPaths` of the positions (`lfpP_acc`, `Access.lean`), which
  is the class's bound (`classBound`), in both regimes;
* hence **the class grows with the parameter set** (`Fam_psK_mono`,
  `ContClause.mono`): the support in the smaller set is in the larger
  — no separate monotonicity proof;
* the class at the one-fibre set is inhabited when the class is
  inhabited at all (`Fam_psK_inhab_one`): by induction over the
  container's family, every constructor instance has a counterpart
  at `{pt}` — the parameter fields replaced by the point, the recursive
  fields by the counterparts the induction supplies, the ordinary
  fields kept (`FitsFields_psK_repl` once more).

Together these are the container's clause (`ContClause`,
`IndSem.lean`) the block's operator is accessible, hence monotone,
under (`contClause_of`).  The facts about the container they need
(`NestFacts`) are what the container's own installation left in the
model (`BlockModel.lean`) and what the nested block's checks add
(the class's arguments fit, the sorts agree, N3).

Con-leche: `Model/Inductives/ContAcc.lean` and `ContAccFrame.lean`
(`frameIterAcc`) with `SetModel/Access.lean`'s `lfpP_acc` for
accessibility.  Con-leche proves monotonicity separately, by
positivity plus leastness — the container case of
`Model/Annot/BlockLfpMono.lean` through `SetModel/HoleClose.lean`
(`lfpTuple_le_on`) and `Model/Inductives/ContLeaf.lean`
(`monoOn_of_famLe`); the fragment derives it from accessibility.
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Small list and environment facts -/

omit [IndLib V] in
/-- The value at the seam of a pushed list `l₁ ++ x :: l₂` is `x`. -/
theorem consList_append_cons_self (l₁ : List V) (x : V) (l₂ : List V) (ρ : Nat → V) :
    consList (l₁ ++ x :: l₂) ρ l₁.length = x := by
  rw [consList_append, ← Nat.zero_add l₁.length, consList_ge]; rfl

omit [IndLib V] in
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
first) of a field list: the parameter field, a recursive field (an empty
telescope) with no index expressions, or an ordinary field mentioning
neither the nested parameter nor a later-listed (earlier) parameter
field — `Positive`'s match, with the constructor's field list
abstracted so that it passes to the tails. -/
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

/-- An ordinary field not mentioning the nested parameter is not the
parameter field. -/
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

/-- A positive container has no container field. -/
theorem noCont_of_positive (hpos : N.Positive) : N.KS.NoCont := by
  intro c hc f hf
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  have := (hpos.2.2.2.2 c hc).2 i f hi
  cases f with
  | ordinary _ => rfl
  | reflexive _ _ => rfl
  | container => exact this.elim

/-- The container's specification is plain. -/
theorem KS_nest : N.KS.nest = none := rfl

end NestInfo

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-- **What is known about the container** when a block nests through
it: its set in the model is its family's graph (its installation's
law), it is positive in the nested position, no field reads an
earlier recursive field, the universe bound on its fields holds at
every fitting parameter list (its own checks), the class's arguments
fit its parameters at every parameter set in the result universe (the
nested block's check), and its result universe at the instantiation
is the block's (N3). -/
structure NestFacts : Prop where
  /-- The container's set is its family's graph. -/
  fam : ∀ ls', M N.K.name ls' = N.KS.famSet M ls'
  /-- The container is positive in the nested position. -/
  positive : N.Positive
  /-- No field of the container reads an earlier recursive field. -/
  noRecDep : N.KS.NoRecDep
  /-- The universe bound on the container's fields, at fitting
  parameters. -/
  domsBounded : ∀ ps', FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params ps' →
    N.KS.DomsBounded M (S.lsK ls N) ps'
  /-- The class's arguments fit the container's parameters at every
  parameter set in the result universe. -/
  argsFit : ∀ ps, FitsVals M (S.ψ ls) base S.params ps → ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) →
    FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params (S.psK M ls N ps X)
  /-- The container's result universe at the instantiation is the
  block's. -/
  u₀_eq : N.KS.u₀ (S.lsK ls N) = S.u₀ ls
  /-- The class's arguments fill all but the nested position of the
  container's parameters (`NestScoped`). -/
  args_len : N.args.length + 1 = N.nPK

variable {S M ls N}

/-- The container's regime at the instantiation is the block's. -/
theorem NestFacts.z_eq (hf : S.NestFacts M ls N) : N.KS.z (S.lsK ls N) = S.z ls := by
  apply Bool.eq_iff_iff.mpr
  rw [z_iff, z_iff, hf.u₀_eq]

/-- The container's clause on the container itself: nothing (it is
plain). -/
theorem NestFacts.contOkK (_hf : S.NestFacts M ls N) (ps' : List V) :
    N.KS.ContOk M (S.lsK ls N) ps' :=
  N.KS.contOk_of_plain M _ N.KS_nest ps'

/-- The universe bound on the container's fields at the instantiation
with a parameter set of the universe. -/
theorem NestFacts.domsBoundedK (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) :
    N.KS.DomsBounded M (S.lsK ls N) (S.psK M ls N ps X) :=
  hf.domsBounded _ (hf.argsFit ps hp X hX)

/-! ## The nested position among the container's parameter values -/

/-- The container's parameter values, split at the nested position. -/
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

/-- The nested parameter's value is the parameter set. -/
theorem envP_psK_member (hf : S.NestFacts M ls N) {ps : List V} {X : V} :
    envP (S.psK M ls N ps X) (N.nPK - 1 - N.p) = X := by
  rw [envP, psK_eq, ← S.length_dropK hf]
  exact consList_append_cons_self _ _ _ _

/-- The other parameter values do not depend on the parameter set. -/
theorem envP_psK_ne (hf : S.NestFacts M ls N) {ps : List V} {X Y : V} {i : Nat}
    (hi : i ≠ N.nPK - 1 - N.p) :
    envP (S.psK M ls N ps X) i = envP (S.psK M ls N ps Y) i := by
  show consList (S.psK M ls N ps X) base i = consList (S.psK M ls N ps Y) base i
  rw [S.psK_eq, S.psK_eq]
  exact consList_append_cons_ne (by rw [S.length_dropK hf]; exact hi)

/-- The nested parameter's variable under `k` field values reads the parameter set. -/
theorem interp_memberVar (hf : S.NestFacts M ls N) (φ : Name → Nat) {ps : List V} {X : V}
    {vs : List V} {k : Nat} (hv : vs.length = k) :
    interp M φ (consList vs (envP (S.psK M ls N ps X))) (.bvar (N.memberVar k)) = X := by
  have := hf.positive.2.1
  rw [interp_bvar, NestInfo.memberVar,
    show k + N.nPK - 1 - N.p = (N.nPK - 1 - N.p) + vs.length by omega, consList_ge]
  exact S.envP_psK_member hf

/-- **Reading alike at two parameter sets**: an expression not mentioning
the nested parameter's variable reads alike under two field-value lists agreeing
at the variables it uses, over the container's parameters at two
parameter sets. -/
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
  rw [classSet, hf.fam, famSet, famSetF, hI, List.nil_append,
    show S.classArgsV M ls N ps X = (S.psK M ls N ps X).reverse by simp [psK],
    appList_lamCtx_false_fits M _ hfit]
  simp only [nI, hI, List.length_nil, shiftE_zero_zero, readEnv_consList hlen, readEnv_zero]

/-! ## Fitting the container's fields, parameter-field and recursive values replaced

By positivity, a constructor of the container reads the parameter set
only through the parameter fields and its own family only through the
recursive fields, and no ordinary field reads either kind.  So a
fitting list stays fitting when the parameter-field values are replaced by
members of another parameter set, the recursive values by members of
another family's fibre, and the ordinary values are kept
(`FitsFields_psK_repl`) — the one lemma accessibility and the
one-fibre counterpart below rest on.  Con-leche: the
telescope lemma `spineFit_mono` of `HoleMono.lean` along the relation
of the container's instantiation (`CtorPos`, `NestRec.lean`'s
`trans`). -/

/-- **A replacement of a fitting list** (innermost first): at a parameter
field a member of `Y`, at a recursive field a member of `W' []`, at
an ordinary field the same value. -/
def Repl (N : NestInfo) (Y : V) (W' : List V → V) : List Field → List V → List V → Prop
  | [], [], [] => True
  | f :: fields, v :: vs, v' :: vs' =>
    Repl N Y W' fields vs vs' ∧
      (if N.isMember fields.length f then v' ∈ˢ Y else if f.isRec then v' ∈ˢ W' [] else v' = v)
  | _, _, _ => False

theorem Repl_length {Y : V} {W' : List V → V} :
    ∀ {fields : List Field} {fs fs' : List V}, Repl N Y W' fields fs fs' →
      fs.length = fields.length ∧ fs'.length = fields.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by
    obtain ⟨h1, h2⟩ := Repl_length h.1
    simp [h1, h2]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- The values at the positions an ordinary field may read agree
between a list and its replacement: positivity (no earlier parameter
field) and no earlier recursive field. -/
theorem Repl_consList_eq {Y : V} {W' : List V → V} :
    ∀ {fields : List Field} {fs fs' : List V}, Repl N Y W' fields fs fs' →
      ∀ i f, fields[i]? = some f → N.isMember (fields.length - 1 - i) f = false → f.isRec = false →
        consList fs base i = consList fs' base i
  | [], [], [], _, i, _, hf, _, _ => by simp at hf
  | f :: fields, v :: vs, v' :: vs', ⟨h1, h2⟩, 0, f', hf, hm, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hm
    simp only [hm, hr, Bool.false_eq_true, if_false] at h2
    simp [consList_cons, cons_zero, h2]
  | f :: fields, v :: vs, v' :: vs', ⟨h1, _⟩, i + 1, f', hf, hm, hr => by
    simp only [List.getElem?_cons_succ] at hf
    simp only [consList_cons, cons_succ]
    refine Repl_consList_eq h1 i f' hf ?_ hr
    rwa [show (f :: fields).length - 1 - (i + 1) = fields.length - 1 - i by
      simp only [List.length_cons]; omega] at hm
  | [], [], _ :: _, h, _, _, _, _, _ => h.elim
  | [], _ :: _, _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

/-- **A fitting list of a positive container stays fitting under a
replacement**, at the parameter set and family the replacement reads:
a parameter field's value lands in the new parameter set, a recursive
field's in the new family's fibre, and an ordinary field — mentioning
neither the nested parameter nor an earlier parameter or recursive field
— reads the same set at both.  (The fields are a suffix of a
constructor's, so that positivity's clause and the no-dependency
condition pass to the tails.) -/
theorem FitsFields_psK_repl (hf : S.NestFacts M ls N) {X Y : V} {W W' : List V → V} {ps : List V} :
    ∀ {fields : List Field} {fs fs' : List V},
      (∀ i f, fields[i]? = some f → N.FieldPos fields i f) →
      ListNoRecDep fields →
      N.KS.FitsFields M (S.lsK ls N) W (S.psK M ls N ps X) fields fs →
      Repl N Y W' fields fs fs' →
      N.KS.FitsFields M (S.lsK ls N) W' (S.psK M ls N ps Y) fields fs'
  | [], [], [], _, _, _, _ => trivial
  | f :: rest, v :: vs, v' :: vs', hpos, hnr, hfit, ⟨hrepl, hv'⟩ => by
    have hlen : vs.length = rest.length := N.KS.FitsFields_length M _ hfit.1
    have hlen' : vs'.length = rest.length := (Repl_length hrepl).2
    refine ⟨FitsFields_psK_repl hf (N.FieldPos_tail hpos) hnr.tail hfit.1 hrepl, ?_⟩
    have hfv := hfit.2
    have hFP := hpos 0 f rfl
    cases f with
    | ordinary A =>
      simp only [NestInfo.FieldPos, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hFP
      rcases hFP with hA | ⟨hA, hA'⟩
      · -- the parameter field
        subst hA
        simp only [N.isMember_self, if_true] at hv'
        simp only [fieldSet]
        rw [S.interp_memberVar hf _ hlen']
        exact hv'
      · -- an ordinary field, not the parameter field
        have hnm := N.isMember_eq_false_of_usesVar hA
        simp only [hnm, Field.isRec, Bool.false_eq_true, if_false] at hv'
        subst hv'
        simp only [fieldSet] at hfv ⊢
        rw [S.interp_psK_env_congr hf _ X Y A hlen hlen' hA] at hfv
        · exact hfv
        · intro i hi hu
          obtain ⟨f', hf'⟩ : ∃ f', rest[i]? = some f' :=
            ⟨rest[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
          refine Repl_consList_eq hrepl i f' hf' ?_ ?_
          · cases hm : N.isMember (rest.length - 1 - i) f'
            · rfl
            · exfalso
              have := hA' (i + 1) f' (by simpa using hf') (by omega)
                (by rw [show rest.length - (i + 1) = rest.length - 1 - i by omega]; exact hm)
              rw [Nat.add_sub_cancel] at this
              rw [this] at hu
              exact Bool.false_ne_true hu
          · cases hr : f'.isRec
            · rfl
            · exfalso
              have := hnr.head i f' hf' hr
              rw [this] at hu
              exact Bool.false_ne_true hu
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hFP
      have hnm : N.isMember rest.length (.reflexive [] []) = false := rfl
      simp only [hnm, Field.isRec, Bool.false_eq_true, if_false, if_true] at hv'
      simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil]
      exact hv'
    | container => exact hFP.elim
  | [], [], _ :: _, _, _, _, h => h.elim
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, _, _, h => h.elim

/-- The positivity clause and the no-dependency condition of a
constructor's whole field list. -/
theorem fieldPos_of (hf : S.NestFacts M ls N) {c : CtorSpec} (hc : c ∈ N.K.ctors) :
    (∀ i f, c.fields[i]? = some f → N.FieldPos c.fields i f) ∧ ListNoRecDep c.fields :=
  ⟨N.FieldPos_of_positive hf.positive hc, by
    have := N.KS.noRecDep_drop hf.noRecDep hc 0
    rwa [List.drop_zero] at this⟩

/-- A container constructor's index values are empty (positivity: no
indices). -/
theorem KS_idxVals (hf : S.NestFacts M ls N) {c : CtorSpec} (hc : c ∈ N.K.ctors) (ρ : Nat → V) :
    N.KS.idxVals M (S.lsK ls N) ρ c.idx = [] := by
  rw [(hf.positive.2.2.2.2 c hc).1]; rfl

/-! ## The class is accessible in the parameter set: positivity plus the nested case -/

variable (S M ls N) in
/-- **The container's operator, jointly in the parameter set and its own
family**: the parameter set at the left index, the family at the right.
Con-leche: the joint operator `Θ` of `lfpP_acc`. -/
noncomputable def jointOp (ps : List V) (Z : Unit ⊕ List V → V) : List V → V :=
  N.KS.famOp M (S.lsK ls N) (S.psK M ls N ps (Z (Sum.inl ()))) fun is => Z (Sum.inr is)

/-- The container's family at a parameter set is the least family of the
joint operator at that parameter. -/
theorem lfpP_jointOp (hf : S.NestFacts M ls N) (ps : List V) (X : V) :
    lfpP (S.u₀ ls) (S.jointOp M ls N ps) (fun _ => X) = N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) := by
  unfold lfpP Fam jointOp
  rw [hf.u₀_eq]
  rfl

/-- **The container's operator is accessible jointly in the parameter set
and its own family**, with one code per field position: a
constructor value depends on its parameter fields (occurrences in the
parameter set) and its recursive fields (occurrences in the family), and
fits at every parameter set and family holding them
(`FitsFields_psK_repl`).  Con-leche: `frameCtor_acc`
(`ContAccFrame.lean`). -/
theorem jointOp_acc (hf : S.NestFacts M ls N) (ps : List V) :
    AccFam (S.u₀ ls) (S.jointOp M ls N ps) (natsBelow N.maxFields) := by
  intro Z hZ is x hx
  obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := (N.KS.mem_famOp M _).mp hx
  have hcm := List.mem_of_getElem? hc
  obtain ⟨hpos, hnr⟩ := S.fieldPos_of hf hcm
  have hlen := N.KS.FitsFields_length M _ hfit
  classical
  -- the support: the parameter and recursive positions, their values
  refine ⟨sep (natsBelow c.fields.length) fun b =>
      ∃ f, c.fields[c.fields.length - 1 - idx b]? = some f ∧
        (N.isMember (idx b) f = true ∨ f.isRec = true),
    fun b => if N.isMember (idx b) (c.fields.getD (c.fields.length - 1 - idx b) .container)
      then (Sum.inl (), fieldVal fs (idx b)) else (Sum.inr [], fieldVal fs (idx b)), ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hb, -⟩ := mem_sep.mp hb
    obtain ⟨k, hk, rfl⟩ := mem_natsBelow.mp hb
    exact mem_natsBelow.mpr ⟨k, Nat.lt_of_lt_of_le hk (N.length_le_maxFields hcm), rfl⟩
  · intro b hb
    obtain ⟨hb, f, hf', hkind⟩ := mem_sep.mp hb
    obtain ⟨k, hk, rfl⟩ := mem_natsBelow.mp hb
    dsimp only
    rw [idx_nat] at hf' hkind ⊢
    have hget := N.KS.FitsFields_get M _ hfit hf' hk
    have hgetD : c.fields.getD (c.fields.length - 1 - k) .container = f := by
      rw [List.getD_eq_getElem?_getD, hf']; rfl
    have hFP := hpos _ f hf'
    unfold InFam
    rw [hgetD]
    cases f with
    | ordinary A =>
      simp only [NestInfo.FieldPos] at hFP
      rw [show c.fields.length - 1 - (c.fields.length - 1 - k) = k by omega] at hFP
      rcases hFP with hA | ⟨hA, -⟩
      · subst hA
        simp only [N.isMember_self, if_true]
        simp only [fieldSet] at hget
        rwa [S.interp_memberVar hf _ (by simp [earlier, hlen]; omega)] at hget
      · exfalso
        rcases hkind with hm | hr
        · rw [N.isMember_eq_false_of_usesVar hA] at hm; exact Bool.false_ne_true hm
        · simp [Field.isRec] at hr
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hFP
      simp only [NestInfo.isMember, Bool.false_eq_true, if_false]
      simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil] at hget
      exact hget
    | container => exact hFP.elim
  · intro Z' hZ' hsupp
    refine (N.KS.mem_famOp M _).mpr ⟨j, c, fs, hc, ?_, ?_, rfl⟩
    · refine S.FitsFields_psK_repl hf hpos hnr hfit ?_
      -- the replacement is the list itself: the occurrences held by `Z'`
      suffices key : ∀ (L : List Field) (vs : List V) (n : Nat), L = c.fields.drop n →
          vs = fs.drop n → Repl N (Z' (Sum.inl ())) (fun is => Z' (Sum.inr is)) L vs vs by
        exact key c.fields fs 0 (by simp) (by simp)
      intro L vs n hL hvs
      induction L generalizing vs n with
      | nil =>
        cases vs with
        | nil => trivial
        | cons v vs =>
          exfalso
          have : (fs.drop n).length = (c.fields.drop n).length := by simp [List.length_drop, hlen]
          rw [← hvs, ← hL] at this
          simp at this
      | cons f L ih =>
        cases vs with
        | nil =>
          exfalso
          have : (fs.drop n).length = (c.fields.drop n).length := by simp [List.length_drop, hlen]
          rw [← hvs, ← hL] at this
          simp at this
        | cons v vs =>
          have hL' : L = c.fields.drop (n + 1) := by
            rw [← List.drop_drop, ← hL]; rfl
          have hvs' : vs = fs.drop (n + 1) := by
            rw [← List.drop_drop, ← hvs]; rfl
          refine ⟨ih vs (n + 1) hL' hvs', ?_⟩
          -- the position of `f`: `L.length` fields come before it
          have hn : n < c.fields.length := by
            have := congrArg List.length hL
            simp only [List.length_cons, List.length_drop] at this
            omega
          have hfpos : c.fields[c.fields.length - 1 - L.length]? = some f := by
            have hLl : L.length = c.fields.length - (n + 1) := by
              have := congrArg List.length hL
              simp only [List.length_cons, List.length_drop] at this
              omega
            rw [hLl, show c.fields.length - 1 - (c.fields.length - (n + 1)) = n by omega]
            have := congrArg (fun l => l[0]?) hL
            simpa [List.getElem?_drop] using this.symm
          have hfv : fieldVal fs L.length = v := by
            have hLl : L.length = c.fields.length - (n + 1) := by
              have := congrArg List.length hL
              simp only [List.length_cons, List.length_drop] at this
              omega
            unfold fieldVal
            rw [hLl, hlen, show c.fields.length - 1 - (c.fields.length - (n + 1)) = n by omega]
            have := congrArg (fun l => l[0]?) hvs
            simp only [List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero] at this
            rw [List.getD_eq_getElem?_getD, ← this]; rfl
          have hFP := hpos _ f hfpos
          have hkl : L.length < c.fields.length := by
            have := congrArg List.length hL
            simp only [List.length_cons, List.length_drop] at this
            omega
          have hgetD : c.fields.getD (c.fields.length - 1 - L.length) .container = f := by
            rw [List.getD_eq_getElem?_getD, hfpos]; rfl
          cases f with
          | ordinary A =>
            simp only [NestInfo.FieldPos] at hFP
            rw [show c.fields.length - 1 - (c.fields.length - 1 - L.length) = L.length by omega] at hFP
            rcases hFP with hA | ⟨hA, -⟩
            · subst hA
              simp only [N.isMember_self, if_true]
              have := hsupp (nat L.length) (mem_sep.mpr ⟨mem_natsBelow.mpr ⟨_, hkl, rfl⟩,
                _, by rw [idx_nat]; exact hfpos, Or.inl (by rw [idx_nat]; exact N.isMember_self _)⟩)
              unfold InFam at this
              dsimp only at this
              rw [idx_nat, hgetD, N.isMember_self] at this
              simpa [hfv] using this
            · simp [N.isMember_eq_false_of_usesVar hA, Field.isRec]
          | reflexive tele es =>
            obtain ⟨rfl, rfl⟩ := hFP
            have hnm : N.isMember L.length (.reflexive [] []) = false := rfl
            simp only [hnm, Field.isRec, Bool.false_eq_true, if_false, if_true]
            have := hsupp (nat L.length) (mem_sep.mpr ⟨mem_natsBelow.mpr ⟨_, hkl, rfl⟩,
              _, by rw [idx_nat]; exact hfpos, Or.inr rfl⟩)
            unfold InFam at this
            dsimp only at this
            rw [idx_nat, hgetD] at this
            simp only [NestInfo.isMember, Bool.false_eq_true, if_false] at this
            rwa [hfv] at this
          | container => exact hFP.elim
    · rw [his, S.KS_idxVals hf hcm, S.KS_idxVals hf hcm]

/-- The joint operator maps families in the universe to families in
the universe (the container's own `famOp_maps` at the instantiation). -/
theorem jointOp_maps (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (X : Unit → V) (Y : List V → V)
    (hX : InUniv (S.u₀ ls) X) (hY : InUniv (S.u₀ ls) Y) :
    InUniv (S.u₀ ls) (S.jointOp M ls N ps (Sum.elim X Y)) := by
  have := N.KS.famOp_maps M (S.lsK ls N) (hf.domsBoundedK hp (hX ())) (hf.contOkK _)
    (fun is => Y is) (by rw [hf.u₀_eq]; exact hY)
  rw [hf.u₀_eq] at this
  exact this

/-- **The container's family is accessible in the parameter set**, with
the class's bound: the nested case of accessibility (`lfpP_acc`)
applied to the joint operator — in both regimes (at a proposition the
container's family is closed in `{pt}`, `lfpP_acc`).  Con-leche:
`accConcl_of_frameAccOut` (`ContAcc.lean`) over `frameIterAcc`, above
a proposition. -/
theorem Fam_psK_acc (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X : V}
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) {v : V}
    (hv : v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) []) :
    ∃ (B : V) (g : V → V), B ⊆ˢ S.classBound ∧ (∀ b, b ∈ˢ B → g b ∈ˢ X) ∧
      ∀ X', X' ∈ˢ (univ (S.u₀ ls) : V) → (∀ b, b ∈ˢ B → g b ∈ˢ X') →
        v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X') [] := by
  have hacc := lfpP_acc (fun hn => natsBelow_mem_univ hn N.maxFields) (S.jointOp_maps hf hp)
    (S.jointOp_acc hf ps)
  rw [← S.lfpP_jointOp hf ps X] at hv
  obtain ⟨B, g, hB, hg, hs⟩ := hacc (fun _ => X) (fun _ => hX) [] v hv
  refine ⟨B, fun b => (g b).2, ?_, fun b hb => hg b hb, fun X' hX' h' => ?_⟩
  · unfold classBound
    rw [hN]
    exact hB
  · rw [← S.lfpP_jointOp hf ps X']
    exact hs (fun _ => X') (fun _ => hX') fun b hb => h' b hb

/-- **The class grows with the parameter set**, by accessibility: the
support in `X` is in the larger `Y` (as `AccFam.mono`).  Con-leche
proves it separately, by positivity plus leastness:
`lfpTuple_le_on` (`SetModel/HoleClose.lean`) with `CtorPos` at the
instantiation. -/
theorem Fam_psK_mono (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X Y : V} (hXY : X ⊆ˢ Y)
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) (hY : Y ∈ˢ (univ (S.u₀ ls) : V)) :
    N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] ⊆ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps Y) [] := by
  intro v hv
  obtain ⟨B, g, -, hg, hs⟩ := S.Fam_psK_acc hf hN hp hX hv
  exact hs Y hY fun b hb => hXY _ (hg b hb)

/-! ## The class at the one-fibre set -/

/-- **The container's family at the one-fibre set is inhabited when
the family at any parameter set of the universe is**: by induction over
the family, every constructor instance has a counterpart at `{pt}`
— the parameter fields replaced by the point, the recursive fields by
the counterparts the induction supplies, the ordinary fields kept. -/
theorem Fam_psK_inhab_one (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V))
    (hex : ∃ v, v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) []) :
    ∃ v, v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps one) [] := by
  obtain ⟨v, hv⟩ := hex
  have hbX := hf.domsBoundedK hp hX
  have hb1 := hf.domsBoundedK hp (one_mem_univ _)
  have hco1 := hf.contOkK (S.psK M ls N ps one)
  refine N.KS.Fam_induction M _ hf.noRecDep hbX (hf.contOkK _)
    (fun _ _ => ∃ v, v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps one) []) ?_ [] v hv
  intro is x hs
  obtain ⟨j, c, fs, hc, hfit, -, rfl⟩ := hs
  have hcm := List.mem_of_getElem? hc
  obtain ⟨hpos, hnr⟩ := S.fieldPos_of hf hcm
  classical
  -- the counterpart's fields: the point at the parameter fields, a counterpart at the recursive ones
  let W₁ : List V → V := N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps one)
  suffices key : ∀ (L : List Field) (vs : List V),
      (∀ i f, L[i]? = some f → N.FieldPos L i f) →
      N.KS.FitsFields M (S.lsK ls N) (fun is' => sep (N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) is')
        fun _ => ∃ v, v ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps one) []) (S.psK M ls N ps X) L vs →
      ∃ vs', Repl N one W₁ L vs vs' by
    obtain ⟨fs', hrepl⟩ := key c.fields fs hpos hfit
    have hfit' := S.FitsFields_psK_repl hf hpos hnr hfit hrepl
    refine ⟨N.KS.ctorVal (S.lsK ls N) j fs', ?_⟩
    have := N.KS.ctorVal_mem_Fam M _ hf.noRecDep hb1 hco1 hc hfit'
    rwa [S.KS_idxVals hf hcm] at this
  intro L
  induction L with
  | nil =>
    intro vs _ hfitL
    cases vs with
    | nil => exact ⟨[], trivial⟩
    | cons _ _ => exact hfitL.elim
  | cons f L ih =>
    intro vs hposL hfitL
    cases vs with
    | nil => exact hfitL.elim
    | cons v vs =>
      obtain ⟨vs', hvs'⟩ := ih vs (N.FieldPos_tail hposL) hfitL.1
      have hfv := hfitL.2
      have hFP := hposL 0 f rfl
      cases f with
      | ordinary A =>
        simp only [NestInfo.FieldPos, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at hFP
        rcases hFP with hA | ⟨hA, -⟩
        · subst hA
          exact ⟨pt :: vs', hvs', by simp [N.isMember_self, mem_one]⟩
        · exact ⟨v :: vs', hvs', by simp [N.isMember_eq_false_of_usesVar hA, Field.isRec]⟩
      | reflexive tele es =>
        obtain ⟨rfl, rfl⟩ := hFP
        simp only [fieldSet, piCtx_nil, idxVals, List.map_nil, List.reverse_nil, mem_sep] at hfv
        obtain ⟨w, hw⟩ := hfv.2
        have hnm : N.isMember L.length (.reflexive [] []) = false := rfl
        exact ⟨w :: vs', hvs', by simp [hnm, Field.isRec, W₁, hw]⟩
      | container => exact hFP.elim

/-! ## The container's clause -/

/-- **The container's clause, from positivity and leastness**
(`ContClause`): the class is the container's family at the
instantiation (`classSet_eq_Fam`), which lies in the result universe
(`Fam_mem_univ`, N3), is accessible with the class's bound
(`Fam_psK_acc`, in both regimes), and is inhabited at the one-fibre
set when inhabited at all (`Fam_psK_inhab_one`).  That it grows with
the parameter set follows (`ContClause.mono`). -/
theorem contClause_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) : S.ContClause M ls N ps where
  mem_univ := fun X hX => by
    rw [S.classSet_eq_Fam hf hp hX, ← hf.u₀_eq]
    exact N.KS.Fam_mem_univ M _ _ _
  acc := fun X hX v hv => by
    rw [S.classSet_eq_Fam hf hp hX] at hv
    obtain ⟨B, g, hB, hg, hs⟩ := S.Fam_psK_acc hf hN hp hX hv
    refine ⟨B, g, hB, hg, fun X' hX' h' => ?_⟩
    rw [S.classSet_eq_Fam hf hp hX']
    exact hs X' hX' h'
  inhab_one := fun X hX hex => by
    rw [S.classSet_eq_Fam hf hp hX] at hex
    rw [S.classSet_eq_Fam hf hp (one_mem_univ _)]
    exact S.Fam_psK_inhab_one hf hp hX hex

/-- **The container's clause holds** for a nested block, at every
fitting parameter list. -/
theorem contOk_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) : S.ContOk M ls ps := by
  intro N' hN'
  rw [hN, Option.some.injEq] at hN'
  subst hN'
  exact S.contClause_of hf hN hp

end IndSpec

end Fragment
