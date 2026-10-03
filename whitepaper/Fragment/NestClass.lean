module

public import Fragment.NestSem
public import Fragment.NestRec

@[expose] public section

/-!
# The class, read in the block's terms

The container's constructors are generated into the block's recursors
in the block's own terms (`classCtor`, `Decl.lean`): the member field
becomes a recursive field (reflexive with an empty telescope) at the
member's index expressions, the container's recursive fields become
container fields, and an ordinary
field has the container's parameters replaced by the class's
arguments (`instChainAt`).  This file shows that the fields of a
translated constructor fit (`ClassFits`, `NestRec.lean`) exactly when
the container's own fields fit at the instantiation
(`ClassFits_iff`), and derives from the container's fixed point the
**laws of the class** the recursors' model works from (`ClassLaws`:
inversion, introduction and induction are the container's `mem_Fam`,
`ctorVal_mem_Fam` and `Fam_induction` at the instantiation, read in
the block's terms; the class's size and monotonicity are the
container's clause, `NestSem.lean`).

The one syntactic fact underneath is the reading of the substitution
`instChainAt` (`interp_instChainAt`): substituting arguments for the
binders above `d` innermost ones reads as the environment with the
arguments' values inserted there.
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

/-! ## The substitution chain under binders, read -/

section Subst

variable {V : Type u} [SetLib V] (M : Name → List Nat → V) (φ : Name → Nat)

omit [SetLib V] M φ in
theorem instE_consList' {vs : List V} {k : Nat} (h : vs.length = k) (x : V) (ρ : Nat → V) :
    instE k x (consList vs ρ) = consList vs (cons x ρ) := h ▸ instE_consList vs x ρ

/-- **The substitution chain under `d` binders, read**: the arguments
(outermost first) read under the base environment are inserted,
innermost first, under the `d` values. -/
theorem interp_instChainAt {d : Nat} (ρ₀ : Nat → V) :
    ∀ (as : List Expr) (e : Expr) (ys : List V), ys.length = d →
      interp M φ (consList ys ρ₀) (Expr.instChainAt e as d) =
        interp M φ (consList ys (consList (as.map (interp M φ ρ₀)).reverse ρ₀)) e
  | [], e, ys, _ => by simp
  | a :: as, e, ys, hy => by
    rw [Expr.instChainAt_cons, interp_instChainAt ρ₀ as _ ys hy, interp_inst]
    have hlen : (ys ++ (as.map (interp M φ ρ₀)).reverse).length = d + as.length := by
      simp [hy]
    rw [← consList_append, shiftE_consList' hlen, instE_consList' hlen]
    simp [consList_append, List.map_cons, List.reverse_cons]

end Subst

/-- A variable a term closed below `k` uses is below `k`. -/
theorem Expr.usesVar_lt_of_closedAt : ∀ {e : Expr} {k i : Nat}, e.closedAt k = true →
    e.usesVar i = true → i < k
  | .bvar j, k, i, hc, hu => by
    simp only [Expr.closedAt_bvar, decide_eq_true_eq] at hc
    simp only [Expr.usesVar_bvar, decide_eq_true_eq] at hu
    omega
  | .sort _, _, _, _, hu => by simp at hu
  | .const _ _, _, _, _, hu => by simp at hu
  | .app f a, k, i, hc, hu => by
    simp only [Expr.closedAt_app, Bool.and_eq_true] at hc
    simp only [Expr.usesVar_app, Bool.or_eq_true] at hu
    rcases hu with hu | hu
    · exact Expr.usesVar_lt_of_closedAt hc.1 hu
    · exact Expr.usesVar_lt_of_closedAt hc.2 hu
  | .lam A _ b, k, i, hc, hu => by
    simp only [Expr.closedAt_lam, Bool.and_eq_true] at hc
    simp only [Expr.usesVar_lam, Bool.or_eq_true] at hu
    rcases hu with hu | hu
    · exact Expr.usesVar_lt_of_closedAt hc.1 hu
    · have := Expr.usesVar_lt_of_closedAt hc.2 hu; omega
  | .pi A _ B, k, i, hc, hu => by
    simp only [Expr.closedAt_pi, Bool.and_eq_true] at hc
    simp only [Expr.usesVar_pi, Bool.or_eq_true] at hu
    rcases hu with hu | hu
    · exact Expr.usesVar_lt_of_closedAt hc.1 hu
    · have := Expr.usesVar_lt_of_closedAt hc.2 hu; omega

section Envs

variable {V : Type u}

/-- Two environments with one value pushed at the same depth differ at
that index only. -/
theorem consList_cons_agree (vs : List V) (X Y : V) (ρ : Nat → V) :
    ∀ i, i ≠ vs.length → consList vs (cons X ρ) i = consList vs (cons Y ρ) i := by
  intro i hi
  by_cases hlt : i < vs.length
  · rw [consList_lt hlt, consList_lt hlt]
  · obtain ⟨j, rfl⟩ : ∃ j, i = (j + 1) + vs.length := ⟨i - vs.length - 1, by omega⟩
    rw [consList_ge, consList_ge]
    rfl

end Envs

namespace IndSpec

variable {V : Type u} [IndLib V]
variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-! ## The container's parameter environment at the instantiation -/

/-- The class's arguments before the member, as values. -/
def argsBefore (ps : List V) : List V := (N.args.take N.p).map (interp M (S.ψ ls) (envP ps))

/-- The class's arguments after the member, as values. -/
def argsAfter (ps : List V) : List V := (N.args.drop N.p).map (interp M (S.ψ ls) (envP ps))

/-- The container's parameter environment at the instantiation: the
arguments after the member (innermost), the member set, the arguments
before it. -/
theorem envP_psK (ps : List V) (X : V) :
    envP (S.psK M ls N ps X) =
      consList (S.argsAfter M ls N ps).reverse (cons X (consList (S.argsBefore M ls N ps).reverse base)) := by
  unfold envP psK classArgsV argsAfter argsBefore
  simp [List.reverse_append, consList_append]

theorem length_argsAfter (hlen : N.args.length + 1 = N.nPK) (hp : N.p < N.nPK) (ps : List V) :
    (S.argsAfter M ls N ps).length = N.nPK - 1 - N.p := by
  simp only [argsAfter, List.length_map, List.length_drop]
  omega

/-- The member's variable, under `k` binders above the container's
parameters, reads the member set. -/
theorem read_memberVar (hlen : N.args.length + 1 = N.nPK) (hp : N.p < N.nPK) {fs : List V} {k : Nat}
    (hk : fs.length = k) (ps : List V) (X : V) :
    consList fs (envP (S.psK M ls N ps X)) (N.memberVar k) = X := by
  rw [envP_psK, ← consList_append, show N.memberVar k = 0 + (fs ++ (S.argsAfter M ls N ps).reverse).length by
    simp only [NestInfo.memberVar, List.length_append, List.length_reverse, hk,
      S.length_argsAfter M ls N hlen hp]
    omega, consList_ge]
  rfl

/-- A term closed below the container's parameters and `k` binders,
not using the member's variable, reads alike at any two member sets. -/
theorem read_pfree (hlen : N.args.length + 1 = N.nPK) (hp : N.p < N.nPK) {fs : List V} {k : Nat}
    (hk : fs.length = k) (ps : List V) (X Y : V) {A : Expr} (φ' : Name → Nat)
    (hu : A.usesVar (N.memberVar k) = false) :
    interp M φ' (consList fs (envP (S.psK M ls N ps X))) A =
      interp M φ' (consList fs (envP (S.psK M ls N ps Y))) A := by
  rw [envP_psK, envP_psK, ← consList_append, ← consList_append]
  refine interp_usesVar fun i hi => ?_
  refine consList_cons_agree _ _ _ _ i fun h => ?_
  have : i = N.memberVar k := by
    rw [h, NestInfo.memberVar, List.length_append, List.length_reverse, hk,
      S.length_argsAfter M ls N hlen hp]
    omega
  rw [this, hu] at hi
  exact Bool.false_ne_true hi

/-- The environment of the class's arguments read under the block's
parameters is the container's parameter environment at the member
expression's (arbitrary) reading, below the container's parameters. -/
theorem classArgs_read (ps : List V) :
    ((S.classArgs N 0).map (interp M (S.ψ ls) (envP ps))) =
      S.classArgsV M ls N ps (interp M (S.ψ ls) (envP ps) (S.famAt 0 (N.idx.map (Expr.liftN 0 ·)))) := by
  unfold classArgs classArgsV
  simp only [List.map_append, List.map_map, List.map_singleton]
  have h : ∀ e : Expr, interp M (S.ψ ls) (envP ps) (Expr.liftN 0 e) = interp M (S.ψ ls) (envP ps) e := by
    intro e; rw [interp_liftN, shiftE_zero_zero]
  have hf : (interp M (S.ψ ls) (envP ps) ∘ fun x => Expr.liftN 0 x) = interp M (S.ψ ls) (envP ps) := by
    funext e; exact h e
  rw [hf]

/-! ## The container's fields, read in the block's terms -/

section Corr

variable {env : Env}

/-- The positivity clause of a field, for a suffix of a constructor's
fields (the number of later fields is the same in the suffix). -/
theorem positive_field (hpos : N.Positive) {c : CtorSpec} (hc : c ∈ N.K.ctors)
    {fields : List Field} {n : Nat} (hd : c.fields.drop n = fields) {i : Nat} {f : Field}
    (hi : fields[i]? = some f) :
    match f with
    | Field.ordinary A => A = Expr.bvar (N.memberVar (fields.length - 1 - i)) ∨
        (A.usesVar (N.memberVar (fields.length - 1 - i)) = false ∧
          ∀ i' f', fields[i']? = some f' → i < i' →
            N.isMember (fields.length - 1 - i') f' = true → A.usesVar (i' - i - 1) = false)
    | Field.reflexive tele es => tele = [] ∧ es = []
    | Field.container => False := by
  subst hd
  have hlt : i < (c.fields.drop n).length := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.length_drop] at hlt
  have h := (hpos.2.2.2.2 c hc).2 (n + i) f (by rw [List.getElem?_drop] at hi; exact hi)
  have hk : c.fields.length - 1 - (n + i) = (c.fields.drop n).length - 1 - i := by
    rw [List.length_drop]; omega
  cases f with
  | ordinary A =>
    rw [hk] at h
    rcases h with h | ⟨hu, hlater⟩
    · exact Or.inl h
    · refine Or.inr ⟨hu, fun i' f' hi' hii hm => ?_⟩
      have hlt' : i' < (c.fields.drop n).length := (List.getElem?_eq_some_iff.mp hi').1
      rw [List.length_drop] at hlt'
      have hk' : c.fields.length - 1 - (n + i') = (c.fields.drop n).length - 1 - i' := by
        rw [List.length_drop]; omega
      have := hlater (n + i') f' (by rw [List.getElem?_drop] at hi'; exact hi') (by omega)
        (by rw [hk']; exact hm)
      rwa [show n + i' - (n + i) - 1 = i' - i - 1 by omega] at this
  | reflexive _ _ => exact h
  | container => exact h

/-- A domain not using the member's variable is not the member
field. -/
theorem isMember_false_of_usesVar {k : Nat} {A : Expr} (hu : A.usesVar (N.memberVar k) = false) :
    N.isMember k (.ordinary A) = false := by
  cases A with
  | bvar j =>
    simp only [Expr.usesVar_bvar, decide_eq_false_iff_not] at hu
    simp [NestInfo.isMember, hu]
  | _ => rfl

/-- **An ordinary field of the container, read in the block's terms**
(the member field included): its translated field's set at any member
set `X` is the container's own field set at the instantiation `psK X`
— whatever the regime and the approximant (an ordinary field's set is
its domain's reading). -/
theorem classFieldSet_eq_ordinary (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) {fields : List Field} {n : Nat} (hd : c.fields.drop n = fields)
    {i : Nat} {A : Expr} (hi : fields[i]? = some (.ordinary A)) (X : V) (Q : V → Prop) (ps : List V)
    (W : List V → V) {fs : List V} (hk : fs.length = fields.length - 1 - i) :
    S.classFieldSet M ls N X Q ps fs (S.classField N (fields.length - 1 - i) (.ordinary A))
      = N.KS.fieldSet M (S.lsK ls N) W (S.psK M ls N ps X) fs (.ordinary A) := by
  have hpf := positive_field N hf.positive hc hd hi
  have hpN : N.p < N.nPK := hf.positive.2.1
  rcases hpf with rfl | ⟨hu, -⟩
  · -- the member field
    simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, classFieldSet, fieldSet,
      interp_bvar]
    rw [S.read_memberVar M ls N hlen hpN hk]
  · -- an ordinary field, not mentioning the member
    rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)]
    simp only [classFieldSet, fieldSet]
    rw [interp_instChainAt M (S.ψ ls) (envP ps) (S.classArgs N 0) _ fs hk, S.classArgs_read M ls N ps,
      interp_instL]
    -- the container's scope of the domain
    have hlt : i < fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hsc : Expr.Scoped env N.KS.lparams (N.KS.nP + (fields.length - 1 - i)) A := by
      have := (hKS.2.2.2.1 c hc).1 (n + i) (.ordinary A)
        (by subst hd; rw [List.getElem?_drop] at hi; exact hi)
      subst hd
      rw [List.length_drop] at hlt ⊢
      rwa [show c.fields.length - 1 - (n + i) = c.fields.length - n - 1 - i by omega] at this
    have hnPK : N.KS.nP = N.nPK := rfl
    -- the valuation: the container's parameters instantiated
    rw [interp_lparams (ps := N.K.lparams) hsc.2.2 (φ' := N.KS.ψ (S.lsK ls N))
      (fun m hm => (valOf_map_eval (S.ψ ls) (ps := N.K.lparams) hlsK hm).symm)]
    -- the environment below the container's parameters, then the member's position
    have hG : interp M (N.KS.ψ (S.lsK ls N))
        (consList fs (consList (S.classArgsV M ls N ps
          (interp M (S.ψ ls) (envP ps) (S.famAt 0 (N.idx.map (Expr.liftN 0 ·))))).reverse (envP ps))) A
        = interp M (N.KS.ψ (S.lsK ls N))
          (consList fs (envP (S.psK M ls N ps
            (interp M (S.ψ ls) (envP ps) (S.famAt 0 (N.idx.map (Expr.liftN 0 ·))))))) A := by
      refine interp_closedAt (k := N.KS.nP + (fields.length - 1 - i)) hsc.1 fun j hj => ?_
      rw [show envP (S.psK M ls N ps _) = consList (S.classArgsV M ls N ps _).reverse base from rfl,
        ← consList_append, ← consList_append]
      refine consList_agree_lt j ?_
      have h1 : N.KS.nP = N.args.length + 1 := hlen.symm
      have h2 : N.p ≤ N.args.length := by
        have h3 := hpN; have h4 := hlen; unfold NestInfo.nPK at h3 h4; omega
      simp only [List.length_append, List.length_reverse, hk]
      unfold classArgsV
      simp only [List.length_append, List.length_map, List.length_take, List.length_drop,
        List.length_singleton]
      omega
    rw [hG, S.read_pfree M ls N hlen hpN hk ps _ X _ hu]

/-- **A field of the container, read in the block's terms**: its
translated field's set at a member set `X` and a restriction `Q` is
the container's own field set at the instantiation `psK X`, relative
to an approximant whose fibre is the container's family at `X`
restricted by `Q`. -/
theorem classFieldSet_eq (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) {fields : List Field} {n : Nat} (hd : c.fields.drop n = fields)
    {i : Nat} {f : Field} (hi : fields[i]? = some f) (X : V) (Q : V → Prop) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hX : X ∈ˢ (univ (S.u₀ ls) : V))
    {W : List V → V}
    (hW : ∀ y, y ∈ˢ W [] ↔ (y ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] ∧ Q y))
    {fs : List V} (hk : fs.length = fields.length - 1 - i) :
    S.classFieldSet M ls N X Q ps fs (S.classField N (fields.length - 1 - i) f)
      = N.KS.fieldSet M (S.lsK ls N) W (S.psK M ls N ps X) fs f := by
  have hpf := positive_field N hf.positive hc hd hi
  cases f with
  | ordinary A => exact S.classFieldSet_eq_ordinary M ls N hf hlen hlsK hKS hc hd hi X Q ps W hk
  | reflexive tele es =>
    obtain ⟨rfl, rfl⟩ := hpf
    simp only [classField, classFieldSet, fieldSet, piCtx_nil, idxVals, List.map_nil,
      List.reverse_nil]
    rw [S.classSet_eq_Fam hf hp hX]
    apply ext
    intro y
    rw [mem_sep, hW]
  | container => exact hpf.elim

theorem ClassFits_length' {X : V} {Q : V → Prop} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.ClassFits M ls N X Q ps fields fs → fs.length = fields.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [ClassFits_length' h.1]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **The translated fields fit exactly when the container's own fields
fit at the instantiation.** -/
theorem ClassFits_iff (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) (X : V) (Q : V → Prop) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hX : X ∈ˢ (univ (S.u₀ ls) : V))
    {W : List V → V}
    (hW : ∀ y, y ∈ˢ W [] ↔ (y ∈ˢ N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] ∧ Q y)) :
    ∀ {fields : List Field} {n : Nat}, c.fields.drop n = fields → ∀ {fs : List V},
      S.ClassFits M ls N X Q ps (S.classFields N fields) fs ↔
        N.KS.FitsFields M (S.lsK ls N) W (S.psK M ls N ps X) fields fs
  | [], _, _, [] => by simp [ClassFits, FitsFields]
  | [], _, _, _ :: _ => by simp [ClassFits, FitsFields]
  | _ :: _, _, _, [] => by simp [ClassFits, FitsFields]
  | f :: rest, n, hd, v :: vs => by
    have hd' : c.fields.drop (n + 1) = rest := by rw [← List.drop_drop, hd]; rfl
    have ih := ClassFits_iff hf hlen hlsK hKS hc X Q hp hX hW hd' (fs := vs)
    simp only [classFields_cons, ClassFits, FitsFields]
    rw [ih]
    constructor
    · rintro ⟨h1, h2⟩
      have hl : vs.length = rest.length := N.KS.FitsFields_length M _ h1
      refine ⟨h1, ?_⟩
      have := S.classFieldSet_eq M ls N hf hlen hlsK hKS hc hd (i := 0) rfl X Q hp hX hW
        (fs := vs) (by simpa using hl)
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at this
      rwa [this] at h2
    · rintro ⟨h1, h2⟩
      have hl : vs.length = rest.length := N.KS.FitsFields_length M _ h1
      refine ⟨h1, ?_⟩
      have := S.classFieldSet_eq M ls N hf hlen hlsK hKS hc hd (i := 0) rfl X Q hp hX hW
        (fs := vs) (by simpa using hl)
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero] at this
      rwa [this]

/-- The container's constructors are tagged from `0`. -/
theorem KS_tagOf (j : Nat) : N.KS.tagOf j = j := by
  simp [IndSpec.tagOf, IndSpec.nKS, NestInfo.KS, IndBase.spec]

/-- **The class's laws** from the container's fixed point: inversion,
introduction and induction are the container's `mem_Fam`,
`ctorVal_mem_Fam` and `Fam_induction` at the instantiation, read in
the block's terms through `ClassFits_iff`; size and monotonicity are
the container's clause (`contClause_of`). -/
theorem classLaws_of (hf : S.NestFacts M ls N) (hlen : N.args.length + 1 = N.nPK)
    (hlsK : N.lsK.length = N.K.lparams.length) (hKS : N.KS.Scoped env) (hN : S.nest = some N)
    (hz : S.z ls = false) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps) :
    S.ClassLaws M ls N ps where
  inv := fun X hX x hx => by
    have hzK : N.KS.z (S.lsK ls N) = false := by rw [hf.z_eq]; exact hz
    have hbX := hf.domsBoundedK hp hX
    rw [S.classSet_eq_Fam hf hp hX, N.KS.mem_Fam_false M _ hf.noRecDep hbX (hf.contOkK _) hzK] at hx
    obtain ⟨j, c, fs, hc, hfit, -, hx'⟩ := hx
    refine ⟨j, c, fs, hc, ?_, by rw [hx', KS_tagOf]⟩
    simp only [classCtor]
    rw [S.ClassFits_iff M ls N hf hlen hlsK hKS (List.mem_of_getElem? hc) X (fun _ => True) hp hX
      (W := N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X)) (fun _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      (List.drop_zero (l := c.fields))]
    exact hfit
  intro := fun X hX j c fs hc hfit => by
    have hzK : N.KS.z (S.lsK ls N) = false := by rw [hf.z_eq]; exact hz
    have hbX := hf.domsBoundedK hp hX
    have hcm := List.mem_of_getElem? hc
    simp only [classCtor] at hfit
    rw [S.ClassFits_iff M ls N hf hlen hlsK hKS hcm X (fun _ => True) hp hX
      (W := N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X)) (fun _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      (List.drop_zero (l := c.fields))] at hfit
    have := N.KS.ctorVal_mem_Fam M (S.lsK ls N) hf.noRecDep hbX (hf.contOkK _) hc hfit
    rw [S.KS_idxVals hf hcm] at this
    simp only [ctorVal, hzK, Bool.false_eq_true, if_false, KS_tagOf] at this
    rw [S.classSet_eq_Fam hf hp hX]
    exact this
  ind := fun X hX Q hQ x hx => by
    have hzK : N.KS.z (S.lsK ls N) = false := by rw [hf.z_eq]; exact hz
    have hbX := hf.domsBoundedK hp hX
    rw [S.classSet_eq_Fam hf hp hX] at hx
    refine N.KS.Fam_induction M _ hf.noRecDep hbX (hf.contOkK _) (fun _ y => Q y) ?_ [] x hx
    intro is y hs
    obtain ⟨j, c, fs, hc, hfit, -, rfl⟩ := hs
    have hcm := List.mem_of_getElem? hc
    simp only [ctorVal, hzK, Bool.false_eq_true, if_false, KS_tagOf]
    refine hQ j c fs hc ?_
    simp only [classCtor]
    rw [S.ClassFits_iff M ls N hf hlen hlsK hKS hcm X _ hp hX
      (W := fun is' => sep (N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) is') fun y => Q y)
      (fun y => by
        rw [mem_sep, S.classSet_eq_Fam hf hp hX]
        exact ⟨fun h => ⟨h.1, h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩)
      (List.drop_zero (l := c.fields))]
    exact hfit
  mem_univ := fun X hX => (S.contClause_of hf hN hp).mem_univ X hX
  mono := fun X Y hXY hX hY => (S.contClause_of hf hN hp).mono X Y hXY hX hY

end Corr

end IndSpec

end Fragment
