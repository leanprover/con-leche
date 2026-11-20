module

public import ConLeche.MainTheorem
public import ConLecheTests.IotaEqTests

public section

/-!
# A hidden definition and a hole that contradicts it (task #613)

The shape of the `CmpHomeA`/`CmpHomeC` fixtures: a module defines `f` without exposing its
body, and the challenge imports it and has a hole whose statement contradicts `f`'s value.  A
solution that redeclares `f` with another value, or any other solution, must not be accepted.

`no_model` is the model-level fact: no `Model` of an environment that stores `def f : T := T.a`
and the hole `t : f = T.b` as an axiom exists, because the model makes `f` denote `T.a`
(`Model.defn_eq`), `Eq` is set equality, and `T.a` and `T.b` denote different sets
(`IotaEqTest.T_a_ne_T_b`, from `Model.rule_eqs`).  The hole reads `f`, `T.b` and `Eq`, and `f`
reads `T.a`, so all of the shape is in a challenge's environment that holds the hole and what it
reads.

The fixtures themselves use `def f : Nat := 3` and `t : f = 5`.  The argument is the same; the
step it needs in place of `T_a_ne_T_b` is that `3` and `5` denote different sets in every model,
which follows from `Nat.rec`'s rule equations the same way and is not spelled out here.  The
two-constructor enumeration has the least to read off.
-/

namespace ConLeche.CompareAttackTest

open BasisDSL SetTheory ConLeche.SetModel ConLeche.IotaEqTest

universe w
variable {V : Type w} [SetTheory V]

/-- `f`. -/
@[expose] def fN : Name := bn "f"
/-- The hole `t`. -/
@[expose] def holeN : Name := bn "t"
/-- `f : T`. -/
@[expose] def fCV : ConstantVal := ⟨fN, [], cnst tN⟩
/-- The level `1`: `T : Type`. -/
@[expose] def l1 : Level := .succ .zero
/-- `@Eq.{1} T f T.b`. -/
@[expose] def holeTy : Expr := ap3 (cnst eqName [l1]) (cnst tN) (cnst fN) (cnst tbN)
/-- The hole's statement, `t : f = T.b`. -/
@[expose] def holeCV : ConstantVal := ⟨holeN, [], holeTy⟩

/-- **The attack's environment**: `inductive T | a | b` with its recursor, `Eq` at one level
parameter, `def f : T := T.a` and the hole `t : f = T.b` as the axiom of its statement. -/
structure AttackEnv (env : Env) : Prop where
  hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {})
  hTa : env.find? taN = some (.ctorInfo taCV 0 0 tN)
  hTb : env.find? tbN = some (.ctorInfo tbCV 0 0 tN)
  hRec : env.find? trecN = some (.recInfo trecCV 3 3 false [ruleA, ruleB])
  hEq : ∃ eqI : ConstantInfo, env.find? eqName = some eqI ∧
    eqI.toConstantVal.levelParams.length = 1
  hF : ∃ hint, env.find? fN = some (.defnInfo fCV (cnst taN) hint)
  hHole : env.find? holeN = some (.axiomInfo holeCV)

/-- **No model of the attack's environment**: `f` denotes `T.a`, so the hole's type denotes
`eqv ⟦T.a⟧ ⟦T.b⟧`, which is empty. -/
theorem no_model {env : Env} (M : Model V env) (h : AttackEnv env) : False := by
  obtain ⟨_, hEq, hEqLps⟩ := h.hEq
  obtain ⟨_, hfd⟩ := h.hF
  have hne := T_a_ne_T_b M h.hT h.hTa h.hTb h.hRec hEq hEqLps
  -- `f` denotes `T.a`
  have hfv : M.cval fN one = M.cval taN one :=
    M.cval_of_defn (List.mem_of_find?_eq_some hfd) (φ := one) (ρ := fun _ => empty)
      (Denotes_const0 h.hTa rfl)
  -- the hole's type, read
  obtain ⟨P, hP, hm⟩ := M.mem _ (List.mem_of_find?_eq_some h.hHole) one (fun _ => empty)
  change Denotes M.cval env one _ holeTy P at hP
  obtain ⟨F, B, rfl, hF, hB⟩ := Denotes_app_inv hP
  obtain ⟨F', A, rfl, hF', hA⟩ := Denotes_app_inv hF
  obtain ⟨E, Ty, rfl, hE, hTy⟩ := Denotes_app_inv hF'
  obtain rfl := Denotes_functional hTy (Denotes_T M h.hT _)
  obtain rfl := Denotes_functional hB (Denotes_const0 h.hTb rfl)
  obtain rfl := Denotes_functional hA (Denotes.const hfd rfl)
  -- the three memberships `Eq`'s graph is read at
  have hTU : M.cval tN one ∈ˢ univ (Level.eval one l1) := by
    obtain ⟨Z, hZ, hz⟩ := M.mem _ (List.mem_of_find?_eq_some h.hT) one (fun _ => empty)
    cases hZ
    exact hz
  have ha : M.cval fN (Level.substFn one [] []) ∈ˢ M.cval tN one := by
    rw [substFn_nil, hfv]; exact mem_ctor M h.hT rfl rfl h.hTa
  have hb : M.cval tbN (Level.substFn one [] []) ∈ˢ M.cval tN one := by
    rw [substFn_nil]; exact mem_ctor M h.hT rfl rfl h.hTb
  change _ ∈ˢ app (app (app E (M.cval tN one)) (M.cval fN (Level.substFn one [] [])))
    (M.cval tbN (Level.substFn one [] [])) at hm
  rw [M.eq_equality l1 one _ E _ _ _ hE hTU ha hb] at hm
  have he := eq_of_mem_eqv hm
  have he' : M.cval fN one = M.cval tbN one := he
  exact hne (hfv ▸ he')

open Frontend in
end ConLeche.CompareAttackTest
