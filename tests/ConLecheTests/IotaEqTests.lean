module

public import ConLeche.Denotes
public import ConLeche.Kernel.Basis.Eq
public import ConLeche.Kernel.Basis.Quot
meta import ConLeche.Denotes
meta import ConLeche.Kernel.Basis.Eq
meta import ConLeche.Kernel.Basis.Quot

public section

/-!
# The recursor rules as propositions (task #610 spike 2)

`iotaEq` builds a recursor rule's ι equation as a closed `∀ … , @Eq …`
term.  The `#guard`s pin it on the pinned `Eq.rec` (an indexed family:
the index comes from `Eq.refl`'s conclusion), `Quot.lift` and `Quot.ind`
(the quotient eliminators are stored recursors) and a two-constructor
enumeration.  The theorem at the end is what the equations are for: in
every model where they hold, the enumeration's constructors denote
different sets.
-/

namespace ConLeche.IotaEqTest

open BasisDSL SetTheory ConLeche.SetModel

/-- Looking up the pinned `Eq` and `Quot` blocks. -/
def basisFind (n : Name) : Option ConstantInfo :=
  (eqBasis ++ quotBasis).find? (·.name == n)

/-- The first rule's equation of a stored recursor. -/
def firstEq (find? : Name → Option ConstantInfo) : ConstantInfo → Option Expr
  | .recInfo cv mI rP _ (rl :: _) => iotaEq find? cv mI rP rl
  | _ => none

/-- A rule's right-hand side. -/
def firstRhs : ConstantInfo → Expr
  | .recInfo _ _ _ _ (rl :: _) => rl.rhs
  | _ => default

/- `Eq.rec`: `∀ α a motive refl, @Eq.{u_1} (motive a (Eq.refl a))
(Eq.rec α a motive refl a (Eq.refl α a)) (rhs α a motive refl)` — the
index `a` is the second argument of `Eq.refl`'s conclusion `Eq α a a`. -/
#guard firstEq basisFind eqRecA == some (
  pi "α" (srt u) <|
  pi "a" (bv 0) <|
  pi "motive" eqRecMotive <|
  pi "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
  ap3 (cnst eqName [u1])
    (ap2 (bv 1) (bv 2) (ap2 (cnst eqReflName [u]) (bv 3) (bv 2)))
    (Expr.mkAppN (cnst (eqName.str "rec") [u1, u])
      [bv 3, bv 2, bv 1, bv 0, bv 2, ap2 (cnst eqReflName [u]) (bv 3) (bv 2)])
    (Expr.mkAppN (firstRhs eqRecA) [bv 3, bv 2, bv 1, bv 0]))

/- `Quot.lift`: `∀ α r β f h a, @Eq.{v} β (Quot.lift f h (Quot.mk r a)) (rhs α r β f h a)`. -/
#guard firstEq basisFind quotLiftA == some (
  pi "α" (srt u) <|
  pi "r" quotRel <|
  pi "β" (srt v) <|
  pi "f" quotLiftF <|
  pi "h" quotLiftH <|
  pi "a" (bv 4) <|
  ap3 (cnst eqName [v]) (bv 3)
    (Expr.mkAppN (cnst quotLiftName [u, v])
      [bv 5, bv 4, bv 3, bv 2, bv 1, ap3 (cnst quotMkName [u]) (bv 5) (bv 4) (bv 0)])
    (Expr.mkAppN (firstRhs quotLiftA) [bv 5, bv 4, bv 3, bv 2, bv 1, bv 0]))

/- `Quot.ind`: `∀ α r β mk a, @Eq.{0} (β (Quot.mk r a)) (Quot.ind mk (Quot.mk r a)) (rhs …)`. -/
#guard firstEq basisFind quotIndA == some (
  pi "α" (srt u) <|
  pi "r" quotRel <|
  pi "β" quotIndMotive <|
  pi "mk" quotIndMk <|
  pi "a" (bv 3) <|
  ap3 (cnst eqName [.zero])
    (.app (bv 2) (ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 0)))
    (Expr.mkAppN (cnst quotIndName [u])
      [bv 4, bv 3, bv 2, bv 1, ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 0)])
    (Expr.mkAppN (firstRhs quotIndA) [bv 4, bv 3, bv 2, bv 1, bv 0]))

/-! ### `inductive T | a | b` -/

/-- `T`. -/
def tN : Name := bn "T"
/-- `T.a`. -/
def taN : Name := tN.str "a"
/-- `T.b`. -/
def tbN : Name := tN.str "b"
/-- `T.rec`. -/
def trecN : Name := tN.str "rec"

/-- The motive's domain: `T → Sort u`. -/
def tMotive : Expr := piA (cnst tN) (srt u)

/-- The minors' domains, in the motive's context. -/
def tMinA : Expr := .app (bv 0) (cnst taN)
/-- The second minor's domain, in the motive's and the first minor's context. -/
def tMinB : Expr := .app (bv 1) (cnst tbN)

/-- `T.a : T`. -/
def taCV : ConstantVal := ⟨taN, [], cnst tN⟩
/-- `T.b : T`. -/
def tbCV : ConstantVal := ⟨tbN, [], cnst tN⟩

/-- `T.rec.{u} : (motive : T → Sort u) → motive T.a → motive T.b → (t : T) → motive t`. -/
def trecCV : ConstantVal :=
  ⟨trecN, [uN], pi "motive" tMotive <| pi "a" tMinA <| pi "b" tMinB <|
    pi "t" (cnst tN) (.app (bv 3) (bv 0))⟩

/-- The rule for `T.a`: the first minor. -/
def ruleA : RecRule := rule taN 0 (lm "motive" tMotive <| lm "a" tMinA <| lm "b" tMinB <| bv 1)
/-- The rule for `T.b`: the second minor. -/
def ruleB : RecRule := rule tbN 0 (lm "motive" tMotive <| lm "a" tMinA <| lm "b" tMinB <| bv 0)

/-- The equation of the rule for the constructor `c` with right-hand side `r`. -/
def tEq (c : Name) (r : Expr) : Expr :=
  pi "motive" tMotive <| pi "a" tMinA <| pi "b" tMinB <|
    ap3 (cnst eqName [u]) (.app (bv 2) (cnst c))
      (Expr.mkAppN (cnst trecN [u]) [bv 2, bv 1, bv 0, cnst c])
      (Expr.mkAppN r [bv 2, bv 1, bv 0])

/-- A lookup holding only the two constructors. -/
def tFind (n : Name) : Option ConstantInfo :=
  [ConstantInfo.ctorInfo taCV 0 0 tN, .ctorInfo tbCV 0 0 tN].find? (·.name == n)

#guard iotaEq tFind trecCV 3 3 ruleA == some (tEq taN ruleA.rhs)
#guard iotaEq tFind trecCV 3 3 ruleB == some (tEq tbN ruleB.rhs)

theorem iotaEq_ruleA {find? : Name → Option ConstantInfo}
    (h : find? taN = some (.ctorInfo taCV 0 0 tN)) :
    iotaEq find? trecCV 3 3 ruleA = some (tEq taN ruleA.rhs) := by
  unfold iotaEq; rw [show ruleA.ctor = taN from rfl, h]; rfl

theorem iotaEq_ruleB {find? : Name → Option ConstantInfo}
    (h : find? tbN = some (.ctorInfo tbCV 0 0 tN)) :
    iotaEq find? trecCV 3 3 ruleB = some (tEq tbN ruleB.rhs) := by
  unfold iotaEq; rw [show ruleB.ctor = tbN from rfl, h]; rfl

/-! ### The constructors are distinct in every model of the rules -/

universe w
variable {V : Type w} [SetTheory V]

theorem Denotes_pi_inv {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {A B : Expr} {X : V} (h : Denotes cval env φ ρ (.forallE A B) X) :
    ∃ A' B', X = piV A' B' ∧ Denotes cval env φ ρ A A' ∧
      ∀ x, x ∈ˢ A' → Denotes cval env φ (push x ρ) B (B' x) := by
  cases h with
  | pi hA hB => exact ⟨_, _, rfl, hA, hB⟩

theorem Denotes_app_inv {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {f a : Expr} {X : V} (h : Denotes cval env φ ρ (.app f a) X) :
    ∃ F Y, X = app F Y ∧ Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a Y := by
  cases h with
  | app hf ha => exact ⟨_, _, rfl, hf, ha⟩

/-- A constant without level parameters, read. -/
theorem Denotes_const0 {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {n : Name} {cv : ConstantVal} {nP nF : Nat} {T : Name}
    (hf : env.find? n = some (.ctorInfo cv nP nF T)) (hl : cv.levelParams = []) :
    Denotes cval env φ ρ (.const n []) (cval n (Level.substFn φ [] [])) := by
  have h := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) (us := []) hf (by simp [ConstantInfo.toConstantVal, hl])
  simpa [ConstantInfo.toConstantVal, hl] using h

/-- The constant assignment `1`: the motive's universe is `Type`. -/
def one : LevelParam → Nat := fun _ => 1

theorem substFn_nil (φ : LevelParam → Nat) : Level.substFn φ [] [] = φ := rfl

theorem substFn_self (φ : LevelParam → Nat) : Level.substFn φ [uN] [u] = φ := by
  funext q; simp only [Level.substFn]; split <;> simp_all [Level.eval, u]

/-- `T` reads as `cval T`. -/
theorem Denotes_T {env : Env} (M : Model V env)
    (hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {})) (ρ : BVarIdx → V) :
    Denotes M.cval env one ρ (cnst tN) (M.cval tN one) := by
  have h := Denotes.const (cval := M.cval) (φ := one) (ρ := ρ) (us := []) hT rfl
  simpa [ConstantInfo.toConstantVal, substFn_nil, cnst] using h

/-- A constructor of `T` is a member of what `T` denotes. -/
theorem mem_ctor {env : Env} (M : Model V env)
    (hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {}))
    {c : Name} {cv : ConstantVal} (hn : cv.name = c) (ht : cv.type = cnst tN)
    (hf : env.find? c = some (.ctorInfo cv 0 0 tN)) : M.cval c one ∈ˢ M.cval tN one := by
  obtain ⟨Z, hZ, hm⟩ := M.mem _ (List.mem_of_find?_eq_some hf) one (fun _ => empty)
  simp only [ConstantInfo.toConstantVal, ConstantInfo.name, hn, ht] at hZ hm
  obtain rfl := Denotes_functional hZ (Denotes_T M hT _)
  exact hm

/-- **Reading the motive and the minors.**  A member `x` of what
`∀ (motive : T → Sort u) (a : motive T.a) (b : motive T.b), body` denotes,
applied to the motive `fun _ => Prop` and the minors `∅` and `{pt}`, is a
member of what `body` denotes there. -/
theorem tele_app {env : Env} (M : Model V env)
    (hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {}))
    (hTa : env.find? taN = some (.ctorInfo taCV 0 0 tN))
    (hTb : env.find? tbN = some (.ctorInfo tbCV 0 0 tN))
    {ρ : BVarIdx → V} {body : Expr} {X x : V}
    (hX : Denotes M.cval env one ρ (pi "motive" tMotive <| pi "a" tMinA <| pi "b" tMinB body) X)
    (hx : x ∈ˢ X) :
    ∃ Y, Denotes M.cval env one
        (push unitSet (push empty (push (lamV (M.cval tN one) fun _ => univ 0) ρ))) body Y ∧
      app (app (app x (lamV (M.cval tN one) fun _ => univ 0)) empty) unitSet ∈ˢ Y := by
  let cT := M.cval tN one
  let m : V := lamV cT fun _ => univ 0
  have hTd := Denotes_T M hT
  have happ : ∀ {c : Name} {cv : ConstantVal}, cv.name = c → cv.levelParams = [] →
      cv.type = cnst tN → env.find? c = some (.ctorInfo cv 0 0 tN) →
      ∀ (i : Nat) (ρ' : BVarIdx → V), ρ' i = m →
      ∀ Y, Denotes M.cval env one ρ' (.app (bv i) (cnst c)) Y → Y = univ 0 := by
    intro c cv hn hl ht hf i ρ' h0 Y hY
    obtain ⟨F, Z, rfl, hF, hZ⟩ := Denotes_app_inv hY
    cases hF
    obtain rfl := Denotes_functional hZ (Denotes_const0 hf hl)
    rw [h0, substFn_nil]
    exact app_lamV (mem_ctor M hT hn ht hf)
  -- the motive
  obtain ⟨A1, B1, rfl, hA1, hB1⟩ := Denotes_pi_inv hX
  obtain rfl := Denotes_functional hA1 (.pi (hTd ρ) fun _ _ => .sort)
  have hm : m ∈ˢ piV cT (fun _ => univ (Level.eval one u)) :=
    lamV_mem (fun _ _ => univ_mem_univ 0) (fun _ _ => IsTy_univ _)
  -- the first minor
  obtain ⟨A2, B2, hB2e, hA2, hB2⟩ := Denotes_pi_inv (hB1 m hm)
  have hx1 := app_mem_piV hx hm
  rw [hB2e] at hx1
  obtain rfl := happ (c := taN) rfl rfl rfl hTa 0 _ rfl _ hA2
  have hx2 := app_mem_piV hx1 (empty_mem_univ 0)
  -- the second minor
  obtain ⟨A3, B3, hB3e, hA3, hB3⟩ := Denotes_pi_inv (hB2 empty (empty_mem_univ 0))
  rw [hB3e] at hx2
  obtain rfl := happ (c := tbN) rfl rfl rfl hTb 1 _ rfl _ hA3
  exact ⟨_, hB3 unitSet (unitSet_mem_univ 0), app_mem_piV hx2 (unitSet_mem_univ 0)⟩

/-- Every piece of an equation of `T.rec` denotes at every valuation, once `Eq` is stored. -/
theorem den_pi {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ty body : Expr} (hA : ∀ ρ, ∃ A, Denotes cval env φ ρ ty A)
    (hB : ∀ ρ, ∃ Y, Denotes cval env φ ρ body Y) (ρ : BVarIdx → V) :
    ∃ X, Denotes cval env φ ρ (.forallE ty body) X := by
  obtain ⟨A, hA⟩ := hA ρ
  exact ⟨_, .pi hA fun x _ => (hB (push x ρ)).choose_spec⟩

theorem den_lam {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ty body : Expr} (hA : ∀ ρ, ∃ A, Denotes cval env φ ρ ty A)
    (hB : ∀ ρ, ∃ Y, Denotes cval env φ ρ body Y) (ρ : BVarIdx → V) :
    ∃ X, Denotes cval env φ ρ (.lam ty body) X := by
  obtain ⟨A, hA⟩ := hA ρ
  exact ⟨_, .lam hA fun x _ => (hB (push x ρ)).choose_spec⟩

theorem den_app {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {f a : Expr} (hf : ∀ ρ, ∃ F, Denotes cval env φ ρ f F)
    (ha : ∀ ρ, ∃ Y, Denotes cval env φ ρ a Y) (ρ : BVarIdx → V) :
    ∃ X, Denotes cval env φ ρ (.app f a) X := by
  obtain ⟨F, hf⟩ := hf ρ
  obtain ⟨Y, ha⟩ := ha ρ
  exact ⟨_, .app hf ha⟩

/-- **A rule's equation denotes**, where `Eq` is stored with one level parameter. -/
theorem den_tEq {env : Env} (M : Model V env)
    (hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {}))
    (hTa : env.find? taN = some (.ctorInfo taCV 0 0 tN))
    (hTb : env.find? tbN = some (.ctorInfo tbCV 0 0 tN))
    (hR : env.find? trecN = some (.recInfo trecCV 3 3 false [ruleA, ruleB]))
    {eqI : ConstantInfo} (hEq : env.find? eqName = some eqI)
    (hEl : eqI.toConstantVal.levelParams.length = 1)
    {c : Name} {cv : ConstantVal} (hl : cv.levelParams = [])
    (hf : env.find? c = some (.ctorInfo cv 0 0 tN)) {r : Expr}
    (hr : ∀ ρ, ∃ Y, Denotes M.cval env one ρ r Y) (ρ : BVarIdx → V) :
    ∃ P, Denotes M.cval env one ρ (tEq c (lm "motive" tMotive <| lm "a" tMinA <| lm "b" tMinB r))
      P := by
  have hc : ∀ {n : Name} {cv : ConstantVal}, cv.levelParams = [] →
      env.find? n = some (.ctorInfo cv 0 0 tN) → ∀ ρ, ∃ Y, Denotes M.cval env one ρ (cnst n) Y :=
    fun hl hf ρ => ⟨_, Denotes_const0 hf hl⟩
  have hb : ∀ i ρ, ∃ Y, Denotes M.cval env one ρ (bv i) Y := fun _ _ => ⟨_, .bvar⟩
  have hTd : ∀ ρ, ∃ Y, Denotes M.cval env one ρ (cnst tN) Y := fun ρ => ⟨_, Denotes_T M hT ρ⟩
  have hmot : ∀ ρ, ∃ Y, Denotes M.cval env one ρ tMotive Y :=
    den_pi hTd fun _ => ⟨_, .sort⟩
  have hmA : ∀ ρ, ∃ Y, Denotes M.cval env one ρ tMinA Y := den_app (hb 0) (hc rfl hTa)
  have hmB : ∀ ρ, ∃ Y, Denotes M.cval env one ρ tMinB Y := den_app (hb 1) (hc rfl hTb)
  have hrhs := den_lam hmot (den_lam hmA (den_lam hmB hr))
  have hrec : ∀ ρ, ∃ Y, Denotes M.cval env one ρ (cnst trecN [u]) Y :=
    fun _ => ⟨_, .const hR rfl⟩
  have heq : ∀ ρ, ∃ Y, Denotes M.cval env one ρ (cnst eqName [u]) Y :=
    fun _ => ⟨_, .const hEq (by rw [hEl]; rfl)⟩
  exact den_pi hmot (den_pi hmA (den_pi hmB (den_app (den_app (den_app heq
    (den_app (hb 2) (hc hl hf)))
    (den_app (den_app (den_app (den_app hrec (hb 2)) (hb 1)) (hb 0)) (hc hl hf)))
    (den_app (den_app (den_app hrhs (hb 2)) (hb 1)) (hb 0))))) ρ

/-- **In every model of `inductive T | a | b` with its recursor where the ι
equations hold, `T.a` and `T.b` denote different sets** (at the level
assignment `1`, which the constructors, having no level parameters, are
read at alongside the motive's universe `Type`).  At the motive
`fun _ => Prop` and the minors `False` (`∅`) and `True` (`{pt}`), the two
rule equations make `T.rec` send `T.a` to `∅` and `T.b` to `{pt}`. -/
theorem T_a_ne_T_b {env : Env} (M : Model V env) (hrules : RuleEqsHold M.cval env)
    (hT : env.find? tN = some (.indInfo ⟨tN, [], srt (.succ .zero)⟩ {}))
    (hTa : env.find? taN = some (.ctorInfo taCV 0 0 tN))
    (hTb : env.find? tbN = some (.ctorInfo tbCV 0 0 tN))
    (hR : env.find? trecN = some (.recInfo trecCV 3 3 false [ruleA, ruleB]))
    {eqI : ConstantInfo} (hEq : env.find? eqName = some eqI)
    (hEl : eqI.toConstantVal.levelParams.length = 1) :
    M.cval taN one ≠ M.cval tbN one := by
  intro hab
  let ρ : BVarIdx → V := fun _ => empty
  let cT := M.cval tN one
  let m : V := lamV cT fun _ => univ 0
  let ρ3 : BVarIdx → V := push unitSet (push empty (push m ρ))
  have hRmem := List.mem_of_find?_eq_some hR
  -- the recursor's value at the motive, the minors and a constructor is a truth value
  obtain ⟨XR, hXR, hmR⟩ := M.mem _ hRmem one ρ
  obtain ⟨Y4, hY4, hy4⟩ := tele_app M hT hTa hTb hXR hmR
  obtain ⟨A4, B4, rfl, hA4, hB4⟩ := Denotes_pi_inv hY4
  obtain rfl := Denotes_functional hA4 (Denotes_T M hT ρ3)
  have hrecTy : ∀ {c : Name} {cv : ConstantVal}, cv.name = c → cv.levelParams = [] →
      cv.type = cnst tN → env.find? c = some (.ctorInfo cv 0 0 tN) →
      app (app (app (app (M.cval trecN one) m) empty) unitSet) (M.cval c one) ∈ˢ (univ 0 : V) := by
    intro c cv hn hl ht hf
    have hc := mem_ctor M hT hn ht hf
    have h := app_mem_piV hy4 hc
    have hb : Denotes M.cval env one (push (M.cval c one) ρ3) (.app (bv 3) (bv 0)) (app m (M.cval c one)) :=
      .app .bvar .bvar
    rw [Denotes_functional (hB4 _ hc) hb, app_lamV hc] at h
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, trecCV] using h
  -- one rule's equation
  have hrule : ∀ {c : Name} {cv : ConstantVal} {rl : RecRule} (sel : V), cv.name = c →
      cv.levelParams = [] → cv.type = cnst tN → env.find? c = some (.ctorInfo cv 0 0 tN) →
      rl ∈ [ruleA, ruleB] → iotaEq env.find? trecCV 3 3 rl = some (tEq c rl.rhs) →
      Denotes M.cval env one ρ3 (Expr.mkAppN rl.rhs [bv 2, bv 1, bv 0]) sel →
      sel ∈ˢ (univ 0 : V) →
      app (app (app (app (M.cval trecN one) m) empty) unitSet) (M.cval c one) = sel := by
    intro c cv rl sel hn hl ht hf hrl he hsel hselU
    obtain ⟨P, hP⟩ : ∃ P, Denotes M.cval env one ρ (tEq c rl.rhs) P := by
      rcases List.mem_cons.mp hrl with rfl | hrl
      · exact den_tEq M hT hTa hTb hR hEq hEl hl hf (fun _ => ⟨_, .bvar⟩) ρ
      · obtain rfl := List.mem_singleton.mp hrl
        exact den_tEq M hT hTa hTb hR hEq hEl hl hf (fun _ => ⟨_, .bvar⟩) ρ
    have hmem : tEq c rl.rhs ∈ ruleEqs env := by
      refine List.mem_flatMap.mpr ⟨_, hRmem, ?_⟩
      simp only [ConstantInfo.name, ConstantInfo.toConstantVal, trecCV]
      rw [hR]
      exact List.mem_filterMap.mpr ⟨rl, hrl, he⟩
    obtain ⟨x, hx⟩ := hrules _ hmem one ρ P hP
    obtain ⟨Y, hY, hy⟩ := tele_app M hT hTa hTb hP hx
    obtain ⟨F, R, rfl, hF, hR'⟩ := Denotes_app_inv hY
    obtain ⟨F', L, rfl, hF', hL⟩ := Denotes_app_inv hF
    obtain ⟨E, TY, rfl, hE, hTY⟩ := Denotes_app_inv hF'
    obtain rfl := Denotes_functional hR' hsel
    have hc := mem_ctor M hT hn ht hf
    obtain rfl := Denotes_functional hTY (.app .bvar (Denotes_const0 hf hl))
    have hL' : Denotes M.cval env one ρ3 (Expr.mkAppN (cnst trecN [u]) [bv 2, bv 1, bv 0, cnst c])
        (app (app (app (app (M.cval trecN one) m) empty) unitSet) (M.cval c one)) := by
      have h := Denotes.const (cval := M.cval) (φ := one) (ρ := ρ3) (us := [u]) hR rfl
      simp only [ConstantInfo.toConstantVal, trecCV, substFn_self] at h
      exact .app (.app (.app (.app h .bvar) .bvar) .bvar) (show Denotes _ _ _ _ (cnst c) _ from Denotes_const0 (ρ := ρ3) hf hl)
    obtain rfl := Denotes_functional hL hL'
    rw [show push unitSet (push empty (push m ρ)) 2 = m from rfl, substFn_nil, app_lamV hc] at hy
    rw [M.eq_equality u one ρ3 E _ _ _ hE (univ_mem_univ 0) (hrecTy hn hl ht hf) hselU] at hy
    exact eq_of_mem_eqv hy
  -- the right-hand sides: the first and the second minor
  have hlam : ∀ (r : Expr) (sel : V → V → V), (∀ a b (ρ' : BVarIdx → V), Denotes M.cval env one
      (push b (push a ρ')) r (sel a b)) →
      Denotes M.cval env one ρ3 (Expr.mkAppN (lm "motive" tMotive <| lm "a" tMinA <| lm "b" tMinB r)
        [bv 2, bv 1, bv 0]) (sel empty unitSet) := by
    intro r sel hr
    have hmin : ∀ {c : Name} {cv : ConstantVal}, cv.name = c → cv.levelParams = [] →
        cv.type = cnst tN → env.find? c = some (.ctorInfo cv 0 0 tN) →
        ∀ (i : Nat) (ρ' : BVarIdx → V) (m' : V), ρ' i = m' →
        Denotes M.cval env one ρ' (.app (bv i) (cnst c)) (app m' (M.cval c one)) := by
      intro c cv hn hl ht hf i ρ' m' h
      have h2 := Denotes.app (cval := M.cval) (env := env) (φ := one) (ρ := ρ') (Denotes.bvar (i := i))
        (show Denotes _ _ _ _ (cnst c) _ from Denotes_const0 (ρ := ρ') hf hl)
      rw [h, substFn_nil] at h2
      exact h2
    let A1 : V := piV cT fun _ => univ (Level.eval one u)
    have hL : Denotes M.cval env one ρ3 (lm "motive" tMotive <| lm "a" tMinA <| lm "b" tMinB r)
        (lamV A1 fun m' => lamV (app m' (M.cval taN one)) fun a =>
          lamV (app m' (M.cval tbN one)) fun b => sel a b) :=
      .lam (.pi (Denotes_T M hT ρ3) fun _ _ => .sort) fun m' _ =>
        .lam (hmin (c := taN) (cv := taCV) rfl rfl rfl hTa 0 _ m' rfl) fun a _ =>
          .lam (hmin (c := tbN) (cv := tbCV) rfl rfl rfl hTb 1 _ m' rfl) fun b _ => hr a b _
    have hm : m ∈ˢ A1 := lamV_mem (fun _ _ => univ_mem_univ 0) (fun _ _ => IsTy_univ _)
    have hval := Denotes.app (Denotes.app (Denotes.app hL (Denotes.bvar (i := 2)))
      (Denotes.bvar (i := 1))) (Denotes.bvar (i := 0) (ρ := ρ3))
    have e2 : ρ3 2 = m := rfl
    have e1 : ρ3 1 = empty := rfl
    have e0 : ρ3 0 = unitSet := rfl
    have ha0 : (empty : V) ∈ˢ app m (M.cval taN one) := by
      rw [app_lamV (mem_ctor (c := taN) (cv := taCV) M hT rfl rfl hTa)]; exact empty_mem_univ 0
    have hb0 : (unitSet : V) ∈ˢ app m (M.cval tbN one) := by
      rw [app_lamV (mem_ctor (c := tbN) (cv := tbCV) M hT rfl rfl hTb)]; exact unitSet_mem_univ 0
    rw [e2, e1, e0, app_lamV hm, app_lamV ha0, app_lamV hb0] at hval
    exact hval
  have ha := hrule (c := taN) (cv := taCV) (rl := ruleA) empty rfl rfl rfl hTa (by simp) (iotaEq_ruleA hTa)
    (hlam (bv 1) (fun a _ => a) fun _ _ _ => .bvar) (empty_mem_univ 0)
  have hb := hrule (c := tbN) (cv := tbCV) (rl := ruleB) unitSet rfl rfl rfl hTb (by simp) (iotaEq_ruleB hTb)
    (hlam (bv 0) (fun _ b => b) fun _ _ _ => .bvar) (unitSet_mem_univ 0)
  rw [hab, hb] at ha
  exact not_mem_empty pt (ha ▸ pt_mem_unitSet)

end ConLeche.IotaEqTest
