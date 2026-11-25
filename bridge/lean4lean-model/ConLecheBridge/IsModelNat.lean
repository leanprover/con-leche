import ConLeche.Semantics.IsModelBasis
import ConLeche.Kernel.Basis.Nat
import ConLeche.SetTheory.Derive.Natrec

/-!
# `Nat` in a model of a stream

`IsModel` (`ConLeche/IsModel.lean`) fixes nothing by name: `Nat` is whatever `model` makes it.
As for `False` and `Eq` (`ConLeche/Semantics/IsModelBasis.lean`), what `Nat` denotes follows
from its declarations' own clauses.  For a stream that declares the prelude's `Nat`
(`DeclaresNat`) and `Eq`, in **every** set theory `V` and every model:

* `nat_eq_omega`: what `Nat` denotes is a copy of `V`'s own `ω`.  The numeral at `i ∈ ω`
  (`natOfOmega`: `⟦Nat.succ⟧` iterated on `⟦Nat.zero⟧` by `V`'s recursion on `ω`) is a member
  of `⟦Nat⟧`, every member is one, and distinct members of `ω` give distinct numerals.
* `nat_standard`: so if `ω` is standard (`OmegaStandard`: every member is a meta-level
  `vnat k`), the literals' values `natLitVal model : Nat → V` are exactly the members of
  `⟦Nat⟧`, each once: an isomorphism of Lean's `Nat` with what `Nat` denotes.
  `omegaStandard_of_nat` is the converse.

`SetTheory` is first-order, so if it has a model it has one whose `ω` is not standard (by
compactness; not proved here), and there `⟦Nat⟧` has non-standard members too.  "Standard" is
relative to the meta-theory: it compares `⟦Nat⟧` with the `Nat` of the Lean these theorems are
stated in.

The proofs read three things off the stream's records:

* surjectivity is `Nat.rec`'s typing clause at a motive into `Prop` (`nat_ind`), at the
  property "is the numeral at a member of `ω`" — first-order, since that image is a set;
* injectivity is `Nat.rec`'s two rule equations (`natRec_rules`), at the motives
  `fun _ => Prop` (`natSucc_ne_zero`) and `fun _ => Nat` (`natSucc_inj`);
* `Eq` being equality (`IsModel.eq_eqv`) turns the rule equations into equations of sets.

Nothing here needs Mathlib; the module is in the bridge package because its consumer,
`ConLecheBridge/StandardNat.lean`, is.
-/

namespace ConLecheBridge

open ConLeche ConLeche.SetTheory ConLeche.SetModel ConLeche.BasisDSL

universe w

/-! ## The prelude's `Nat`, as a stream carries it -/

/-- `Nat.rec`. -/
def natRecName : Name := natName.str "rec"

/-- The domain of `Nat.rec`'s motive at the level `l`: `Nat → Sort l`. -/
def natMotiveAt (l : Level) : Expr := pi "t" natT (srt l)

/-- `Nat.rec`'s type at the level `l`. -/
def natRecTypeAt (l : Level) : Expr :=
  piI "motive" (natMotiveAt l) <|
  pi "zero" (.app (bv 0) (cnst natZeroName)) <|
  pi "succ" natRecSucc <|
  pi "t" natT (.app (bv 3) (bv 0))

/-- `Nat.rec`'s rule for `Nat.zero`, at the level `l`. -/
def natRuleZeroAt (l : Level) : RecRule :=
  rule natZeroName 0 <|
    lm "motive" (natMotiveAt l) <|
    lm "zero" (.app (bv 0) (cnst natZeroName)) <|
    lm "succ" natRecSucc <|
    bv 1

/-- `Nat.rec`'s rule for `Nat.succ`, at the level `l`. -/
def natRuleSuccAt (l : Level) : RecRule :=
  rule natSuccName 1 <|
    lm "motive" (natMotiveAt l) <|
    lm "zero" (.app (bv 0) (cnst natZeroName)) <|
    lm "succ" natRecSucc <|
    lm "n" natT <|
    ap2 (bv 1) (bv 0) (ap4 (cnst natRecName [l]) (bv 3) (bv 2) (bv 1) (bv 0))

/-- `Nat.rec`'s name, level parameter and type, at the level-parameter name `p`. -/
def natRecCV (p : Name) : ConstantVal := ⟨natRecName, [p], natRecTypeAt (.param p)⟩

/-- `Nat.rec` at the level-parameter name `p`, written out. -/
def natRecAt (p : Name) : ConstantInfo :=
  .recInfo (natRecCV p) 3 3 false [natRuleZeroAt (.param p), natRuleSuccAt (.param p)]

/-- The pinned `Nat.rec` (`natRecA`) at another level-parameter name is `natRecAt`. -/
theorem natRecA_atLps (p : Name) : natRecA.atLps [p] = natRecAt p := by rfl

/-- **`C` declares the prelude's `Nat`**: the pinned block (`natBasis`) — the type former, the
two constructors, and the recursor with its two rules at some level-parameter name.  As for
`DeclaresFalse` and `DeclaresEq`, the type former and the constructors are read by their name,
level parameters and type; the recursor is the whole record, since its rules are read. -/
def DeclaresNat (C : ConstantInfo → Prop) : Prop :=
  HasConstant C natName [] type1 ∧
  HasConstant C natZeroName [] natT ∧
  HasConstant C natSuccName [] (pi "n" natT natT) ∧
  ∃ p, C (natRecA.atLps [p])

/-- The equation of `Nat.rec`'s rule for `Nat.zero`:
`∀ motive zero succ, @Eq (motive Nat.zero) (Nat.rec motive zero succ Nat.zero)
(rhs motive zero succ)`. -/
def natIotaZero (l : Level) : Expr :=
  pi "motive" (natMotiveAt l) <|
  pi "zero" (.app (bv 0) (cnst natZeroName)) <|
  pi "succ" natRecSucc <|
  ap3 (cnst eqName [l]) (.app (bv 2) (cnst natZeroName))
    (Expr.mkAppN (cnst natRecName [l]) [bv 2, bv 1, bv 0, cnst natZeroName])
    (Expr.mkAppN (natRuleZeroAt l).rhs [bv 2, bv 1, bv 0])

/-- The equation of `Nat.rec`'s rule for `Nat.succ`:
`∀ motive zero succ n, @Eq (motive (Nat.succ n)) (Nat.rec motive zero succ (Nat.succ n))
(rhs motive zero succ n)`. -/
def natIotaSucc (l : Level) : Expr :=
  pi "motive" (natMotiveAt l) <|
  pi "zero" (.app (bv 0) (cnst natZeroName)) <|
  pi "succ" natRecSucc <|
  pi "n" natT <|
  ap3 (cnst eqName [l]) (.app (bv 3) (.app (cnst natSuccName) (bv 0)))
    (Expr.mkAppN (cnst natRecName [l]) [bv 3, bv 2, bv 1, .app (cnst natSuccName) (bv 0)])
    (Expr.mkAppN (natRuleSuccAt l).rhs [bv 3, bv 2, bv 1, bv 0])

theorem iotaEqOf_natZero (p : Name) :
    iotaEqOf (natRecCV p) 3 3 0 (natRuleZeroAt (.param p)) = some (natIotaZero (.param p)) := by
  rfl

theorem iotaEqOf_natSucc (p : Name) :
    iotaEqOf (natRecCV p) 3 3 1 (natRuleSuccAt (.param p)) = some (natIotaSucc (.param p)) := by
  rfl

variable {V : Type w} [SetTheory V] {model : Name → List Nat → V} {R : ConstantInfo → Prop}

/-! ## The constructors and the induction principle -/

/-- `Nat` denotes a type of the universe `1`. -/
theorem nat_mem_univ (h : IsModel V model R) (hN : DeclaresNat R) :
    model natName [] ∈ˢ (univ 1 : V) :=
  h.mem_of_hasRecord hN.1 [] rfl

/-- `Nat.zero` denotes a member of what `Nat` denotes. -/
theorem natZero_mem (h : IsModel V model R) (hN : DeclaresNat R) :
    model natZeroName [] ∈ˢ model natName [] :=
  h.mem_of_hasRecord hN.2.1 [] rfl

/-- `Nat.succ` takes what `Nat` denotes to itself. -/
theorem natSucc_mem (h : IsModel V model R) (hN : DeclaresNat R) {n : V}
    (hn : n ∈ˢ model natName []) : app (model natSuccName []) n ∈ˢ model natName [] := by
  have hS : model natSuccName [] ∈ˢ Expr.eval model (Level.assign [] []) ρ₀
      (.forallE (.const natName []) (.const natName [])) := h.mem_of_hasRecord hN.2.2.1 [] rfl
  rw [eval_forallE] at hS
  exact app_mem_piV hS hn

/-- **Induction over what `Nat` denotes**, for every property whose truth values form a graph
over it: `Nat.rec`'s own clause, at the motive `fun n => truthVal (P n)` (into `Prop`) and the
canonical proofs as minor premises. -/
theorem nat_ind (h : IsModel V model R) (hN : DeclaresNat R) {P : V → Prop}
    (hP : HasGraph (model natName []) fun n => truthVal (P n))
    (h0 : P (model natZeroName []))
    (hs : ∀ n, n ∈ˢ model natName [] → P n → P (app (model natSuccName []) n)) :
    ∀ x, x ∈ˢ model natName [] → P x := by
  intro x hx
  obtain ⟨p, hp⟩ := hN.2.2.2
  rw [natRecA_atLps] at hp
  have hR : model natRecName [0] ∈ˢ Expr.eval model (Level.assign [p] [0]) ρ₀
      (natRecTypeAt (.param p)) := (h _ hp [0] rfl).1
  simp only [natRecTypeAt, natMotiveAt, natRecSucc, natT, pi, piI, srt, cnst, bv,
    eval_forallE, eval_app, eval_const, eval_sort, eval_bvar, push, List.map_nil, Level.eval,
    Level.assign, ite_true] at hR
  have hmc : ∀ n, n ∈ˢ model natName [] →
      app (lamV (model natName []) (fun n => truthVal (P n)) hP) n = truthVal (P n) :=
    fun n hn => app_lamV hn
  have hmot : lamV (model natName []) (fun n => truthVal (P n)) hP ∈ˢ
      piV (model natName []) (fun _ => (univ 0 : V)) (hasSigmaPairs_const _ _) :=
    lamV_mem (fun n _ => by rw [univ_zero]; exact truthVal_mem_univZero _) (fun _ _ => IsTy_univ 0)
  have h1 := app_mem_piV hR hmot
  have h2 := app_mem_piV h1 (a := pt) (by
    rw [hmc _ (natZero_mem h hN)]; exact pt_mem_truthVal h0)
  have h3 := app_mem_piV h2 (a := pt) (by
    refine (pt_mem_piV_iff (fun _ _ => IsTy_piV)).mpr fun n hn => ?_
    refine (pt_mem_piV_iff (fun _ _ => ?_)).mpr fun ih hih => ?_
    · rw [hmc _ (natSucc_mem h hN hn)]; exact Or.inl (truthVal_mem_univZero _)
    · rw [hmc _ hn] at hih
      rw [hmc _ (natSucc_mem h hN hn)]
      exact pt_mem_truthVal (hs n hn (of_mem_truthVal hih)))
  have h4 := app_mem_piV h3 hx
  rw [hmc x hx] at h4
  exact of_mem_truthVal h4

/-! ## The numerals -/

/-- Every numeral denotes a member of what `Nat` denotes. -/
theorem natLitVal_mem (h : IsModel V model R) (hN : DeclaresNat R) :
    ∀ k, natLitVal model k ∈ˢ model natName []
  | 0 => natZero_mem h hN
  | k + 1 => natSucc_mem h hN (natLitVal_mem h hN k)

/-- The graph `i ↦ ⟦Nat.succ⟧` over `ω`: the curried step `natrec` iterates. -/
noncomputable def natSuccStep (model : Name → List Nat → V) : V :=
  lamV omega (fun _ => model natSuccName []) (hasGraph_of_defFun1 (DefFun.const _))

/-- **The numeral at a member of `ω`**: `⟦Nat.succ⟧` iterated on `⟦Nat.zero⟧` by the set
theory's own recursion on `ω` (`natrec`).  At a standard `vnat k` it is the literal `k`'s value
(`natOfOmega_vnat`); a non-standard member of `ω` has a numeral too. -/
noncomputable def natOfOmega (model : Name → List Nat → V) (i : V) : V :=
  natrec (model natZeroName []) (natSuccStep model) i

theorem natOfOmega_empty : natOfOmega model empty = model natZeroName [] :=
  natrec_empty _ _

theorem natOfOmega_vsucc {i : V} (hi : i ∈ˢ (omega : V)) :
    natOfOmega model (vsucc i) = app (model natSuccName []) (natOfOmega model i) := by
  unfold natOfOmega
  rw [natrec_vsucc _ _ hi]
  unfold natSuccStep
  rw [app_lamV hi]

/-- At a standard natural, the numeral is the literal's value. -/
theorem natOfOmega_vnat : ∀ k, natOfOmega model (vnat k) = natLitVal model k
  | 0 => natOfOmega_empty
  | k + 1 => by
    show natOfOmega model (vsucc (vnat k)) = app (model natSuccName []) (natLitVal model k)
    rw [natOfOmega_vsucc (vnat_mem_omega k), natOfOmega_vnat k]

theorem natOfOmega_defFun : DefFun 1 fun v : Fin 1 → V => natOfOmega model (v 0) :=
  DefFun.natrec_apply (DefFun.const _) (DefFun.const _) (DefFun.proj 0)

/-- The numeral at a member of `ω` is a member of what `Nat` denotes. -/
theorem natOfOmega_mem (h : IsModel V model R) (hN : DeclaresNat R) {i : V}
    (hi : i ∈ˢ (omega : V)) : natOfOmega model i ∈ˢ model natName [] := by
  have hG : HasGraph (omega : V) fun _ => model natName [] := hasGraph_of_defFun1 (DefFun.const _)
  have key := natrec_mem_vsucc (M := lamV omega (fun _ => model natName []) hG)
    (z := model natZeroName []) (s := natSuccStep model) (n := i)
    (by rw [app_lamV empty_mem_omega]; exact natZero_mem h hN)
    (fun k hk ih hih => by
      rw [app_lamV hk] at hih
      rw [app_lamV (vsucc_mem_omega hk)]
      unfold natSuccStep
      rw [app_lamV hk]
      exact natSucc_mem h hN hih) hi
  rw [app_lamV hi] at key
  exact key

/-- **Every member of what `Nat` denotes is the numeral at a member of `ω`.**  By `nat_ind` at
the property "is in the image of `ω`", which is first-order: the image is a set. -/
theorem exists_omega_of_mem (h : IsModel V model R) (hN : DeclaresNat R) {x : V}
    (hx : x ∈ˢ model natName []) : ∃ i, i ∈ˢ (omega : V) ∧ x = natOfOmega model i := by
  have hImg : HasImage (natOfOmega model) (omega : V) :=
    hasImage_of_defFun1 natOfOmega_defFun omega
  have key := nat_ind h hN (P := fun x => x ∈ˢ image (natOfOmega model) omega hImg)
    (hasGraph_of_defFun1
      (DefFun.truthVal_apply (DefRel.mem_apply (DefFun.proj 0) (DefFun.const _))))
    (mem_image.mpr ⟨empty, empty_mem_omega, natOfOmega_empty.symm⟩)
    (fun n _ hn => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
      exact mem_image.mpr ⟨vsucc i, vsucc_mem_omega hi, (natOfOmega_vsucc hi).symm⟩)
  exact mem_image.mp (key x hx)

/-! ## The recursor computes -/

/-- The successor minor premise's function space at the motive `m` is a set. -/
theorem hasSigmaPairs_succMinor (model : Name → List Nat → V) (m : V) :
    HasSigmaPairs (model natName []) fun n =>
      piV (app m n) (fun _ => app m (app (model natSuccName []) n)) (hasSigmaPairs_const _ _) :=
  hasSigmaPairs_of_defFun1 (DefFun.piV_apply_curry
    (A := fun v => app m (v 0)) (B := fun _ v => app m (app (model natSuccName []) (v 0)))
    (DefFun.app_apply (DefFun.const m) (DefFun.proj 0))
    (DefFun.app_apply (DefFun.const m) (DefFun.app_apply (DefFun.const _) (DefFun.proj 1))))

/-- **`Nat.rec` is typed and computes by its two rules**, at every motive `m` into a universe
`k` and all minor premises `z` and `s`: the recursor's own clause and its two rule equations
(`RuleHolds`), which `Eq` being equality (`IsModel.eq_eqv`) turns into equations of sets. -/
theorem natRec_rules (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R)
    {k : Nat} {m z s : V}
    (hm : m ∈ˢ piV (model natName []) (fun _ => (univ k : V)) (hasSigmaPairs_const _ _))
    (hz : z ∈ˢ app m (model natZeroName []))
    (hs : s ∈ˢ piV (model natName []) (fun n =>
      piV (app m n) (fun _ => app m (app (model natSuccName []) n)) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_succMinor model m)) :
    (∀ x, x ∈ˢ model natName [] →
      app (app (app (app (model natRecName [k]) m) z) s) x ∈ˢ app m x) ∧
    app (app (app (app (model natRecName [k]) m) z) s) (model natZeroName []) = z ∧
    ∀ n, n ∈ˢ model natName [] →
      app (app (app (app (model natRecName [k]) m) z) s) (app (model natSuccName []) n) =
        app (app s n) (app (app (app (app (model natRecName [k]) m) z) s) n) := by
  obtain ⟨p, hp⟩ := hN.2.2.2
  rw [natRecA_atLps] at hp
  obtain ⟨hR, hrules⟩ := h _ hp [k] rfl
  have hR : model natRecName [k] ∈ˢ Expr.eval model (Level.assign [p] [k]) ρ₀
      (natRecTypeAt (.param p)) := hR
  have hrules : ∀ i rl, [natRuleZeroAt (.param p), natRuleSuccAt (.param p)][i]? = some rl →
      RuleHolds V model (Level.assign [p] [k]) (natRecCV p) 3 3 i rl := hrules
  have hφ : Level.assign [p] [k] p = k := by simp [Level.assign]
  -- the recursor's value at the motive and the minors is a member of the motive's value
  have hty : ∀ x, x ∈ˢ model natName [] →
      app (app (app (app (model natRecName [k]) m) z) s) x ∈ˢ app m x := by
    intro x hx
    simp only [natRecTypeAt, natMotiveAt, natRecSucc, natT, pi, piI, srt, cnst, bv,
      eval_forallE, eval_app, eval_const, eval_sort, eval_bvar, push, List.map_nil, Level.eval,
      hφ] at hR
    have h1 := app_mem_piV hR hm
    have h2 := app_mem_piV h1 hz
    have h3 := app_mem_piV h2 hs
    exact app_mem_piV h3 hx
  -- the motive and the minors are members of what the rules' binder domains denote
  have hmE : ∀ ρ : BVarIdx → V,
      m ∈ˢ Expr.eval model (Level.assign [p] [k]) ρ (natMotiveAt (.param p)) := by
    intro ρ
    simp only [natMotiveAt, natT, pi, srt, cnst, eval_forallE, eval_const, eval_sort,
      List.map_nil, Level.eval, hφ]
    exact hm
  have hzE : ∀ ρ : BVarIdx → V,
      z ∈ˢ Expr.eval model (Level.assign [p] [k]) (push m ρ) (.app (bv 0) (cnst natZeroName)) := by
    intro ρ
    simp only [bv, cnst, eval_app, eval_bvar, eval_const, push, List.map_nil]
    exact hz
  have hsE : ∀ ρ : BVarIdx → V,
      s ∈ˢ Expr.eval model (Level.assign [p] [k]) (push z (push m ρ)) natRecSucc := by
    intro ρ
    simp only [natRecSucc, natT, pi, bv, cnst, eval_forallE, eval_app, eval_bvar, eval_const,
      push, List.map_nil]
    exact hs
  -- the rule for `Nat.zero`
  have hzero : app (app (app (app (model natRecName [k]) m) z) s) (model natZeroName []) = z := by
    obtain ⟨x0, hx0⟩ := hrules 0 _ rfl _ (iotaEqOf_natZero p)
    simp only [natIotaZero, natMotiveAt, natRecSucc, natT, pi, ap3, srt, cnst, bv, Expr.mkAppN,
      eval_forallE, eval_app, eval_const, eval_sort, eval_bvar, push, List.map_cons, List.map_nil,
      Level.eval, hφ] at hx0
    have h1 := app_mem_piV hx0 hm
    have h2 := app_mem_piV h1 hz
    have h3 := app_mem_piV h2 hs
    have hr : app (app (app (Expr.eval model (Level.assign [p] [k]) (push s (push z (push m ρ₀)))
        (natRuleZeroAt (.param p)).rhs) m) z) s = z := by
      simp only [natRuleZeroAt, rule, lm]
      rw [eval_lam, app_lamV (hmE _), eval_lam, app_lamV (hzE _), eval_lam, app_lamV (hsE _)]
      simp only [bv, eval_bvar, push]
    rw [hr, IsModel.eq_eqv h hE (app_mem_piV hm (natZero_mem h hN)) (hty _ (natZero_mem h hN)) hz]
      at h3
    exact eq_of_mem_eqv h3
  refine ⟨hty, hzero, fun n hn => ?_⟩
  -- the rule for `Nat.succ`
  obtain ⟨x1, hx1⟩ := hrules 1 _ rfl _ (iotaEqOf_natSucc p)
  simp only [natIotaSucc, natMotiveAt, natRecSucc, natT, pi, ap3, srt, cnst, bv, Expr.mkAppN,
    eval_forallE, eval_app, eval_const, eval_sort, eval_bvar, push, List.map_cons, List.map_nil,
    Level.eval, hφ] at hx1
  have h1 := app_mem_piV hx1 hm
  have h2 := app_mem_piV h1 hz
  have h3 := app_mem_piV h2 hs
  have h4 := app_mem_piV h3 hn
  have hnE : ∀ ρ : BVarIdx → V, n ∈ˢ Expr.eval model (Level.assign [p] [k]) ρ natT := fun _ => hn
  have hr : app (app (app (app (Expr.eval model (Level.assign [p] [k])
      (push n (push s (push z (push m ρ₀)))) (natRuleSuccAt (.param p)).rhs) m) z) s) n =
      app (app s n) (app (app (app (app (model natRecName [k]) m) z) s) n) := by
    simp only [natRuleSuccAt, rule, lm]
    rw [eval_lam, app_lamV (hmE _), eval_lam, app_lamV (hzE _), eval_lam, app_lamV (hsE _),
      eval_lam, app_lamV (hnE _)]
    simp only [ap2, ap4, bv, cnst, eval_app, eval_bvar, eval_const, push, List.map_cons,
      List.map_nil, Level.eval, hφ]
  have hsn1 := app_mem_piV hs hn
  have hsn := app_mem_piV hsn1 (hty n hn)
  rw [hr, IsModel.eq_eqv h hE (app_mem_piV hm (natSucc_mem h hN hn))
    (hty _ (natSucc_mem h hN hn)) hsn] at h4
  exact eq_of_mem_eqv h4

/-! ## The constructors are free -/

/-- The constant motive `fun _ => T`. -/
noncomputable def natConstMotive (model : Name → List Nat → V) (T : V) : V :=
  lamV (model natName []) (fun _ => T) (hasGraph_of_defFun1 (DefFun.const _))

theorem natConstMotive_app {T c : V} (hc : c ∈ˢ model natName []) :
    app (natConstMotive model T) c = T :=
  app_lamV hc

theorem natConstMotive_mem {k : Nat} {T : V} (hT : T ∈ˢ (univ k : V)) :
    natConstMotive model T ∈ˢ
      piV (model natName []) (fun _ => (univ k : V)) (hasSigmaPairs_const _ _) :=
  lamV_mem (fun _ _ => hT) (fun _ _ => IsTy_univ k)

/-- **A successor minor premise that ignores its induction hypothesis**, `fun n _ => g n`, is a
member of the minor premise's function space. -/
theorem natMinor_mem (h : IsModel V model R) (hN : DeclaresNat R) {k : Nat} {m : V}
    (hm : m ∈ˢ piV (model natName []) (fun _ => (univ k : V)) (hasSigmaPairs_const _ _))
    {g : V → V} (hg : DefFun 2 fun v : Fin 2 → V => g (v 1))
    (hgm : ∀ a, a ∈ˢ model natName [] → g a ∈ˢ app m (app (model natSuccName []) a)) :
    lamV (model natName [])
        (fun a => lamV (app m a) (fun _ => g a) (hasGraph_of_defFun1 (DefFun.const _)))
        (hasGraph_of_defFun1 (DefFun.lamV_apply_curry
          (F := fun _ v => g (v 0)) (A := fun v => app m (v 0)) hg
          (DefFun.app_apply (DefFun.const m) (DefFun.proj 0)))) ∈ˢ
      piV (model natName []) (fun n =>
        piV (app m n) (fun _ => app m (app (model natSuccName []) n)) (hasSigmaPairs_const _ _))
        (hasSigmaPairs_succMinor model m) :=
  lamV_mem
    (fun a ha => lamV_mem (fun _ _ => hgm a ha)
      (fun _ _ => IsTy_of_mem_univ (app_mem_piV hm (natSucc_mem h hN ha))))
    (fun _ _ => IsTy_piV)

/-- **`Nat.succ n` is never `Nat.zero`**: `Nat.rec` at the motive `fun _ => Prop` and the minor
premises `True` (`{pt}`) and `fun _ _ => False` (`∅`) takes `Nat.zero` to `{pt}` and every
successor to `∅`. -/
theorem natSucc_ne_zero (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R) {n : V}
    (hn : n ∈ˢ model natName []) : app (model natSuccName []) n ≠ model natZeroName [] := by
  intro heq
  have hm := natConstMotive_mem (model := model) (univ_mem_univ (V := V) 0)
  have hz : (unitSet : V) ∈ˢ app (natConstMotive model (univ 0)) (model natZeroName []) := by
    rw [natConstMotive_app (natZero_mem h hN)]; exact unitSet_mem_univ 0
  have hs := natMinor_mem h hN hm (g := fun _ => (empty : V)) DefFun.empty
    (fun a ha => by rw [natConstMotive_app (natSucc_mem h hN ha)]; exact empty_mem_univ 0)
  obtain ⟨hty, hzero, hsucc⟩ := natRec_rules h hN hE hm hz hs
  have h1 := hsucc n hn
  rw [heq, hzero, app_lamV hn, app_lamV (hty n hn)] at h1
  exact unitSet_ne_empty h1

/-- **`Nat.succ` is injective**: `Nat.rec` at the motive `fun _ => Nat` and the minor premises
`Nat.zero` and `fun n _ => n` is a predecessor. -/
theorem natSucc_inj (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R) {a b : V}
    (ha : a ∈ˢ model natName []) (hb : b ∈ˢ model natName [])
    (hab : app (model natSuccName []) a = app (model natSuccName []) b) : a = b := by
  have hm := natConstMotive_mem (model := model) (nat_mem_univ h hN)
  have hz : model natZeroName [] ∈ˢ
      app (natConstMotive model (model natName [])) (model natZeroName []) := by
    rw [natConstMotive_app (natZero_mem h hN)]; exact natZero_mem h hN
  have hs := natMinor_mem h hN hm (g := fun c => c) (DefFun.proj 1)
    (fun c hc => by rw [natConstMotive_app (natSucc_mem h hN hc)]; exact hc)
  obtain ⟨hty, -, hsucc⟩ := natRec_rules h hN hE hm hz hs
  have ea := hsucc a ha
  have eb := hsucc b hb
  rw [app_lamV ha, app_lamV (hty a ha)] at ea
  rw [app_lamV hb, app_lamV (hty b hb)] at eb
  rw [hab] at ea
  exact ea.symm.trans eb

/-- **The numerals are distinct.** -/
theorem natLitVal_inj (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R) :
    ∀ {k l : Nat}, natLitVal model k = natLitVal model l → k = l
  | 0, 0, _ => rfl
  | 0, l + 1, e => absurd e.symm (natSucc_ne_zero h hN hE (natLitVal_mem h hN l))
  | k + 1, 0, e => absurd e (natSucc_ne_zero h hN hE (natLitVal_mem h hN k))
  | k + 1, l + 1, e =>
    congrArg (· + 1) (natLitVal_inj h hN hE
      (natSucc_inj h hN hE (natLitVal_mem h hN k) (natLitVal_mem h hN l) e))

/-! ## `Nat` denotes a copy of `ω` -/

/-- **Distinct members of `ω` have distinct numerals**, by the set theory's own induction on
`ω` (the property is first-order). -/
theorem natOfOmega_inj (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R)
    {i j : V} (hi : i ∈ˢ (omega : V)) (hj : j ∈ˢ (omega : V))
    (e : natOfOmega model i = natOfOmega model j) : i = j := by
  have key : ∀ i, i ∈ˢ (omega : V) →
      ∀ j, j ∈ˢ (omega : V) → natOfOmega model i = natOfOmega model j → i = j := by
    refine omega_ind_of_def
      (p := fun i => ∀ j, j ∈ˢ (omega : V) → natOfOmega model i = natOfOmega model j → i = j)
      ?_ ?_ ?_
    · unfold natOfOmega
      fo_def [DefFun.omega_const, DefFun.natrec_apply]
    · intro j hj e
      rcases omega_cases hj with rfl | ⟨j', hj', rfl⟩
      · rfl
      · rw [natOfOmega_empty, natOfOmega_vsucc hj'] at e
        exact absurd e.symm (natSucc_ne_zero h hN hE (natOfOmega_mem h hN hj'))
    · intro i hi ih j hj e
      rcases omega_cases hj with rfl | ⟨j', hj', rfl⟩
      · rw [natOfOmega_empty, natOfOmega_vsucc hi] at e
        exact absurd e (natSucc_ne_zero h hN hE (natOfOmega_mem h hN hi))
      · rw [natOfOmega_vsucc hi, natOfOmega_vsucc hj'] at e
        rw [ih j' hj' (natSucc_inj h hN hE (natOfOmega_mem h hN hi) (natOfOmega_mem h hN hj') e)]
  exact key i hi j hj e

/-- **In every set theory, what `Nat` denotes is a copy of its `ω`**: in every model of a
stream declaring the prelude's `Nat` and `Eq`, the numerals `natOfOmega model` at the members of
`ω` are exactly the members of what `Nat` denotes, each once.  So `Nat` has a non-standard
member exactly when `ω` has one. -/
theorem nat_eq_omega (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R) :
    (∀ x, x ∈ˢ model natName [] ↔ ∃ i, i ∈ˢ (omega : V) ∧ x = natOfOmega model i) ∧
    ∀ i j, i ∈ˢ (omega : V) → j ∈ˢ (omega : V) →
      natOfOmega model i = natOfOmega model j → i = j := by
  refine ⟨fun x => ⟨exists_omega_of_mem h hN, ?_⟩, fun _ _ hi hj => natOfOmega_inj h hN hE hi hj⟩
  rintro ⟨i, hi, rfl⟩
  exact natOfOmega_mem h hN hi

/-! ## Standard naturals -/

/-- **The set theory's `ω` is standard**: every member of `ω` is a meta-level numeral `vnat k`.
This is a second-order property; `SetTheory`, being first-order, does not imply it. -/
def OmegaStandard (V : Type w) [SetTheory V] : Prop :=
  ∀ i : V, i ∈ˢ (omega : V) → ∃ k : Nat, i = vnat k

/-- **Over a standard `ω`, `Nat` denotes the standard naturals**: in every model of a stream
declaring the prelude's `Nat` and `Eq`, the literals' values `natLitVal model : Nat → V` are
exactly the members of what `Nat` denotes, each once.  `natLitVal model` takes `0` to
`⟦Nat.zero⟧` and `k + 1` to `⟦Nat.succ⟧` at `k`'s value by definition, so it is an isomorphism
of Lean's `Nat` with what `Nat` denotes. -/
theorem nat_standard (hω : OmegaStandard V) (h : IsModel V model R) (hN : DeclaresNat R)
    (hE : DeclaresEq R) :
    (∀ x, x ∈ˢ model natName [] ↔ ∃ k : Nat, x = natLitVal model k) ∧
    ∀ k l : Nat, natLitVal model k = natLitVal model l → k = l := by
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun _ _ => natLitVal_inj h hN hE⟩
  · obtain ⟨i, hi, rfl⟩ := exists_omega_of_mem h hN hx
    obtain ⟨k, rfl⟩ := hω i hi
    exact ⟨k, natOfOmega_vnat k⟩
  · rintro ⟨k, rfl⟩
    exact natLitVal_mem h hN k

/-- **The hypothesis is needed**: if every member of what `Nat` denotes is a literal's value,
`ω` is standard. -/
theorem omegaStandard_of_nat (h : IsModel V model R) (hN : DeclaresNat R) (hE : DeclaresEq R)
    (hstd : ∀ x, x ∈ˢ model natName [] → ∃ k : Nat, x = natLitVal model k) :
    OmegaStandard V := by
  intro i hi
  obtain ⟨k, hk⟩ := hstd _ (natOfOmega_mem h hN hi)
  rw [← natOfOmega_vnat k] at hk
  exact ⟨k, natOfOmega_inj h hN hE hi (vnat_mem_omega k) hk⟩

end ConLecheBridge
