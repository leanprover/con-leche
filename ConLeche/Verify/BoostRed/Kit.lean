module

public import ConLeche.Rules.Rel

public section

/-!
# Boost: `Red` derivations under pins

The building blocks of a *boost admissibility*
derivation: a proof that `Red env d (c (lit n)) (lit (F n))` exists in
every environment whose stored closure of `c` is the pinned one.

* **Pins** are hypotheses about the environment, one per closure
  constant: the stored declaration is syntactically the pinned one
  (`DefPin`, `RecPin`, `CtorPin`), a stored family is never `Prop`
  (`IndNeverProp`, what ι's case split reads), a projection slot has
  its table entry (`ProjPin`).  The `bv_decide` gate establishes them
  by one syntactic comparison per constant (`Verify/BoostRed/BVGate.lean`).
* **Step lemmas** restate the `Red` rules the derivation chains (δ, β
  under a spine, ι at case 2, the structural projection) with every
  premise that is a stored-data lookup discharged from a pin; what is
  left is computation on closed data (`rfl`).

Nothing here is semantic: the lemmas are about the rules tier's `Red`
alone, whose soundness is proved once (`Model/Rules/Sound.lean`).
-/

namespace ConLeche.Rules.BoostRed

open ConLeche

/-- The stored declaration of `n` is a definition with exactly the
pinned level parameters and value. -/
@[expose] def DefPin (env : Env) (n : Name) (lps : List Name) (v : Expr) : Prop :=
  ∃ cv hint, env.find? n = some (.defnInfo cv v hint) ∧ cv.levelParams = lps

/-- The stored declaration of `n` is a recursor with the pinned level
parameters, type, arities and rules. -/
@[expose] def RecPin (env : Env) (n : Name) (lps : List Name) (ty : Expr) (mI rP : Nat)
    (rules : List RecRule) : Prop :=
  ∃ cv, env.find? n = some (.recInfo cv mI rP rules) ∧ cv.levelParams = lps ∧
    cv.type = ty

/-- The stored declaration of `n` is a constructor with the pinned level
parameters and type. -/
@[expose] def CtorPin (env : Env) (n : Name) (lps : List Name) (ty : Expr) : Prop :=
  ∃ cv nP nF, env.find? n = some (.ctorInfo cv nP nF) ∧ cv.levelParams = lps ∧
    cv.type = ty

/-- The stored family `T` (with `k` level parameters) is never `Prop`,
at every level instantiation: the datum ι's case split reads
(`iotaCtorNeverProp`). -/
@[expose] def IndNeverProp (env : Env) (T : Name) (k : Nat) : Prop :=
  ∃ cvT caps, env.find? T = some (.indInfo cvT caps) ∧ cvT.levelParams.length = k ∧
    ∀ us : List Level, us.length = k → capsNeverZero cvT.levelParams us caps = true

/-- The projection slot `i` of the structure `sn` has its table entry,
naming the constructor `ctor`, at the pinned arities, and fires at
every level instantiation (the structure is never `Prop`). -/
@[expose] def ProjPin (env : Env) (sn : Name) (i : Nat) (ctor : Name) (lps : List Name)
    (nP nF : Nat) : Prop :=
  ∃ entry : ProjEntry, env.findProj? sn i = some entry ∧ entry.ctor = ctor ∧
    entry.levelParams = lps ∧ entry.numParams = nP ∧ entry.numFields = nF ∧
    ∀ us, entry.fireOk us = true

/-! ## Congruence under a spine, and β -/

theorem Red.appFnN {env : Env} {d : Nat} :
    ∀ {f f' : Expr} (args : List Expr), Red env d f f' →
      Red env d (Expr.mkAppN f args) (Expr.mkAppN f' args)
  | _, _, [], h => h
  | _, _, _ :: as, h => Red.appFnN as (Red.appFn h)

/-- A term whose loose bound variables are below `k` is unchanged by
instantiating at `k` or above (`Model/Rules/ProofFastSound.lean`'s
`instantiate1_of_bounded`, restated in the `Verify` tier). -/
theorem instantiate1_bounded {v : Expr} :
    ∀ (e : Expr) {k j : Nat}, e.looseBVarsBounded k = true → k ≤ j →
      e.instantiate1 v j = e
  | .bvar i, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Expr.instantiate1]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _
  | .lit _, _, _, _, _ => rfl
  | .app f a, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_bounded f h.1 hkj, instantiate1_bounded a h.2 hkj]
  | .lam t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_bounded t h.1 hkj, instantiate1_bounded b h.2 (by omega)]
  | .forallE t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_bounded t h.1 hkj, instantiate1_bounded b h.2 (by omega)]
  | .letE t x b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_bounded t h.1.1 hkj, instantiate1_bounded x h.1.2 hkj,
      instantiate1_bounded b h.2 (by omega)]
  | .proj _ _ e, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_bounded e h hkj]

/-- A closed term is unchanged by `instantiate1`. -/
theorem instantiate1_closed (v : Expr) (e : Expr) (j : Nat)
    (h : e.looseBVarsBounded 0 = true) : e.instantiate1 v j = e :=
  instantiate1_bounded e h (Nat.zero_le j)

/-! ### Closedness, compositionally (the generator's side goals) -/

theorem lbb_mono : ∀ (e : Expr) {k j : Nat}, e.looseBVarsBounded k = true → k ≤ j →
    e.looseBVarsBounded j = true
  | .bvar i, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _
  | .lit _, _, _, _, _ => rfl
  | .app f a, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨lbb_mono f h.1 hkj, lbb_mono a h.2 hkj⟩
  | .lam t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨lbb_mono t h.1 hkj, lbb_mono b h.2 (by omega)⟩
  | .forallE t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨lbb_mono t h.1 hkj, lbb_mono b h.2 (by omega)⟩
  | .letE t x b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨lbb_mono t h.1.1 hkj, lbb_mono x h.1.2 hkj⟩, lbb_mono b h.2 (by omega)⟩
  | .proj _ _ e, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded] at h ⊢
    exact lbb_mono e h hkj

theorem lbb_atom (e : Expr) (k : Nat) (h : e.looseBVarsBounded 0 = true) :
    e.looseBVarsBounded k = true :=
  lbb_mono e h (Nat.zero_le k)

/-! ## δ under a pin -/

theorem Red.deltaPin {env : Env} {d : Nat} {n : Name} {lps : List Name} {v : Expr}
    (h : DefPin env n lps v) (e : Expr) (us : List Level)
    (hf : e.getAppFn = .const n us) (hl : us.length = lps.length) :
    Red env d e (Expr.mkAppN (v.instantiateLevelParams lps us) e.getAppArgs) := by
  obtain ⟨cv, hint, hfind, hlps⟩ := h
  apply Red.delta
  simp only [unfoldDefinition, hf, hfind, hlps, hl, ite_true]

/-! ## The structural projection under a pin -/

theorem Red.projPin {env : Env} {d : Nat} {sn : Name} {i : Nat} {ctor : Name}
    {lps : List Name} {nP nF : Nat} {cty : Expr}
    (hp : ProjPin env sn i ctor lps nP nF) (hc : CtorPin env ctor lps cty)
    (e : Expr) (us : List Level)
    (hhead : e.getAppFn = .const ctor us) (hi : i < nF)
    (hlen : e.getAppArgs.length = nP + nF) (hus : us.length = lps.length)
    (hpeel : (Expr.peelPis e.getAppArgs.length
      (cty.instantiateLevelParams lps us)).isSome = true) :
    Red env d (.proj sn i e) (e.getAppArgs.getD (nP + i) (.bvar 0)) := by
  obtain ⟨entry, hent, hctor, hlps, hnP, hnF, hfire⟩ := hp
  obtain ⟨cv, cnP, cnF, hfind, hclps, hcty⟩ := hc
  subst hctor hlps hnP hnF
  exact Red.proj hent hhead hi hlen hus (hfire us) hfind
    (by rw [hclps, hcty]; exact hpeel)

/-! ## ι at case 2 under pins

The family of the major's constructor is never `Prop` (`IndNeverProp`),
so `iotaCase3` is `false` and every case-3 premise of `Red.iota` is
vacuous: the step carries no comparison, no certificate and no
inference. -/

theorem iotaCase3_false {env : Env} {rl : RecRule} {cvj : ConstantVal}
    {us : List Level} {T : Name} {tus : List Level} {k : Nat}
    (hT : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : IndNeverProp env T k) (hlen : us.length = k) :
    iotaCase3 env.find? rl cvj us = false := by
  obtain ⟨cvT, caps, hfind, hk, hnz⟩ := hind
  have : iotaCtorNeverProp env.find? cvj us = true := by
    simp only [iotaCtorNeverProp, hT, hfind, hk, hlen, beq_self_eq_true,
      Bool.true_and]
    exact hnz us hlen
  simp [iotaCase3, this]

theorem Red.iota2 {env : Env} {d : Nat} {c : Name} {lps : List Name} {rty : Expr}
    {mI rP : Nat} {rules : List RecRule} {cj : Name} {clps : List Name} {cty : Expr}
    {T : Name} {k : Nat}
    (hrec : RecPin env c lps rty mI rP rules) (hctor : CtorPin env cj clps cty)
    (hind : IndNeverProp env T k)
    (e : Expr) (us : List Level) (major : Expr) (usj : List Level) (rl : RecRule)
    (tus : List Level)
    (hhead : e.getAppFn = .const c us)
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = lps.length)
    (hmaj : Red env d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmh : major.getAppFn = .const cj usj)
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hT : (cty.piResult).getAppFn = .const T tus)
    (hk : (recFireComparands rl lps us clps e.getAppArgs rP).1.length = k)
    (hpeel : (Expr.peelPis e.getAppArgs.length
      (rty.instantiateLevelParams lps us)).isSome = true) :
    Red env d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams lps us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  obtain ⟨cv, hfind, hlps, hty⟩ := hrec
  obtain ⟨cvj, cnP, cnF, hcfind, hclps, hcty⟩ := hctor
  subst hlps hty hclps hcty
  have h3 : iotaCase3 env.find? rl cvj
      (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1 = false :=
    iotaCase3_false hT hind hk
  exact Red.iota (residual := .bvar 0) hhead hfind hlen hus hmaj hmh hcfind hrule hmlen
    (fun h => by rw [h3] at h; cases h) (fun h => by rw [h3] at h; cases h) hpeel
    (fun h => by rw [h3] at h; cases h) (fun h => by rw [h3] at h; cases h)
    (fun h => by rw [h3] at h; cases h)

/-! ## The relaxed K-like step under a pin -/

/-- A K-like recursor (one rule, flagged K, no fields) fires at its
pinned rule without reading the major. -/
theorem Red.kRecPin {env : Env} {d : Nat} {c : Name} {lps : List Name} {rty : Expr}
    {mI rP : Nat} {rl : RecRule}
    (hrec : RecPin env c lps rty mI rP [rl]) (hk : rl.k = true) (hnf : rl.nfields = 0)
    (e : Expr) (us : List Level)
    (hhead : e.getAppFn = .const c us)
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = lps.length)
    (hpeel : (Expr.peelPis e.getAppArgs.length
      (rty.instantiateLevelParams lps us)).isSome = true) :
    Red env d e (Expr.mkAppN (rl.rhs.instantiateLevelParams lps us) (e.getAppArgs.take rP)) := by
  obtain ⟨cv, hfind, hlps, hty⟩ := hrec
  subst hlps hty
  exact Red.kRec hhead hfind hk hnf hlen hus hpeel

/-! ## The literal steps -/

end ConLeche.Rules.BoostRed

namespace ConLeche.Rules.BoostRed

/-- A `Bool` value as the checker's constructor constant (the target of a
`Bool`-valued boost). -/
@[expose] def boolE : Bool → ConLeche.Expr
  | true => .const boolTrueName []
  | false => .const boolFalseName []

end ConLeche.Rules.BoostRed
