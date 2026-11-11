module

public import ConLeche.Rules.Rel

public section

/-!
# Erased reduction and its lifting (task #423 soundness, layer (c0))

The ground engine (`ConLeche/Kernel/Ground.lean`) evaluates a closed term
with its types, motives and (outside recursor majors) proofs **erased**:
such an argument is compiled to the neutral and never built, and a value
the engine cannot read is the neutral too.  So the engine's state does not
denote the terms of the checked declaration; it denotes those terms with
some subterms forgotten.  This file gives that reading a reduction
relation and lifts it to `Red`:

* `bot` is the forgotten term, and `Approx s t` says that `s` is `t` with
  some subterms replaced by `bot` (`s` is less defined than `t`).
* `ERed env s s'` is reduction on such terms: the `Red` rules the engine
  takes (β, ζ, δ, ι outside case 3, the K step `Red.iotaK`, the projection,
  the literal rules, the two congruences), each with the same premises as
  its `Red` rule, plus `forget` (a reduct may forget more).  No rule fires
  on `bot`.
* **`ERed.lift`**: an erased reduction lifts to a `Red` reduction of every
  term the erased one approximates, with a reduct the erased reduct
  approximates.

The engine's soundness proof shows that its run is an `ERed` reduction of
the compiled term, which approximates the site's term (compiler
correctness); a run ending in `Bool.true` then lifts to
`Red env d t (.const boolTrueName [])` (`ERed.lift_const`).  This is
evaluation via erasure (Felicissimo et al., *Consolidating Equality in a
Proof Irrelevant Universe*, 2026, §6) read backwards: there the typed
reduction is simulated by the erased one; here every erased step the
engine takes is matched by a typed one, so no typing is needed.

Sharing is free in this reading: two equal erased terms are one term, so
a memo hit on equal argument cells reuses a derivation, including where
the arguments differ in erased content (all of it is `bot`).
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Rules

/-- **The forgotten term.**  A sort: the engine compiles types to the
neutral, so the term it forgets most often is one.  No `ERed` rule fires
on a sort. -/
@[expose] def bot : Expr := .sort .zero

/-- **`s` approximates `t`**: `t` with some subterms replaced by `bot`. -/
inductive Approx : Expr → Expr → Prop where
  | bot (t : Expr) : Approx bot t
  | bvar (i : Nat) : Approx (.bvar i) (.bvar i)
  | fvar (i : Nat) (ty : Expr) : Approx (.fvar i ty) (.fvar i ty)
  | sort (u : Level) : Approx (.sort u) (.sort u)
  | const (c : Name) (us : List Level) : Approx (.const c us) (.const c us)
  | lit (l : Literal) : Approx (.lit l) (.lit l)
  | app {f f' a a' : Expr} : Approx f f' → Approx a a' → Approx (.app f a) (.app f' a')
  | lam {ty ty' b b' : Expr} : Approx ty ty' → Approx b b' → Approx (.lam ty b) (.lam ty' b')
  | forallE {ty ty' b b' : Expr} :
      Approx ty ty' → Approx b b' → Approx (.forallE ty b) (.forallE ty' b')
  | letE {ty ty' v v' b b' : Expr} :
      Approx ty ty' → Approx v v' → Approx b b' → Approx (.letE ty v b) (.letE ty' v' b')
  | proj {s : Name} {i : Nat} {e e' : Expr} : Approx e e' → Approx (.proj s i e) (.proj s i e')

/-- Pointwise approximation of two argument lists. -/
inductive Approx.Args : List Expr → List Expr → Prop where
  | nil : Approx.Args [] []
  | cons {a b : Expr} {as bs : List Expr} : Approx a b → Approx.Args as bs →
      Approx.Args (a :: as) (b :: bs)

namespace Approx

theorem Args.append {as bs cs ds : List Expr} (h₁ : Approx.Args as bs) (h₂ : Approx.Args cs ds) :
    Approx.Args (as ++ cs) (bs ++ ds) := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => exact .cons ha ih

theorem refl : ∀ (t : Expr), Approx t t
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty
  | .sort u => .sort u
  | .const c us => .const c us
  | .lit l => .lit l
  | .app f a => .app (refl f) (refl a)
  | .lam ty b => .lam (refl ty) (refl b)
  | .forallE ty b => .forallE (refl ty) (refl b)
  | .letE ty v b => .letE (refl ty) (refl v) (refl b)
  | .proj _ _ e => .proj (refl e)

theorem trans {a b c : Expr} (h₁ : Approx a b) (h₂ : Approx b c) : Approx a c := by
  induction h₁ generalizing c with
  | bot => exact .bot c
  | bvar | fvar | sort | const | lit => exact h₂
  | app _ _ ihf iha =>
    cases h₂ with
    | app h₃ h₄ => exact .app (ihf h₃) (iha h₄)
  | lam _ _ ih₁ ih₂ =>
    cases h₂ with
    | lam h₃ h₄ => exact .lam (ih₁ h₃) (ih₂ h₄)
  | forallE _ _ ih₁ ih₂ =>
    cases h₂ with
    | forallE h₃ h₄ => exact .forallE (ih₁ h₃) (ih₂ h₄)
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | letE h₄ h₅ h₆ => exact .letE (ih₁ h₄) (ih₂ h₅) (ih₃ h₆)
  | proj _ ih =>
    cases h₂ with
    | proj h₃ => exact .proj (ih h₃)

/-- Inversions: a term that is not `bot` fixes the head constructor. -/
theorem app_inv {f a t : Expr} (h : Approx (.app f a) t) :
    ∃ f' a', t = .app f' a' ∧ Approx f f' ∧ Approx a a' := by
  cases h with
  | app h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem lam_inv {ty b t : Expr} (h : Approx (.lam ty b) t) :
    ∃ ty' b', t = .lam ty' b' ∧ Approx ty ty' ∧ Approx b b' := by
  cases h with
  | lam h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem letE_inv {ty v b t : Expr} (h : Approx (.letE ty v b) t) :
    ∃ ty' v' b', t = .letE ty' v' b' ∧ Approx ty ty' ∧ Approx v v' ∧ Approx b b' := by
  cases h with
  | letE h₁ h₂ h₃ => exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

theorem proj_inv {s : Name} {i : Nat} {e t : Expr} (h : Approx (.proj s i e) t) :
    ∃ e', t = .proj s i e' ∧ Approx e e' := by
  cases h with
  | proj h₁ => exact ⟨_, rfl, h₁⟩

theorem const_inv {c : Name} {us : List Level} {t : Expr} (h : Approx (.const c us) t) :
    t = .const c us := by
  cases h; rfl

theorem lit_inv {l : Literal} {t : Expr} (h : Approx (.lit l) t) : t = .lit l := by
  cases h; rfl

/-- A literal reading is never forgotten. -/
theorem rawNatLit {w w' : Expr} {n : Nat} (h : Approx w w') (hw : rawNatLit? w = some n) :
    w' = w := by
  cases h with
  | bot => rw [show rawNatLit? Ground.bot = none from rfl] at hw; cases hw
  | const => rfl
  | lit => rfl
  | _ => simp [rawNatLit?] at hw

/-- **Substitution is monotone** in both the term and the value. -/
theorem instantiate1 {s t a b : Expr} (h : Approx s t) (hab : Approx a b) (d : Nat) :
    Approx (s.instantiate1 a d) (t.instantiate1 b d) := by
  induction h generalizing d with
  | bot t => exact .bot _
  | bvar i =>
    simp only [Expr.instantiate1]
    split
    · exact hab
    · split <;> exact .bvar _
  | fvar => exact .fvar _ _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | app _ _ ihf iha => exact .app (ihf d) (iha d)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ d) (ih₂ (d + 1))
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ d) (ih₂ (d + 1))
  | letE _ _ _ ih₁ ih₂ ih₃ => exact .letE (ih₁ d) (ih₂ d) (ih₃ (d + 1))
  | proj _ ih => exact .proj (ih d)

theorem mkAppN {f f' : Expr} {as bs : List Expr} (hf : Approx f f')
    (hab : Approx.Args as bs) : Approx (Expr.mkAppN f as) (Expr.mkAppN f' bs) := by
  induction hab generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app hf ha)

/-- **A spine with a constant head**: the approximated term has the same
head and pointwise approximated arguments. -/
theorem spine {s t : Expr} {c : Name} {us : List Level} (h : Approx s t)
    (hs : s.getAppFn = .const c us) :
    t.getAppFn = .const c us ∧ Approx.Args s.getAppArgs t.getAppArgs := by
  induction h with
  | bot => exact absurd hs (by simp [Ground.bot, Expr.getAppFn])
  | const => exact ⟨hs, .nil⟩
  | app hf ha ihf _ =>
    simp only [Expr.getAppFn] at hs
    obtain ⟨h₁, h₂⟩ := ihf hs
    refine ⟨h₁, ?_⟩
    simp only [Expr.getAppArgs]
    exact h₂.append (.cons ha .nil)
  | _ => simp [Expr.getAppFn] at hs

theorem forall₂_length {as bs : List Expr} (h : Approx.Args as bs) :
    as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall₂_getD {as bs : List Expr} (h : Approx.Args as bs) (i : Nat) (x : Expr) :
    Approx (as.getD i x) (bs.getD i x) := by
  induction h generalizing i with
  | nil => exact refl x
  | cons ha _ ih =>
    cases i with
    | zero => exact ha
    | succ i => exact ih i

theorem forall₂_take {as bs : List Expr} (h : Approx.Args as bs) (n : Nat) :
    Approx.Args (as.take n) (bs.take n) := by
  induction h generalizing n with
  | nil => simp only [List.take_nil]; exact .nil
  | cons ha _ ih =>
    cases n with
    | zero => simp only [List.take_zero]; exact .nil
    | succ n => exact .cons ha (ih n)

theorem forall₂_drop {as bs : List Expr} (h : Approx.Args as bs) (n : Nat) :
    Approx.Args (as.drop n) (bs.drop n) := by
  induction h generalizing n with
  | nil => simp only [List.drop_nil]; exact .nil
  | cons _ h' ih =>
    cases n with
    | zero => exact .cons ‹_› h'
    | succ n => exact ih n

end Approx

/-- The comparand levels of a rule do not read the redex's arguments. -/
theorem recFireComparands_fst (rl : RecRule) (cnP : Nat) (lps : List Name) (us : List Level)
    (cl : List Name) (as bs : List Expr) (rP : Nat) :
    (recFireComparands rl cnP lps us cl as rP).1 = (recFireComparands rl cnP lps us cl bs rP).1 := by
  unfold recFireComparands; split <;> rfl

/-- **Erased reduction**: the `Red` rules the ground engine takes, on terms
with forgotten subterms, plus `forget`.  ι is the rule outside case 3 (its
four certificate premises are vacuous there); the K step is `Red.iotaK`. -/
inductive ERed (env : Env) : Expr → Expr → Prop where
  | refl {e : Expr} : ERed env e e
  | trans {a b c : Expr} : ERed env a b → ERed env b c → ERed env a c
  /-- a reduct may forget more -/
  | forget {a b c : Expr} : ERed env a b → Approx c b → ERed env a c
  | appFn {f f' a : Expr} : ERed env f f' → ERed env (.app f a) (.app f' a)
  | projArg {sn : Name} {i : Nat} {e e' : Expr} :
      ERed env e e' → ERed env (.proj sn i e) (.proj sn i e')
  | beta {ty body a : Expr} : ERed env (.app (.lam ty body) a) (body.instantiate1 a)
  | zeta {ty v body : Expr} : ERed env (.letE ty v body) (body.instantiate1 v)
  | delta {e e' : Expr} : unfoldDefinition env e = some e' → ERed env e e'
  | natLit {n : Nat} :
      natLitStored env = true → ERed env (.lit (.natVal n)) (natLitToConstructor n)
  | strLit {s : String} :
      strLitStored env = true → ERed env (.lit (.strVal s)) (strLitToConstructor s)
  | natSucc {a w : Expr} {n : Nat} :
      natLitStored env = true → ERed env a w → rawNatLit? w = some n →
      ERed env (.app (.const natSuccName []) a) (.lit (.natVal (n + 1)))
  | natOp {c : Name} {a wa b wb r : Expr} {n₁ n₂ : Nat} :
      c ∈ natBinOpNames →
      ERed env a wa → rawNatLit? wa = some n₁ →
      ERed env b wb → rawNatLit? wb = some n₂ →
      natOpResult c n₁ n₂ = some r →
      ERed env (.app (.app (.const c []) a) b) r
  | proj {sn : Name} {i : Nat} {e : Expr} {entry : ProjEntry}
      {us : List Level} {cvC : ConstantVal} {nP nF : Nat} :
      env.findProj? sn i = some entry →
      e.getAppFn = .const entry.ctor us →
      i < entry.numFields →
      e.getAppArgs.length = entry.numParams + entry.numFields →
      us.length = entry.levelParams.length →
      env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
      (Expr.peelPis e.getAppArgs.length
        (cvC.type.instantiateLevelParams cvC.levelParams us)).isSome = true →
      ERed env (.proj sn i e) (e.getAppArgs.getD (entry.numParams + i) (.bvar 0))
  | iota {e : Expr} {c : Name} {us : List Level} {cv : ConstantVal}
      {mI rP : Nat} {isK : Bool} {rules : List RecRule} {major : Expr} {cj : Name}
      {usj : List Level} {cvj : ConstantVal} {cnP cnF : Nat} {rl : RecRule} :
      e.getAppFn = .const c us →
      env.find? c = some (.recInfo cv mI rP isK rules) →
      e.getAppArgs.length = mI + 1 →
      us.length = cv.levelParams.length →
      ERed env (e.getAppArgs.getD mI (.bvar 0)) major →
      major.getAppFn = .const cj usj →
      env.find? cj = some (.ctorInfo cvj cnP cnF) →
      rules.find? (fun r' => r'.ctor == cj) = some rl →
      major.getAppArgs.length = cnP + rl.nfields →
      IotaCase env isK cvj (recFireComparands rl cnP cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 false →
      (Expr.peelPis e.getAppArgs.length
        (cv.type.instantiateLevelParams cv.levelParams us)).isSome = true →
      ERed env e
        (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP ++ major.getAppArgs.drop cnP))
  | iotaK {e : Expr} {c : Name} {us : List Level} {cv : ConstantVal}
      {mI rP : Nat} {rl : RecRule} :
      e.getAppFn = .const c us →
      env.find? c = some (.recInfo cv mI rP true [rl]) →
      e.getAppArgs.length = mI + 1 →
      us.length = cv.levelParams.length →
      (Expr.peelPis e.getAppArgs.length
        (cv.type.instantiateLevelParams cv.levelParams us)).isSome = true →
      ERed env e
        (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP))

/-- δ on an approximated spine. -/
theorem unfoldDefinition_approx {env : Env} {s t s' : Expr} (h : Approx s t)
    (hs : unfoldDefinition env s = some s') :
    ∃ t', unfoldDefinition env t = some t' ∧ Approx s' t' := by
  unfold unfoldDefinition at hs
  split at hs
  · rename_i n us hfn
    obtain ⟨htf, hargs⟩ := h.spine hfn
    unfold unfoldDefinition
    rw [htf]
    split at hs
    · rename_i cv v hint hfind
      simp only [hfind]
      split at hs
      · rename_i hlen
        obtain rfl := (Option.some.inj hs).symm
        exact ⟨_, by simp [hlen], Approx.mkAppN (Approx.refl _) hargs⟩
      · exact absurd hs (by simp)
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- **The lifting**: an erased reduction of `s` is matched, for every `t`
that `s` approximates, by a `Red` reduction of `t` whose reduct the erased
reduct approximates. -/
theorem ERed.lift {env : Env} {d : Nat} {s s' : Expr} (h : ERed env s s') :
    ∀ {t : Expr}, Approx s t → ∃ t', Red env d t t' ∧ Approx s' t' := by
  induction h with
  | refl => intro t ht; exact ⟨t, .refl, ht⟩
  | trans _ _ ih₁ ih₂ =>
    intro t ht
    obtain ⟨t₁, hr₁, ha₁⟩ := ih₁ ht
    obtain ⟨t₂, hr₂, ha₂⟩ := ih₂ ha₁
    exact ⟨t₂, .trans hr₁ hr₂, ha₂⟩
  | forget _ hc ih =>
    intro t ht
    obtain ⟨t₁, hr₁, ha₁⟩ := ih ht
    exact ⟨t₁, hr₁, hc.trans ha₁⟩
  | appFn _ ih =>
    intro t ht
    obtain ⟨g, b, rfl, hg, hb⟩ := ht.app_inv
    obtain ⟨g', hr, ha⟩ := ih hg
    exact ⟨_, .appFn hr, .app ha hb⟩
  | projArg _ ih =>
    intro t ht
    obtain ⟨e', rfl, he⟩ := ht.proj_inv
    obtain ⟨e'', hr, ha⟩ := ih he
    exact ⟨_, .projArg hr, .proj ha⟩
  | beta =>
    intro t ht
    obtain ⟨g, a', rfl, hg, ha⟩ := ht.app_inv
    obtain ⟨ty', b', rfl, -, hb⟩ := hg.lam_inv
    exact ⟨_, .beta, hb.instantiate1 ha 0⟩
  | zeta =>
    intro t ht
    obtain ⟨ty', v', b', rfl, -, hv, hb⟩ := ht.letE_inv
    exact ⟨_, .zeta, hb.instantiate1 hv 0⟩
  | delta hu =>
    intro t ht
    obtain ⟨t', hu', ha⟩ := unfoldDefinition_approx ht hu
    exact ⟨t', .delta hu', ha⟩
  | natLit hn =>
    intro t ht
    obtain rfl := ht.lit_inv
    exact ⟨_, .natLit hn, Approx.refl _⟩
  | strLit hs =>
    intro t ht
    obtain rfl := ht.lit_inv
    exact ⟨_, .strLit hs, Approx.refl _⟩
  | natSucc hn _ hw ih =>
    intro t ht
    obtain ⟨g, a', rfl, hg, ha⟩ := ht.app_inv
    obtain rfl := hg.const_inv
    obtain ⟨w', hr, haw⟩ := ih ha
    obtain rfl := haw.rawNatLit hw
    exact ⟨_, .natSucc hn hr hw, Approx.refl _⟩
  | natOp hc _ hwa _ hwb hres iha ihb =>
    intro t ht
    obtain ⟨g, b', rfl, hg, hb⟩ := ht.app_inv
    obtain ⟨g', a', rfl, hg', ha⟩ := hg.app_inv
    obtain rfl := hg'.const_inv
    obtain ⟨wa', hra, haa⟩ := iha ha
    obtain rfl := haa.rawNatLit hwa
    obtain ⟨wb', hrb, hab⟩ := ihb hb
    obtain rfl := hab.rawNatLit hwb
    exact ⟨_, .natOp hc hra hwa hrb hwb hres, Approx.refl _⟩
  | proj hfp hfn hi hlen hlv hfc hpi =>
    intro t ht
    obtain ⟨e', rfl, he⟩ := ht.proj_inv
    obtain ⟨hfn', hargs⟩ := he.spine hfn
    have hl := Approx.forall₂_length hargs
    refine ⟨_, .proj hfp hfn' hi (hl ▸ hlen) hlv hfc (hl ▸ hpi), ?_⟩
    exact Approx.forall₂_getD hargs _ _
  | @iota e c us cv mI rP isK rules major cj usj cvj cnP cnF rl hfn hrec hlen hus _ hmfn hcj
      hrule hmlen hcase hpi ih =>
    intro t ht
    obtain ⟨hfn', hargs⟩ := ht.spine hfn
    have hl := Approx.forall₂_length hargs
    obtain ⟨major', hrm, ham⟩ := ih (Approx.forall₂_getD hargs mI (.bvar 0))
    obtain ⟨hmfn', hmargs⟩ := ham.spine hmfn
    have hml := Approx.forall₂_length hmargs
    refine ⟨_, Red.iota (c3 := false) (residual := .bvar 0) hfn' hrec (hl ▸ hlen) hus hrm hmfn'
      hcj hrule (hml ▸ hmlen) ?_ (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
      (hl ▸ hpi) (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
      (fun h => absurd h (by simp)), ?_⟩
    · rw [← recFireComparands_fst rl cnP cv.levelParams us cvj.levelParams e.getAppArgs]
      exact hcase
    · exact Approx.mkAppN (Approx.refl _)
        ((Approx.forall₂_take hargs rP).append (Approx.forall₂_drop hmargs cnP))
  | @iotaK e c us cv mI rP rl hfn hrec hlen hus hpi =>
    intro t ht
    obtain ⟨hfn', hargs⟩ := ht.spine hfn
    have hl := Approx.forall₂_length hargs
    exact ⟨_, .iotaK hfn' hrec (hl ▸ hlen) hus (hl ▸ hpi),
      Approx.mkAppN (Approx.refl _) (Approx.forall₂_take hargs rP)⟩

/-- **The site's corollary**: an erased reduction to a constant (no
forgotten part) of a term approximating `t` is a reduction of `t` to that
constant. -/
theorem ERed.lift_const {env : Env} {d : Nat} {s t : Expr} {c : Name} {us : List Level}
    (h : ERed env s (.const c us)) (ht : Approx s t) : Red env d t (.const c us) := by
  obtain ⟨t', hr, ha⟩ := h.lift (d := d) ht
  rw [ha.const_inv] at hr
  exact hr

end ConLeche.Verify.Ground
