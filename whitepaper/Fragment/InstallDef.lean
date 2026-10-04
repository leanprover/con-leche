module

public import Fragment.Sound
public import Fragment.GenScope
public import Fragment.IndCommon

@[expose] public section

/-!
# Installing a definition

The first of the two ways the environment grows: a definition the
checker accepts (`DefOk`, `Decl.lean`) is added, and having a model
(`EnvModel`, `EnvModel.lean`) is preserved.  The new constant's set is
its value's denotation at the positional valuation of its level
parameters (`defVal`); the old constants keep their sets.

Two pieces of bookkeeping carry the argument:

* **A closed environment** (`Env.Scoped`): every stored term is in
  scope of the environment itself, so no stored term mentions the
  fresh name — which is why the old laws survive the new assignment
  (`EnvModel.transport`: a model's laws read the assignment only at
  the constants the stored terms mention, `Hygiene.lean`).
* **The value's set is its denotation at every use**
  (`defVal_eq`): the value is closed, so the environment is
  irrelevant; it mentions no fresh constant, so the old and the new
  assignment agree on it; and it uses only its own level parameters,
  at which the positional valuation is the use's substituted
  valuation (`valOf_map_eval`).

The three laws for the new constant then come from soundness
(`Sound.lean`) at the transported model: the declared type is
well-denoted (`Infer`), the value is a member of it (`Infer` and
`DefEq`), and the value denotes the constant (`defVal_eq`).
Con-leche: `ConLeche/Model/Install/Defn.lean`.
-/

namespace Fragment
open SetLib

universe u

/-! ## A closed environment -/

namespace Env

/-- The constant just stored is found. -/
theorem find?_add_self (env : Env) (c : Name) (ci : ConstInfo) :
    (env.add c ci).find? c = some ci := by
  rw [find?_add, ite_eq_left rfl]

/-- Any other name is found as before. -/
theorem find?_add_of_ne (env : Env) {n c : Name} (ci : ConstInfo) (h : n ≠ c) :
    (env.add c ci).find? n = env.find? n := by
  rw [find?_add, ite_eq_right h]

/-- A stored name stays stored. -/
theorem isSome_find?_add {env : Env} {n : Name} (h : (env.find? n).isSome) (c : Name)
    (ci : ConstInfo) : ((env.add c ci).find? n).isSome := by
  rw [find?_add]
  split
  · rfl
  · exact h

/-- A stored name is not the fresh one. -/
theorem ne_of_isSome_find? {env : Env} {n c : Name} (hn : (env.find? n).isSome)
    (hc : env.find? c = none) : n ≠ c := by
  rintro rfl
  rw [hc] at hn
  exact Bool.false_ne_true hn

end Env

namespace Expr

/-- A term in scope stays in scope when the environment grows. -/
theorem Scoped.add {env : Env} {ps : List Name} {k : Nat} {e : Expr} (h : Scoped env ps k e)
    (c : Name) (ci : ConstInfo) : Scoped (env.add c ci) ps k e :=
  ⟨h.1, fun d hd => Env.isSome_find?_add (h.2.1 d hd) c ci, h.2.2⟩

end Expr

/-- Every stored term is closed, mentions only stored constants and
uses only its constant's level parameters, and every recursor rule
fires on a stored constructor: the environment is closed under
itself. -/
def Env.Scoped (env : Env) : Prop :=
  ∀ c ci, env.find? c = some ci →
    Expr.Scoped env ci.lparams 0 ci.type ∧
    (∀ v, ci.value? = some v → Expr.Scoped env ci.lparams 0 v) ∧
    (∀ nP nM nMin nI rules, ci.kind = .recursor nP nM nMin nI rules →
      ∀ rl ∈ rules, Expr.Scoped env ci.lparams 0 rl.rhs ∧ (env.find? rl.ctor).isSome)

/-- The empty environment is closed. -/
theorem Env.Scoped.empty : Env.Scoped Env.empty := fun _ _ h => by simp at h

/-- A closed environment stays closed under a fresh constant whose
type and value are in scope of it, and whose rules (at a recursor) are
in scope of the extended environment. -/
theorem Env.Scoped.add {env : Env} {c : Name} {ci : ConstInfo} (hs : Env.Scoped env)
    (hfresh : env.find? c = none) (hty : Expr.Scoped env ci.lparams 0 ci.type)
    (hv : ∀ v, ci.value? = some v → Expr.Scoped env ci.lparams 0 v)
    (hrules : ∀ nP nM nMin nI rules, ci.kind = .recursor nP nM nMin nI rules →
      ∀ rl ∈ rules, Expr.Scoped (env.add c ci) ci.lparams 0 rl.rhs ∧
        ((env.add c ci).find? rl.ctor).isSome) :
    Env.Scoped (env.add c ci) := by
  intro n ci' hfind
  rw [Env.find?_add] at hfind
  split at hfind
  · rename_i h
    cases hfind
    subst h
    exact ⟨hty.add _ _, fun v hv' => (hv v hv').add _ _, hrules⟩
  · have h := hs n ci' hfind
    refine ⟨h.1.add c ci, fun v hv' => (h.2.1 v hv').add c ci, ?_⟩
    intro nP nM nMin nI rules hk rl hrl
    have h' := h.2.2 nP nM nMin nI rules hk rl hrl
    exact ⟨h'.1.add c ci, Env.isSome_find?_add h'.2 c ci⟩

/-! ## The value walks read the model through the telescope -/

variable {V : Type u} [IndLib V]

/-- The value walks read the model only through the telescope's
constants. -/
theorem TeleFitV_congr_model {M M' : Name → List Nat → V} {φ : Name → Nat} :
    ∀ {ρ : Nat → V} {T : Expr} {vs : List V}, (∀ c ∈ T.consts, ∀ ls, M c ls = M' c ls) →
      (TeleFitV M φ ρ T vs ↔ TeleFitV M' φ ρ T vs)
  | ρ, T, [], _ => ⟨fun _ => TeleFitV_nil M' φ ρ T, fun _ => TeleFitV_nil M φ ρ T⟩
  | ρ, T, v :: vs, h => by
    cases T with
    | pi A pw B =>
      rw [Expr.consts_pi] at h
      rw [TeleFitV_pi_cons, TeleFitV_pi_cons,
        interp_consts fun c hc => h c (List.mem_append_left _ hc),
        TeleFitV_congr_model fun c hc => h c (List.mem_append_right _ hc)]
    | _ => exact Iff.rfl

omit [IndLib V] in
/-- The body a telescope leaves mentions only the telescope's
constants. -/
theorem piBodyV_consts : ∀ {ρ : Nat → V} {T : Expr} {vs : List V} {B : Expr} {ρ' : Nat → V},
    piBodyV ρ T vs = some (B, ρ') → ∀ c ∈ B.consts, c ∈ T.consts
  | ρ, T, [], B, ρ', h, c, hc => by
    rw [piBodyV_nil, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
    exact hc
  | ρ, T, v :: vs, B, ρ', h, c, hc => by
    cases T with
    | pi A pw B' =>
      simp only [piBodyV] at h
      rw [Expr.consts_pi]
      exact List.mem_append_right _ (piBodyV_consts h c hc)
    | _ => simp [piBodyV] at h

/-! ## Transport -/

/-- A model's laws survive changing the assignment away from the
stored names: every stored term mentions only stored constants. -/
def EnvModel.transport {env : Env} (m : EnvModel V env) (hs : Env.Scoped env)
    (M' : Name → List Nat → V) (h : ∀ c, (env.find? c).isSome → ∀ ls, m.M c ls = M' c ls) :
    EnvModel V env where
  M := M'
  type_ok := fun c ci hfind φ ρ ls hlen => by
    have hc : ∀ d ∈ (ci.type.instL ci.lparams ls).consts, ∀ ls', m.M d ls' = M' d ls' :=
      fun d hd ls' => by
        rw [Expr.consts_instL] at hd
        exact h d ((hs c ci hfind).1.2.1 d hd) ls'
    have := m.type_ok c ci hfind φ ρ ls hlen
    rwa [WellDenoted_consts hc, interp_consts hc, h c (by simp [hfind])] at this
  unfold := fun c ci v hfind hv φ ρ ls hlen => by
    have hc : ∀ d ∈ (v.instL ci.lparams ls).consts, ∀ ls', m.M d ls' = M' d ls' :=
      fun d hd ls' => by
        rw [Expr.consts_instL] at hd
        exact h d (((hs c ci hfind).2.1 v hv).2.1 d hd) ls'
    have := m.unfold c ci v hfind hv φ ρ ls hlen
    rwa [WellDenoted_consts hc, interp_consts hc, h c (by simp [hfind])] at this
  rec_rules := fun c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij => by
    have law := m.rec_rules c ci nP nM nMin nI rules hfind hkind rl hrl hinst cij hcij
    have hsc := hs c ci hfind
    have hsj := hs rl.ctor cij hcij
    have hT : ∀ us, ∀ d ∈ (ci.type.instL ci.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d (hsc.1.2.1 d hd) ls
    have hTj : ∀ us, ∀ d ∈ (cij.type.instL cij.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d (hsj.1.2.1 d hd) ls
    have hR : ∀ us, ∀ d ∈ (rl.rhs.instL ci.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d ((hsc.2.2 nP nM nMin nI rules hkind rl hrl).1.2.1 d hd) ls
    have hc : ∀ ls, m.M c ls = M' c ls := h c (by simp [hfind])
    have hctor : ∀ ls, m.M rl.ctor ls = M' rl.ctor ls := h rl.ctor (by simp [hcij])
    intro φ ρ us usj xs ys h1 h2 h3 h4 hfit1 hfit2 hlv hps hidx
    rw [← hctor, ← TeleFitV_congr_model (hT us)] at hfit1
    rw [← TeleFitV_congr_model (hTj usj)] at hfit2
    have hidx' : ∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip (xs.drop (nP + nM + nMin)), p.1 = p.2 := by
      intro B ρ' I lsI rps ridx hpb hB hlen
      have hmap : ridx.map (interp m.M φ ρ') = ridx.map (interp M' φ ρ') := by
        apply List.map_congr_left
        intro e he
        apply interp_consts
        intro d hd ls
        apply hTj usj
        apply piBodyV_consts hpb
        rw [hB, Expr.consts_mkAppN, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e, List.mem_append_right _ he, hd⟩
      rw [hmap]
      exact hidx B ρ' I lsI rps ridx hpb hB hlen
    have res := law φ ρ us usj xs ys h1 h2 h3 h4 hfit1 hfit2 hlv hps hidx'
    rwa [hc, hctor, interp_consts (hR us), WellDenoted_consts (hR us)] at res
  rec_rules_nested := fun c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij I nPc nf
      hcij hcijk => by
    have law := m.rec_rules_nested c ci nP nM nMin nI rules hfind hkind rl hrl lvs pinst hinst cij
      I nPc nf hcij hcijk
    have hsc := hs c ci hfind
    have hsj := hs rl.ctor cij hcij
    have hT : ∀ us, ∀ d ∈ (ci.type.instL ci.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d (hsc.1.2.1 d hd) ls
    have hTj : ∀ us, ∀ d ∈ (cij.type.instL cij.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d (hsj.1.2.1 d hd) ls
    have hR : ∀ us, ∀ d ∈ (rl.rhs.instL ci.lparams us).consts, ∀ ls, m.M d ls = M' d ls :=
      fun us d hd ls => by
        rw [Expr.consts_instL] at hd
        exact h d ((hsc.2.2 nP nM nMin nI rules hkind rl hrl).1.2.1 d hd) ls
    have hc : ∀ ls, m.M c ls = M' c ls := h c (by simp [hfind])
    have hctor : ∀ ls, m.M rl.ctor ls = M' rl.ctor ls := h rl.ctor (by simp [hcij])
    intro φ ρ us usj xs ys h1 h2 h3 h4 hfit1 hfit2 hidx
    rw [← hctor, ← TeleFitV_congr_model (hT us)] at hfit1
    rw [← TeleFitV_congr_model (hTj usj)] at hfit2
    have hidx' : ∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nPc →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip (xs.drop (nP + nM + nMin)), p.1 = p.2 := by
      intro B ρ' I lsI rps ridx hpb hB hlen
      have hmap : ridx.map (interp m.M φ ρ') = ridx.map (interp M' φ ρ') := by
        apply List.map_congr_left
        intro e he
        apply interp_consts
        intro d hd ls
        apply hTj usj
        apply piBodyV_consts hpb
        rw [hB, Expr.consts_mkAppN, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e, List.mem_append_right _ he, hd⟩
      rw [hmap]
      exact hidx B ρ' I lsI rps ridx hpb hB hlen
    have res := law φ ρ us usj xs ys h1 h2 h3 h4 hfit1 hfit2 hidx'
    rwa [hc, hctor, interp_consts (hR us), WellDenoted_consts (hR us)] at res

/-- The transported model's assignment is the new one. -/
theorem EnvModel.transport_M {env : Env} (m : EnvModel V env) (hs : Env.Scoped env)
    (M' : Name → List Nat → V) (h : ∀ c, (env.find? c).isSome → ∀ ls, m.M c ls = M' c ls) :
    (m.transport hs M' h).M = M' := rfl

/-! ## The value's set -/

/-- The value's set at concrete levels: read at the positional
valuation, in the closed environment. -/
noncomputable def defVal (M : Name → List Nat → V) (ci : ConstInfo) (v : Expr) (ls : List Nat) : V :=
  interp M (valOf ci.lparams ls) base v

/-- **The value's set is its denotation at every use.**  At a use
under a valuation `φ` and levels `ls`, the value's set (at the
evaluated levels, under the old assignment) is the instantiated
value's denotation under any assignment agreeing with the old one on
the stored constants, and any environment: the value is closed,
mentions only stored constants and uses only its level parameters. -/
theorem defVal_eq {env : Env} {ci : ConstInfo} {v : Expr} {M M' : Name → List Nat → V}
    (hvs : Expr.Scoped env ci.lparams 0 v)
    (hM : ∀ d, (env.find? d).isSome → ∀ ls, M d ls = M' d ls)
    (φ : Name → Nat) (ρ : Nat → V) {ls : List Level} (hlen : ls.length = ci.lparams.length) :
    defVal M ci v (ls.map (Level.eval φ)) = interp M' φ ρ (v.instL ci.lparams ls) := by
  unfold defVal
  rw [interp_instL, interp_consts fun d hd ls => hM d (hvs.2.1 d hd) ls,
    interp_lparams hvs.2.2 fun n hn => valOf_map_eval φ hlen hn,
    interp_closedAt (ρ' := ρ) hvs.1 fun i hi => absurd hi (Nat.not_lt_zero i)]

/-! ## Installing a definition -/

variable [LevelOracle]

/-- A closed environment stays closed under an accepted definition. -/
theorem Env.Scoped.add_def {env : Env} {c : Name} {ci : ConstInfo} (hs : Env.Scoped env)
    (hok : DefOk env c ci) : Env.Scoped (env.add c ci) := by
  have hts := hok.type_scoped
  have hvs := hok.value_scoped
  obtain ⟨hfresh, _, ⟨v, _, hkind, _, _, _⟩, _⟩ := hok
  refine hs.add hfresh hts (fun v' hv' => ?_) (fun _ _ _ _ _ hk => ?_)
  · simp only [ConstInfo.value?, hkind, ConstKind.value?, Option.some.injEq] at hv'
    rw [← hv']
    exact hvs v hkind
  · rw [hkind] at hk
    cases hk

/-- **Installing a definition preserves having a model.**  The new
constant's set is its value's (`defVal`); every stored constant keeps
its set. -/
theorem install_def {env : Env} {c : Name} {ci : ConstInfo} (hs : Env.Scoped env)
    (m : EnvModel V env) (hok : DefOk env c ci) :
    ∃ m' : EnvModel V (env.add c ci), ∀ n, (env.find? n).isSome → ∀ ls, m'.M n ls = m.M n ls := by
  have hvs' := hok.value_scoped
  obtain ⟨hfresh, ⟨s, u, hT, _⟩, ⟨v, T, hkind, hv, hd, _⟩, _⟩ := hok
  have hvs := hvs' v hkind
  -- The new assignment: the value's set at `c`, the old sets elsewhere.
  obtain ⟨M', hM'c, hM'n⟩ : ∃ M' : Name → List Nat → V,
      (∀ ls, M' c ls = defVal m.M ci v ls) ∧ (∀ n, n ≠ c → ∀ ls, M' n ls = m.M n ls) :=
    ⟨fun n ls => if n = c then defVal m.M ci v ls else m.M n ls, fun ls => by simp,
      fun n hn ls => by simp [hn]⟩
  have hM' : ∀ n, (env.find? n).isSome → ∀ ls, m.M n ls = M' n ls :=
    fun n hn ls => (hM'n n (Env.ne_of_isSome_find? hn hfresh) ls).symm
  -- The old laws, at the new assignment.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : EnvModel V env, m₀.M = M' := ⟨m.transport hs M' hM', rfl⟩
  -- The new constant's laws, from soundness at the transported model.
  have hval : ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      M' c (ls.map (Level.eval φ)) = interp M' φ ρ (v.instL ci.lparams ls) :=
    fun φ ρ ls hlen => by rw [hM'c, defVal_eq hvs hM' φ ρ hlen]
  have hnew : ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted M' φ ρ (ci.type.instL ci.lparams ls) ∧
      WellDenoted M' φ ρ (v.instL ci.lparams ls) ∧
      interp M' φ ρ (v.instL ci.lparams ls) ∈ˢ interp M' φ ρ (ci.type.instL ci.lparams ls) := by
    intro φ ρ ls _
    have hTsem := infer_sound (m := m₀) (φ := Level.substVal φ ci.lparams ls) hT ρ (Sat_nil _ _ _)
    have hvsem := infer_sound (m := m₀) (φ := Level.substVal φ ci.lparams ls) hv ρ (Sat_nil _ _ _)
    have heq := defeq_sound (m := m₀) (φ := Level.substVal φ ci.lparams ls) hd ρ (Sat_nil _ _ _)
      hvsem.2.1 hTsem.1
    rw [hm₀] at hTsem hvsem heq
    rw [WellDenoted_instL, WellDenoted_instL, interp_instL, interp_instL, ← heq]
    exact ⟨hTsem.1, hvsem.1, hvsem.2.2⟩
  refine ⟨{ M := M', type_ok := ?_, unfold := ?_, rec_rules := ?_, rec_rules_nested := ?_ },
    fun n hn ls => hM'n n (Env.ne_of_isSome_find? hn hfresh) ls⟩
  · -- `type_ok`
    intro n ci' hfind φ ρ ls hlen
    rw [Env.find?_add] at hfind
    split at hfind
    · rename_i h
      cases hfind
      subst h
      have := hnew φ ρ ls hlen
      rw [hval φ ρ ls hlen]
      exact ⟨this.1, this.2.2⟩
    · have := m₀.type_ok n ci' hfind φ ρ ls hlen
      rwa [hm₀] at this
  · -- `unfold`
    intro n ci' v' hfind hv' φ ρ ls hlen
    rw [Env.find?_add] at hfind
    split at hfind
    · rename_i h
      cases hfind
      subst h
      simp only [ConstInfo.value?, hkind, ConstKind.value?, Option.some.injEq] at hv'
      subst hv'
      exact ⟨(hnew φ ρ ls hlen).2.1, (hval φ ρ ls hlen).symm⟩
    · have := m₀.unfold n ci' v' hfind hv' φ ρ ls hlen
      rwa [hm₀] at this
  · -- `rec_rules`: the new constant is a definition, not a recursor
    intro n ci' nP nM nMin nI rules hfind hk rl hrl hinst cij hcij
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      rw [hkind] at hk
      cases hk
    · have hctor := ((hs n ci' hfind).2.2 nP nM nMin nI rules hk rl hrl).2
      rw [Env.find?_add_of_ne env ci (Env.ne_of_isSome_find? hctor hfresh)] at hcij
      have := m₀.rec_rules n ci' nP nM nMin nI rules hfind hk rl hrl hinst cij hcij
      rwa [hm₀] at this
  · -- `rec_rules_nested`: likewise
    intro n ci' nP nM nMin nI rules hfind hk rl hrl lvs pinst hinst cij I nPc nf hcij hcijk
    rw [Env.find?_add] at hfind
    split at hfind
    · cases hfind
      rw [hkind] at hk
      cases hk
    · have hctor := ((hs n ci' hfind).2.2 nP nM nMin nI rules hk rl hrl).2
      rw [Env.find?_add_of_ne env ci (Env.ne_of_isSome_find? hctor hfresh)] at hcij
      have := m₀.rec_rules_nested n ci' nP nM nMin nI rules hfind hk rl hrl lvs pinst hinst cij I
        nPc nf hcij hcijk
      rwa [hm₀] at this

end Fragment
