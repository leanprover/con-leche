import Setlec.Model.Core.PairEta

/-!
# Checker-core soundness: Spine

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims mode m φ fuel) (ihd : DefEqClaims mode m φ fuel)
  (ihi : InferClaims mode m φ fuel)

/-- Pointwise interpretation of an expression spine. -/
def InterpSpine (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : List Expr → List V → Prop
  | [], [] => True
  | x :: xs, v :: vs =>
    interpExpr V cval env φ d ρ x = some v ∧
    InterpSpine cval env φ d ρ xs vs
  | _, _ => False

theorem InterpSpine.length {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs → vs.length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: vs, h => by
    simp only [List.length_cons]
    exact congrArg (· + 1) (InterpSpine.length h.2)

theorem InterpSpine.of_mapM {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs : List V},
      xs.mapM (interpExpr V cval env φ d ρ) = some vs →
      InterpSpine cval env φ d ρ xs vs := by
  intro xs
  induction xs with
  | nil =>
    intro vs h
    obtain rfl : vs = [] := by simpa using h.symm
    trivial
  | cons x xs ih =>
    intro vs h
    rw [List.mapM_cons] at h
    cases hx : interpExpr V cval env φ d ρ x with
    | none => rw [hx] at h; exact nomatch h
    | some v =>
      rw [hx] at h
      cases hxs : xs.mapM (interpExpr V cval env φ d ρ) with
      | none => rw [hxs] at h; exact nomatch h
      | some vs' =>
        rw [hxs] at h
        obtain rfl : vs = v :: vs' := by simpa using h.symm
        exact ⟨hx, ih hxs⟩

theorem InterpSpine.mapM_eq {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs →
      xs.mapM (interpExpr V cval env φ d ρ) = some vs
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, v :: vs, h => by
    rw [List.mapM_cons, h.1, InterpSpine.mapM_eq h.2]
    rfl

theorem InterpSpine.append_inv {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {d : Nat} {ρ : Nat → V} :
    ∀ {xs ys : List Expr} {ws : List V},
      InterpSpine cval env φ d ρ (xs ++ ys) ws →
      ∃ vs us, ws = vs ++ us ∧ InterpSpine cval env φ d ρ xs vs ∧
        InterpSpine cval env φ d ρ ys us
  | [], ys, ws, h => ⟨[], ws, rfl, trivial, h⟩
  | x :: xs, ys, [], h => nomatch h
  | x :: xs, ys, w :: ws, h => by
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨vs, us, rfl, h1, h2⟩ := InterpSpine.append_inv hrest
    exact ⟨w :: vs, us, rfl, ⟨hx, h1⟩, h2⟩

theorem InterpSpine.take {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (n : Nat) {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ (xs.take n) (vs.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, InterpSpine.take n h.2⟩

theorem InterpSpine.drop {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (n : Nat) {xs : List Expr} {vs : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ (xs.drop n) (vs.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | n + 1, _ :: _, _ :: _, h => InterpSpine.drop n h.2

theorem InterpSpine.append {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ {xs ys : List Expr} {vs us : List V},
      InterpSpine cval env φ d ρ xs vs → InterpSpine cval env φ d ρ ys us →
      InterpSpine cval env φ d ρ (xs ++ ys) (vs ++ us)
  | [], _, [], _, _, h2 => h2
  | [], _, _ :: _, _, h1, _ => nomatch h1
  | _ :: _, _, [], _, h1, _ => nomatch h1
  | _ :: _, _, _ :: _, _, h1, h2 =>
    ⟨h1.1, InterpSpine.append h1.2 h2⟩

/-- An argument spine interprets pointwise to its values. -/
theorem InstArgs.toInterpSpine {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      InstArgs cval env φ D ρ as vs → InterpSpine cval env φ D ρ as vs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => ⟨h.1.2.2, InstArgs.toInterpSpine h.2⟩

/-- Inversion of an application spine's `AnnotOk`: the head and every
argument are `AnnotOk`, the head interprets, and the argument values
form a typed chain interpreting the whole spine. -/
theorem annotOk_spine_inv {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr), xs ≠ [] →
      AnnotOk V cval env φ d ρ (Expr.mkAppN f xs) →
      AnnotOk V cval env φ d ρ f ∧
      (∀ x ∈ xs, AnnotOk V cval env φ d ρ x) ∧
      ∃ vf vs, interpExpr V cval env φ d ρ f = some vf ∧
        InterpSpine cval env φ d ρ xs vs ∧ ChainSlots V vf vs ∧
        interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
          some (SpineFold V vf vs)
  | [], _, hne, _ => absurd rfl hne
  | [x], f, _, ha => by
    simp only [Expr.mkAppN, AnnotOk] at ha ⊢
    obtain ⟨hf, hx, vf, vx, A, B, hif, hix, hp, hm⟩ := ha
    refine ⟨hf, by simpa using hx, vf, [vx], hif, ⟨hix, trivial⟩,
      ⟨⟨A, B, hp, hm⟩, trivial⟩, ?_⟩
    rw [interpExpr, hif, hix]
    rfl
  | x :: y :: xs, f, _, ha => by
    have hstep : Expr.mkAppN f (x :: y :: xs) =
        Expr.mkAppN (Expr.app f x) (y :: xs) := rfl
    rw [hstep] at ha
    obtain ⟨hfx, hrest, vfx, vs, hifx, hisp, hchain, hifold⟩ :=
      annotOk_spine_inv (y :: xs) (Expr.app f x) (by simp) ha
    simp only [AnnotOk] at hfx
    obtain ⟨hf, hx, vf, vx, A, B, hif, hix, hp, hm⟩ := hfx
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf vx) := by
      rw [interpExpr, hif, hix]
    rw [happ] at hifx
    obtain rfl := Option.some.inj hifx
    refine ⟨hf, ?_, vf, vx :: vs, hif, ⟨hix, hisp⟩,
      ⟨⟨A, B, hp, hm⟩, hchain⟩, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hrest z hz
    · rw [hstep]
      exact hifold

/-- Interpreting an application spine is folding set application: no
side conditions, the `app` case of the interpretation composes
unconditionally. -/
theorem interp_mkAppN {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr) {vf : V} {vs : List V},
      interpExpr V cval env φ d ρ f = some vf →
      InterpSpine cval env φ d ρ xs vs →
      interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
        some (SpineFold V vf vs)
  | [], f, vf, [], hif, _ => hif
  | [], f, vf, _ :: _, _, hsp => nomatch hsp
  | x :: xs, f, vf, [], _, hsp => nomatch hsp
  | x :: xs, f, vf, v :: vs, hif, hsp => by
    obtain ⟨hix, hsp'⟩ := hsp
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf v) := by
      rw [interpExpr, hif, hix]
    rw [show Expr.mkAppN f (x :: xs) = Expr.mkAppN (Expr.app f x) xs from rfl,
      interp_mkAppN xs (Expr.app f x) happ hsp']
    rfl

/-- Forward construction of an application spine's `AnnotOk` and
interpretation from its parts. -/
theorem annotOk_spine {cval : ConstVal V} {env : Env} {φ : Name → Nat}
    {d : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (f : Expr) {vf : V} {vs : List V},
      AnnotOk V cval env φ d ρ f →
      interpExpr V cval env φ d ρ f = some vf →
      (∀ x ∈ xs, AnnotOk V cval env φ d ρ x) →
      InterpSpine cval env φ d ρ xs vs → ChainSlots V vf vs →
      AnnotOk V cval env φ d ρ (Expr.mkAppN f xs) ∧
      interpExpr V cval env φ d ρ (Expr.mkAppN f xs) =
        some (SpineFold V vf vs)
  | [], f, vf, [], hf, hif, _, _, _ => ⟨hf, hif⟩
  | [], f, vf, _ :: _, _, _, _, hsp, _ => nomatch hsp
  | x :: xs, f, vf, [], _, _, _, hsp, _ => nomatch hsp
  | x :: xs, f, vf, v :: vs, hf, hif, hxs, hsp, hchain => by
    obtain ⟨hix, hsp'⟩ := hsp
    obtain ⟨hslot, hchain'⟩ := hchain
    obtain ⟨A, B, hp, hm⟩ := hslot
    have happ : interpExpr V cval env φ d ρ (Expr.app f x) =
        some (SetTheory.app vf v) := by
      rw [interpExpr, hif, hix]
    have hafx : AnnotOk V cval env φ d ρ (Expr.app f x) := by
      simp only [AnnotOk]
      exact ⟨hf, hxs x List.mem_cons_self, vf, v, A, B, hif, hix,
        hp, hm⟩
    exact annotOk_spine xs (Expr.app f x) (vf := SetTheory.app vf v)
      (vs := vs) hafx happ
      (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) hsp' hchain'

theorem InterpSpine.functional {d : Nat} {ρ : Nat → V} :
    ∀ {xs : List Expr} {vs vs' : List V},
      InterpSpine cval env φ d ρ xs vs →
      InterpSpine cval env φ d ρ xs vs' → vs = vs' := by
  intro xs
  induction xs with
  | nil =>
    intro vs vs' h h'
    match vs, h with
    | [], _ =>
      match vs', h' with
      | [], _ => rfl
  | cons x xs ih =>
    intro vs vs' h h'
    match vs, h with
    | v :: vs, ⟨hv, hrest⟩ =>
      match vs', h' with
      | v' :: vs', ⟨hv', hrest'⟩ =>
        rw [hv] at hv'
        obtain rfl := Option.some.inj hv'
        rw [ih hrest hrest']

/-- The head of an interpreted application spine interprets. -/
theorem interp_mkAppN_head_some {cval : ConstVal V} {env : Env}
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (h : Expr) {w : V},
      interpExpr V cval env φ D ρ (Expr.mkAppN h xs) = some w →
      ∃ vh, interpExpr V cval env φ D ρ h = some vh
  | [], _, w, hi => ⟨w, hi⟩
  | x :: xs, h, w, hi => by
    obtain ⟨v', hv'⟩ := interp_mkAppN_head_some xs (.app h x)
      (show interpExpr V cval env φ D ρ (Expr.mkAppN (.app h x) xs) =
        some w from hi)
    revert hv'
    simp only [interpExpr]
    cases hf : interpExpr V cval env φ D ρ h with
    | none =>
      cases ha : interpExpr V cval env φ D ρ x with
      | none => intro hv'; exact nomatch hv'
      | some va => intro hv'; exact nomatch hv'
    | some vh => intro _; exact ⟨vh, rfl⟩

/-- A list of length `n + 1` splits off its last element at `n`. -/
theorem take_concat_of_length {α : Type _} :
    ∀ {l : List α} {n : Nat}, l.length = n + 1 →
      ∃ x, l = l.take n ++ [x] ∧ l[n]? = some x
  | [], n, h => nomatch h
  | [x], 0, _ => ⟨x, rfl, rfl⟩
  | x :: y :: l, 0, h => by simp at h
  | x :: y :: l, n + 1, h => by
    obtain ⟨z, hz, hg⟩ := take_concat_of_length
      (l := y :: l) (n := n) (by simpa using h)
    refine ⟨z, ?_, ?_⟩
    · have : x :: y :: l = x :: (y :: l) := rfl
      rw [this, List.take_succ_cons, List.cons_append, ← hz]
    · simpa using hg

end Claims

end Setlec
