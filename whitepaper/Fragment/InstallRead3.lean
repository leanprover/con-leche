module

public import Fragment.InstallRead2

@[expose] public section

/-!
# Reading a block, continued: the recursor's context agrees

The recursor's set is an abstraction over its context read in the
model with the former and the constructors at its own valuation; its
type is read in the final model at any valuation and environment.
The two readings of every entry of the recursor's context agree at
fitting prefixes (`agree_recCtx`): the parameters and indices are
expressions of the specification, the major's type and the motive's
read as the fibre and the motive space, and a minor premise's type
reads as the product over its fields (the field context agrees) and
its inductive hypotheses (their types read as the sets `IhTyped`
names) into the motive at the constructor value.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable {S : IndSpec} {M : Name → List Nat → V} {φ : Name → Nat} {env : Env}
  {F : List Nat → List V → List V → V}

/-- Two readers whose valuations agree on the block's level parameters
and on the elimination level. -/
def RecAgree (φ₁ φ₂ : Name → Nat) (S : IndSpec) : Prop := Level.eval φ₁ S.ℓ = Level.eval φ₂ S.ℓ

theorem RecAgree.q_holds {φ₁ φ₂ : Name → Nat} (h : RecAgree φ₁ φ₂ S) :
    S.q.holds φ₁ = S.q.holds φ₂ := by
  rw [S.q_holds, S.q_holds, h]

/-- A specification expression reads alike in two readers. -/
theorem Reader.read₂ {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ F M₁ φ₁) (R₂ : S.Reader (env := env) M φ F M₂ φ₂)
    {k : Nat} {e : Expr} (he : Expr.Scoped env S.lparams k e) {vs ps : List V} {ρ₁ ρ₂ : Nat → V}
    (hk : k ≤ vs.length + ps.length) :
    interp M₁ φ₁ (consList vs (consList ps ρ₁)) e = interp M₂ φ₂ (consList vs (consList ps ρ₂)) e := by
  rw [R₁.read he hk, R₂.read he hk]

/-- The parameter context agrees between two readers. -/
theorem Reader.agree_params₂ (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ F M₁ φ₁) (R₂ : S.Reader (env := env) M φ F M₂ φ₂)
    (ρ₁ ρ₂ : Nat → V) : CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ S.params := by
  intro i A hA vs hvs
  have hl := FitsVals_length M₁ φ₁ hvs
  have hi : i < S.params.length := (List.getElem?_eq_some_iff.mp hA).1
  have := R₁.read₂ R₂ (ps := []) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (hS.1 i A hA) (vs := vs)
    (by simp only [hl, List.length_drop, List.length_nil, Nat.add_zero, nP]; omega)
  simpa using this

/-- Dropping entries of a lifted context is lifting the dropped
context (an entry's lift depends only on the entries below it). -/
theorem _root_.Fragment.Expr.liftCtx_drop (f : Nat → Expr → Expr) :
    ∀ (Γ : List Expr) (n : Nat), (Expr.liftCtx f Γ).drop n = Expr.liftCtx f (Γ.drop n)
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: Γ, n + 1 => by simp [Expr.liftCtx_drop f Γ n]

/-- The lifted field context agrees between two readers, once
well-denoted in the second. -/
theorem Reader.agree_fieldCtxAt (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ F M₁ φ₁) (R₂ : S.Reader (env := env) M φ F M₂ φ₂)
    {c : CtorSpec} (hc : c ∈ S.ctors) {o : Nat} {os₁ os₂ ps : List V} {ρ₁ ρ₂ : Nat → V}
    (ho₁ : os₁.length = o) (ho₂ : os₂.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    CtxAgree M₁ M₂ φ₁ φ₂ (consList os₁ (consList ps ρ₁)) (consList os₂ (consList ps ρ₂))
      (S.fieldCtxAt c o) := by
  have hag := R₁.agree_fieldCtx hS R₂ (ρ₁ := ρ₁) (ρ₂ := ρ₂) hps hp (hS.2.2.2.1 c hc).1 hwd
  intro i A hA vs hvs
  unfold fieldCtxAt at hA hvs
  rw [Expr.liftCtx_getElem?, S.length_fieldCtx] at hA
  simp only [Option.map_eq_some_iff] at hA
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  have hl := FitsVals_length M₁ φ₁ hvs
  have hi : i < (S.fieldCtx c.fields).length := (List.getElem?_eq_some_iff.mp hA₀).1
  have hvl : vs.length = c.fields.length - 1 - i := by
    rw [hl, List.length_drop, Expr.length_liftCtx, S.length_fieldCtx]; omega
  rw [Expr.liftCtx_drop, FitsVals_liftCtx_liftN M₁ φ₁ _ _ _ ho₁] at hvs
  rw [← hvl, interp_liftCtx_liftN_entry M₁ φ₁ ρ₁ _ ho₁, interp_liftCtx_liftN_entry M₂ φ₂ ρ₂ _ ho₂]
  exact hag i A₀ hA₀ vs hvs

/-- The inductive hypotheses' context agrees between two readers
(their types read as the sets `IhTyped` names). -/
theorem Reader.agree_ihCtxAux (hS : S.Scoped env) (hpl : S.nest = none) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader (env := env) M φ F M₁ φ₁) (R₂ : S.Reader (env := env) M φ F M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) {c : CtorSpec} (hc : c ∈ S.ctors) {o : Nat} {fs os ps : List V}
    {ρ₁ ρ₂ : Nat → V} (hf : fs.length = c.fields.length) (ho : os.length = o) (hpos : 0 < o)
    (hps : ps.length = S.nP) :
    ∀ (L : List (Nat × Field)), (∀ kf ∈ L, kf ∈ c.recFields) → ∀ {l : Nat} {ihsE : List V},
      ihsE.length = l →
      CtxAgree M₁ M₂ φ₁ φ₂ (consList ihsE (consList fs (consList os (consList ps ρ₁))))
        (consList ihsE (consList fs (consList os (consList ps ρ₂)))) (S.ihCtxAux c.fields.length o L l)
  | [], _, _, _, _ => fun i A hA => by simp [ihCtxAux] at hA
  | kf :: rest, hL, l, ihsE, hi => by
    simp only [ihCtxAux]
    refine CtxAgree_append ?_ fun ws hws => ?_
    · intro i A hA vs hvs
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
        subst hA
        cases vs with
        | nil =>
          simp only [consList_nil]
          rw [R₁.read_ihTy hS hpl hc (hL kf List.mem_cons_self) hi hf ho hpos hps,
            R₂.read_ihTy hS hpl hc (hL kf List.mem_cons_self) hi hf ho hpos hps, hq.q_holds]
        | cons _ _ => exact absurd (FitsVals_length M₁ φ₁ hvs) (by simp)
      | succ i => simp at hA
    · obtain ⟨ih, rfl⟩ : ∃ ih, ws = [ih] := by
        have hl := FitsVals_length M₁ φ₁ hws
        cases ws with
        | nil => simp at hl
        | cons a t => cases t with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hl
      have := R₁.agree_ihCtxAux hS hpl R₂ hq hc (ρ₁ := ρ₁) (ρ₂ := ρ₂) hf ho hpos hps rest
        (fun kf' h => hL kf' (List.mem_cons_of_mem kf h)) (l := l + 1) (ihsE := ih :: ihsE)
        (by simp [hi])
      simpa using this

/-- **A minor premise's type reads alike in two readers** (the readers
agreeing on the elimination level), once the constructor's fields are
well-denoted in the second. -/
theorem Reader₂.agree_minorTy (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hpl : S.nest = none) (hfresh : env.find? S.name = none)
    {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) {minsE : List V} {m : V} {ps : List V}
    {ρ₁ ρ₂ : Nat → V} (hminsE : minsE.length = j) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hwd : CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    interp M₁ φ₁ (consList minsE (cons m (consList ps ρ₁))) (S.minorTy c j)
      = interp M₂ φ₂ (consList minsE (cons m (consList ps ρ₂))) (S.minorTy c j) := by
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hos : (minsE ++ [m]).length = j + 1 := by simp [hminsE]
  have henv : ∀ ρ : Nat → V, consList minsE (cons m (consList ps ρ)) = consList (minsE ++ [m]) (consList ps ρ) := by
    intro ρ; simp [consList_append]
  unfold minorTy
  rw [interp_mkPis, interp_mkPis, hq.q_holds, henv, henv]
  -- the field context agrees, and fits carry over
  have hagF := R₁.R.agree_fieldCtxAt hS R₂.R hcm (ρ₁ := ρ₁) (ρ₂ := ρ₂) hos hos hps hp hwd
  have hfits : ∀ fs, FitsVals M₁ φ₁ (consList (minsE ++ [m]) (consList ps ρ₁)) (S.fieldCtxAt c (j + 1)) fs →
      fs.length = c.fields.length ∧
      S.FitsFields M (S.lparams.map φ) (S.Fam M (S.lparams.map φ) ps) ps c.fields fs ∧
      (∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
        IdxFitAt S M φ ps (earlier fs k) f) := by
    intro fs hfs
    have hfs₂ := (FitsVals_congr₂ hagF).mp hfs
    unfold fieldCtxAt at hfs₂
    rw [FitsVals_liftCtx_liftN M₂ φ₂ _ _ _ hos] at hfs₂
    have hiff := R₂.R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hps hp hwd (vs := fs)
    have hfit := hiff.1.mp hfs₂
    exact ⟨S.FitsFields_length M _ hfit, hfit, hiff.2 hfit⟩
  refine piCtx_congr₂ ?_ fun vs hvs => ?_
  · refine CtxAgree_append hagF fun fs hfs => ?_
    obtain ⟨hf, -, -⟩ := hfits fs hfs
    rw [ihCtx_eq]
    exact R₁.R.agree_ihCtxAux hS hpl R₂.R hq hcm hf hos (by omega) hps c.recFields (fun _ h => h)
      (ihsE := []) rfl
  · obtain ⟨ihsR, fs, rfl, hl₁⟩ : ∃ ihsR fs, vs = ihsR ++ fs ∧ ihsR.length = (S.ihCtx c j).length := by
      have hl := FitsVals_length M₁ φ₁ hvs
      refine ⟨vs.take (S.ihCtx c j).length, vs.drop (S.ihCtx c j).length,
        (List.take_append_drop _ _).symm, ?_⟩
      simp at hl; simp [hl]
    obtain ⟨hwsF, -⟩ := (FitsVals_append M₁ φ₁ hl₁).mp hvs
    obtain ⟨hf, hfit, hidx⟩ := hfits fs hwsF
    have hi : ihsR.length = c.recFields.length := by rw [hl₁, ihCtx_eq, length_ihCtxAux]
    rw [consList_append ihsR fs (consList (minsE ++ [m]) (consList ps ρ₁)),
      consList_append ihsR fs (consList (minsE ++ [m]) (consList ps ρ₂)),
      R₁.read_concl_minor hS hfresh hc (ihsE := ihsR) (os := minsE ++ [m]) hi hf hos hps hp hfit hidx,
      R₂.read_concl_minor hS hfresh hc (ihsE := ihsR) (os := minsE ++ [m]) hi hf hos hps hp hfit hidx]

/-- The minors' context agrees between two readers. -/
theorem Reader₂.agree_minorsFrom (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hpl : S.nest = none) (hfresh : env.find? S.name = none) {m : V} {ps : List V}
    {ρ₁ ρ₂ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hwd : ∀ c ∈ S.ctors, CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    ∀ (cs : List CtorSpec) (j : Nat), (∀ i c, cs[i]? = some c → S.ctors[j + i]? = some c) →
      ∀ {minsE : List V}, minsE.length = j →
      CtxAgree M₁ M₂ φ₁ φ₂ (consList minsE (cons m (consList ps ρ₁)))
        (consList minsE (cons m (consList ps ρ₂))) (S.minorsFrom cs j)
  | [], _, _, _, _ => fun i A hA => by simp [minorsFrom] at hA
  | c :: cs, j, hcs, minsE, hminsE => by
    simp only [minorsFrom]
    have hc : S.ctors[j]? = some c := by simpa using hcs 0 c rfl
    refine CtxAgree_append ?_ fun ws hws => ?_
    · intro i A hA vs hvs
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
        subst hA
        cases vs with
        | nil =>
          simp only [consList_nil]
          exact R₁.agree_minorTy hS R₂ hq hpl hfresh hc hminsE hps hp (hwd c (List.mem_of_getElem? hc))
        | cons _ _ => exact absurd (FitsVals_length M₁ φ₁ hvs) (by simp)
      | succ i => simp at hA
    · obtain ⟨v, rfl⟩ : ∃ v, ws = [v] := by
        have hl := FitsVals_length M₁ φ₁ hws
        cases ws with
        | nil => simp at hl
        | cons a t => cases t with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hl
      have := R₁.agree_minorsFrom hS R₂ hq hpl hfresh (m := m) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hps hp hwd cs (j + 1)
        (fun i c' hc' => by have := hcs (i + 1) c' (by simpa using hc'); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
        (minsE := v :: minsE) (by simp [hminsE])
      simpa using this

/-- **The recursor's context agrees between two readers** — the sets
of its five parts read alike. -/
theorem Reader₂.agree_recCtx (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V}
    {φ₁ φ₂ : Name → Nat}
    (R₁ : S.Reader₂ (env := env) M φ M₁ φ₁) (R₂ : S.Reader₂ (env := env) M φ M₂ φ₂)
    (hq : RecAgree φ₁ φ₂ S) (hpl : S.nest = none) (hfresh : env.find? S.name = none) (ρ₁ ρ₂ : Nat → V)
    (hwd : ∀ c ∈ S.ctors, ∀ ps, ps.length = S.nP →
      FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx c.fields)) :
    CtxAgree M₁ M₂ φ₁ φ₂ ρ₁ ρ₂ S.recCtx := by
  unfold recCtx
  refine CtxAgree_append (R₁.R.agree_params₂ hS R₂.R ρ₁ ρ₂) fun ps hps₁ => ?_
  have hp := (R₁.R.fits_params hS).mp hps₁
  have hps : ps.length = S.nP := by have := FitsVals_length _ _ hps₁; simpa [nP] using this
  refine CtxAgree_append ?_ fun ms hms => ?_
  · intro i A hA vs hvs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
      subst hA
      cases vs with
      | nil =>
        simp only [consList_nil]
        rw [R₁.R.read_motiveTy hS hps hp, R₂.R.read_motiveTy hS hps hp, hq]
      | cons _ _ => exact absurd (FitsVals_length M₁ φ₁ hvs) (by simp)
    | succ i => simp at hA
  obtain ⟨m, rfl⟩ : ∃ m, ms = [m] := by
    have hl := FitsVals_length M₁ φ₁ hms
    cases ms with
    | nil => simp at hl
    | cons a t => cases t with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at hl
  simp only [consList_cons, consList_nil]
  refine CtxAgree_append ?_ fun mins hmins => ?_
  · rw [minorsCtx_eq]
    exact R₁.agree_minorsFrom hS R₂ hq hpl hfresh hps hp (fun c hc => hwd c hc ps hps hp) S.ctors 0
      (fun i c hc => by simpa using hc) (minsE := []) rfl
  have hmn : mins.length = S.n := by have := FitsVals_length _ _ hmins; simpa [length_minorsCtx] using this
  have hos : (mins ++ [m]).length = S.n + 1 := by simp [hmn]
  have henv : ∀ ρ : Nat → V, consList mins (cons m (consList ps ρ)) = consList (mins ++ [m]) (consList ps ρ) := by
    intro ρ; simp [consList_append]
  rw [henv, henv]
  refine CtxAgree.of_cons ?_ fun is his => ?_
  · intro i A hA vs hvs
    unfold indicesAt at hA hvs
    rw [Expr.liftCtx_getElem?] at hA
    simp only [Option.map_eq_some_iff] at hA
    obtain ⟨A₀, hA₀, rfl⟩ := hA
    have hl := FitsVals_length M₁ φ₁ hvs
    have hi : i < S.indices.length := (List.getElem?_eq_some_iff.mp hA₀).1
    have hvl : vs.length = S.indices.length - 1 - i := by
      rw [hl, List.length_drop, Expr.length_liftCtx]; omega
    rw [← hvl, interp_liftCtx_liftN_entry M₁ φ₁ ρ₁ _ hos, interp_liftCtx_liftN_entry M₂ φ₂ ρ₂ _ hos]
    exact R₁.R.read₂ R₂.R (hS.2.1 i A₀ hA₀) (by simp only [hvl, hps, nI]; omega)
  · unfold indicesAt at his
    rw [FitsVals_liftCtx_liftN M₁ φ₁ _ _ _ hos, R₁.R.fits_indices hS hps] at his
    rw [R₁.R.read_famVars hS hos hps hp his, R₂.R.read_famVars hS hos hps hp his]

end IndSpec

end Fragment
