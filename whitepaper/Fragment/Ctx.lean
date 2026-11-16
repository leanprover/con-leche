module

public import Fragment.Tele
public import Fragment.Decl
public import Fragment.Hygiene

@[expose] public section

/-!
# Contexts, semantically

The value-level reading of the generators of `Decl.lean`: a Π-type or
an abstraction over a context (`mkPis`/`mkLams`) denotes a nested
`piV`/`lamV` over the context's domains read under the values so far
(`piCtx`/`lamCtx`), a list of values **fits** a context when each is a
member of its domain under the earlier ones (`FitsVals`), and the
generators' liftings (`atCtx`, `liftCtx`) read under an environment
built from value lists as the unlifted expression under the
environment with the lifted-over values dropped (`interp_atCtx`).

The lemmas are the introduction, elimination and β laws of `piV`/
`lamV` (`Lib.lean`) iterated along a context, the invariant's binder
clauses iterated (`WellDenoted_mkPis`, `mkLams_ok`), and the
correspondence with the value walks of `EnvModel.lean`
(`TeleFitV_mkPis`, `piBodyV_mkPis`).
-/

namespace Fragment
open SetLib

universe u

/-! ## Reading an environment back -/

section ReadEnv

variable {V : Type u}

/-- The first `n` values of an environment, innermost first. -/
def readEnv (n : Nat) (ρ : Nat → V) : List V := (List.range n).map ρ

theorem length_readEnv (n : Nat) (ρ : Nat → V) : (readEnv n ρ).length = n := by
  simp [readEnv]

@[simp] theorem readEnv_zero (ρ : Nat → V) : readEnv 0 ρ = [] := rfl

theorem readEnv_consList {vs : List V} {n : Nat} (h : vs.length = n) (ρ : Nat → V) :
    readEnv n (consList vs ρ) = vs := by
  subst h
  apply List.ext_getElem (by simp [readEnv])
  intro i h1 h2
  simp [readEnv, consList_lt h2]

/-- Shifting over a middle block of pushed values drops it. -/
theorem shiftE_consList_mid {vs ws : List V} {n k : Nat} (hv : vs.length = k) (hw : ws.length = n)
    (ρ : Nat → V) : shiftE n k (consList vs (consList ws ρ)) = consList vs ρ := by
  induction vs generalizing k with
  | nil =>
    subst hv hw
    exact shiftE_consList ws ρ
  | cons v vs ih =>
    subst hv
    rw [List.length_cons, consList_cons, consList_cons, ← cons_shiftE, ih rfl]

/-- A walk along a telescope in two legs. -/
theorem piBodyV_append : ∀ (vs ws : List V) (ρ : Nat → V) (T : Expr),
    piBodyV ρ T (vs ++ ws) = (piBodyV ρ T vs).bind fun p => piBodyV p.2 p.1 ws
  | [], ws, ρ, T => by rw [List.nil_append, piBodyV_nil]; rfl
  | v :: vs, ws, ρ, .pi A B => by
    simp only [List.cons_append, piBodyV]
    exact piBodyV_append vs ws _ _
  | _ :: _, _, _, .bvar _ => rfl
  | _ :: _, _, _, .sort _ => rfl
  | _ :: _, _, _, .const _ _ => rfl
  | _ :: _, _, _, .app _ _ => rfl
  | _ :: _, _, _, .lam _ _ => rfl
  | _ :: _, _, _, .letE _ _ _ => rfl

end ReadEnv

variable {V : Type u} [SetLib V] (M : Name → List Nat → V) (φ : Name → Nat)

/-! ## Function spaces and abstractions over a context -/

/-- A pair of a zip is a pair of the zip of the reversed lists. -/
theorem _root_.List.mem_zip_reverse {α β : Type _} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → ∀ {p : α × β}, p ∈ l₁.zip l₂ → p ∈ l₁.reverse.zip l₂.reverse
  | [], [], _, _, h => h
  | a :: l₁, b :: l₂, hl, p, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.reverse_cons, List.reverse_cons, List.zip_append (by simp [hl])]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ (List.mem_zip_reverse hl h)
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- The function space over a context (innermost first), the body read under
the environment the binders build: what `mkPis` denotes. -/
noncomputable def piCtx : (Nat → V) → List Expr → ((Nat → V) → V) → V
  | ρ, [], F => F ρ
  | ρ, A :: Γ, F => piCtx ρ Γ fun ρ' => piV (interp M φ ρ' A) fun x => F (cons x ρ')

/-- The abstraction over a context: what `mkLams` denotes. -/
noncomputable def lamCtx : (Nat → V) → List Expr → ((Nat → V) → V) → V
  | ρ, [], F => F ρ
  | ρ, A :: Γ, F => lamCtx ρ Γ fun ρ' => lamV (interp M φ ρ' A) fun x => F (cons x ρ')

/-- **Values fitting a context** (both innermost first): each value is
a member of its domain read under the earlier values. -/
def FitsVals : (Nat → V) → List Expr → List V → Prop
  | _, [], [] => True
  | ρ, A :: Γ, v :: vs => FitsVals ρ Γ vs ∧ v ∈ˢ interp M φ (consList vs ρ) A
  | _, _, _ => False

/-- The domains of a context are well-denoted types under every
fitting prefix. -/
def CtxWD : (Nat → V) → List Expr → Prop
  | _, [] => True
  | ρ, A :: Γ => CtxWD ρ Γ ∧ ∀ vs, FitsVals M φ ρ Γ vs →
      WellDenoted M φ (consList vs ρ) A ∧ IsTy (interp M φ (consList vs ρ) A)

@[simp] theorem piCtx_nil (ρ : Nat → V) (F : (Nat → V) → V) : piCtx M φ ρ [] F = F ρ := rfl
@[simp] theorem piCtx_cons (ρ : Nat → V) (A : Expr) (Γ : List Expr) (F : (Nat → V) → V) :
    piCtx M φ ρ (A :: Γ) F =
      piCtx M φ ρ Γ fun ρ' => piV (interp M φ ρ' A) fun x => F (cons x ρ') := rfl
@[simp] theorem lamCtx_nil (ρ : Nat → V) (F : (Nat → V) → V) : lamCtx M φ ρ [] F = F ρ := rfl
@[simp] theorem lamCtx_cons (ρ : Nat → V) (A : Expr) (Γ : List Expr) (F : (Nat → V) → V) :
    lamCtx M φ ρ (A :: Γ) F =
      lamCtx M φ ρ Γ fun ρ' => lamV (interp M φ ρ' A) fun x => F (cons x ρ') := rfl

@[simp] theorem FitsVals_nil_nil (ρ : Nat → V) : FitsVals M φ ρ [] [] = True := rfl
@[simp] theorem FitsVals_nil_cons (ρ : Nat → V) (v : V) (vs : List V) :
    FitsVals M φ ρ [] (v :: vs) = False := rfl
@[simp] theorem FitsVals_cons_nil (ρ : Nat → V) (A : Expr) (Γ : List Expr) :
    FitsVals M φ ρ (A :: Γ) [] = False := rfl
theorem FitsVals_cons (ρ : Nat → V) (A : Expr) (Γ : List Expr) (v : V) (vs : List V) :
    FitsVals M φ ρ (A :: Γ) (v :: vs) =
      (FitsVals M φ ρ Γ vs ∧ v ∈ˢ interp M φ (consList vs ρ) A) := rfl
@[simp] theorem CtxWD_nil (ρ : Nat → V) : CtxWD M φ ρ [] = True := rfl
theorem CtxWD_cons (ρ : Nat → V) (A : Expr) (Γ : List Expr) :
    CtxWD M φ ρ (A :: Γ) =
      (CtxWD M φ ρ Γ ∧ ∀ vs, FitsVals M φ ρ Γ vs →
        WellDenoted M φ (consList vs ρ) A ∧ IsTy (interp M φ (consList vs ρ) A)) := rfl

/-- The domains of a context are types under every fitting prefix (the
type half of `CtxWD`). -/
def CtxTy : (Nat → V) → List Expr → Prop
  | _, [] => True
  | ρ, A :: Γ => CtxTy ρ Γ ∧ ∀ vs, FitsVals M φ ρ Γ vs → IsTy (interp M φ (consList vs ρ) A)

@[simp] theorem CtxTy_nil (ρ : Nat → V) : CtxTy M φ ρ [] = True := rfl
theorem CtxTy_cons (ρ : Nat → V) (A : Expr) (Γ : List Expr) :
    CtxTy M φ ρ (A :: Γ) =
      (CtxTy M φ ρ Γ ∧ ∀ vs, FitsVals M φ ρ Γ vs → IsTy (interp M φ (consList vs ρ) A)) := rfl

theorem CtxWD.ty : ∀ {ρ : Nat → V} {Γ : List Expr}, CtxWD M φ ρ Γ → CtxTy M φ ρ Γ
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨CtxWD.ty h.1, fun vs hvs => (h.2 vs hvs).2⟩

/-- **Fitting values compared where neither is the point are equal**:
the two lists fit one context of types, so position by position, under
equal earlier values, the two values lie in one type — whose members
are all the point or none of them (`IsTy.eq_of_ne_pt`). -/
theorem FitsVals_eq_of_cond : ∀ {ρ : Nat → V} {Γ : List Expr} {vs ws : List V},
    CtxTy M φ ρ Γ → FitsVals M φ ρ Γ vs → FitsVals M φ ρ Γ ws →
    (∀ p ∈ vs.zip ws, p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) → vs = ws
  | _, [], [], [], _, _, _, _ => rfl
  | _, A :: Γ, v :: vs, w :: ws, hT, hv, hw, h => by
    have ih := FitsVals_eq_of_cond hT.1 hv.1 hw.1 fun p hp => h p (List.mem_cons_of_mem _ hp)
    subst ih
    rw [(hT.2 vs hv.1).eq_of_ne_pt hv.2 hw.2 (h (v, w) List.mem_cons_self)]
  | _, [], _ :: _, _, _, hv, _, _ => hv.elim
  | _, [], [], _ :: _, _, _, hw, _ => hw.elim
  | _, _ :: _, [], _, _, hv, _, _ => hv.elim
  | _, _ :: _, _ :: _, [], _, _, hw, _ => hw.elim

theorem FitsVals_length : ∀ {ρ : Nat → V} {Γ : List Expr} {vs : List V},
    FitsVals M φ ρ Γ vs → vs.length = Γ.length := by
  intro ρ Γ vs h
  induction Γ generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons v vs => exact h.elim
  | cons A Γ ih =>
    cases vs with
    | nil => exact h.elim
    | cons v vs => simp [ih h.1]

theorem FitsVals_append {ρ : Nat → V} {Γ Δ : List Expr} {vs ws : List V}
    (hv : vs.length = Γ.length) :
    FitsVals M φ ρ (Γ ++ Δ) (vs ++ ws) ↔ FitsVals M φ ρ Δ ws ∧ FitsVals M φ (consList ws ρ) Γ vs := by
  induction Γ generalizing vs with
  | nil =>
    cases vs with
    | nil => simp
    | cons v vs => simp at hv
  | cons A Γ ih =>
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hv
      rw [List.cons_append, List.cons_append, FitsVals_cons, FitsVals_cons, ih hv,
        consList_append, and_assoc]

/-- `mkPis` denotes `piCtx`. -/
theorem interp_mkPis : ∀ (Γ : List Expr) (b : Expr) (ρ : Nat → V),
    interp M φ ρ (Expr.mkPis Γ b) = piCtx M φ ρ Γ fun ρ' => interp M φ ρ' b := by
  intro Γ
  induction Γ with
  | nil => intro b ρ; rfl
  | cons A Γ ih =>
    intro b ρ
    rw [Expr.mkPis_cons, ih, piCtx_cons]
    rfl

/-- `mkLams` denotes `lamCtx`. -/
theorem interp_mkLams : ∀ (Γ : List Expr) (b : Expr) (ρ : Nat → V),
    interp M φ ρ (Expr.mkLams Γ b) = lamCtx M φ ρ Γ fun ρ' => interp M φ ρ' b := by
  intro Γ
  induction Γ with
  | nil => intro b ρ; rfl
  | cons A Γ ih =>
    intro b ρ
    rw [Expr.mkLams_cons, ih, lamCtx_cons]
    rfl

theorem piCtx_congr {ρ : Nat → V} {Γ : List Expr} {F G : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) = G (consList vs ρ)) :
    piCtx M φ ρ Γ F = piCtx M φ ρ Γ G := by
  induction Γ generalizing F G with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    rw [piCtx_cons, piCtx_cons]
    refine ih fun vs hvs => piV_congr fun x hx => ?_
    exact h (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)

theorem lamCtx_congr {ρ : Nat → V} {Γ : List Expr} {F G : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) = G (consList vs ρ)) :
    lamCtx M φ ρ Γ F = lamCtx M φ ρ Γ G := by
  induction Γ generalizing F G with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    rw [lamCtx_cons, lamCtx_cons]
    refine ih fun vs hvs => lamV_congr fun x hx => ?_
    exact h (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)

/-- Introduction: an abstraction whose body lands fibre-wise in the function
space's body, which is a type there, is a member of the function space. -/
theorem lamCtx_mem_piCtx {ρ : Nat → V} {Γ : List Expr} {F G : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) ∈ˢ G (consList vs ρ))
    (hG : ∀ ws, FitsVals M φ ρ Γ ws → IsTy (G (consList ws ρ))) :
    lamCtx M φ ρ Γ F ∈ˢ piCtx M φ ρ Γ G := by
  induction Γ generalizing F G with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    rw [lamCtx_cons, piCtx_cons]
    refine ih (fun vs hvs => lamV_mem (fun x hx => ?_) fun x hx => ?_) fun _ _ => IsTy_piV
    · exact h (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)
    · exact hG (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)

/-- Elimination: a member of the function space applied to fitting values
(outermost first, hence the reversal) lands in the body. -/
theorem appList_mem_of_piCtx {ρ : Nat → V} {Γ : List Expr} {G : (Nat → V) → V} {f : V}
    {vs : List V} (hf : f ∈ˢ piCtx M φ ρ Γ G) (hfit : FitsVals M φ ρ Γ vs) :
    appList f vs.reverse ∈ˢ G (consList vs ρ) := by
  induction Γ generalizing G vs with
  | nil =>
    cases vs with
    | nil => exact hf
    | cons v vs => exact hfit.elim
  | cons A Γ ih =>
    cases vs with
    | nil => exact hfit.elim
    | cons v vs =>
      rw [FitsVals_cons] at hfit
      rw [piCtx_cons] at hf
      rw [List.reverse_cons, appList_append, appList_cons, appList_nil]
      exact app_mem_piV (ih hf hfit.1) hfit.2

/-- **β**: an abstraction applied to fitting values computes its body —
with no premise on the body (`SetLib.app_lamV`). -/
theorem appList_lamCtx {ρ : Nat → V} {Γ : List Expr} {F : (Nat → V) → V}
    {vs : List V} (hfit : FitsVals M φ ρ Γ vs) :
    appList (lamCtx M φ ρ Γ F) vs.reverse = F (consList vs ρ) := by
  induction Γ generalizing F vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons v vs => exact hfit.elim
  | cons A Γ ih =>
    cases vs with
    | nil => exact hfit.elim
    | cons v vs =>
      rw [FitsVals_cons] at hfit
      rw [lamCtx_cons, List.reverse_cons, appList_append, appList_cons, appList_nil,
        ih (F := fun ρ' => lamV (interp M φ ρ' A) fun x => F (cons x ρ')) hfit.1]
      exact app_lamV hfit.2

/-- An abstraction whose body is the point under every fitting
environment is the point. -/
theorem lamCtx_eq_pt {ρ : Nat → V} {Γ : List Expr} {F : (Nat → V) → V}
    (h : ∀ vs, FitsVals M φ ρ Γ vs → F (consList vs ρ) = pt) :
    lamCtx M φ ρ Γ F = pt := by
  induction Γ generalizing F with
  | nil => exact h [] trivial
  | cons A Γ ih =>
    rw [lamCtx_cons]
    exact ih fun vs hvs => lamV_eq_pt fun x hx =>
      h (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)

/-- The function space is in a positive universe when its domains and its
body are. -/
theorem piCtx_mem_univ {ρ : Nat → V} {Γ : List Expr} {G : (Nat → V) → V} {n : Nat}
    (hn : n ≠ 0)
    (hdom : ∀ i A, Γ[i]? = some A → ∀ vs, FitsVals M φ ρ (Γ.drop (i + 1)) vs →
      interp M φ (consList vs ρ) A ∈ˢ (univ n : V))
    (hG : ∀ vs, FitsVals M φ ρ Γ vs → G (consList vs ρ) ∈ˢ (univ n : V)) :
    piCtx M φ ρ Γ G ∈ˢ (univ n : V) := by
  induction Γ generalizing G with
  | nil => exact hG [] trivial
  | cons A Γ ih =>
    rw [piCtx_cons]
    refine ih (fun i B hB vs hvs => hdom (i + 1) B hB vs hvs) fun vs hvs => ?_
    unfold piV
    cases propB (interp M φ (consList vs ρ) A) (fun x => G (cons x (consList vs ρ))) with
    | true =>
      exact univ_mono (Nat.zero_le n) piR_true_mem_univ_zero
    | false =>
      exact piR_false_mem_univ hn (hdom 0 A rfl vs hvs) fun x hx =>
        hG (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)

/-- **The invariant of a Π-type over a context**: the domains are
well-denoted types under fitting prefixes, the body is well-denoted
under fitting values, and a type there (which says something only when
there IS a binder: at the empty context the Π-type is the bare
body). -/
theorem WellDenoted_mkPis (Γ : List Expr) (b : Expr) (ρ : Nat → V) :
    WellDenoted M φ ρ (Expr.mkPis Γ b) ↔
      CtxWD M φ ρ Γ ∧ ∀ vs, FitsVals M φ ρ Γ vs →
        WellDenoted M φ (consList vs ρ) b ∧
        (Γ ≠ [] → IsTy (interp M φ (consList vs ρ) b)) := by
  induction Γ generalizing b with
  | nil =>
    constructor
    · intro h
      refine ⟨trivial, fun vs hvs => ?_⟩
      cases vs with
      | nil => exact ⟨h, fun h' => absurd rfl h'⟩
      | cons v vs => exact hvs.elim
    · intro h
      exact (h.2 [] trivial).1
  | cons A Γ ih =>
    rw [Expr.mkPis_cons, ih, CtxWD_cons]
    constructor
    · rintro ⟨hctx, hb⟩
      refine ⟨⟨hctx, fun vs hvs => ?_⟩, fun vs hvs => ?_⟩
      · have := (hb vs hvs).1
        rw [WellDenoted_pi] at this
        exact ⟨this.1, this.2.1⟩
      · cases vs with
        | nil => exact hvs.elim
        | cons v vs =>
          rw [FitsVals_cons] at hvs
          have := (hb vs hvs.1).1
          rw [WellDenoted_pi] at this
          exact ⟨this.2.2.1 v hvs.2, fun _ => this.2.2.2 v hvs.2⟩
    · rintro ⟨⟨hctx, hA⟩, hb⟩
      refine ⟨hctx, fun vs hvs => ⟨?_, fun _ => ?_⟩⟩
      · rw [WellDenoted_pi]
        refine ⟨(hA vs hvs).1, (hA vs hvs).2, fun x hx => ?_, fun x hx => ?_⟩
        · exact (hb (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)).1
        · exact (hb (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)).2
            (List.cons_ne_nil A Γ)
      · rw [interp_pi]
        exact IsTy_piV

/-- **The body of a Π-type denoting a type is not the point**, under
every fitting environment: at the empty context the body is the
Π-type; under a binder it is a type by the invariant. -/
theorem body_ne_pt_of_mkPis {Γ : List Expr} {b : Expr} {ρ : Nat → V}
    (hw : WellDenoted M φ ρ (Expr.mkPis Γ b)) (hT : IsTy (interp M φ ρ (Expr.mkPis Γ b))) :
    ∀ vs, FitsVals M φ ρ Γ vs → interp M φ (consList vs ρ) b ≠ pt := by
  intro vs hvs
  cases Γ with
  | nil =>
    cases vs with
    | nil => simpa using hT.ne_pt
    | cons _ _ => exact hvs.elim
  | cons A Γ => exact ((((WellDenoted_mkPis M φ _ _ _).mp hw).2 vs hvs).2 (List.cons_ne_nil A Γ)).ne_pt

/-- A Π-type over a context denotes a type when its body does, at the
empty context; over a nonempty one it is one outright (`IsTy_piV`). -/
theorem IsTy_interp_mkPis :
    ∀ {Γ : List Expr} {b : Expr} {ρ : Nat → V}, (Γ = [] → IsTy (interp M φ ρ b)) →
      IsTy (interp M φ ρ (Expr.mkPis Γ b))
  | [], _, _, h => h rfl
  | A :: Γ, b, ρ, _ => by
    rw [Expr.mkPis_cons]
    cases Γ with
    | nil => simp only [Expr.mkPis_nil, interp_pi]; exact IsTy_piV
    | cons B Γ' =>
      exact IsTy_interp_mkPis (Γ := B :: Γ') (b := .pi A b) fun h => by cases h

/-- **An abstraction against its Π-type**: if the Π-type is
well-denoted and the body lands in the Π-type's body under every fitting
environment, the abstraction is well-denoted and a member of the
function space (the invariant's λ clause, iterated). -/
theorem mkLams_ok {Γ : List Expr} {b T : Expr} {ρ : Nat → V}
    (hT : WellDenoted M φ ρ (Expr.mkPis Γ T))
    (hb : ∀ vs, FitsVals M φ ρ Γ vs →
      WellDenoted M φ (consList vs ρ) b ∧
      interp M φ (consList vs ρ) b ∈ˢ interp M φ (consList vs ρ) T) :
    WellDenoted M φ ρ (Expr.mkLams Γ b) ∧
      interp M φ ρ (Expr.mkLams Γ b) ∈ˢ interp M φ ρ (Expr.mkPis Γ T) := by
  induction Γ generalizing b T with
  | nil => exact hb [] trivial
  | cons A Γ ih =>
    have hT' := (WellDenoted_mkPis M φ (A :: Γ) T ρ).mp hT
    rw [CtxWD_cons] at hT'
    rw [Expr.mkPis_cons] at hT ⊢
    rw [Expr.mkLams_cons]
    refine ih hT fun vs hvs => ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      exact ⟨(hT'.1.2 vs hvs).1, (hT'.1.2 vs hvs).2, fun x hx =>
        (hb (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)).1⟩
    · rw [interp_lam, interp_pi]
      exact lamV_mem (fun x hx => (hb (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)).2)
        fun x hx => (hT'.2 (x :: vs) ((FitsVals_cons M φ ρ A Γ x vs).symm ▸ ⟨hvs, hx⟩)).2
          (List.cons_ne_nil A Γ)

/-! ## The value walks of `EnvModel.lean` on a generated telescope -/

/-- A longer walk continues into the body under the fitting values. -/
theorem TeleFitV_mkPis_append {Γ : List Expr} {vs ws : List V} {b : Expr}
    {ρ : Nat → V} (h : vs.length = Γ.length) :
    TeleFitV M φ ρ (Expr.mkPis Γ b) (vs ++ ws) ↔
      FitsVals M φ ρ Γ vs.reverse ∧ TeleFitV M φ (consList vs.reverse ρ) b ws := by
  induction Γ generalizing b vs ws with
  | nil =>
    cases vs with
    | nil => simp
    | cons v vs => simp at h
  | cons A Γ ih =>
    rcases List.eq_nil_or_concat vs with rfl | ⟨vs, v, rfl⟩
    · simp at h
    · rw [List.concat_eq_append] at h ⊢
      have h : vs.length = Γ.length := by simp at h; omega
      rw [List.append_assoc, List.singleton_append, Expr.mkPis_cons, ih h, TeleFitV_pi_cons,
        List.reverse_append, List.reverse_singleton, List.singleton_append, FitsVals_cons,
        consList_cons, and_assoc]

/-- A value walk along a Π-type over a context, of exactly the
context's length (values outermost first): the values fit, reversed. -/
theorem TeleFitV_mkPis {Γ : List Expr} {vs : List V} {b : Expr} {ρ : Nat → V}
    (h : vs.length = Γ.length) :
    TeleFitV M φ ρ (Expr.mkPis Γ b) vs ↔ FitsVals M φ ρ Γ vs.reverse := by
  have := TeleFitV_mkPis_append M φ (ws := []) (b := b) (ρ := ρ) h
  rw [List.append_nil] at this
  rw [this]
  exact and_iff_left (TeleFitV_nil M φ _ _)

omit [SetLib V] in
theorem piBodyV_mkPis {Γ : List Expr} {vs : List V} {b : Expr} {ρ : Nat → V}
    (h : vs.length = Γ.length) :
    piBodyV ρ (Expr.mkPis Γ b) vs = some (b, consList vs.reverse ρ) := by
  induction Γ generalizing b vs with
  | nil =>
    cases vs with
    | nil => exact piBodyV_nil ρ b
    | cons v vs => simp at h
  | cons A Γ ih =>
    rcases List.eq_nil_or_concat vs with rfl | ⟨vs, v, rfl⟩
    · simp at h
    · rw [List.concat_eq_append] at h ⊢
      have h : vs.length = Γ.length := by simp at h; omega
      rw [Expr.mkPis_cons, piBodyV_append, ih h, Option.bind_some]
      simp only [piBodyV, piBodyV_nil, List.reverse_append, List.reverse_singleton,
        List.singleton_append, consList_cons]

/-- `hasPis` through `mkPis`, with binders to spare. -/
theorem hasPis_mkPis_add : ∀ (Γ : List Expr) (b : Expr) (n : Nat),
    b.hasPis n = true → (Expr.mkPis Γ b).hasPis (Γ.length + n) = true
  | [], b, n, h => by rw [Expr.mkPis_nil, List.length_nil, Nat.zero_add]; exact h
  | A :: Γ, b, n, h => by
    rw [Expr.mkPis_cons, List.length_cons, Nat.add_right_comm]
    exact hasPis_mkPis_add Γ (.pi A b) (n + 1) (by simpa using h)

theorem hasPis_mkPis (Γ : List Expr) (b : Expr) :
    (Expr.mkPis Γ b).hasPis Γ.length = true :=
  hasPis_mkPis_add Γ b 0 (Expr.hasPis_zero b)

/-! ## The generators' liftings, read -/

/-- The variables `varsAt o n` read as the `n` values sitting `o` up,
outermost first. -/
theorem interp_varsAt (o n : Nat) (ρ : Nat → V) :
    (Expr.varsAt o n).map (interp M φ ρ) = (readEnv n (shiftE o 0 ρ)).reverse := by
  apply List.ext_getElem
  · simp [Expr.varsAt, readEnv]
  · intro i h1 h2
    have hi : i < n := by simpa [Expr.varsAt] using h1
    simp only [Expr.varsAt, readEnv, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range, interp_bvar, shiftE, Nat.not_lt_zero, ite_false]
    congr 1
    omega

/-- **The one lifting, read**: `atCtx nF k l o d e` under the
environment of a minor premise or a rule — `d` own values, `l`
hypotheses, `nF` fields, `o` extras, the parameters — is `e` under its
own: the `d` values, the `k` earlier fields, the parameters. -/
theorem interp_atCtx {nF k l o d : Nat} {ys ihs fs os ps : List V} (ρ : Nat → V) (e : Expr)
    (hy : ys.length = d) (hi : ihs.length = l) (hf : fs.length = nF) (ho : os.length = o)
    (hk : k ≤ nF) :
    interp M φ (consList ys (consList ihs (consList fs (consList os (consList ps ρ)))))
        (Expr.atCtx nF k l o d e)
      = interp M φ (consList ys (consList (fs.drop (nF - k)) (consList ps ρ))) e := by
  rw [Expr.atCtx, interp_liftN, interp_liftN]
  congr 1
  have hnk : nF - k + k = nF := Nat.sub_add_cancel hk
  have h1 : consList ys (consList ihs (consList fs (consList os (consList ps ρ)))) =
      consList (ys ++ ihs ++ fs) (consList os (consList ps ρ)) := by
    simp [consList_append]
  rw [h1, shiftE_consList_mid (by simp [hy, hi, hf]; omega) ho]
  have h2 : ys ++ ihs ++ fs = ys ++ ((ihs ++ fs.take (nF - k)) ++ fs.drop (nF - k)) := by
    simp [List.take_append_drop]
  rw [h2, consList_append, consList_append,
    shiftE_consList_mid hy (by simp [hi, hf, List.length_take]; omega)]

/-- A context lifted entry-wise by `atCtx` (at its own depth) is fitted
by the same values as the unlifted one, under the corresponding
environments. -/
theorem FitsVals_liftCtx_atCtx {nF k l o : Nat} {ihs fs os ps : List V} (ρ : Nat → V)
    (Γ : List Expr) (vs : List V)
    (hi : ihs.length = l) (hf : fs.length = nF) (ho : os.length = o) (hk : k ≤ nF) :
    FitsVals M φ (consList ihs (consList fs (consList os (consList ps ρ))))
        (Expr.liftCtx (fun t T => Expr.atCtx nF k l o t T) Γ) vs ↔
      FitsVals M φ (consList (fs.drop (nF - k)) (consList ps ρ)) Γ vs := by
  induction Γ generalizing vs with
  | nil => cases vs <;> exact Iff.rfl
  | cons A Γ ih =>
    cases vs with
    | nil => exact Iff.rfl
    | cons v vs =>
      rw [Expr.liftCtx_cons, FitsVals_cons, FitsVals_cons, ih]
      by_cases hlen : vs.length = Γ.length
      · rw [interp_atCtx M φ ρ A hlen hi hf ho hk]
      · constructor <;> rintro ⟨h, -⟩ <;> exact absurd (FitsVals_length M φ h) hlen

/-- A context lifted entry-wise by `liftN o` over `o` extras between
the parameters and it. -/
theorem FitsVals_liftCtx_liftN {o : Nat} {os ps : List V} (ρ : Nat → V) (Γ : List Expr)
    (vs : List V) (ho : os.length = o) :
    FitsVals M φ (consList os (consList ps ρ)) (Expr.liftCtx (fun k A => A.liftN o k) Γ) vs ↔
      FitsVals M φ (consList ps ρ) Γ vs := by
  induction Γ generalizing vs with
  | nil => cases vs <;> exact Iff.rfl
  | cons A Γ ih =>
    cases vs with
    | nil => exact Iff.rfl
    | cons v vs =>
      rw [Expr.liftCtx_cons, FitsVals_cons, FitsVals_cons, ih]
      by_cases hlen : vs.length = Γ.length
      · rw [interp_liftN, shiftE_consList_mid hlen ho]
      · constructor <;> rintro ⟨h, -⟩ <;> exact absurd (FitsVals_length M φ h) hlen

theorem interp_liftCtx_liftN_entry {o : Nat} {os ps vs : List V} (ρ : Nat → V) (A : Expr)
    (ho : os.length = o) :
    interp M φ (consList vs (consList os (consList ps ρ))) (A.liftN o vs.length) =
      interp M φ (consList vs (consList ps ρ)) A := by
  rw [interp_liftN, shiftE_consList_mid rfl ho]

end Fragment
