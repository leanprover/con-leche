module

public import ConLeche.Model.Inductives.ClassFieldAcc
public import ConLeche.Semantics.Inductives.TeleAcc
public import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Verify.BridgeWfImp

public section

/-!
# A crest's field telescope, accessible with ONE bound: the kit (P2d, DESIGN CLASSCHECK / P2D4)

T4's accessibility (`fieldD_acc`/`classCtorWalk_acc`) makes every field of
an abstracted crest accessible under the earlier ones, each with a bound
reading only its walk output's non-hole positions (`PiAccThenC`).  The
class facts need ONE bound for all valuations of the space: the telescope
bound (`teleBound`) over the walk's NORMAL FORM (whose ordinary fields
read no recursive field, U4).  This file moves the walked fields'
accessibility onto the normal form's fields (`teleAccP_of_piAccThenC`,
the class version of the old walk's `teleAccP_of_piAccThen`), with the
generic pieces re-homed here out of the delete-listed `BlockAccRun`
(`teleSmall_mkPisAV`, `TeleAccP.congr`, `resC_of_resultIdxConst`, U4 on
the opened normal form, `noBVar_or`) and `NestPosAcc`
(`nestOcc_nil_of_leaves`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx ClassInfo)

universe w

/-- No leaf at `q`: no occurrence in `[q, q + 1)`. -/
theorem nestOcc_nil_of_leaves {q : Nat} :
    ∀ (e : Expr), (∀ z ∈ e.fvarLeaves, z.1 ≠ q) → e.nestOcc [] q (q + 1) = false := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl
  | const n _ => intro _; simp [Expr.nestOcc]
  | fvar i ty _ =>
    intro h
    have := h (i, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.nestOcc, decide_eq_false_iff_not]
    omega
  | app f a ihf iha =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨ihf fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      iha fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | lam ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | forallE ty b _ iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff]
    exact ⟨⟨iht fun z hz => h z (by simp [Expr.fvarLeaves, hz]),
      ihv fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩,
      ihb fun z hz => h z (by simp [Expr.fvarLeaves, hz])⟩
  | proj _ _ e ihe =>
    intro h
    simp only [Expr.nestOcc]
    exact ihe fun z hz => h z (by simp [Expr.fvarLeaves, hz])


variable {V : Type w} [SetTheory V]

/-! ## The walked fields' values are small -/

/-- **The walked fields' values are small** at every frame of the
relation: they read like the datum's fields, whose hereditary grading
bounds them. -/
theorem teleSmall_mkPisAV {w : Nat} (hw : w ≠ 0) :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (Δ : List AnnotTerm)
      (R : FrameRel V),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abN.map (·.2.2))) →
      TeleSmall w abD.length R (mkPisAV abD B)
  | [], [], _, _, _, _, _, _ => trivial
  | x :: abD, y :: abN, B, Δ, R, hE, hdom, hok => by
    have hE' := hE
    simp only [List.map_cons] at hE'
    obtain ⟨h0, hrest⟩ := hE'
    refine ⟨fun ρ ρ₀ hR a ha => ?_, ?_⟩
    · have hok0 := hok ρ ρ₀ hR
      simp only [List.map_cons] at hok0
      rw [h0 ρ (hdom ρ ρ₀ hR).1] at ha
      exact (univ_isTGUniverse hw).transitive hok0.1 ha
    · refine teleSmall_mkPisAV hw abD abN B (x.2.2 :: Δ) (R.underBoth x.2.2) hrest
        (underBoth_dom hdom) ?_
      rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
      have hok0 := hok ρ ρ₀ hR
      simp only [List.map_cons] at hok0
      exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
  | [], _ :: _, _, _, _, hE, _, _ => hE.elim
  | _ :: _, [], _, _, _, hE, _, _ => hE.elim


/-! ## The walked accessibility onto the normal form's fields -/

/-- `TeleAccP` reads the bounds from field `l` on only. -/
theorem TeleAccP.congr {w : Nat} {Af Af' : Nat → (Nat → V) → V} :
    ∀ (Fs : List AnnotTerm) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ l', l ≤ l' → l' < l + Fs.length → Af l' = Af' l') → TeleAccP w Af l Q R Fs →
        TeleAccP w Af' l Q R Fs
  | [], _, _, _, _, _ => trivial
  | F :: Fs, l, Q, R, h, ⟨h1, h2, h3, h4⟩ => by
    have hl : Af l = Af' l := h l (Nat.le_refl _) (by simp)
    refine ⟨hl ▸ h1, hl ▸ h2, h3, ?_⟩
    exact TeleAccP.congr Fs (l + 1) (shiftQ Q) (R.underBoth F)
      (fun l' hl' hl'' => h l' (by omega) (by simp at hl'' ⊢; omega)) h4

theorem shiftQ_congr {Q Q' : Nat → Nat → Prop} (h : ∀ i n, Q i n ↔ Q' i n) :
    ∀ i n, shiftQ Q i n ↔ shiftQ Q' i n
  | 0, _ => Iff.rfl
  | i + 1, n => h i n

/-- **The walked fields' accessibility moves onto the normal form's
fields** (the class check's `PiAccThenC`): one bound per field, reading
only its walk output's non-hole positions, and the walk's result fact at
the relation under the normal form's fields. -/
theorem teleAccP_of_piAccThenC {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {cls : List ClassInfo}
    {hi : Nat} {Qf : FrameRel V → AnnotTerm → Prop} :
    ∀ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (d l : Nat) (nds : List Expr)
      (Δ : List AnnotTerm) (R : FrameRel V) (Q : Nat → Nat → Prop),
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      (∀ ρ ρ₀, R ρ ρ₀ → Sat V Δ ρ ∧ Sat V Δ ρ₀) →
      (∀ ρ ρ₀, R ρ ρ₀ → FieldsBound w ρ (abN.map (·.2.2))) →
      (∀ i n, ClassHoleQ ctx cls hi d i n ↔ Q i n) → hi ≤ d →
      PiAccThenC w ctx cls hi Qf abD.length d nds R (mkPisAV abD B) →
      ∃ Af : Nat → (Nat → V) → V, TeleAccP w Af l Q R (abN.map (·.2.2)) ∧
        (∀ (i : Nat) (nd : Expr), i < abD.length → nds[i]? = some nd →
          InvOn (MentP ctx.nP hi (d + i) nd) (Af (l + i))) ∧
        Qf (R.underBothTele (abN.map (·.2.2))) B
  | [], [], B, _, _, _, _, R, _, _, _, _, _, _, hP =>
    ⟨fun _ _ => empty, trivial, fun _ _ h => absurd h (Nat.not_lt_zero _), hP⟩
  | x :: abD, y :: abN, B, d, l, nds, Δ, R, Q, hE, hdom, hok, hQ, hd, hP => by
    have hE' := hE
    simp only [List.map_cons] at hE'
    obtain ⟨h0, hrest⟩ := hE'
    match nds, hP with
    | [], hP => exact hP.elim
    | nd :: nds', ⟨⟨Af0, hacc0, hsz0, hinv0⟩, hP'⟩ =>
      have hUE : R.underBoth x.2.2 = R.underBoth y.2.2 := underBoth_eq_of_eqOn h0 hdom
      have hok' : ∀ σ σ₀, R.underBoth x.2.2 σ σ₀ → FieldsBound w σ (abN.map (·.2.2)) := by
        rintro _ _ ⟨a, ρ, ρ₀, rfl, rfl, hR, ha, -⟩
        have hok0 := hok ρ ρ₀ hR
        simp only [List.map_cons] at hok0
        exact hok0.2 a (h0 ρ (hdom ρ ρ₀ hR).1 ▸ ha)
      have hQ' : ∀ i n, ClassHoleQ ctx cls hi (d + 1) i n ↔ shiftQ Q i n := by
        intro i n
        rw [← shiftQ_classHoleQ hd i n]
        exact shiftQ_congr hQ i n
      obtain ⟨Af', htele', hinv', hQf⟩ :=
        teleAccP_of_piAccThenC hw abD abN B (d + 1) (l + 1) nds' (x.2.2 :: Δ) (R.underBoth x.2.2)
          (shiftQ Q) hrest (underBoth_dom hdom) hok' hQ' (by omega) hP'
      classical
      refine ⟨fun l' => if l' = l then Af0 else Af' l', ?_, ?_, ?_⟩
      · simp only [List.map_cons]
        refine ⟨?_, ?_, fun ρ ρ₀ hR => ?_, ?_⟩
        · simp only
          exact AccOn.of_eqOn (P := Sat V Δ) hdom (fun ρ hρ => (h0 ρ hρ).symm)
            (AccOn.congrQ hQ hacc0)
        · simp only
          exact hsz0
        · have hok0 := hok ρ ρ₀ hR
          simp only [List.map_cons] at hok0
          exact hok0.1
        · rw [← hUE]
          exact TeleAccP.congr _ (l + 1) (shiftQ Q) _
            (fun l' hl' _ => by simp only [if_neg (show l' ≠ l by omega)]) htele'
      · intro i nd' hi hnd
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
          subst hnd
          simp only [Nat.add_zero]
          exact hinv0
        | succ i =>
          simp only [List.getElem?_cons_succ] at hnd
          simp only [if_neg (show l + (i + 1) ≠ l by omega)]
          have := hinv' i nd' (by simpa using hi) hnd
          rwa [show d + 1 + i = d + (i + 1) by omega, show l + 1 + i = l + (i + 1) by omega]
            at this
      · show Qf ((R.underBoth y.2.2).underBothTele (abN.map (·.2.2))) B
        rw [← hUE]
        exact hQf
  | [], _ :: _, _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim
  | _ :: _, [], _, _, _, _, _, _, _, hE, _, _, _, _, _ => hE.elim

/-! ## The result indices -/

/-- **The result indices read alike** at two frames under a spine fitting
the fields at both, from the walk's result fact. -/
theorem resC_of_resultIdxConst {nP : Nat} {R : FrameRel V} {Fs : List AnnotTerm} {h : Nat}
    {ps es : List AnnotTerm} (hps : ps.length = nP)
    (hQ : ResultIdxConst nP (R.underBothTele Fs) (AnnotTerm.mkAppN (.bvar h) (ps ++ es))) :
    ∀ ρ ρ', R ρ ρ' → ∀ fs, SpineFit ρ Fs fs → SpineFit ρ' Fs fs →
      ∀ e ∈ es, interp V (consList fs ρ) e = interp V (consList fs ρ') e := by
  obtain ⟨i, vs, heq, hvs⟩ := hQ
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj heq.symm
  intro ρ ρ' hR fs hf hf' e he
  refine hvs e ?_ _ _ (FrameRel.underBothTele_consList Fs fs hR hf hf')
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append]
  exact he

/-! ## U4 on the opened normal form -/

section Syntax

open ConLeche (openPisAtFvars structUsedLater)

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses — at any base depth. -/
theorem u4_nestOccAt {b nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (b) = some (xs, rest))
    (hW : Expr.WScoped (b) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (b + j) (b + j + 1) = false := by
  obtain ⟨⟨bs, r⟩, hst⟩ := Option.isSome_iff_exists.mp
    (stripPis_of_openPis nF hop (j + 1) (by omega))
  have hfree : r.hasLooseBVar 0 = false := by
    unfold structUsedLater at hU
    rw [Nat.zero_add, hst] at hU
    simpa [Expr.hasLooseBVarB_eq] using hU
  obtain ⟨h1, -⟩ := openPisAtFvars_leaf_free nF j hop hj hst hfree fun z hz => by
    have := Expr.fvarLeaves_lt_of_wscoped hW z hz
    omega
  refine nestOcc_nil_of_leaves _ fun z hz => ?_
  obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF tyN (b) hop l x hx
  exact h1 l hjl _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])

/-- **U4, on the opened normal form**: a later field's domain does not
mention a field no later binder uses. -/
theorem u4_nestOcc {ctx : NestCtx} {nF j l : Nat} {tyN rest : Expr} {xs : List Expr} {x : Expr}
    (hop : openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) tyN) (hU : structUsedLater tyN 0 j = false)
    (hj : j < nF) (hjl : j < l) (hx : xs[l]? = some x) :
    x.fvarTypeD.nestOcc [] (ctx.hiAt 0 + j) (ctx.hiAt 0 + j + 1) = false :=
  u4_nestOccAt hop hW hU hj hjl hx

end Syntax

/-- NoBVar of a disjunction. -/
theorem noBVar_or {P₁ P₂ : Nat → Prop} {e : AnnotTerm} (h₁ : NoBVar P₁ e) (h₂ : NoBVar P₂ e) :
    NoBVar (fun i => P₁ i ∨ P₂ i) e := by
  have := noBVar_exists' (α := Bool) (P := fun b i => if b then P₁ i else P₂ i) (e := e)
    fun b => by cases b <;> simpa
  refine NoBVar.mono (fun i hi => ?_) this
  rcases hi with h | h
  · exact ⟨true, by simpa using h⟩
  · exact ⟨false, by simpa using h⟩

end ConLeche.Model
