import Setlec.SetP.Direct.DirectRecKit2P
import Setlec.SetP.OkPTransport

/-!
# The composite frame (task #175 W4c, P3 module 6, part 10)

The recursor's minor premise is opened by the checker at depth
`nP + 2` — under the minor's own binder — with the field variables
`xFvs`; the terms compared there (the field-domain pins, the minor's
body, the rule's λ-domains) live in a frame that is **not** an opening
of any single type: the recursor's parameters and motive, then the
minor slot, then the fields.  `CompOpenedP` packages that frame — the
minor type's reading lifted to depth `nP + 2` and peeled along `xFvs`
(`Γm`, `Rm`) — with the one thing the claims need of it: the
context-correlation `CtxOkP` for any term over its variables
(`compCtx`), the minor slot's entry `E` free (the minor space's own
identification runs at a padded slot, the rule's law at the real one).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The composite context at the field-`j` frame: the first `j` field
entries above the minor-slot entry `E`, the motive and the parameters. -/
def compCtx (Γm Γr : List AVExpr) (nF : Nat) (E : AVExpr) (j : Nat) : List AVExpr :=
  Γm.drop (nF - j) ++ (E :: Γr.drop 2)

omit [SetTheory V] in
theorem compCtx_length {Γm Γr : List AVExpr} {nP nF : Nat} (hm : Γm.length = nF)
    (hr : Γr.length = nP + 3) {E : AVExpr} {j : Nat} (hj : j ≤ nF) :
    (compCtx Γm Γr nF E j).length = nP + 2 + j := by
  simp [compCtx, hm, hr]; omega

omit [SetTheory V] in
theorem compCtx_drop_fields {Γm Γr : List AVExpr} {nF : Nat} (hm : Γm.length = nF)
    {E : AVExpr} {i j : Nat} (hij : i ≤ j) (hj : j ≤ nF) :
    (compCtx Γm Γr nF E j).drop (j - i) = compCtx Γm Γr nF E i := by
  simp only [compCtx]
  rw [List.drop_append_of_le_length (by simp [hm]; omega), List.drop_drop]
  congr 2
  omega

omit [SetTheory V] in
theorem compCtx_drop_rec {Γm Γr : List AVExpr} {nP nF : Nat} (hm : Γm.length = nF)
    {E : AVExpr} {j : Nat} (hj : j ≤ nF) {idx : Nat} (hidx : idx ≤ nP + 1) :
    (compCtx Γm Γr nF E j).drop (nP + 2 + j - idx) = Γr.drop (nP + 3 - idx) := by
  simp only [compCtx]
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp [hm]; omega), List.nil_append]
  have hlen : (Γm.drop (nF - j)).length = j := by simp [hm]; omega
  rw [hlen, show nP + 2 + j - idx - j = (nP + 1 - idx) + 1 from by omega,
    List.drop_succ_cons, List.drop_drop]
  congr 1; omega

omit [SetTheory V] in
theorem compCtx_getElem?_rec {Γm Γr : List AVExpr} {nP nF : Nat} (hm : Γm.length = nF)
    (hr : Γr.length = nP + 3) {E : AVExpr} {j : Nat} (hj : j ≤ nF)
    {idx : Nat} (hidx : idx ≤ nP) :
    (compCtx Γm Γr nF E j)[nP + 2 + j - 1 - idx]? = some (Γr.getD (nP + 2 - idx) default) := by
  simp only [compCtx]
  have hlen : (Γm.drop (nF - j)).length = j := by simp [hm]; omega
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show nP + 2 + j - 1 - idx - j = (nP - idx) + 1 from by omega, List.getElem?_cons_succ,
    List.getElem?_drop, show 2 + (nP - idx) = nP + 2 - idx from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

omit [SetTheory V] in
theorem compCtx_getElem?_minor {Γm Γr : List AVExpr} {nP nF : Nat} (hm : Γm.length = nF)
    {E : AVExpr} {j : Nat} (hj : j ≤ nF) :
    (compCtx Γm Γr nF E j)[nP + 2 + j - 1 - (nP + 1)]? = some E := by
  simp only [compCtx]
  have hlen : (Γm.drop (nF - j)).length = j := by simp [hm]; omega
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show nP + 2 + j - 1 - (nP + 1) - j = 0 from by omega]
  rfl

omit [SetTheory V] in
theorem compCtx_getElem?_field {Γm Γr : List AVExpr} {nF : Nat} (hm : Γm.length = nF)
    {E : AVExpr} {j : Nat} (hj : j ≤ nF) {i : Nat} (hi : i < j) :
    (compCtx Γm Γr nF E j)[j - 1 - i]? = some (Γm.getD (nF - 1 - i) default) := by
  simp only [compCtx]
  have hlen : (Γm.drop (nF - j)).length = j := by simp [hm]; omega
  rw [List.getElem?_append_left (by rw [hlen]; omega), List.getElem?_drop,
    show nF - j + (j - 1 - i) = nF - 1 - i from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- **The composite frame.** -/
structure CompOpenedP {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (nP nF : Nat) (fvsR xFvs : List Expr) (minBody : Expr) (T2 : AVExpr)
    (Γr Γm : List AVExpr) (Rm : AVExpr) : Prop where
  lenR : Γr.length = nP + 3
  lenX : xFvs.length = nF
  lenM : Γm.length = nF
  /-- the opened tower's reading at depth `nP + 2` peels along the fields -/
  tele : PiTeleP nF T2 Γm Rm
  /-- the minor's body reads to the core at the full depth -/
  body : denoteP m.acval env φ (nP + 2 + nF) minBody = some Rm
  /-- each field variable's annotation reads to its entry at its depth -/
  domsX : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
    denoteP m.acval env φ (nP + 2 + i) (Expr.fvarTypeD x)
      = some (Γm.getD (nF - 1 - i) default)
  /-- the field variables: indexed by position from `nP + 2`, scoped,
  bounded, leaf-bounded, over the parameters, the motive and the
  fields -/
  varX : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
    (∃ nm ty, x = Expr.fvar (nP + 2 + i) nm ty) ∧
    Expr.WScoped (nP + 2 + i) (Expr.fvarTypeD x) ∧
    (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (Expr.fvarTypeD x) ∧
    ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs
  /-- the field entries are graded under the composite frame, at any
  minor-slot entry -/
  okΓm : ∀ (E : AVExpr) (i : Nat), i < nF → ∀ ρ : Nat → V,
    Sat2 V (compCtx Γm Γr nF E i) ρ → AnnotOkP V ρ (Γm.getD (nF - 1 - i) default)
  /-- any term over the frame's variables correlates with the composite
  context at its depth; a term mentioning the minor variable needs the
  real minor entry -/
  ctx : ∀ (E : AVExpr) {j : Nat}, j ≤ nF → ∀ {e : Expr}, Expr.WScoped (nP + 2 + j) e →
    (∀ l ∈ e.fvarLeaves,
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) ∧
      (l.1 = nP + 1 → E = Γr.getD 1 default)) →
    CtxOkP m φ (nP + 2 + j) (compCtx Γm Γr nF E j) e
  /-- the minor's body is scoped over the frame's variables -/
  bodyScoped : Expr.WScoped (nP + 2 + nF) minBody ∧ minBody.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded minBody ∧
    ∀ l ∈ minBody.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs

/-- A leaf of a term over an opening sits at its own position. -/
theorem fvs_getElem?_of_mem {fvs : List Expr} {d : Nat}
    (hidx : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ nm ty, x = Expr.fvar (d + i) nm ty)
    {l : Nat × Name × Expr} (hl : Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) :
    d ≤ l.1 ∧ fvs[l.1 - d]? = some (Expr.fvar l.1 l.2.1 l.2.2) := by
  obtain ⟨p, hp⟩ := List.getElem?_of_mem hl
  obtain ⟨nm, ty, hx⟩ := hidx p _ hp
  obtain ⟨h1, -, -⟩ : l.1 = d + p ∧ l.2.1 = nm ∧ l.2.2 = ty := by
    injection hx with a b c
    exact ⟨a, b, c⟩
  refine ⟨by omega, ?_⟩
  rw [show l.1 - d = p from by omega]
  exact hp

/-- **The composite frame, from the recursor's opening and a tower over
its first `nP + 1` variables opened at depth `nP + 2`** (the minor's
type, or the constructor's residual at the recursor's parameters). -/
theorem compOpenedP_ofTy {m : EnvS2Core V env} {nP nF : Nat} {tyR : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    {tym : Expr} (hw1 : Expr.WScoped (nP + 1) tym) (hb1 : tym.looseBVarsBounded 0 = true)
    (hleafM : ∀ l ∈ tym.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1))
    {T2 : AVExpr} (hread2 : denoteP m.acval env φ (nP + 2) tym = some T2)
    (hokT2 : ∀ (E : AVExpr) (ρ : Nat → V), Sat2 V (E :: Γr.drop 2) ρ → AnnotOkP V ρ T2)
    {xFvs : List Expr} {minBody : Expr}
    (hopX : openPisAtFvars nF tym (nP + 2) = some (xFvs, minBody)) :
    ∃ (Γm : List AVExpr) (Rm : AVExpr),
      CompOpenedP m φ nP nF fvsR xFvs minBody T2 Γr Γm Rm := by
  have hlenR : Γr.length = nP + 3 := hR.len
  have hidxR0 : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x →
      ∃ nm ty, x = Expr.fvar (0 + i) nm ty := fun i x hx => by
    obtain ⟨nm, ty, h⟩ := hidxR i x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  obtain ⟨Γm, Rm, htele, hbody, hdoms⟩ := openPisAtFvars_denotePTele nF hopX hread2
  have hlenX : xFvs.length = nF := openPisAtFvars_length nF hopX
  have hlenM : Γm.length = nF := htele.length
  have hidxX := openPisAtFvars_index nF tym (nP + 2) hopX
  have hwsX := openPisAtFvars_typeWScoped nF hopX (Expr.WScoped.mono (by omega) hw1)
  obtain ⟨hbO, hbX⟩ := openPisAtFvars_bounded nF hopX hb1
  obtain ⟨-, hwO⟩ := openPisAtFvars_WScoped nF tym (nP + 2) hopX
    (Expr.WScoped.mono (by omega) hw1)
  have hleavesX := openPisAtFvars_leaves nF hopX
  -- positions
  have hposR : ∀ l : Nat × Name × Expr, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR →
      fvsR[l.1]? = some (Expr.fvar l.1 l.2.1 l.2.2) := fun l hl => by
    have := (fvs_getElem?_of_mem hidxR0 hl).2
    rwa [Nat.sub_zero] at this
  have hposX : ∀ l : Nat × Name × Expr, Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs →
      nP + 2 ≤ l.1 ∧ xFvs[l.1 - (nP + 2)]? = some (Expr.fvar l.1 l.2.1 l.2.2) :=
    fun l hl => fvs_getElem?_of_mem hidxX hl
  have hbndR : ∀ l : Nat × Name × Expr, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR →
      l.2.2.looseBVarsBounded 0 = true := fun l hl => by
    have := (hR.var l.1 _ (hposR l hl)).2.2.1
    simpa [Expr.fvarTypeD] using this
  have hbndX : ∀ l : Nat × Name × Expr, Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs →
      l.2.2.looseBVarsBounded 0 = true := fun l hl => by
    have := hbX _ hl
    simpa [Expr.fvarTypeD] using this
  -- a leaf reachable from the minor's opening is a recursor variable
  -- below the minor or a field variable
  have hopener : ∀ l, (l ∈ minBody.fvarLeaves ∨ ∃ x ∈ xFvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs := by
    intro l hl
    rcases hleavesX l hl with h | h
    · exact Or.inl (hleafM l h)
    · exact Or.inr h
  have hbndAny : ∀ l : Nat × Name × Expr,
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) →
      l.2.2.looseBVarsBounded 0 = true := by
    intro l hl
    rcases hl with h | h
    · exact hbndR l (List.mem_of_mem_take h)
    · exact hbndX l h
  have hleafOfX : ∀ (y : Expr), y ∈ xFvs → ∀ l ∈ (Expr.fvarTypeD y).fvarLeaves,
      l ∈ y.fvarLeaves := by
    intro y hy l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem hy
    obtain ⟨nm, ty, rfl⟩ := hidxX p y hp
    simp only [Expr.fvarTypeD] at hl
    simp only [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  have htakeUp : ∀ l : Nat × Name × Expr, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    have hq' : q < nP + 1 := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hq'] at hq
    exact List.mem_of_getElem?
      (by rw [List.getElem?_take_of_lt (i := q) (j := nP + 2) (by omega)]; exact hq)
  -- the field entries' gradings, from the minor type's
  have hokΓm : ∀ (E : AVExpr) (i : Nat), i < nF → ∀ ρ : Nat → V,
      Sat2 V (compCtx Γm Γr nF E i) ρ → AnnotOkP V ρ (Γm.getD (nF - 1 - i) default) := by
    intro E
    exact (piTeleP_graded (V := V) htele (Δ₀ := E :: Γr.drop 2) (hokT2 E)).1
  refine ⟨Γm, Rm, hlenR, hlenX, hlenM, htele, hbody, hdoms, ?_, hokΓm, ?_, ?_⟩
  · -- the field variables
    intro i x hx
    have hmem := List.mem_of_getElem? hx
    refine ⟨hidxX i x hx, hwsX i x hx, hbX x hmem, ?_, ?_⟩
    · intro l hl
      exact hbndAny l (hopener l (Or.inr ⟨x, hmem, hleafOfX x hmem l hl⟩))
    · intro l hl
      exact hopener l (Or.inr ⟨x, hmem, hleafOfX x hmem l hl⟩)
  · -- the context correlation
    intro E j hj e hwe hleaf
    refine ⟨compCtx_length hlenM hlenR hj, fun l hl => ?_⟩
    have hlt := Expr.fvarLeaves_lt_of_wscoped hwe l hl
    obtain ⟨hmem, hE⟩ := hleaf l hl
    rcases hmem with hmR | hmX
    · -- a recursor variable (index ≤ nP + 1)
      have hlt2 : l.1 < nP + 2 := by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem hmR
        have hq' : q < nP + 2 := by
          have := (List.getElem?_eq_some_iff.mp hq).1
          simp at this; omega
        rw [List.getElem?_take_of_lt hq'] at hq
        obtain ⟨nm, ty, hx⟩ := hidxR q _ hq
        have : l.1 = q := by injection hx
        omega
      have hp := hposR l (List.mem_of_mem_take hmR)
      obtain ⟨-, hwl, -, -, -⟩ := hR.var l.1 _ hp
      simp only [Expr.fvarTypeD] at hwl
      have hrd := hR.doms l.1 _ hp
      simp only [Expr.fvarTypeD] at hrd
      have hrdD : denoteP m.acval env φ (nP + 2 + j) l.2.2
          = some ((Γr.getD (nP + 2 - l.1) default).liftN (nP + 2 + j - l.1) 0) := by
        rw [denoteP_lift m.acval_closed hwl (nP + 2 + j) (by omega), hrd,
          show nP + 3 - 1 - l.1 = nP + 2 - l.1 from by omega]
        rfl
      refine ⟨hlt, hwl.fvarsBelow, _, Γr.getD (nP + 2 - l.1) default, hrdD, ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge l.1 (nP + 1) with h1 | h1
        · exact compCtx_getElem?_rec hlenM hlenR hj (by omega)
        · obtain h2 : l.1 = nP + 1 := by omega
          rw [h2, compCtx_getElem?_minor hlenM hj, hE h2,
            show nP + 2 - (nP + 1) = 1 from by omega]
      · intro ρ _
        rw [interp2_liftN, shiftE_zero]
        congr 1
        funext i
        congr 1
        omega
      · intro ρ hρ
        refine (AnnotOkP_liftN V _ _ 0 ρ).mpr ?_
        rw [shiftE_zero]
        have hs := Sat2_drop hρ (nP + 2 + j - l.1)
        rw [compCtx_drop_rec hlenM hj (by omega)] at hs
        have := hR.okΓ l.1 (by omega) _ hs
        rw [show nP + 3 - 1 - l.1 = nP + 2 - l.1 from by omega] at this
        exact this
    · -- a field variable
      obtain ⟨hge, hp⟩ := hposX l hmX
      have hi : l.1 - (nP + 2) < j := by omega
      have hwl := hwsX _ _ hp
      simp only [Expr.fvarTypeD] at hwl
      rw [show nP + 2 + (l.1 - (nP + 2)) = l.1 from by omega] at hwl
      have hrd := hdoms _ _ hp
      simp only [Expr.fvarTypeD] at hrd
      rw [show nP + 2 + (l.1 - (nP + 2)) = l.1 from by omega] at hrd
      have hrdD : denoteP m.acval env φ (nP + 2 + j) l.2.2
          = some ((Γm.getD (nF - 1 - (l.1 - (nP + 2))) default).liftN (nP + 2 + j - l.1) 0) := by
        rw [denoteP_lift m.acval_closed hwl (nP + 2 + j) (by omega), hrd]
        rfl
      refine ⟨hlt, hwl.fvarsBelow, _, Γm.getD (nF - 1 - (l.1 - (nP + 2))) default, hrdD, ?_, ?_, ?_⟩
      · rw [show nP + 2 + j - 1 - l.1 = j - 1 - (l.1 - (nP + 2)) from by omega]
        exact compCtx_getElem?_field hlenM hj hi
      · intro ρ _
        rw [interp2_liftN, shiftE_zero]
        congr 1
        funext i
        congr 1
        omega
      · intro ρ hρ
        refine (AnnotOkP_liftN V _ _ 0 ρ).mpr ?_
        rw [shiftE_zero]
        have hs := Sat2_drop hρ (nP + 2 + j - l.1)
        have hdrop : (compCtx Γm Γr nF E j).drop (nP + 2 + j - l.1)
            = compCtx Γm Γr nF E (l.1 - (nP + 2)) := by
          rw [show nP + 2 + j - l.1 = j - (l.1 - (nP + 2)) from by omega]
          exact compCtx_drop_fields hlenM (by omega) hj
        rw [hdrop] at hs
        exact hokΓm E _ (by omega) _ hs
  · -- the body
    refine ⟨hwO, hbO, fun l hl => hbndAny l (hopener l (Or.inl hl)), fun l hl => ?_⟩
    rcases hopener l (Or.inl hl) with h | h
    · exact Or.inl (htakeUp l h)
    · exact Or.inr h

/-- **The composite frame from the minor's type**, its reading one deeper
being the minor entry lifted. -/
theorem compOpenedP_of {m : EnvS2Core V env} {nP nF : Nat} {tyR : Expr}
    {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    {nmm : Name} {tym : Expr} (hmin : fvsR[nP + 1]? = some (.fvar (nP + 1) nmm tym))
    {xFvs : List Expr} {minBody : Expr}
    (hopX : openPisAtFvars nF tym (nP + 2) = some (xFvs, minBody)) :
    ∃ (Γm : List AVExpr) (Rm : AVExpr),
      CompOpenedP m φ nP nF fvsR xFvs minBody ((Γr.getD 1 default).liftN 1 0) Γr Γm Rm := by
  have hidxR0 : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x →
      ∃ nm ty, x = Expr.fvar (0 + i) nm ty := fun i x hx => by
    obtain ⟨nm, ty, h⟩ := hidxR i x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  obtain ⟨-, hw1, hb1, -, hleaf1⟩ := hR.var (nP + 1) _ hmin
  simp only [Expr.fvarTypeD] at hw1 hb1 hleaf1
  have hread1 : denoteP m.acval env φ (nP + 1) tym = some (Γr.getD 1 default) := by
    have := hR.doms (nP + 1) _ hmin
    simp only [Expr.fvarTypeD] at this
    rw [show nP + 3 - 1 - (nP + 1) = 1 from by omega] at this
    exact this
  have hread2 : denoteP m.acval env φ (nP + 2) tym
      = some ((Γr.getD 1 default).liftN 1 0) := by
    rw [denoteP_lift m.acval_closed hw1 (nP + 2) (by omega), hread1,
      show nP + 2 - (nP + 1) = 1 from by omega]
    rfl
  have hleafM : ∀ l ∈ tym.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 1) := by
    intro l hl
    have hlt := Expr.fvarLeaves_lt_of_wscoped hw1 l hl
    have := (fvs_getElem?_of_mem hidxR0 (hleaf1 l hl)).2
    rw [Nat.sub_zero] at this
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact this)
  refine compOpenedP_ofTy hR hidxR hw1 hb1 hleafM hread2 ?_ hopX
  intro E ρ hρ
  have ht := Sat2_tail hρ
  have hok := hR.okΓ (nP + 1) (by omega) _
    (by rw [show nP + 3 - (nP + 1) = 2 from by omega]; exact ht)
  rw [show nP + 3 - 1 - (nP + 1) = 1 from by omega] at hok
  refine (AnnotOkP_liftN V 1 _ 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact hok

end Setlec.Semantics
