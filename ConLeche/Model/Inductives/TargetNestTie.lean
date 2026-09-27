module

public import ConLeche.Model.Inductives.TargetNestOwn
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.InstLevels
import ConLeche.Model.Levels
import ConLeche.Model.Inductives.ContSubst

public section

/-!
# The class ↔ node reading tie (PRIMREC / NESTKN-NL, piece (i))

A pair `q` of the recursor route pairs a class with a node at an INSTANCE `I` (levels
`I.us`, parameters `I.ds` at the canonical parameter variables).  The node lemma reads
the node at the instance's FRAME — the instance's parameters read over the prefix's
parameter values (`instFr`, call-independent, `keyFrame_inst`).  This module ties the
class's own reading to it.

* `erasedEq_replaceFVars_vars` — a renaming of variables to variables of the same index
  (the route's `rn`) is invisible up to erasure;
* `seed_frame` — a SEED pair: the class's frame (`keyFrame` of its major's parameters at
  the rule prefix) IS the instance frame, the instance's parameters being the major's
  renamed (`SeedRK`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-- **Renaming variables to variables of the same index is invisible up to erasure.** -/
theorem erasedEq_replaceFVars_vars {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → ∃ ty, b = .fvar i ty) :
    ∀ e : Expr, Expr.ErasedEq (e.replaceFVars f) e := by
  intro e
  induction e with
  | fvar i ty _ =>
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => exact Expr.ErasedEq.rfl _
    | some b =>
      obtain ⟨ty', rfl⟩ := hf i b hi
      simp [Expr.ErasedEq]
  | app a b iha ihb => exact ⟨iha, ihb⟩
  | lam ty b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | forallE ty b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | letE ty v b iht ihv ihb => exact ⟨iht, ihv, ihb⟩
  | proj s i x ih => exact ⟨rfl, rfl, ih⟩
  | _ => exact Expr.ErasedEq.rfl _

section Frame

variable {env : Env} {mT : EnvModel V env} {φ : Name → Nat}

/-- **The instance frame**: the instance's parameters read at the prefix's parameter
count `nP`, over the prefix's parameter values `xs.take nP`. -/
@[expose] noncomputable def instFr (dsaI : List AnnotTerm) (nP : Nat) (xs : List V)
    (ρ : Nat → V) : Nat → V :=
  keyFrame dsaI nP (consList (xs.take nP) ρ)

/-- **A seed's frame is its instance's** (see the module docstring): the major's
parameters `ds` scoped at `nP` (variables below the block's parameters), the instance's
parameters erasure-equal to them renamed by `rn` (variables to variables of the same
index); then the class's frame at any prefix spine is the instance frame. -/
theorem seed_frame {nP rP : Nat} (hle : nP ≤ rP) {ds dsI : List Expr}
    {rn : Expr → Expr} (hrn : ∀ x, Expr.ErasedEq (rn x) x)
    (hdsE : dsI.map Expr.eraseFVarTys = (ds.map rn).map Expr.eraseFVarTys)
    (hws : ∀ x ∈ ds, Expr.WScoped nP x)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval env φ rP ds dsa)
    {dsaI : List AnnotTerm} (hdsaI : DenoteMetaSpine mT.acval env φ nP dsI dsaI)
    {xs : List V} (hxl : xs.length = rP) (ρ : Nat → V) :
    keyFrame dsa rP (consList xs ρ) = instFr dsaI nP xs ρ := by
  -- the instance's parameters read as the major's, at `nP`
  have hspine : DenoteMetaSpine mT.acval env φ nP ds dsaI := by
    have hl : dsI.length = ds.length := by
      have := congrArg List.length hdsE; simpa using this
    suffices ∀ (as bs : List Expr) (vs : List AnnotTerm), as.length = bs.length →
        (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.ErasedEq a b) →
        DenoteMetaSpine mT.acval env φ nP as vs → DenoteMetaSpine mT.acval env φ nP bs vs by
      refine this dsI ds dsaI hl (fun i a b ha hb => ?_) hdsaI
      have h1 : (dsI.map Expr.eraseFVarTys)[i]? = some a.eraseFVarTys := by simp [ha]
      rw [hdsE] at h1
      simp only [List.map_map, List.getElem?_map, hb, Option.map_some, Option.some.injEq,
        Function.comp] at h1
      exact Expr.ErasedEq.trans (Expr.eraseFVarTys_eq_iff.mp h1.symm) (hrn b)
    intro as
    induction as with
    | nil => intro bs vs hl _ h; cases bs <;> simp_all
    | cons a as ih =>
      intro bs vs hl he h
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        cases h with
        | cons ha h' =>
          refine .cons ?_ (ih bs _ (by simpa using hl) (fun i a' b' h1 h2 =>
            he (i + 1) a' b' (by simpa using h1) (by simpa using h2)) h')
          rw [← denoteMeta_erasedEq (he 0 a b rfl rfl) nP]; exact ha
  -- the major's reading at the rule prefix is the lift
  have hl := DenoteMetaSpine.lift (m := mT) (φ := φ) hle hws hspine
  obtain rfl := DenoteMetaSpine.unique hdsa hl
  unfold instFr
  have hk := keyFrame_lift dsaI nP (xs.drop nP) (consList (xs.take nP) ρ)
  rw [show (xs.drop nP).length = rP - nP by simp [hxl]] at hk
  rw [← hk, ← consList_append, List.take_append_drop,
    show nP + (rP - nP) = rP by omega]

end Frame


section Callee

variable {μ : CheckMode}

/-- A read spine, through a renaming invisible up to erasure. -/
theorem DenoteMetaSpine.erased {mT : EnvModel V env} {φ : Name → Nat} {d : Nat}
    {rn : Expr → Expr} (hrn : ∀ x, Expr.ErasedEq (rn x) x) :
    ∀ {ds : List Expr} {dsa : List AnnotTerm}, DenoteMetaSpine mT.acval env φ d ds dsa →
      DenoteMetaSpine mT.acval env φ d (ds.map rn) dsa
  | _, _, .nil => .nil
  | _, _, .cons ha h => .cons (by rw [denoteMeta_erasedEq (hrn _) d]; exact ha)
      (DenoteMetaSpine.erased hrn h)

/-- **A callee's frame is its leaf's read-back parameters' frame** (the match at the rule
prefix, `matchRK` as run): the callee's parameters `ds` renamed (`rn`, invisible up to
erasure) were checked pairwise defeq to the read-back ones `dsL` at the prefix depth `E`;
at every valuation of the prefix's walk context, the key frame of the callee's reading
is the key frame of the read-back reading. -/
theorem callee_frame (hμ : μ.verifiedChecks = true) {mT : EnvModel V env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F E : Nat} {Lh : List Expr} (hL : FvarList E Lh)
    {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ E σ Δ Lh) {cn : Name}
    {ds dsL : List Expr} {rn : Expr → Expr} (hrn : ∀ x, Expr.ErasedEq (rn x) x)
    (hp : ConLeche.paramsMismatchRK (ConLeche.fueledOps μ F) env E cn (ds.map rn) dsL = .ok none)
    (hCL : ∀ x ∈ ds.map rn, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    (hLL : ∀ x ∈ dsL, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval env φ E ds dsa) :
    ∃ dsLa, dsL.mapM (denoteMeta mT.acval env φ E) = some dsLa ∧
      keyFrame dsa E σ = keyFrame dsLa E σ := by
  obtain ⟨dsa₁, dsa₂, h1, h2, heq⟩ := nestParams_tie hμ hacl hin hL hW hp hCL hLL
  rw [DenoteMetaSpine.mapM_eq (DenoteMetaSpine.erased hrn hdsa)] at h1
  obtain rfl := Option.some.inj h1
  refine ⟨dsa₂, h2, ?_⟩
  unfold keyFrame
  rw [heq]

end Callee


/-! ## The read-back at the instance, read -/

section Rb

/-- The read-back's image of a home variable below the layout's holes (`rbInstRK`'s
substitution, fields excluded). -/
@[expose] def rbImg (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (lay : ConLeche.LayRK) :
    Nat → Option Expr := fun i =>
  let ctx := H.ctx
  let nP := ctx.nP
  let k := ctx.names.length
  let L := lay.L
  let base : Nat → Option Expr := fun i =>
    if i < nP then I.ds[i]?
    else if i < nP + k then some (.const (ctx.names.getD (i - nP) .anonymous) I.us)
    else none
  if i < nP + k then base i
  else if i < nP + k + L.nF then
    (L.fams[i - nP - k]?).map fun (kk, _) => (ConLeche.lvlRK H I kk.expr).replaceFVars base
  else if i < L.hi then
    (L.grp[i - nP - k - L.nF]?).map fun g => .const g (L.lvls.map (ConLeche.lvl1RK H I))
  else none

omit [SetTheory V] in
theorem rbInstRK_eq (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (lay : ConLeche.LayRK)
    (e : Expr) : ConLeche.rbInstRK H I lay [] e = (ConLeche.lvlRK H I e).replaceFVars (rbImg H I lay) := by
  unfold ConLeche.rbInstRK rbImg
  simp only
  congr 1
  funext i
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp

variable {env : Env}

/-- **The read-back at the instance, read** (`denoteMeta_relocRK`'s twin): a term of the
home's layout context (free variables below the layout's holes) reads, read back at the
instance, as its reading at the instance's levels substituted by the images' readings at
the depth `E`. -/
theorem denoteMeta_rbInstRK (mT : EnvModel V env) {H : ConLeche.HomeRK} {I : ConLeche.InstRK}
    {lay : ConLeche.LayRK} {E : Nat} {φ : Name → Nat} {x : Nat → AnnotTerm}
    (hx : ∀ i, i < lay.L.hi → ∃ b, rbImg H I lay i = some b ∧ Expr.WScoped E b ∧
      b.looseBVarsBounded 0 = true ∧ denoteMeta mT.acval env φ E b = some (x i))
    {e : Expr} (he : e.fvarsBelow lay.L.hi) :
    denoteMeta mT.acval env φ E (ConLeche.rbInstRK H I lay [] e)
      = (denoteMeta mT.acval env (Level.substFn φ H.ctx.lps I.us) lay.L.hi e).map
          (AnnotTerm.substAV (substTau lay.L.hi E x) · 0) := by
  rw [rbInstRK_eq]
  let s : Nat → Expr := fun i => (rbImg H I lay i).getD (.sort .zero)
  have hE := ConLeche.Expr.replaceFVars_erasedEq_substFvars (b := lay.L.hi) (D := E)
    (g := rbImg H I lay) (s := s) (fun v hv ty => by
      obtain ⟨b, hb, -⟩ := hx v hv
      simp only [s, hb, Option.getD_some]
      exact ConLeche.Expr.ErasedEq.rfl _)
    (ConLeche.lvlRK H I e) (by
      unfold ConLeche.lvlRK
      split
      · exact he
      · exact fvarsBelow_instantiateLevelParams _ _ he)
  rw [denoteMeta_erasedEq hE E]
  have h := denoteMeta_substFvars (φ := φ) mT (b := lay.L.hi) (D := E) (s := s) (x := x)
    (fun i hi => by
      obtain ⟨b, hb, h1, h2, h3⟩ := hx i hi
      simp only [s, hb, Option.getD_some]
      exact ⟨h1, h2, h3⟩)
    (ConLeche.lvlRK H I e) 0 (by
      unfold ConLeche.lvlRK
      split
      · simpa using he
      · simpa using fvarsBelow_instantiateLevelParams _ _ he)
  simp only [Nat.add_zero] at h
  rw [h, denoteMeta_lvlRK (acvalParamsAt_of_core mT)]

end Rb


section Truth

variable {env : Env}

/-- The read-back images' readings at depth `E` (the instance's parameters, the members'
formers, the families' keys, the own group's formers — the layout's TRUE hole values). -/
@[expose] noncomputable def rbX (mT : EnvModel V env) (φ : Name → Nat) (H : ConLeche.HomeRK)
    (I : ConLeche.InstRK) (lay : ConLeche.LayRK) (E : Nat) : Nat → AnnotTerm := fun i =>
  (denoteMeta mT.acval env φ E ((rbImg H I lay i).getD (.sort .zero))).getD default

/-- **A layout's TRUE valuation at a prefix valuation `σ`** (intrinsic): the home's
parameters at the instance's parameters' values, every hole at its constant's or key's
value (`rbImg`). -/
@[expose] noncomputable def layTruth (mT : EnvModel V env) (φ : Name → Nat) (H : ConLeche.HomeRK)
    (I : ConLeche.InstRK) (lay : ConLeche.LayRK) (E : Nat) (σ : Nat → V) : Nat → V :=
  substE V (substTau lay.L.hi E (rbX mT φ H I lay E)) 0 σ

/-- **The read-back reads as the home reading at the layout's truth.** -/
theorem rbInstRK_interp (mT : EnvModel V env) {H : ConLeche.HomeRK} {I : ConLeche.InstRK}
    {lay : ConLeche.LayRK} {E : Nat} {φ : Name → Nat}
    (hx : ∀ i, i < lay.L.hi → ∃ b, rbImg H I lay i = some b ∧ Expr.WScoped E b ∧
      b.looseBVarsBounded 0 = true ∧ ∃ a, denoteMeta mT.acval env φ E b = some a)
    {e : Expr} (he : e.fvarsBelow lay.L.hi) {A : AnnotTerm}
    (hA : denoteMeta mT.acval env (Level.substFn φ H.ctx.lps I.us) lay.L.hi e = some A)
    (σ : Nat → V) :
    ∃ B, denoteMeta mT.acval env φ E (ConLeche.rbInstRK H I lay [] e) = some B ∧
      interp V σ B = interp V (layTruth mT φ H I lay E σ) A := by
  have h := denoteMeta_rbInstRK mT (φ := φ) (x := rbX mT φ H I lay E) (fun i hi => by
    obtain ⟨b, hb, h1, h2, a, ha⟩ := hx i hi
    refine ⟨b, hb, h1, h2, ?_⟩
    simp [rbX, hb, ha]) he
  rw [hA, Option.map_some] at h
  exact ⟨_, h, by rw [interp_substAV]; rfl⟩

/-- **The callee tie at a call** (the match as run, read): the callee's frame — its
parameters `ds` (read `dsa` at the prefix depth `E`) — is the key frame of the leaf's
parameters `ps` read at the caller layout's TRUE valuation. -/
theorem callee_tie {μ : CheckMode} (hμ : μ.verifiedChecks = true) {mT : EnvModel V env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F E : Nat} {Lh : List Expr} (hL : FvarList E Lh)
    {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ E σ Δ Lh) {cn : Name}
    {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {lay : ConLeche.LayRK}
    (hx : ∀ i, i < lay.L.hi → ∃ b, rbImg H I lay i = some b ∧ Expr.WScoped E b ∧
      b.looseBVarsBounded 0 = true ∧ ∃ a, denoteMeta mT.acval env φ E b = some a)
    {ds ps : List Expr} {rn : Expr → Expr} (hrn : ∀ x, Expr.ErasedEq (rn x) x)
    (hp : ConLeche.paramsMismatchRK (ConLeche.fueledOps μ F) env E cn (ds.map rn)
      (ps.map (ConLeche.rbInstRK H I lay [])) = .ok none)
    (hCL : ∀ x ∈ ds.map rn, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    (hLL : ∀ x ∈ ps.map (ConLeche.rbInstRK H I lay []), ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Lh)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval env φ E ds dsa)
    (hpsb : ∀ x ∈ ps, x.fvarsBelow lay.L.hi) {psa : List AnnotTerm}
    (hpsa : DenoteMetaSpine mT.acval env (Level.substFn φ H.ctx.lps I.us) lay.L.hi ps psa) :
    keyFrame dsa E σ
      = consList (psa.map (interp V (layTruth mT φ H I lay E σ))) (fun j => σ (j + E)) := by
  obtain ⟨dsLa, hL', hkf⟩ := callee_frame hμ hacl hin hL hW hrn hp hCL hLL hdsa
  rw [hkf]
  unfold keyFrame
  congr 1
  -- the read-back's readings, entry by entry
  suffices ∀ (ps : List Expr) (psa dsLa : List AnnotTerm), (∀ x ∈ ps, x.fvarsBelow lay.L.hi) →
      DenoteMetaSpine mT.acval env (Level.substFn φ H.ctx.lps I.us) lay.L.hi ps psa →
      (ps.map (ConLeche.rbInstRK H I lay [])).mapM (denoteMeta mT.acval env φ E) = some dsLa →
      dsLa.map (interp V σ) = psa.map (interp V (layTruth mT φ H I lay E σ)) from
    this ps psa dsLa hpsb hpsa hL'
  intro ps
  induction ps with
  | nil => intro psa dsLa _ h1 h2; cases h1; simp at h2; subst h2; rfl
  | cons x xs ih =>
    intro psa dsLa hb h1 h2
    cases h1 with
    | cons hx1 h1' =>
      obtain ⟨B, hB, hBi⟩ := rbInstRK_interp mT hx (hb x List.mem_cons_self) hx1 σ
      simp only [List.map_cons, List.mapM_cons, hB] at h2
      cases hr : (xs.map (ConLeche.rbInstRK H I lay [])).mapM (denoteMeta mT.acval env φ E) with
      | none => rw [hr] at h2; simp at h2
      | some rs =>
        rw [hr] at h2
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h2
        subst h2
        simp only [List.map_cons, hBi, ih _ rs (fun y hy => hb y (List.mem_cons_of_mem _ hy)) h1' hr]

end Truth

end ConLeche.Model
