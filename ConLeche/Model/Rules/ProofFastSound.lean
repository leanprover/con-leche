module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSound
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.WellDenotedTransport
public import ConLeche.Verify.PropReadInst
import ConLeche.Verify.PropWhen

public section

/-!
# The proof-irrelevance fast arm at the value reading (task #342 L18)

`isProofFast` (`ConLeche/Kernel/PropRead.lean`) answers "a proof" off
head symbols and stored types: through λs, `let`s and applications to a
head — a constant, or a free variable — whose type is a ∀-telescope
whose residual is an application of a type former (a constant, a free
variable, or a binder of the telescope) whose own type, peeled through
identity wrappers (`outParam`, …), ends in a sort that is zero at every
valuation.  `prf_of_isProofFast` is the model justification: such a term is
the point.

The steps, all at the value reading:
* **a type former's application lands in its peeled sort**
  (`typeFormer_mem_univ`): the application is a type, so not the point;
  every prefix of its spine is then a graph ("not pt" source (2)), whose
  domain is the binder's (`AppliesTo.mem`); a wrapper on the way is a
  δ-unfolding and β-steps, identities of the value
  (`redSem_unwrapIdDefs`);
* **a ∀ whose residual's sort is zero is a truth value**
  (`typeSort_mem_univZero`): its fibres are, and a function space of
  truth values is one (`piV_mem_univ`);
* **a member of a truth value is the point**, and so is anything applied
  to it, and an abstraction of it, and a `let` of it.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-! ## Reductions along a spine -/

/-- A reduction of a spine's head is one of the spine. -/
theorem redSem_mkAppN_congr {d : Nat} :
    ∀ (rest : List Expr) {f f' : Expr}, RedSem m φ d f f' →
      RedSem m φ d (Expr.mkAppN f rest) (Expr.mkAppN f' rest)
  | [], _, _, h => h
  | a :: rest, _, _, h => redSem_mkAppN_congr rest (Red.appFn_sound (a := a) h)

/-- A term whose loose bound variables are below `k` is unchanged by
instantiating at `k` or above. -/
theorem instantiate1_of_bounded {v : Expr} :
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
    rw [instantiate1_of_bounded f h.1 hkj, instantiate1_of_bounded a h.2 hkj]
  | .lam t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_of_bounded t h.1 hkj, instantiate1_of_bounded b h.2 (by omega)]
  | .forallE t b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_of_bounded t h.1 hkj, instantiate1_of_bounded b h.2 (by omega)]
  | .letE t x b, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_of_bounded t h.1.1 hkj, instantiate1_of_bounded x h.1.2 hkj,
      instantiate1_of_bounded b h.2 (by omega)]
  | .proj s i e, k, j, h, hkj => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.instantiate1]
    rw [instantiate1_of_bounded e h hkj]

/-- `m` nested λs around a body. -/
inductive IsLams : Nat → Expr → Expr → Prop where
  | zero {e : Expr} : IsLams 0 e e
  | succ {m : Nat} {t b body : Expr} :
      IsLams m b body → IsLams (m + 1) (.lam t b) body

theorem isLams_of_lamProj? :
    ∀ {k₀ : Nat} {e : Expr} {k j : Nat}, ConLeche.lamProj? k₀ e = some (k, j) →
      ∃ n, k = k₀ + n ∧ IsLams n e (.bvar j) ∧ j < k
  | k₀, .lam t b, k, j, h => by
    obtain ⟨n, hk, hl, hj⟩ := isLams_of_lamProj? (k₀ := k₀ + 1) (e := b) h
    exact ⟨n + 1, by omega, .succ hl, hj⟩
  | k₀, .bvar i, k, j, h => by
    simp only [ConLeche.lamProj?] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨0, rfl, .zero, by assumption⟩
    · exact nomatch h
  | _, .fvar _ _, _, _, h | _, .sort _, _, _, h | _, .const _ _, _, _, h
  | _, .app _ _, _, _, h | _, .forallE _ _, _, _, h | _, .letE _ _ _, _, _, h
  | _, .lit _, _, _, h | _, .proj _ _ _, _, _, h => nomatch h

theorem IsLams.instantiate1 {v : Expr} :
    ∀ {n : Nat} {e body : Expr} (k : Nat), IsLams n e body →
      IsLams n (e.instantiate1 v k) (body.instantiate1 v (k + n))
  | _, _, _, k, .zero => by simpa using IsLams.zero
  | _, _, _, k, .succ (m := n) h => by
    simp only [Expr.instantiate1]
    have := IsLams.instantiate1 (v := v) (k + 1) h
    rw [show k + 1 + n = k + (n + 1) by omega] at this
    exact .succ this

theorem isLams_instantiateLevelParams (ks : List Name) (us : List ConLeche.Level) :
    ∀ {n : Nat} {e body : Expr}, IsLams n e body →
      IsLams n (e.instantiateLevelParams ks us) (body.instantiateLevelParams ks us)
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (isLams_instantiateLevelParams ks us h)

/-- **β along a projection telescope**: `(fun x₁ … x_n => x_{n-j}) a₁ … a_n`
reduces to `a_{n-j}` (closed arguments). -/
theorem redSem_lams_bvar {d : Nat} :
    ∀ (args : List Expr) {n j : Nat} {e : Expr}, IsLams n e (.bvar j) →
      args.length = n → j < n → (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      RedSem m φ d (Expr.mkAppN e args) (args.getD (n - 1 - j) e)
  | [], n, j, e, _, hlen, hj, _ => by simp at hlen; omega
  | a :: rest, n, j, e, hl, hlen, hj, hcl => by
    cases hl with
    | zero => simp at hlen
    | @succ n' t b _ hl' =>
      have hβ : RedSem m φ d (Expr.mkAppN (.lam t b) (a :: rest))
          (Expr.mkAppN (b.instantiate1 a) rest) :=
        redSem_mkAppN_congr rest Red.beta_sound
      have hla : a.looseBVarsBounded 0 = true := hcl a List.mem_cons_self
      have hrest : ∀ x ∈ rest, x.looseBVarsBounded 0 = true :=
        fun x hx => hcl x (List.mem_cons_of_mem a hx)
      have hlen' : rest.length = n' := by simpa using hlen
      have hl2 := IsLams.instantiate1 (v := a) 0 hl'
      simp only [Nat.zero_add, Expr.instantiate1] at hl2
      by_cases hjn : j = n'
      · -- the projected variable is the first argument: the remaining
        -- β-steps leave the closed argument alone
        subst hjn
        rw [ite_eq_left rfl] at hl2
        refine Red.trans_sound hβ ?_
        rw [show j + 1 - 1 - j = 0 by omega]
        exact redSem_lams_closed rest hl2 hlen' hla hrest
      · rw [ite_eq_right hjn, ite_eq_right (by omega)] at hl2
        have := redSem_lams_bvar (d := d) rest hl2 hlen' (by omega) hrest
        refine Red.trans_sound hβ ?_
        rw [show n' + 1 - 1 - j = (n' - 1 - j) + 1 by omega]
        simp only [List.getD_cons_succ]
        have hi : n' - 1 - j < rest.length := by omega
        rw [show rest.getD (n' - 1 - j) (Expr.lam t b) = rest.getD (n' - 1 - j)
            (b.instantiate1 a) by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]]
        exact this
where
  redSem_lams_closed : ∀ (args : List Expr) {n : Nat} {e c : Expr}, IsLams n e c →
      args.length = n → c.looseBVarsBounded 0 = true →
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      RedSem m φ d (Expr.mkAppN e args) c
    | [], n, e, c, hl, hlen, _, _ => by
      simp at hlen; subst hlen
      cases hl
      exact Red.refl_sound
    | a :: rest, n, e, c, hl, hlen, hc, hcl => by
      cases hl with
      | zero => simp at hlen
      | @succ n' t b _ hl' =>
        have hβ : RedSem m φ d (Expr.mkAppN (.lam t b) (a :: rest))
            (Expr.mkAppN (b.instantiate1 a) rest) :=
          redSem_mkAppN_congr rest Red.beta_sound
        have hl2 := IsLams.instantiate1 (v := a) 0 hl'
        rw [instantiate1_of_bounded c hc (Nat.zero_le _)] at hl2
        exact Red.trans_sound hβ (redSem_lams_closed rest hl2 (by simpa using hlen) hc
          (fun x hx => hcl x (List.mem_cons_of_mem a hx)))

/-- **An identity wrapper's unfolding is a reduction** (δ, then the
wrapper's β-steps), so it keeps the value of a term that is not the
point (`RedSem`). -/
theorem redSem_unwrapIdDefs (hin : RulesInputs V m φ) {d : Nat} :
    ∀ (fuel : Nat) (e : Expr),
      RedSem m φ d e (ConLeche.unwrapIdDefs env.find? fuel e) := by
  intro fuel
  induction fuel with
  | zero => intro e; exact Red.refl_sound
  | succ fuel ih =>
    intro e
    simp only [ConLeche.unwrapIdDefs]
    split
    case h_2 => exact Red.refl_sound
    rename_i c us hfn
    split
    case h_2 => exact Red.refl_sound
    rename_i cv v hint hfc
    split
    case h_2 => exact Red.refl_sound
    rename_i k j hlp
    split
    case isFalse => exact Red.refl_sound
    rename_i hlen
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlen
    refine Red.trans_sound ?_ (ih _)
    -- the δ-unfolding and the β-steps, at a term that reads
    intro hf Δa ea hC hea
    have hea' := hea
    rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp e).symm, hfn] at hea'
    obtain ⟨fa, vs, hfa, -, -⟩ := denote_mkAppN_inv hea'
    obtain ⟨hlv, -⟩ := denote_const_arityK hfc hfa
    have hunf : ConLeche.unfoldDefinition env e = some (Expr.mkAppN
        (v.instantiateLevelParams cv.levelParams us) e.getAppArgs) := by
      simp only [ConLeche.unfoldDefinition, hfn, hfc]
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at hlv
      rw [ite_eq_left hlv]
    obtain ⟨n, hn, hl, hj⟩ := isLams_of_lamProj? hlp
    simp only [Nat.zero_add] at hn
    subst hn
    have hl' := isLams_instantiateLevelParams cv.levelParams us hl
    have hcl : ∀ a ∈ e.getAppArgs, a.looseBVarsBounded 0 = true :=
      ConLeche.looseBVarsBounded_getAppArgs hf.2.1
    have hchain := redSem_lams_bvar (m := m) (φ := φ) (d := d) e.getAppArgs hl'
      hlen.2 hj hcl
    have hi : k - 1 - j < e.getAppArgs.length := by omega
    rw [show e.getAppArgs.getD (k - 1 - j) (v.instantiateLevelParams cv.levelParams us)
        = e.getAppArgs.getD (k - 1 - j) e by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]] at hchain
    exact Red.trans_sound (Red.delta_sound hin hunf) hchain hf hC hea

/-- An instantiated ∀-body's frame, context discipline, reading and
leaves, from the ∀'s and the argument's. -/
theorem forallE_inst_facts {d : Nat} {Δa : List Term} {A B x : Expr}
    {Ba xa : Term} {ρ : Nat → V}
    (hf : Frame d (.forallE A B)) (hC : CtxOkS m φ d Δa (.forallE A B))
    (hBa : denote m.acval env φ (d + 1) (B.instantiate1 (.fvar d A)) = some Ba)
    (hfx : Frame d x) (hCx : CtxOkS m φ d Δa x)
    (hxa : denote m.acval env φ d x = some xa) :
    Frame d (B.instantiate1 x) ∧ CtxOkS m φ d Δa (B.instantiate1 x) ∧
      denote m.acval env φ d (B.instantiate1 x) = some (Ba.inst xa) ∧
      (LeavesGr m φ d (.forallE A B) ρ → LeavesGr m φ d x ρ →
        LeavesGr m φ d (B.instantiate1 x) ρ) := by
  obtain ⟨hwty, hbty, hLbty⟩ := hf
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d A ∧ Expr.WScoped d B := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨-, hbodyb⟩ :
      A.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 B = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  obtain ⟨hwa, hba, hLa⟩ := hfx
  have hsubBody : ∀ l ∈ (B.instantiate1 x).fvarLeaves,
      l ∈ (Expr.forallE A B).fvarLeaves ∨ l ∈ x.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 B 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  refine ⟨⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
      ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, fun l hl => ?_⟩,
    ⟨hC.1, fun l hl => ?_⟩, ?_, fun hLT hLx l hl => ?_⟩
  · rcases hsubBody l hl with hl' | hl'
    · exact hLbty l hl'
    · exact hLa l hl'
  · rcases hsubBody l hl with hl' | hl'
    · exact hC.2 l hl'
    · exact hCx.2 l hl'
  · rw [denote_beta m.acval_closed (acval_inst_self m)
      (ty := A) hbodyw.fvarsBelow hwa hba hxa 0, hBa]
    rfl
  · rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLx l hl'

/-- **A type former's application lands in its peeled sort**: the
application is not the point, so every prefix of its spine is a graph
("not pt" source (2)) whose domain is the binder's (`AppliesTo.mem`), and
an identity wrapper on the way is a reduction (`redSem_unwrapIdDefs`). -/
theorem typeFormer_mem_univ (hin : RulesInputs V m φ) {d : Nat}
    {Δa : List Term} {ρ : Nat → V} (hρ : Sat V Δa ρ) :
    ∀ (args : List Expr) {vs : List Term} {Ty : Expr} {TyA Ha : Term}
      {u0 : ConLeche.Level},
      Frame d Ty → CtxOkS m φ d Δa Ty →
      denote m.acval env φ d Ty = some TyA → LeavesGr m φ d Ty ρ →
      WellDenotedTy V ρ TyA → interp V ρ Ha ∈ˢ interp V ρ TyA →
      (∀ x ∈ args, Frame d x ∧ CtxOkS m φ d Δa x) →
      (∀ x ∈ args, LeavesGr m φ d x ρ) →
      DenoteSpine m.acval env φ d args vs →
      WellDenoted V ρ (Term.mkAppN Ha vs) →
      interp V ρ (Term.mkAppN Ha vs) ≠ pt →
      ConLeche.peelPisW env.find? args.length Ty = some (.sort u0) →
      interp V ρ (Term.mkAppN Ha vs) ∈ˢ (univ (u0.eval φ) : V)
  | [], vs, Ty, TyA, Ha, u0, hf, hC, hTy, hL, hwT, hmem, _, _, hsp, _, _, hpeel => by
    cases hsp
    simp only [List.length_nil, ConLeche.peelPisW] at hpeel
    have hu : ConLeche.unwrapIdDefs env.find? 4 Ty = .sort u0 := Option.some.inj hpeel
    obtain ⟨-, -, TyA', hTyA', hrow⟩ := redSem_unwrapIdDefs (m := m) (φ := φ) (d := d)
      hin 4 Ty hf hC hTy
    rw [hu, denote_sort] at hTyA'
    obtain rfl := Option.some.inj hTyA'
    obtain ⟨-, heq⟩ := hrow ρ hρ hL hwT.1 hwT.ne_pt
    rw [heq, interp_sort] at hmem
    exact hmem
  | x :: xs, vs, Ty, TyA, Ha, u0, hf, hC, hTy, hL, hwT, hmem, hargs, hLargs, hsp,
      hgS, hne, hpeel => by
    cases hsp with | @cons _ xa _ vs' hxa hsp' =>
    simp only [List.length_cons] at hpeel
    rw [ConLeche.peelPisW_succ_eq] at hpeel
    have hW := redSem_unwrapIdDefs (m := m) (φ := φ) (d := d) hin 4 Ty hf hC hTy
    revert hpeel hW
    cases hu : ConLeche.unwrapIdDefs env.find? 4 Ty with
    | forallE A B =>
      intro hpeel hW
      obtain ⟨hfTy', hsubTy', TyA', hTyA', hrow⟩ := hW
      obtain ⟨hwT', heq⟩ := hrow ρ hρ hL hwT.1 hwT.ne_pt
      obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denote_forallE_inv hTyA'
      have hCTy' : CtxOkS m φ d Δa (.forallE A B) := hC.of_subset hsubTy'
      have hLTy' : LeavesGr m φ d (.forallE A B) ρ := hL.of_subset hsubTy'
      have hmem' : interp V ρ Ha ∈ˢ piV (interp V ρ Aa)
          (fun y => interp V (cons y ρ) Ba)
          (interp_hasSigmaPairs_cons ρ (interp V ρ Aa) Ba) := by
        have h2 := hmem
        rw [heq, interp_pi] at h2
        exact h2
      -- the spine is not the point, so its head is a graph
      have hgS' : WellDenoted V ρ (Term.mkAppN (.app Ha xa) vs') := hgS
      have hne' : interp V ρ (Term.mkAppN (.app Ha xa) vs') ≠ pt := hne
      have happ : WellDenoted V ρ (.app Ha xa) := mkAppN_head vs' hgS'
      have hap := happ.app_clause
      have hHne : interp V ρ Ha ≠ pt := by
        intro h0
        exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) vs')
      have hxA : interp V ρ xa ∈ˢ interp V ρ Aa := hap.mem (mem_piSet_of_mem_piV hmem' hHne)
      have hokx : WellDenoted V ρ xa := happ.app_arg
      obtain ⟨hfx, hCx⟩ := hargs x List.mem_cons_self
      obtain ⟨hfB, hCB, hdB, hLB⟩ := forallE_inst_facts (ρ := ρ) hfTy' hCTy' hBa hfx hCx hxa
      have hwB : WellDenotedTy V ρ (Ba.inst xa) :=
        (WellDenotedTy_inst0 hokx).mpr ⟨hwT'.pi_body _ hxA, hwT'.pi_fib _ hxA⟩
      have hmemB : interp V ρ (.app Ha xa) ∈ˢ interp V ρ (Ba.inst xa) := by
        rw [interp_inst0, interp_app]
        exact app_mem_piV hmem' hxA
      exact typeFormer_mem_univ hin hρ xs (Ha := .app Ha xa) hfB hCB hdB
        (hLB hLTy' (hLargs x List.mem_cons_self)) hwB hmemB
        (fun y hy => hargs y (List.mem_cons_of_mem x hy))
        (fun y hy => hLargs y (List.mem_cons_of_mem x hy)) hsp' hgS' hne'
        (ConLeche.peelPisW_sort_instantiate1 env.find? xs.length B 0 hpeel)
    | _ => intro hpeel; exact nomatch hpeel

/-- A free-variable head's facts: its carried type is framed and read,
graded at the valuation, and the variable's value inhabits it (the
context's satisfaction). -/
theorem fvarHead_facts {d : Nat} {Δa : List Term} {a ty : Expr} {k : Nat}
    {ρ : Nat → V} (hfn : a.getAppFn = .fvar k ty) (hf : Frame d a)
    (hC : CtxOkS m φ d Δa a) (hρ : Sat V Δa ρ) (hL : LeavesGr m φ d a ρ) :
    Frame d ty ∧ CtxOkS m φ d Δa ty ∧ LeavesGr m φ d ty ρ ∧
      ∃ tya, denote m.acval env φ d ty = some tya ∧ WellDenotedTy V ρ tya ∧
        interp V ρ (.bvar (d - 1 - k)) ∈ˢ interp V ρ tya := by
  have hleaf : (k, ty) ∈ a.fvarLeaves := mem_fvarLeaves_of_getAppFn hfn
  have hsubty : ∀ l ∈ ty.fvarLeaves, l ∈ a.fvarLeaves := fun l hl =>
    mem_fvarLeaves_of_getAppFn' hfn (mem_fvarLeaves_of_ty hl)
  obtain ⟨hk, -, tya, Aa, hden, hi, hlink⟩ := hC.2 _ hleaf
  have hwh : Expr.WScoped d (Expr.fvar k ty) := by
    rw [← hfn]; exact hf.1.getAppFn
  simp only [Expr.WScoped] at hwh
  refine ⟨⟨hwh.2.mono (by omega), hf.2.2 _ hleaf, fun l hl => hf.2.2 l (hsubty l hl)⟩,
    hC.of_subset hsubty, hL.of_subset hsubty, tya, hden, hL _ hleaf tya hden, ?_⟩
  rw [interp_bvar, hlink ρ hρ]
  exact hρ (d - 1 - k) Aa hi

/-- The type-sort reader at a residual: a constant or free-variable
type former's application, whose type's peeled sort is zero at the
valuation (`typeFormer_mem_univ`). -/
theorem typeSort_head (hin : RulesInputs V m φ) {T : Expr} {d : Nat}
    {Δa : List Term} {TA : Term} {ρ : Nat → V} {pw : ConLeche.PropWhen}
    (h1 : ∀ ty b, T ≠ .forallE ty b) (h2 : ∀ u, T ≠ .sort u)
    (hf : Frame d T) (hC : CtxOkS m φ d Δa T)
    (hTA : denote m.acval env φ d T = some TA) (hρ : Sat V Δa ρ)
    (hL : LeavesGr m φ d T ρ) (hwT : WellDenotedTy V ρ TA)
    (hpw : ConLeche.typeSortPW env.find? T = some pw) (hholds : pw.holds φ = true) :
    interp V ρ TA ∈ˢ (univ 0 : V) := by
  unfold ConLeche.typeSortPW at hpw
  rw [ConLeche.typeSortPWGo_eq_head _ _ _ h1 h2, ConLeche.Expr.numArgs_eq_length] at hpw
  have hspine := hTA
  rw [← ConLeche.Expr.mkAppN_getApp T] at hspine
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denote_mkAppN_inv hspine
  have hframes := frame_spine hf hC
  have hLs := leavesGr_spine hL
  revert hpw hfa
  cases hfn : T.getAppFn with
  | bvar i => intro hpw; simp [ConLeche.headTypePW] at hpw
  | const I vs' =>
    intro hpw hfa
    simp only [ConLeche.headTypePW] at hpw
    revert hpw
    cases hfI : env.find? I with
    | none => intro hpw; exact nomatch hpw
    | some ci =>
      intro hpw
      dsimp only at hpw
      split at hpw
      · next hlen =>
        revert hpw
        cases hres : ConLeche.residualPW (ConLeche.peelPisW env.find? T.getAppArgs.length
            ci.toConstantVal.type) with
        | none => intro hpw; exact nomatch hpw
        | some p =>
          intro hpw
          obtain rfl := Option.some.inj hpw
          obtain ⟨u0, hpeel, rfl⟩ := ConLeche.residualPW_some_inv hres
          obtain ⟨TyA, hTyA, -, hmemI, hnf, hbd⟩ := constTy_pkg hin.const_ty hfI hlen
          obtain ⟨TyA', hTyA', hwTy, -⟩ := hin.const_ty d I ci vs' hfI hlen
          obtain rfl : TyA' = TyA := Option.some.inj (hTyA'.symm.trans (hTyA d))
          rw [denote_const hfI hlen] at hfa
          obtain rfl := Option.some.inj hfa
          have hpeelTy : ConLeche.peelPisW env.find? T.getAppArgs.length
              (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams vs')
              = some (.sort (ConLeche.Level.subst ci.toConstantVal.levelParams vs' u0)) := by
            rw [ConLeche.peelPisW_instantiateLevelParams, hpeel]; rfl
          have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
          have hmem := typeFormer_mem_univ hin hρ T.getAppArgs
            (Frame.of_not_hasFvar hnf hbd) (CtxOkS.of_fvarLeaves_nil hC.1 hnil) (hTyA d)
            (LeavesGr.of_fvarLeaves_nil hnil) (hwTy ρ) (hmemI ρ) hframes hLs hsp hwT.1
            hwT.ne_pt hpeelTy
          have h0 : Level.eval φ (ConLeche.Level.subst ci.toConstantVal.levelParams vs' u0)
              = 0 := by
            rw [← ConLeche.Level.zeronessOf_subst, ConLeche.PropWhen.zeronessOf_sound]
              at hholds
            exact beq_iff_eq.mp hholds
          rw [h0] at hmem
          exact hmem
      · exact nomatch hpw
  | fvar k ty =>
    intro hpw hfa
    simp only [ConLeche.headTypePW] at hpw
    obtain ⟨u0, hpeel, rfl⟩ := ConLeche.residualPW_some_inv hpw
    obtain ⟨hfty, hCty, hLty, tya, htya, hwty, hmemv⟩ :=
      fvarHead_facts hfn hf hC hρ hL
    rw [denote_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    have hmem := typeFormer_mem_univ hin hρ T.getAppArgs hfty hCty htya hLty hwty hmemv
      hframes hLs hsp hwT.1 hwT.ne_pt hpeel
    have h0 : Level.eval φ u0 = 0 := by
      rw [ConLeche.PropWhen.zeronessOf_sound] at hholds
      exact beq_iff_eq.mp hholds
    rw [h0] at hmem
    exact hmem
  | sort _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
    intro hpw; simp [ConLeche.headTypePW] at hpw

/-- **A ∀ whose residual's sort is zero at the valuation is a truth
value**: its fibres are (by recursion through the opened body), a
residual type-former application lands in its zero sort
(`typeFormer_mem_univ`), and a function space of truth values is one. -/
theorem typeSort_mem_univZero (hin : RulesInputs V m φ) :
    ∀ (n : Nat) (T : Expr), T.sizeB < n →
      ∀ {d : Nat} {Δa : List Term} {TA : Term} {ρ : Nat → V}
        {pw : ConLeche.PropWhen},
        Frame d T → CtxOkS m φ d Δa T → denote m.acval env φ d T = some TA →
        Sat V Δa ρ → LeavesGr m φ d T ρ → WellDenotedTy V ρ TA →
        ConLeche.typeSortPW env.find? T = some pw → pw.holds φ = true →
        interp V ρ TA ∈ˢ (univ 0 : V) := by
  intro n
  induction n with
  | zero => intro T h; omega
  | succ n ih =>
    intro T hT d Δa TA ρ pw hf hC hTA hρ hL hwT hpw hholds
    match T, hT, hf, hC, hTA, hL, hpw with
    | .forallE A B, hT, hf, hC, hTA, hL, hpw =>
      obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denote_forallE_inv hTA
      have hpw' := ConLeche.typeSortPW_forallE_open env.find? d hpw
      have hsz : (B.instantiate1 (.fvar d A)).sizeB < n := by
        rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
        simp only [ConLeche.Expr.sizeB] at hT; omega
      have hfib : ∀ x, x ∈ˢ interp V ρ Aa →
          interp V (cons x ρ) Ba ∈ˢ (univ 0 : V) := fun x hx =>
        ih _ hsz (Frame.forallE_open hf (Frame.forallE_ty hf))
          (CtxOkS.openS hC.forallE_ty hC.forallE_body hAa) hBa (Sat_cons V hρ hx)
          (LeavesGr.open hC.forallE_ty hC.forallE_body hL.forallE_ty hL.forallE_body hAa
            hwT.1.pi_dom)
          ⟨hwT.1.pi_body x hx, hwT.1.pi_fib x hx⟩ hpw' hholds
      rw [interp_pi, univ_zero]
      unfold piV
      rw [propN_eq_zero.mpr fun x hx => univ_zero (V := V) ▸ hfib x hx]
      exact piR_zero_mem_univZero
    | .sort u, _, _, _, _, _, hpw =>
      simp only [ConLeche.typeSortPW, ConLeche.typeSortPWGo] at hpw
      obtain rfl := Option.some.inj hpw
      rw [ConLeche.PropWhen.holds_never] at hholds
      exact nomatch hholds
    | .bvar _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .fvar _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .const _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .app _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .lam _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .letE _ _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .lit _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds
    | .proj _ _ _, hT, hf, hC, hTA, hL, hpw =>
      exact typeSort_head hin (by intro _ _ h; cases h) (by intro _ h; cases h) hf hC hTA
        hρ hL hwT hpw hholds

/-- A head the proof reader answers for: a constant or a free variable
whose type the type-sort reader reads as a proposition at the valuation
is the point. -/
theorem prf_head (hin : RulesInputs V m φ) {d : Nat} {Δa : List Term} {a : Expr}
    {aa : Term} {ρ : Nat → V} {pw : ConLeche.PropWhen}
    (hf : Frame d a) (hC : CtxOkS m φ d Δa a)
    (hda : denote m.acval env φ d a = some aa) (hρ : Sat V Δa ρ)
    (hL : LeavesGr m φ d a ρ)
    (hpw : ConLeche.headProofPW env.find? env.findTable? a = some pw) (hprop : pw.isProp = true) :
    interp V ρ aa = pt := by
  have hholds := holds_of_isProp hprop φ
  cases a with
  | const c us =>
    simp only [ConLeche.headProofPW] at hpw
    revert hpw
    cases hfc : env.find? c with
    | none => intro hpw; exact nomatch hpw
    | some ci =>
      intro hpw
      dsimp only at hpw
      split at hpw
      · next hlen =>
        revert hpw
        cases hts : ConLeche.typeSortPW env.find? ci.toConstantVal.type with
        | none => intro hpw; exact nomatch hpw
        | some pw0 =>
          intro hpw
          obtain rfl := Option.some.inj hpw
          have hts' := ConLeche.typeSortPW_instantiateLevelParams m.wf
            ci.toConstantVal.levelParams us hts
          obtain ⟨TyA, hTyA, -, hmemI, hnf, hbd⟩ := constTy_pkg hin.const_ty hfc hlen
          obtain ⟨TyA', hTyA', hwTy, -⟩ := hin.const_ty d c ci us hfc hlen
          obtain rfl : TyA' = TyA := Option.some.inj (hTyA'.symm.trans (hTyA d))
          rw [denote_const hfc hlen] at hda
          obtain rfl := Option.some.inj hda
          have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
          have huniv := typeSort_mem_univZero hin _ _ (Nat.lt_succ_self _)
            (Frame.of_not_hasFvar hnf hbd) (CtxOkS.of_fvarLeaves_nil hC.1 hnil) (hTyA d) hρ
            (LeavesGr.of_fvarLeaves_nil hnil) (hwTy ρ) hts' hholds
          exact mem_univ_zero huniv (hmemI ρ)
      · exact nomatch hpw
  | fvar k ty =>
    simp only [ConLeche.headProofPW] at hpw
    obtain ⟨hfty, hCty, hLty, tya, htya, hwty, hmemv⟩ :=
      fvarHead_facts (a := .fvar k ty) rfl hf hC hρ hL
    have huniv := typeSort_mem_univZero hin _ _ (Nat.lt_succ_self _) hfty hCty htya hρ
      hLty hwty hpw hholds
    rw [denote_fvar] at hda
    obtain rfl := Option.some.inj hda
    exact mem_univ_zero huniv hmemv
  | sort _ | forallE _ _ | lit _ =>
    simp only [ConLeche.headProofPW] at hpw
    obtain rfl := Option.some.inj hpw
    simp at hprop
  | proj sn i e =>
    simp only [ConLeche.headProofPW] at hpw
    revert hpw
    split
    · split
      · split
        · next pw' _ =>
          intro hpw
          split at hpw
          · next hnev =>
            obtain rfl := Option.some.inj hpw
            rw [ConLeche.PropWhen.isNever_iff.mp hnev] at hprop
            simp at hprop
          · exact nomatch hpw
        · intro hpw; exact nomatch hpw
      · intro hpw; exact nomatch hpw
    · intro hpw; exact nomatch hpw
  | bvar _ | app _ _ | lam _ _ | letE _ _ _ =>
    simp [ConLeche.headProofPW] at hpw

/-- **A term whose stored data say "proof" is the point**, by recursion
through its λs (an abstraction of the point), `let`s (the ζ-reduct) and
applications (the point applied) to its head (`prf_head`). -/
theorem prf_core (hin : RulesInputs V m φ) :
    ∀ (n : Nat) (a : Expr), a.proofDepth < n →
      ∀ {d : Nat} {Δa : List Term} {aa : Term} {ρ : Nat → V}
        {pw : ConLeche.PropWhen},
        Frame d a → CtxOkS m φ d Δa a → denote m.acval env φ d a = some aa →
        Sat V Δa ρ → LeavesGr m φ d a ρ → WellDenoted V ρ aa →
        ConLeche.proofPW env.find? env.findTable? a = some pw → pw.isProp = true →
        interp V ρ aa = pt := by
  intro n
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a hn d Δa aa ρ pw hf hC hda hρ hL hwa hpw hprop
    match a, hn, hf, hC, hda, hL, hpw with
    | .lam ty b, hn, hf, hC, hda, hL, hpw =>
      simp only [ConLeche.proofPW] at hpw
      simp only [ConLeche.Expr.proofDepth] at hn
      obtain ⟨tya, ba, htya, hba, rfl⟩ := denote_lam_inv hda
      obtain ⟨hpw', hdep⟩ := ConLeche.proofPW_instantiate1 env.find? env.findTable? (v := .fvar d ty) b 0 hpw
      rw [interp_lam]
      refine lamV_eq_pt fun x hx => ?_
      exact ih _ (by omega) (Frame.lam_open hf (Frame.lam_ty hf))
        (CtxOkS.openS hC.lam_ty hC.lam_body htya) hba (Sat_cons V hρ hx)
        (LeavesGr.open hC.lam_ty hC.lam_body hL.lam_ty hL.lam_body htya hwa.lam_dom)
        (hwa.lam_body x hx) hpw' hprop
    | .letE ty v b, hn, hf, hC, hda, hL, hpw =>
      simp only [ConLeche.proofPW] at hpw
      simp only [ConLeche.Expr.proofDepth] at hn
      obtain ⟨-, va, ba, -, hva, hba, rfl⟩ := denote_letE_inv hda
      obtain ⟨hfr', hsub, hred⟩ := zeta_syntax hf hva hba
      obtain ⟨hpw', hdep⟩ := ConLeche.proofPW_instantiate1 env.find? env.findTable? (v := v) b 0 hpw
      have hgv : WellDenoted V ρ va := hwa.letE_val
      rw [interp_zeta]
      exact ih _ (by omega) hfr' (hC.of_subset hsub) hred hρ (hL.of_subset hsub)
        ((WellDenoted_zeta _ hgv).mp hwa) hpw' hprop
    | .app f x, hn, hf, hC, hda, hL, hpw =>
      simp only [ConLeche.proofPW] at hpw
      simp only [ConLeche.Expr.proofDepth] at hn
      obtain ⟨fa, xa, hfa, -, rfl⟩ := denote_app_inv hda
      rw [interp_app, ih f (by omega) hf.app_fn hC.app_fn hfa hρ hL.app_fn hwa.app_fn hpw
        hprop, app_pt]
    | .const c us, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .fvar k ty, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .sort u, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .forallE t b, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .lit l, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .proj sn i e, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop
    | .bvar i, _, hf, hC, hda, hL, hpw =>
      exact prf_head hin hf hC hda hρ hL hpw hprop

/-- **A term whose stored data say "proof" is the point** — the
`isProofFast` yes-arm's justification (`DefEq.proofFast`). -/
theorem prf_of_isProofFast (hin : RulesInputs V m φ)
    {d : Nat} {a : Expr} {Δa : List Term} {aa : Term}
    (h : ConLeche.isProofFast env.find? env.findTable? a = true) (hfa : Frame d a)
    (hCa : CtxOkS m φ d Δa a)
    (hda : denote m.acval env φ d a = some aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) (hL : LeavesGr m φ d a ρ)
    (hwa : WellDenoted V ρ aa) :
    interp V ρ aa = (pt : V) := by
  obtain ⟨pw, hpw, hprop⟩ := ConLeche.isProofFast_inv env.find? env.findTable? h
  exact prf_core hin _ a (Nat.lt_succ_self _) hfa hCa hda hρ hL hwa hpw hprop

end ConLeche.Model.Rules
