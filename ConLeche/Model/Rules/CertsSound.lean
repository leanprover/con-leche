module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Inst

public section

/-!
# The soundness of the telescope checks and of `DefEqList` (task #305)

The arity-checked telescope (the syntactic arity), the full-grade
certificate `CertsF` (one step per constructor) and `DefEqList`
(pointwise), at one valuation (task #342, L9).  The certificate's slot
comparison is between two types (the argument's inferred type and the
binder's domain), so the conditional `DefEqSem` decides it outright.
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

/-- The checker's arity test (`Expr.peelPis`, no substitution) is
`stripPis`'s. -/
theorem stripPis_isSome_of_peelPis :
    ∀ {n : Nat} {T : Expr}, (Expr.peelPis n T).isSome = true →
      (T.stripPis n).isSome = true
  | 0, _, _ => by simp [ConLeche.Expr.stripPis]
  | n + 1, .forallE _ b, h => by
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_of_peelPis (by simpa [Expr.peelPis] using h)
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => by
    simp [Expr.peelPis] at h

/-- **A graded application that is not the point fits its head's
telescope** (`teleFitPA_of_graded_ne_pt` at the peel's residual): every
prefix of the spine is not the point (`app_pt`), so it is a graph, and
the argument's own application clause puts it in the telescope's domain
(`AppliesTo.mem`). -/
theorem teleFitPA_of_peel_ne_pt {ρ : Nat → V} :
    ∀ (vs : List Term) {T f r : Term},
      Term.peelPis T vs = some r →
      WellDenoted V ρ T → interp V ρ f ∈ˢ interp V ρ T →
      WellDenoted V ρ (Term.mkAppN f vs) →
      interp V ρ (Term.mkAppN f vs) ≠ pt →
      TeleFitPA V ρ T vs r
  | [], T, _, r, hp, _, _, _, _ => by
    obtain rfl : T = r := Option.some.inj hp
    exact .nil
  | x :: xs, .pi A B, f, r, hp, hT, hmem, hg, hne => by
    have hg' : WellDenoted V ρ (Term.mkAppN (.app f x) xs) := hg
    have hne' : interp V ρ (Term.mkAppN (.app f x) xs) ≠ pt := hne
    have happ : WellDenoted V ρ (.app f x) := mkAppN_head xs hg'
    have hap := happ.app_clause
    have hmem' := hmem
    rw [interp_pi] at hmem'
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) xs)
    have hxA : interp V ρ x ∈ˢ interp V ρ A := hap.mem (mem_piSet_of_mem_piV hmem' hfne)
    have hokx : WellDenoted V ρ x := happ.app_arg
    have hBx : WellDenoted V ρ (B.inst x) :=
      (WellDenoted_inst0 _ hokx).mpr (hT.pi_body _ hxA)
    have hmemB : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
      rw [interp_inst0, interp_app]
      exact app_mem_piV hmem' hxA
    exact .cons hxA (teleFitPA_of_peel_ne_pt xs hp hBx hmemB hg' hne')
  | _ :: _, .bvar _, _, _, hp, _, _, _, _ | _ :: _, .sort _, _, _, hp, _, _, _, _
  | _ :: _, .const _ _, _, _, hp, _, _, _, _ | _ :: _, .app _ _, _, _, hp, _, _, _, _
  | _ :: _, .lam _ _, _, _, hp, _, _, _, _ | _ :: _, .letE _ _, _, _, hp, _, _, _, _
  | _ :: _, .eqE _ _, _, _, hp, _, _, _, _ | _ :: _, .fst _, _, _, hp, _, _, _, _
  | _ :: _, .snd _, _, _, hp, _, _, _, _ | _ :: _, .prf, _, _, hp, _, _, _, _ =>
    nomatch hp

/-- **The arity check** (`teleArityOk`): no certificate, the
telescope's syntactic arity only.  An arity-checked walk's spine is the
subject's own; where it is not the point ("not pt" source (2): a
reduction claims nothing of a redex that is the point) it fits its
head's telescope (`teleFitPA_of_peel_ne_pt`), the arity making the
telescope's reading a ∀-chain (`piChain_of_stripPis`). -/
theorem teleArity_sound {d : Nat} {T : Expr} {args : List Expr}
    (harity : (Expr.peelPis args.length T).isSome = true) :
    TeleAritySem m φ d T args := by
  intro _ Δa Ta fa vs _ hTa _ hsp
  have hstrip : (T.stripPis vs.length).isSome = true := by
    rw [← hsp.length]
    exact stripPis_isSome_of_peelPis harity
  obtain ⟨r, hr⟩ := peelPis_of_piChain vs (piChain_of_stripPis vs.length hstrip hTa)
  refine ⟨r, fun ρ _ _ _ hgT hgvs hlic => ?_⟩
  obtain ⟨hgS, hfM, hne⟩ := hlic
  have hfit := teleFitPA_of_peel_ne_pt vs hr hgT hfM hgS hne
  exact ⟨hfit, teleFitPA_rest_graded hfit hgT hgvs⟩

/-! ### The full-grade certificate (task #342 L10, ι's case 3) -/

theorem CertsF.nil_sound {d : Nat} {T : Expr} : CertsFSem m φ d T [] := by
  intro _ Δa Ta vs _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ hgT => ⟨by simp, .nil, hgT⟩⟩

/-- The certified slot: the full-grade inference ESTABLISHES the
argument's grading and its membership in its inferred type, a type
equal to the binder's domain ("not pt" source (1)). -/
theorem CertsF.cert_sound {d : Nat} {ty body arg ta : Expr}
    {rest : List Expr}
    (hta : InferSemFull m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsFSem m φ d (body.instantiate1 arg) rest) :
    CertsFSem m φ d (.forallE ty body) (arg :: rest) := by
  intro hfT Δa Ta vs hCT hTa hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denote m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denote_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody' (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  -- the certificate's two runs, read outside the valuation
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta ⟨hwa, hba, hLa⟩ hCarg haa
  refine ⟨resta, fun ρ hρ hLT hLargs hgT => ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  obtain ⟨hokA, hgtaA, hmem⟩ := hA ρ hρ hLarg
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  -- "not pt" source (1): both sides of the slot comparison are types
  have heq := hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLT.forallE_ty hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  have hmemA : interp V ρ aa ∈ˢ interp V ρ doma := heq ▸ hmem
  have hokBody : WellDenoted V ρ (bodya.inst aa) :=
    (WellDenoted_inst0 _ hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLarg l hl'
  obtain ⟨hgvs', hfit', hgresta⟩ := hfit ρ hρ hLbody
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody
  refine ⟨fun x hx => ?_, .cons hmemA hfit', hgresta⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hokA
  · exact hgvs' x hx'

theorem DefEqList.nil_sound {d : Nat} : DefEqListSem m φ d [] [] := by
  refine ⟨rfl, ?_⟩
  intro Δa asa bsa _ _ hsa hsb _ _ _ _ _ _ p hp
  cases hsa
  cases hsb
  simp at hp

theorem DefEqList.cons_sound {d : Nat} {a b : Expr} {as bs : List Expr}
    (h : DefEqSem m φ d a b) (hs : DefEqListSem m φ d as bs) :
    DefEqListSem m φ d (a :: as) (b :: bs) := by
  refine ⟨by simp [hs.1], ?_⟩
  intro Δa asa bsa hfa hfb hsa hsb ρ hρ hLa hLb hga hgb p hp
  cases hsa with | @cons _ va _ vas hva hsa' =>
  cases hsb with | @cons _ vb _ vbs hvb hsb' =>
  obtain ⟨hfa1, hCa1⟩ := hfa a List.mem_cons_self
  obtain ⟨hfb1, hCb1⟩ := hfb b List.mem_cons_self
  simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact h hfa1 hfb1 hCa1 hCb1 hva hvb ρ hρ (hLa a List.mem_cons_self)
      (hLb b List.mem_cons_self) (hga va List.mem_cons_self)
      (hgb vb List.mem_cons_self)
  · exact hs.2 (fun x hx => hfa x (List.mem_cons_of_mem a hx))
      (fun x hx => hfb x (List.mem_cons_of_mem b hx)) hsa' hsb' ρ hρ
      (fun x hx => hLa x (List.mem_cons_of_mem a hx))
      (fun x hx => hLb x (List.mem_cons_of_mem b hx))
      (fun x hx => hga x (List.mem_cons_of_mem va hx))
      (fun x hx => hgb x (List.mem_cons_of_mem vb hx)) p hp

end ConLeche.Model.Rules
