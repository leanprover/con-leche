import Setlec.SetP.DirectCtorDataP

/-!
# The constructor's frames (task #175 W4c, P3 module 6, part 4)

`ctorFrames`: from the former's and the constructor's data at the
environment holding the former, the binder-domain pins identify the
two parameter frames (`paramFrames`), and the field-sort runs grade
the field chain at the constructor's parameter frame — `FieldsOkB`
(bounded by the result sort in the graph regime, O5), `FieldsValid`,
and `FieldsBound 0` at a propositional structure with the large
eliminator.  These are the premises the former's real leaf and the
constructor's leaf consume.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- An opened type whose reading is a known peel: the opened record
at the peel's reversed domains. -/
theorem openedP_of_peel {m : EnvS2Core V env} {k : Nat} {e : Expr}
    {fvs : List Expr} {o : Expr} {pps : List (Nat × Nat × AVExpr)} {b : AVExpr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (hread : denoteP m.acval env φ 0 e = some (mkPisAV pps b))
    (hlen : pps.length = k)
    (hok : ∀ ρ : Nat → V, AnnotOkP V ρ (mkPisAV pps b)) :
    OpenedP m φ k e fvs o ((pps.map (·.2.2)).reverse) b := by
  obtain ⟨Γ, R, htele, hO⟩ := openedP_of hop hcl hb hread hok
  have hst := stripPisAV_mkPisAV pps b
  rw [hlen] at hst
  obtain ⟨rfl, rfl⟩ := PiTeleP.unique htele (piTeleP_of_stripPisAV hst)
  exact hO

/-- The field entries of the reversed constructor context are the
peel's field domains. -/
theorem fieldsFrom_eq_drop {ds : List (Nat × Nat × AVExpr)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) :
    fieldsFrom ((ds.map (·.2.2)).reverse) (nP + nF) nP nF 0
      = (ds.drop nP).map (·.2.2) := by
  apply List.ext_getElem
  · simp [fieldsFrom, hlen]
  · intro t h1 h2
    simp only [fieldsFrom, List.getElem_map, List.getElem_range, List.getElem_drop]
    have ht : t < nF := by simpa [fieldsFrom] using h1
    rw [Nat.add_zero, getD_reverse_of_peel hlen (by omega)
      (List.getElem?_eq_getElem (by omega))]

/-- The reversed constructor context above the fields is the reversed
parameter context. -/
theorem drop_fields_eq {ds : List (Nat × Nat × AVExpr)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) (i : Nat) (hi : i ≤ nP) :
    ((ds.map (·.2.2)).reverse).drop (nP + nF - i)
      = (((ds.take nP).map (·.2.2)).reverse).drop (nP - i) := by
  rw [reverse_map_take_drop ds nP, List.drop_append]
  have hl : (((ds.drop nP).map (·.2.2)).reverse).length = nF := by
    simp [hlen]
  rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, hl,
    show nP + nF - i - nF = nP - i from by omega]

/-- The field chain's validity, walked like its grading. -/
theorem fieldsValid_of_frame {Γ : List AVExpr} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (okΓ : ∀ i, i < k → ∀ ρ : Nat → V, Sat2 V (Γ.drop (k - i)) ρ →
      AnnotOkP V ρ (Γ.getD (k - 1 - i) default)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat2 V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat2 V (Γ.drop (k - (nP + j))) ρ →
      FieldsValid ρ (fieldsFrom Γ k nP nF j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    refine ⟨(okΓ (nP + j) (by omega) ρ hρ).2, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat2_cons V hρ ha

/-- The field chain's squash bound, walked like its grading. -/
theorem fieldsBound_of_frame {Γ : List AVExpr} {k nP nF : Nat}
    (hk : k = nP + nF) (hΓ : Γ.length = k)
    (hbnd : ∀ j, j < nF → ∀ ρ : Nat → V, Sat2 V (Γ.drop (k - (nP + j))) ρ →
      interp2 V ρ (Γ.getD (k - 1 - (nP + j)) default) ∈ˢ (univ 0 : V)) :
    ∀ (j : Nat), j ≤ nF → ∀ ρ : Nat → V, Sat2 V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound 0 ρ (fieldsFrom Γ k nP nF j) := by
  suffices ∀ (m j : Nat), nF - j = m → j ≤ nF → ∀ ρ : Nat → V,
      Sat2 V (Γ.drop (k - (nP + j))) ρ →
      FieldsBound 0 ρ (fieldsFrom Γ k nP nF j) from
    fun j => this (nF - j) j rfl
  intro m
  induction m with
  | zero =>
    intro j hm hj ρ hρ
    have hjn : j = nF := by omega
    subst hjn
    simp only [fieldsFrom, Nat.sub_self, List.range_zero, List.map_nil]
    trivial
  | succ m ih =>
    intro j hm hj ρ hρ
    have hlt : j < nF := by omega
    rw [fieldsFrom_succ hlt]
    refine ⟨hbnd j hlt ρ hρ, fun a ha => ?_⟩
    refine ih (j + 1) (by omega) (by omega) (cons a ρ) ?_
    rw [show k - (nP + (j + 1)) = k - (nP + j) - 1 from by omega,
      List.drop_eq_getElem_cons (l := Γ) (i := k - (nP + j) - 1) (by omega)]
    have hG : Γ[k - (nP + j) - 1]'(by omega) = Γ.getD (k - 1 - (nP + j)) default := by
      rw [List.getD, List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1; omega
    rw [hG, show k - (nP + j) - 1 + 1 = k - (nP + j) from by omega]
    exact Sat2_cons V hρ ha

/-! ## The frames -/

/-- **The constructor's frames**: the two parameter frames identified
and the field chain graded at the constructor's, from the data of both
constants at the environment holding the former and the stage's
runs. -/
theorem ctorFrames (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa : ConstantVal} {env₀ envC : Env}
    {sorts : List Level} {caps : IndCaps}
    (hCtor : Setlec.checkDirectCtor (Setlec.fueledOps μ F) env₀ env p cvTa
      = .ok (envC, cvCa, sorts))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    -- the recognition's propositionality datum is the result sort's
    (hProp : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    {ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2)))) := by
  obtain ⟨hccv, -, -, fvsP, crest, tfvs, trest, xFvs, hopC, hopT, hdoms, hopX,
    -, hsorts⟩ := Setlec.checkDirectCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopC hsorts
  have hlenP : fvsP.length = p.nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add p.nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (Setlec.SetR.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := Setlec.checkDirectFieldSorts_inv hsorts
  have hpins := Setlec.checkDirectDomsAt_inv hdoms
  -- the constructor's opening's length
  have hlenX : xFvs.length = p.nF := openPisAtFvars_length _ hopX
  -- the two openings, at one assignment
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      ∀ ρ : Nat → V, Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))) := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    have hT : OpenedP mp.base2 ψ p.nP cvTa.type tfvs trest
        ((pps ψ).map (·.2.2)).reverse (.sort (p.resSort.eval ψ)) :=
      openedP_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
    have hC : OpenedP mp.base2 ψ (p.nP + p.nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP)
        ((ds ψ).map (·.2.2)).reverse (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψ) :=
      openedP_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    -- the identification
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hiff : ∀ ρ : Nat → V, Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ := by
      intro ρ
      have := (hpf p.nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs p.nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    refine ⟨hiff, fun ρ hρ => ?_⟩
    -- the field walks, at the constructor's frame
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = p.nP + p.nF := by
      simp [hlenDs]
    have hρ' : Sat2 V ((((ds ψ).map (·.2.2)).reverse).drop (p.nP + p.nF - (p.nP + 0))) ρ := by
      rw [show p.nP + p.nF - (p.nP + 0) = p.nP + p.nF - p.nP from by omega,
        drop_fields_eq hlenDs p.nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    -- per field: the sort row at its own frame
    have hrow : ∀ j, j < p.nF → ∃ u, sorts[j]? = some u ∧
        (p.isProp = false → Level.leq u p.resSort = some true) ∧
        (p.isProp = true → p.large = true →
          (Level.isEquiv u .zero == some true) = true) ∧
        ∀ ρ : Nat → V,
          Sat2 V ((((ds ψ).map (·.2.2)).reverse).drop (p.nP + p.nF - (p.nP + j))) ρ →
          interp2 V ρ ((((ds ψ).map (·.2.2)).reverse).getD
            (p.nP + p.nF - 1 - (p.nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
      refine ⟨u, hu, hleq, hz, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[p.nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (p.nP + j) fv hfvA
      have hCtx := hC.ctx (i := p.nP + j) (by omega) hws hleaf
      have hread := hC.doms (p.nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := p.nP) (nF := p.nF) hlenDs
    refine ⟨?_, ?_, ?_⟩
    · -- `FieldsOkB`
      rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, -, hmem⟩ := hrow j hj
      by_cases hnp : p.isProp = true
      · -- a propositional structure's result sort is zero everywhere
        exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · rw [← hFsEq]
      exact fieldsValid_of_frame rfl hΓlen hC.okΓ 0 (Nat.zero_le _) ρ hρ'
    · intro hp hl
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, -, hz, hmem⟩ := hrow j hj
      have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hz hp hl)) ψ
      have := hmem ρ hρ
      rwa [h0] at this
  exact ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2⟩

end Setlec.SetR.Interp2
