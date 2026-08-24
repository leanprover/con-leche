import Setlec.Model.TypeChecker
import Setlec.Model.IotaWalk
import Setlec.Model.RuleFold

/-!
# Fold facts for a modeled recursor

`modeled_rule_fold` derives one recursor rule's `RecRulesOk` fold
obligation from the checked `R._model.iota_j` theorem, via the
defeq-based install checks: the fold's value spines are relocated onto
the theorem's own opening variables (`interp_instSeq_fvarFrames` — the
interpretations of instantiated telescope domains are determined by
the argument *values*), the theorem's telescope is walked with
memberships transferred along the kernel's per-binder `isDefEqCore`
facts (`pi_walk`), the theorem's inhabitant is eliminated into the
interpreted equation, the `Eq` collapse turns it into the value
equality between the recursor's spine fold and the interpreted
right-hand side of the checked statement, and the latter is the rule's
own interpretation applied along the spine (the statement's right side
is definitionally the *applied* rule, so no β-fold is needed — the
rule's λ-tower is walked only for the reduct's typing slots,
`lam_walk`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-- A fit's argument spine interprets pointwise to its value spine. -/
theorem TeleFitI.toInterpSpine {V : Type u} [SetTheory V]
    {cval : ConstVal V} {env : Env} {φ : Name → Nat} {d : Nat}
    {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      InterpSpine cval env φ d ρ args vs := by
  intro ty args vs rest h
  induction h with
  | nil => trivial
  | cons hity hiarg hx hfb hwa hba hAa _ ih => exact ⟨hiarg, ih⟩

/-! ## The stage facts of the total rule equality (task #58)

`RecRulesOk`'s per-rule clause is the total λ-equality of the
canonical iota left-hand side tower against the stored rule right-hand
side.  `TowerOk.of_stages` assembles the pointwise tower spec from
*flat stage facts at the canonical list valuations*; this section
derives those facts from the kernel-checked `_model.iota_j` pins:
per stage, the frame annotation and the rule tower's instantiated
binder domain are kernel-definitionally equal (`hdeLam`), so their
interpretations agree — the wf packages on both sides come from
sequential telescope walks over the value prefix. -/

/-- The pointwise membership invariant carried through the tower
stages: each chosen value inhabits its frame annotation's
interpretation at the *prefix* canonical valuation. -/
def FramePref (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (spine : List Expr) (xs : List V) : Prop :=
  ∀ (j : Nat) (v : V) (fv : Expr), xs[j]? = some v →
    spine[j]? = some fv →
    ∃ B, interpExpr V cval env φ j
        (fun i => (xs.take j).getD i SetTheory.empty)
        (Expr.fvarTypeD fv) = some B ∧ v ∈ˢ B

/-- Everything `isDefEqCore_sound` wants of one side. -/
def InterpPkg (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (D : Nat) (ρ : Nat → V) (e : Expr) : Prop :=
  WScoped D e ∧ e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e ∧
  FvarsOk V cval env φ D ρ e ∧ AnnotOk V cval env φ D ρ e ∧
  ∃ P, interpExpr V cval env φ D ρ e = some P

/-- The stage-fact tail: a kernel definitional equality between two
packaged sides at the padded master frame canonicalizes onto the stage
frame — the annotation side's interpretation and truthfulness, and the
(erased-)interpretation of the walk side, agree there. -/
theorem stage_out {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {a b : Expr} {k D : Nat} {xs : List V}
    (hk : xs.length = k) (hkD : k ≤ D)
    (hde : isDefEqCore env₀ F D a b = .ok true)
    (hpa : InterpPkg m₀.val env₀ ψ D
      (fun i => xs.getD i SetTheory.empty) a)
    (hpb : InterpPkg m₀.val env₀ ψ D
      (fun i => xs.getD i SetTheory.empty) b)
    (hwa : WScoped k a) (hwb : WScoped k b) :
    ∃ A, interpExpr V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) a = some A ∧
      (∀ e, Expr.ErasedEq e b → interpExpr V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) e = some A) ∧
      AnnotOk V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) a := by
  obtain ⟨hWa, hba, hLa, hFa, hAa, Pa, hPa⟩ := hpa
  obtain ⟨hWb, hbb, hLb, hFb, hAb, Pb, hPb⟩ := hpb
  have hPab : Pa = Pb :=
    isDefEqCore_sound m₀ F hde hWa hWb hba hbb hLa hLb hFa hFb hAa hAb
      hPa hPb
  subst hk
  have htake : xs.take xs.length = xs := List.take_of_length_le
    (Nat.le_refl _)
  -- canonicalize the annotation side
  have hcanA := interp_getD_canon (cval := m₀.val) (env := env₀)
    (φ := ψ) (e := a) (xs := xs) hwa (Nat.le_refl _) hkD
  rw [htake] at hcanA
  have hcanB := interp_getD_canon (cval := m₀.val) (env := env₀)
    (φ := ψ) (e := b) (xs := xs) hwb (Nat.le_refl _) hkD
  rw [htake] at hcanB
  refine ⟨Pa, by rw [← hcanA]; exact hPa, ?_, ?_⟩
  · intro e hee
    rw [interp_erasedEq hee, ← hcanB, hPb, hPab]
  · have h := annotOk_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := a) (xs := xs) hwa (Nat.le_refl _) hkD hAa
    rwa [htake] at h

/-- The rule-tower side's stage package: walking the rule right-hand
side's λ-tower along the frame prefix packages the current stage's
instantiated binder domain at the padded master frame. -/
theorem stage_pkg_lam {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {D : Nat} {ρ : Nat → V}
    {spine : List Expr} {rhsA lrest ld : Expr} {ldoms : List Expr}
    (hlinst : Expr.instLamsAt spine rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ D (spine.map Expr.fvarTypeD) ldoms)
    {k : Nat} {vs : List V}
    (hk : k < spine.length)
    (hld : ldoms[k]? = some ld)
    (hsp : FvarSpine D ρ (spine.take k) vs)
    (hws : ∀ a ∈ spine.take k, WScoped D a)
    (hΘ : ∀ a ∈ spine.take k, FvarsOk V m₀.val env₀ ψ D ρ a)
    (hLs : ∀ a ∈ spine.take k, Expr.LeavesBounded a)
    (hwsK : ∀ a ∈ spine.take k, WScoped k a)
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L) :
    InterpPkg m₀.val env₀ ψ D ρ ld ∧ WScoped k ld := by
  -- split the λ-walk at the prefix
  have hlinst' : Expr.instLamsAt (spine.take k ++ spine.drop k) rhsA =
      some (ldoms, lrest) := by
    rw [List.take_append_drop]
    exact hlinst
  obtain ⟨lds₁, lamMid, lds₂, hopL1, hopL2, hldsSplit⟩ :=
    instLamsAt_append (spine.take k) (spine.drop k) hlinst'
  have hlds₁len : lds₁.length = k := by
    rw [instLamsAt_length _ hopL1, List.length_take]
    omega
  have hlds₁ : lds₁ = ldoms.take k := by
    have h := congrArg (List.take k) hldsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := lds₁) (by omega)] at h
    exact h.symm
  -- the prefix defeq facts
  have hdeTk : DefEqListOk F env₀ D ((spine.take k).map Expr.fvarTypeD)
      lds₁ := by
    have h := DefEqListOk.take k hdeLam
    rwa [← List.map_take, ← hlds₁] at h
  -- the right-hand side's closed facts at the frame
  have hWr : WScoped D rhsA := WScoped.of_not_hasFvar hrhsw
  have hLr : Expr.LeavesBounded rhsA :=
    Expr.LeavesBounded.of_not_hasFvar hrhsw
  have hFr : FvarsOk V m₀.val env₀ ψ D ρ rhsA :=
    FvarsOk.of_not_hasFvar hrhsw
  have hAr : AnnotOk V m₀.val env₀ ψ D ρ rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ hArhs
  obtain ⟨L0, hL0c⟩ := hIrhs
  have hL0 : interpExpr V m₀.val env₀ ψ D ρ rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  -- walk the λ-tower along the prefix
  have hfitLam := lam_walk m₀ F hopL1 hdeTk hsp hws hΘ hLs hWr hrhsb
    hLr hFr hAr ⟨L0, hL0⟩
  obtain ⟨Bmid, hBmid, -, -⟩ := TeleFitLam.fold hfitLam hAr hL0
  obtain ⟨hWlm, hblm, hAlm, hllm⟩ := TeleFitLam.rest_wf hfitLam hWr
    hrhsb hAr
  have hFlm : FvarsOk V m₀.val env₀ ψ D ρ lamMid := by
    intro l hl
    rcases hllm l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at hl'
      cases hl'
    · exact hΘ a ha l hla
  have hLlm : Expr.LeavesBounded lamMid := by
    intro l hl
    rcases hllm l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at hl'
      cases hl'
    · exact hLs a ha l hla
  -- scoping at the stage frame
  obtain ⟨-, hWlmK⟩ := instLamsAt_wscoped (D := k) (spine.take k)
    hopL1 (WScoped.of_not_hasFvar hrhsw) hwsK
  -- invert the head binder
  have hdropC : spine.drop k = spine[k] :: spine.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  rw [hdropC] at hopL2
  obtain ⟨nL, domL, bodyL, mL, lds₂', rfl, hlds₂c, -⟩ :=
    instLamsAt_cons_inv hopL2
  have hdomL : domL = ld := by
    have h0 : ldoms[k]? = some domL := by
      rw [hldsSplit, List.getElem?_append_right (by omega), hlds₁len,
        Nat.sub_self, hlds₂c]
      rfl
    rw [hld] at h0
    exact (Option.some.inj h0).symm
  replace hdomL : ld = domL := hdomL.symm
  subst hdomL
  -- unpack the head binder's facts
  have hAlm' := hAlm
  simp only [AnnotOk] at hAlm'
  obtain ⟨hAld, ⟨cod, hcod⟩, -⟩ := hAlm'
  have hWld : WScoped D ld ∧ WScoped D bodyL := by
    simpa [WScoped] using hWlm
  have hbld : ld.looseBVarsBounded 0 = true ∧
      bodyL.looseBVarsBounded 1 = true := by
    revert hblm; simp [Expr.looseBVarsBounded]
  have hLld : Expr.LeavesBounded ld := fun l hl =>
    hLlm l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl)
  have hFld : FvarsOk V m₀.val env₀ ψ D ρ ld :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFlm
  have hIld : ∃ B, interpExpr V m₀.val env₀ ψ D ρ ld = some B := by
    revert hBmid
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ D ρ ld with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWldK : WScoped k ld := by
    have h := hWlmK
    simp only [WScoped] at h
    exact h.1
  exact ⟨⟨hWld.1, hbld.1, hLld, hFld, hAld, hIld⟩, hWldK⟩

/-- The spine-prefix kit every stage hands to the λ-side walk. -/
def SpineKit (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (D k : Nat) (ρ : Nat → V) (spine : List Expr) (xs : List V) : Prop :=
  FvarSpine D ρ (spine.take k) xs ∧
  (∀ a ∈ spine.take k, WScoped D a) ∧
  (∀ a ∈ spine.take k, FvarsOk V cval env φ D ρ a) ∧
  (∀ a ∈ spine.take k, Expr.LeavesBounded a) ∧
  (∀ a ∈ spine.take k, WScoped k a)

/-- Stage package for the recursor-prefix region (`k < rP`): walk the
member type's telescope along the chosen values; the residual's head
binder is the stage annotation, packaged at the padded master frame. -/
theorem stage_pkg_pre {env₀ : Env} (m₀ : EnvModel V env₀)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {xFvsP : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    {k : Nat} {xs : List V} {fv : Expr}
    (hk : k < rP) (hxs : xs.length = k)
    (hfv : (fvsP ++ xFvsP)[k]? = some fv)
    (hpref : FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs) :
    (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
    SpineKit m₀.val env₀ ψ (rP + cnF) k
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the spine prefix is inside the recursor prefix
  have hTkeq : (fvsP ++ xFvsP).take k = fvsP.take k := by
    rw [List.take_append_of_le_length (by omega)]
  -- fv is the k-th prefix variable, a fvar at index k
  have hfvP : fvsP[k]? = some fv := by
    rw [List.getElem?_append_left (by omega)] at hfv
    exact hfv
  obtain ⟨nmv, hfvShape⟩ := hfvsPShape k fv hfvP
  rw [Nat.zero_add] at hfvShape
  -- the padded value spine over the full prefix
  have hspFull : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP
      (xs ++ List.replicate (rP - k) SetTheory.empty) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_append, List.length_replicate, hxs]; omega)
      (by omega) ?_
    intro j v hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge j k with hj | hj
    · rw [List.getElem?_append_left (by omega)] at hjv
      rw [hjv]
      rfl
    · rw [List.getElem?_append_right (by omega), hxs,
        List.getElem?_replicate] at hjv
      split at hjv
      · rw [List.getElem?_eq_none (by omega)]
        exact Option.some.inj hjv
      · exact nomatch hjv
  have hspTk : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take k) xs := by
    have h := FvarSpine.take k hspFull
    rw [List.take_append_of_le_length (by omega)] at h
    rwa [List.take_of_length_le (l := xs) (by omega)] at h
  -- entry facts on the prefix
  have hwsTk : ∀ a ∈ fvsP.take k, WScoped (rP + cnF) a := by
    intro a ha
    exact ((hfvsPWf a (List.mem_of_mem_take ha)).1).mono (by omega)
  have hLsTk : ∀ a ∈ fvsP.take k, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hwsKTk : ∀ a ∈ fvsP.take k, WScoped k a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    have hjlen : j < (fvsP.take k).length := by
      rcases Nat.lt_or_ge j (fvsP.take k).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hja
        exact nomatch hja
    have hjk : j < k := by
      rw [List.length_take] at hjlen
      omega
    have hja' : fvsP[j]? = some a := by
      rw [List.getElem?_take_of_lt hjk] at hja
      exact hja
    obtain ⟨nm, hshape⟩ := hfvsPShape j a hja'
    rw [Nat.zero_add] at hshape
    have hW := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rw [hshape] at hW ⊢
    simp only [WScoped] at hW ⊢
    exact ⟨hjk, hW.2⟩
  -- the pointwise membership pack at the padded master frame
  have hmem : ∀ (i : Nat) (a : Expr) (v : V),
      ((fvsP.take k).map Expr.fvarTypeD)[i]? = some a →
      xs[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hik : i < k := by
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hv
        exact nomatch hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hik, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- split the member-type walk at the prefix
  have hfvsPInst' : Expr.instPisAt (fvsP.take k ++ fvsP.drop k) tyA =
      some (fvsP.map Expr.fvarTypeD, restP) := by
    rw [List.take_append_drop]
    exact hfvsPInst
  obtain ⟨ds₁, midS, ds₂, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append (fvsP.take k) (fvsP.drop k) hfvsPInst'
  have hds₁len : ds₁.length = k := by
    rw [instPisAt_length _ hopS1, List.length_take]
    omega
  have hds₁ : ds₁ = (fvsP.take k).map Expr.fvarTypeD := by
    have h := congrArg (List.take k) hdsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := ds₁) (by omega)] at h
    rw [List.map_take]
    exact h.symm
  subst hds₁
  -- walk the prefix (fit + spine typing packages + residual facts)
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hLty : Expr.LeavesBounded tyA :=
    Expr.LeavesBounded.of_not_hasFvar htyw
  have hFty : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    FvarsOk.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  have hIty' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA = some T := by
    obtain ⟨T, hT⟩ := hIty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant htyw _ _]
    exact hT
  obtain ⟨hfitTk, hΘTk⟩ := self_walk hopS1 hspTk hwsTk hWty htyb hLty
    hFty hAty' hmem
  obtain ⟨-, hPmid⟩ := peel_walk hopS1 hspTk hwsTk hWty hAty' hIty' hmem
  obtain ⟨Pmid, hPmid⟩ := hPmid
  obtain ⟨hWmid, hbmid, hAmid, hlmid⟩ :=
    TeleFitI.rest_wf hfitTk hWty htyb hAty'
  have hFmid : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midS := by
    intro l hl
    rcases hlmid l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hΘTk a ha l hla
  have hLmid : Expr.LeavesBounded midS := by
    intro l hl
    rcases hlmid l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hLsTk a ha l hla
  -- residual-scoping at the stage frame
  obtain ⟨-, hWmidK⟩ := instPisAt_wscoped (D := k) (fvsP.take k) hopS1
    (WScoped.of_not_hasFvar htyw) hwsKTk
  -- invert the head binder
  have hdropC : fvsP.drop k = fv :: fvsP.drop (k + 1) := by
    have h := List.drop_eq_getElem_cons (l := fvsP) (i := k) (by omega)
    rw [h]
    congr 1
    have := List.getElem?_eq_getElem (l := fvsP) (i := k) (by omega)
    rw [hfvP] at this
    exact (Option.some.inj this).symm
  rw [hdropC] at hopS2
  obtain ⟨nH, domH, bodyH, mH, ds₂', rfl, hds₂c, -⟩ :=
    instPisAt_cons_inv hopS2
  have hdomH : domH = Expr.fvarTypeD fv := by
    have h0 : (fvsP.map Expr.fvarTypeD)[k]? = some domH := by
      rw [hdsSplit, List.getElem?_append_right
        (by rw [List.length_map, List.length_take]; omega)]
      rw [List.length_map, List.length_take,
        show k - min k fvsP.length = 0 from by omega, hds₂c]
      rfl
    rw [List.getElem?_map, hfvP] at h0
    exact (Option.some.inj h0).symm
  replace hdomH : Expr.fvarTypeD fv = domH := hdomH.symm
  subst hdomH
  -- extract the stage annotation's package
  have hAmid' := hAmid
  simp only [AnnotOk] at hAmid'
  obtain ⟨hAdom, ⟨cod, hcod⟩, -⟩ := hAmid'
  have hWdom : WScoped (rP + cnF) (Expr.fvarTypeD fv) ∧
      WScoped (rP + cnF) bodyH := by
    simpa [WScoped] using hWmid
  have hbdom : (Expr.fvarTypeD fv).looseBVarsBounded 0 = true ∧
      bodyH.looseBVarsBounded 1 = true := by
    revert hbmid; simp [Expr.looseBVarsBounded]
  have hLdom : Expr.LeavesBounded (Expr.fvarTypeD fv) :=
    LeavesBounded.of_forallE_ty hLmid
  have hFdom : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFmid
  have hIdom : ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
        some B := by
    revert hPmid
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWdomK : WScoped k (Expr.fvarTypeD fv) := by
    have hW := (hfvsPWf fv (List.mem_of_getElem? hfvP)).1
    rw [hfvShape] at hW
    simp only [WScoped] at hW
    rw [hfvShape]
    exact hW.2
  refine ⟨⟨⟨hWdom.1, hbdom.1, hLdom, hFdom, hAdom, hIdom⟩, hWdomK⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTkeq]; exact hspTk
  · rw [hTkeq]; exact hwsTk
  · rw [hTkeq]; exact hΘTk
  · rw [hTkeq]; exact hLsTk
  · rw [hTkeq]; exact hwsKTk

/-- Stage package for the constructor-field region (`rP ≤ k`): walk
the member type over the full recursor prefix, obtain the (plain- or
nested-specific) constructor-residual package, and walk it along the
chosen field values; the residual's head binder is the stage
annotation. -/
theorem stage_pkg_fld {env₀ : Env} (m₀ : EnvModel V env₀)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {crestP : Expr}
    {xFvsP : List Expr} {crest2 : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    {k : Nat} {xs : List V} {fv : Expr}
    (hctorPkg :
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P)
    (hkl : rP ≤ k) (hk : k < rP + cnF) (hxs : xs.length = k)
    (hfv : (fvsP ++ xFvsP)[k]? = some fv)
    (hpref : FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs) :
    (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
    SpineKit m₀.val env₀ ψ (rP + cnF) k
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
  obtain ⟨hWcr, hbcr, hLcr, hFcr, hAcr, Pcr, hPcr⟩ := hctorPkg
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf cnF rP hopenX hWcr hbcr
    hLcr
  obtain ⟨t, hktr⟩ : ∃ t, k = rP + t := ⟨k - rP, by omega⟩
  have ht : t < cnF := by omega
  -- the k-th spine entry is the t-th field variable
  have hfvX : xFvsP[t]? = some fv := by
    rw [List.getElem?_append_right (by omega), hfvsPLen,
      show k - rP = t from by omega] at hfv
    exact hfv
  obtain ⟨nmv, hfvShape⟩ := hxShape t fv hfvX
  -- the full recursor-prefix spine
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  -- the membership pack over the full recursor prefix
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- tyA's closed facts at the frame
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hLty : Expr.LeavesBounded tyA :=
    Expr.LeavesBounded.of_not_hasFvar htyw
  have hFty : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    FvarsOk.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  obtain ⟨-, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb hLty hFty
    hAty' hmemP
  -- the field-prefix spine
  have hspXFull : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) xFvsP
      (xs.drop rP ++ List.replicate (cnF - t) SetTheory.empty) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_append, List.length_drop,
        List.length_replicate]; omega) (by omega) ?_
    intro j v hjv
    show xs.getD (rP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge j t with hj | hj
    · rw [List.getElem?_append_left
        (by rw [List.length_drop]; omega), List.getElem?_drop] at hjv
      rw [hjv]
      rfl
    · rw [List.getElem?_append_right
        (by rw [List.length_drop]; omega), List.length_drop,
        List.getElem?_replicate] at hjv
      split at hjv
      · rw [List.getElem?_eq_none (by omega)]
        exact Option.some.inj hjv
      · exact nomatch hjv
  have hspXt : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (xFvsP.take t)
      (xs.drop rP) := by
    have h := FvarSpine.take t hspXFull
    rw [List.take_append_of_le_length
      (by rw [List.length_drop]; omega)] at h
    rwa [List.take_of_length_le (l := xs.drop rP)
      (by rw [List.length_drop]; omega)] at h
  have hwsXt : ∀ a ∈ xFvsP.take t, WScoped (rP + cnF) a := fun a ha =>
    (hxWf a (List.mem_of_mem_take ha)).1
  have hLsXt : ∀ a ∈ xFvsP.take t, Expr.LeavesBounded a := fun a ha =>
    (hxWf a (List.mem_of_mem_take ha)).2.2
  -- the membership pack over the field prefix
  have hmemX : ∀ (i : Nat) (a : Expr) (v : V),
      ((xFvsP.take t).map Expr.fvarTypeD)[i]? = some a →
      (xs.drop rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hit : i < t := by
      rcases Nat.lt_or_ge i t with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hix : i < xFvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvsP[i]? = some fvi :=
      ⟨xFvsP[i]'hix, List.getElem?_eq_getElem hix⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hit, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[rP + i]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show rP + i - rP = i from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (rP + i) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape i fvi hfvi
    have hWi : WScoped (rP + i) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- split the constructor-residual walk at the field prefix
  have hxInst' : Expr.instPisAt (xFvsP.take t ++ xFvsP.drop t) crestP =
      some (xFvsP.map Expr.fvarTypeD, crest2) := by
    rw [List.take_append_drop]
    exact hxInst
  obtain ⟨ds₁, midX, ds₂, hopX1, hopX2, hdsSplit⟩ :=
    instPisAt_append (xFvsP.take t) (xFvsP.drop t) hxInst'
  have hds₁len : ds₁.length = t := by
    rw [instPisAt_length _ hopX1, List.length_take]
    omega
  have hds₁ : ds₁ = (xFvsP.take t).map Expr.fvarTypeD := by
    have h := congrArg (List.take t) hdsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := ds₁) (by omega)] at h
    rw [List.map_take]
    exact h.symm
  subst hds₁
  have hWcrD : WScoped (rP + cnF) crestP := hWcr.mono (by omega)
  obtain ⟨hfitX, hΘX⟩ := self_walk hopX1 hspXt hwsXt hWcrD hbcr hLcr
    hFcr hAcr hmemX
  obtain ⟨-, hPmidX⟩ := peel_walk hopX1 hspXt hwsXt hWcrD hAcr
    ⟨Pcr, hPcr⟩ hmemX
  obtain ⟨PmidX, hPmidX⟩ := hPmidX
  obtain ⟨hWmidX, hbmidX, hAmidX, hlmidX⟩ :=
    TeleFitI.rest_wf hfitX hWcrD hbcr hAcr
  have hFmidX : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midX := by
    intro l hl
    rcases hlmidX l hl with hl' | ⟨a, ha, hla⟩
    · exact hFcr l hl'
    · exact hΘX a ha l hla
  have hLmidX : Expr.LeavesBounded midX := by
    intro l hl
    rcases hlmidX l hl with hl' | ⟨a, ha, hla⟩
    · exact hLcr l hl'
    · exact hLsXt a ha l hla
  -- invert the head binder
  have hdropC : xFvsP.drop t = fv :: xFvsP.drop (t + 1) := by
    have h := List.drop_eq_getElem_cons (l := xFvsP) (i := t)
      (by omega)
    rw [h]
    congr 1
    have := List.getElem?_eq_getElem (l := xFvsP) (i := t) (by omega)
    rw [hfvX] at this
    exact (Option.some.inj this).symm
  rw [hdropC] at hopX2
  obtain ⟨nH, domH, bodyH, mH, ds₂', rfl, hds₂c, -⟩ :=
    instPisAt_cons_inv hopX2
  have hdomH : domH = Expr.fvarTypeD fv := by
    have h0 : (xFvsP.map Expr.fvarTypeD)[t]? = some domH := by
      rw [hdsSplit, List.getElem?_append_right
        (by rw [List.length_map, List.length_take]; omega)]
      rw [List.length_map, List.length_take,
        show t - min t xFvsP.length = 0 from by omega, hds₂c]
      rfl
    rw [List.getElem?_map, hfvX] at h0
    exact (Option.some.inj h0).symm
  replace hdomH : Expr.fvarTypeD fv = domH := hdomH.symm
  subst hdomH
  -- extract the stage annotation's package
  have hAmidX' := hAmidX
  simp only [AnnotOk] at hAmidX'
  obtain ⟨hAdom, ⟨cod, hcod⟩, -⟩ := hAmidX'
  have hWdom : WScoped (rP + cnF) (Expr.fvarTypeD fv) ∧
      WScoped (rP + cnF) bodyH := by
    simpa [WScoped] using hWmidX
  have hbdom : (Expr.fvarTypeD fv).looseBVarsBounded 0 = true ∧
      bodyH.looseBVarsBounded 1 = true := by
    revert hbmidX; simp [Expr.looseBVarsBounded]
  have hLdom : Expr.LeavesBounded (Expr.fvarTypeD fv) :=
    LeavesBounded.of_forallE_ty hLmidX
  have hFdom : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFmidX
  have hIdom : ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
        some B := by
    revert hPmidX
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWdomK : WScoped k (Expr.fvarTypeD fv) := by
    have hW := (hxWf fv (List.mem_of_getElem? hfvX)).1
    rw [hfvShape] at hW
    simp only [WScoped] at hW
    rw [hfvShape, hktr]
    exact hW.2
  -- assemble the spine kit at the full stage prefix
  have hTkeq : (fvsP ++ xFvsP).take k = fvsP ++ xFvsP.take t := by
    rw [show k = fvsP.length + t from by omega,
      List.take_length_add_append]
  have hspTk : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) ((fvsP ++ xFvsP).take k)
      xs := by
    rw [hTkeq]
    have h := FvarSpine.append hspP hspXt
    rwa [List.take_append_drop] at h
  refine ⟨⟨⟨hWdom.1, hbdom.1, hLdom, hFdom, hAdom, hIdom⟩, hWdomK⟩,
    hspTk, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hwsP a ha
    · exact hwsXt a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact hLsXt a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · -- a recursor-prefix variable, index below rP ≤ k
      obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      have hjlen : j < fvsP.length := by
        rcases Nat.lt_or_ge j fvsP.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hja
          exact nomatch hja
      obtain ⟨nm, hshape⟩ := hfvsPShape j a hja
      rw [Nat.zero_add] at hshape
      have hW := (hfvsPWf a ha).1
      rw [hshape] at hW ⊢
      simp only [WScoped] at hW ⊢
      exact ⟨by omega, hW.2⟩
    · -- a field variable below the stage
      obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      have hjlen : j < (xFvsP.take t).length := by
        rcases Nat.lt_or_ge j (xFvsP.take t).length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hja
          exact nomatch hja
      have hjt : j < t := by
        rw [List.length_take] at hjlen
        omega
      have hja' : xFvsP[j]? = some a := by
        rw [List.getElem?_take_of_lt hjt] at hja
        exact hja
      obtain ⟨nm, hshape⟩ := hxShape j a hja'
      have hW := (hxWf a (List.mem_of_mem_take ha)).1
      rw [hshape] at hW ⊢
      simp only [WScoped] at hW ⊢
      exact ⟨by omega, hW.2⟩

/-- The flat stage facts (`Hty` of `TowerOk.of_stages`) of a modeled
recursor rule: at every stage, the frame annotation and (anything
erased-equal to) the rule tower's instantiated binder domain interpret
to the same set, the annotation is truthful, and members extend the
frame-membership invariant. -/
theorem modeled_stage {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {crestP : Expr}
    {xFvsP : List Expr} {crest2 : Expr}
    {rhsA lrest : Expr} {ldoms : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hctorPkg : ∀ (xs : List V), xs.length ≤ rP + cnF →
      rP ≤ xs.length →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P)
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA =
      some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L) :
    ∀ (k : Nat) (xs : List V) (fv ld : Expr), xs.length = k →
      (fvsP ++ xFvsP)[k]? = some fv → ldoms[k]? = some ld →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      ∃ A, interpExpr V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
            some A ∧
        (∀ e, Expr.ErasedEq e ld → interpExpr V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) e = some A) ∧
        AnnotOk V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
        ∀ x, x ∈ˢ A →
          FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) (xs ++ [x]) := by
  intro k xs fv ld hxs hfv hld hpref
  have hfvsPLen : fvsP.length = rP :=
    (openPisAtFvars_spec rP 0 hopenP).2.1
  have hxLen : xFvsP.length = cnF :=
    (openPisAtFvars_spec cnF rP hopenX).2.1
  have hspineLen : (fvsP ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPLen, hxLen]
  have hkD : k < rP + cnF := by
    have h1 : k < ldoms.length := by
      rcases Nat.lt_or_ge k ldoms.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hld
        exact nomatch hld
    rw [instLamsAt_length _ hlinst, hspineLen] at h1
    exact h1
  -- the annotation package + spine kit, by region
  have hpkg : (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
      SpineKit m₀.val env₀ ψ (rP + cnF) k
        (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
    rcases Nat.lt_or_ge k rP with hk | hk
    · exact stage_pkg_pre m₀ hopenP htyw htyb hAty hIty hk hxs hfv
        hpref
    · exact stage_pkg_fld m₀ hopenP htyw htyb hAty hopenX
        (hctorPkg xs (by omega) (by omega) hpref) hk hkD hxs hfv hpref
  obtain ⟨⟨hpkgA, hWkA⟩, hsp, hws, hΘ, hLs, hwsK⟩ := hpkg
  -- the λ-side package
  obtain ⟨hpkgB, hWkB⟩ := stage_pkg_lam m₀ F hlinst hdeLam
    (by omega) hld hsp hws hΘ hLs hwsK hrhsw hrhsb hArhs hIrhs
  -- the stage defeq
  have hde : isDefEqCore env₀ F (rP + cnF) (Expr.fvarTypeD fv) ld =
      .ok true := by
    refine DefEqListOk.pointwise hdeLam k ?_ hld
    rw [List.getElem?_map, hfv]
    rfl
  obtain ⟨A, h1, h2, h3⟩ := stage_out m₀ F hxs (by omega) hde hpkgA
    hpkgB hWkA hWkB
  refine ⟨A, h1, h2, h3, ?_⟩
  -- extending the membership invariant
  intro x hx j v fv' hjv hjfv
  rcases Nat.lt_trichotomy j k with hj | hj | hj
  · rw [List.getElem?_append_left (by omega)] at hjv
    obtain ⟨B, hB, hvB⟩ := hpref j v fv' hjv hjfv
    refine ⟨B, ?_, hvB⟩
    rwa [List.take_append_of_le_length (by omega)]
  · subst hj
    rw [List.getElem?_append_right (by omega), hxs, Nat.sub_self] at hjv
    obtain rfl : x = v := Option.some.inj hjv
    have hfv' : fv' = fv := by
      rw [hfv] at hjfv
      exact (Option.some.inj hjfv.symm)
    subst hfv'
    refine ⟨A, ?_, hx⟩
    rw [List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
    exact h1
  · have hlen : (xs ++ [x]).length ≤ j := by
      simp only [List.length_append, List.length_cons,
        List.length_nil, hxs]
      omega
    rw [List.getElem?_eq_none hlen] at hjv
    exact nomatch hjv

/-- The constructor-residual package of a **plain** rule: the
constructor type is walked at the leading recursor parameters, whose
memberships transfer into the walk's domains along the kernel's
parameter-domain pins (`pi_walk_src` over `hdePars`). -/
theorem ctor_pkg_plain {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {tyA : Expr} {rP cnP cnF : Nat} {cty : Expr}
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvsP : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cty =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hplainLe : cnP ≤ rP)
    (hCw : cty.hasFvar = false)
    (hCb : cty.looseBVarsBounded 0 = true)
    (hACty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cty)
    (hICty : ∃ T, interpClosed V m₀.val env₀ ψ cty = some T) :
    ∀ (xs : List V), xs.length ≤ rP + cnF → rP ≤ xs.length →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P := by
  intro xs hlen hge hpref
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the full recursor-prefix spine and its typing packages
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hΘP := (self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw)
    (AnnotOk.closed_invariant htyw _ _ hAty) hmemP).2
  -- restrict to the constructor parameters
  have hspC : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspP
    rwa [List.take_take, Nat.min_eq_left hplainLe] at h
  have hwsC : ∀ a ∈ fvsP.take cnP, WScoped (rP + cnF) a := fun a ha =>
    hwsP a (List.mem_of_mem_take ha)
  have hLsC : ∀ a ∈ fvsP.take cnP, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hFsC : ∀ a ∈ fvsP.take cnP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := fun a ha =>
    hΘP a (List.mem_of_mem_take ha)
  -- the constructor type's closed facts at the frame
  have hWc : WScoped (rP + cnF) cty := WScoped.of_not_hasFvar hCw
  have hAc : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  -- walk the parameters, transferring along the parameter-domain pins
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m₀ F hcinstP hdePars hspC hwsC
    hLsC hFsC hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcr⟩ := peel_walk hcinstP hspC hwsC hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcr
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  -- residual scoping at the recursor prefix
  have hwsCrP : ∀ a ∈ fvsP.take cnP, WScoped rP a := by
    intro a ha
    have h := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcr⟩ := instPisAt_wscoped (D := rP) (fvsP.take cnP)
    hcinstP (WScoped.of_not_hasFvar hCw) hwsCrP
  refine ⟨hWcr, hbcr, ?_, ?_, hAcr, ⟨Pcr, hPcr⟩⟩
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hLsC a ha l hla
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hFsC a ha l hla

/-- The constructor-residual package of a **nested** rule: the
level-instantiated constructor type is walked at the stored parameter
instantiations (opened at the prefix variables), whose memberships
come through the kernel's typed pins (`typed_walk` over
`TypedListOk`); the instantiations' own typing packages fall out of
the member type's major-premise domain. -/
theorem ctor_pkg_nested {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat} {cty : Expr}
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvsP : List Expr}
    {pins : List Expr} {Dn : Name} {lvls : List Level}
    {preM : List (Name × Expr × BinderMeta)}
    {nmM : Name} {domM bodyM : Expr} {bmM : BinderMeta}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hstripM : tyA.stripPis rP = some (preM, .forallE nmM domM bodyM bmM))
    (hdomFn : domM.getAppFn = .const Dn lvls)
    (hdomArgs : domM.getAppArgs = pins)
    (hpinsW : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    (hcinstN : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) cty =
      some (cdomsP, crestP))
    (htlP : TypedListOk F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) cdomsP)
    (hCtw : cty.hasFvar = false)
    (hCtb : cty.looseBVarsBounded 0 = true)
    (hACt : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cty)
    (hICt : ∃ T, interpClosed V m₀.val env₀ ψ cty = some T) :
    ∀ (xs : List V), xs.length ≤ rP + cnF → rP ≤ xs.length →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P := by
  intro xs hlen hge hpref
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the full recursor-prefix spine and its typing packages
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  have hIty' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA = some T := by
    obtain ⟨T, hT⟩ := hIty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant htyw _ _]
    exact hT
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw) hAty' hmemP
  obtain ⟨-, hPrestEx⟩ := peel_walk hfvsPInst hspP hwsP hWty hAty'
    hIty' hmemP
  obtain ⟨Prest, hPrest⟩ := hPrestEx
  obtain ⟨hWrest, hbrest, hArest, hlrest⟩ :=
    TeleFitI.rest_wf hfitP hWty htyb hAty'
  have hFrest : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) restP := by
    intro l hl
    rcases hlrest l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hΘP a ha l hla
  have hLrest : Expr.LeavesBounded restP := by
    intro l hl
    rcases hlrest l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact (hfvsPWf a ha).2.2 l hla
  -- the major premise's domain, instantiated at the prefix
  have hrestEq : restP = .forallE nmM
      (instSeq fvsP (rP - 1) domM)
      (instSeq fvsP (rP - 1 + 1) bodyM) bmM := by
    obtain ⟨h1, -⟩ := instPisAt_stripPis fvsP hfvsPInst
      (by rw [hfvsPLen]; exact hstripM)
    rw [h1, hfvsPLen, instSeq_forallE fvsP (rP - 1) nmM domM bodyM bmM
      (by rw [hfvsPLen]; omega)]
  -- the instantiated parameter spine and its typing packages
  have hdomEq : instSeq fvsP (rP - 1) domM =
      Expr.mkAppN (.const Dn lvls)
        (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) := by
    conv => lhs; rw [show domM = Expr.mkAppN domM.getAppFn
      domM.getAppArgs from (Expr.mkAppN_getApp domM).symm]
    rw [hdomFn, hdomArgs, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    refine List.map_congr_left ?_
    intro p hp
    rw [Expr.instSpine_eq_instSeq]
  rw [hrestEq] at hArest hPrest hWrest hbrest hFrest hLrest
  have hAdomI : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (instSeq fvsP (rP - 1) domM) := by
    have h := hArest
    simp only [AnnotOk] at h
    exact h.1
  have hFdomI : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (instSeq fvsP (rP - 1) domM) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFrest
  have hLdomI : Expr.LeavesBounded (instSeq fvsP (rP - 1) domM) :=
    LeavesBounded.of_forallE_ty hLrest
  -- per-argument facts of the instantiated parameters
  have hcargW : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      WScoped (rP + cnF) a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact instSpine_WScoped (rP - 1)
      (WScoped.of_not_hasFvar (hpinsW p hp).1) hwsP
  have hcargB : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq,
      show rP - 1 = fvsP.length - 1 from by rw [hfvsPLen]]
    refine instSeq_bclosed ?_ ?_
    · intro x hx
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      obtain ⟨nm, hsh⟩ := hfvsPShape j x hj
      rw [hsh]
      rfl
    · rw [hfvsPLen]
      exact (hpinsW p hp).2
  have hcargL : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      Expr.LeavesBounded a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq]
    refine LeavesBounded_instSeq _ _ ?_ ?_
    · exact Expr.LeavesBounded.of_not_hasFvar (hpinsW p hp).1
    · intro x hx
      exact (hfvsPWf x hx).2.2
  have hcargF : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    refine FvarsOk.of_subset (fun l hl => ?_) hFdomI
    rw [hdomEq]
    refine fvarLeaves_getAppArgs ?_ l hl
    rw [Expr.getAppArgs_mkAppN,
      show (Expr.const Dn lvls).getAppArgs = [] from rfl,
      List.nil_append]
    exact ha
  have hcargA : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    have hne : pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ≠
        [] := by
      intro h0
      rw [h0] at ha
      exact nomatch ha
    have hAdom' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const Dn lvls)
          (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p))) := by
      rw [← hdomEq]
      exact hAdomI
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ (.const Dn lvls) hne
      hAdom'
    exact hargsA a ha
  -- walk the level-instantiated constructor type at the pins
  have hWct : WScoped (rP + cnF) cty := WScoped.of_not_hasFvar hCtw
  have hACt' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty :=
    AnnotOk.closed_invariant hCtw _ _ hACt
  have hICt' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty = some T := by
    obtain ⟨T, hT⟩ := hICt
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCtw _ _]
    exact hT
  obtain ⟨cvals, hfitC, hpackC, PcrEx⟩ := typed_walk m₀ F hcinstN htlP
    (fun a ha => ⟨hcargW a ha, hcargB a ha, hcargL a ha, hcargF a ha,
      hcargA a ha⟩)
    hWct hCtb (Expr.LeavesBounded.of_not_hasFvar hCtw)
    (FvarsOk.of_not_hasFvar hCtw) hACt' hICt'
  obtain ⟨Pcr, hPcr⟩ := PcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWct hCtb
    hACt'
  -- residual scoping at the recursor prefix
  have hcargWrP : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      WScoped rP a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine instSpine_WScoped (rP - 1)
      (WScoped.of_not_hasFvar (hpinsW p hp).1) ?_
    intro x hx
    have h := (hfvsPWf x hx).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcr⟩ := instPisAt_wscoped (D := rP)
    (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) hcinstN
    (WScoped.of_not_hasFvar hCtw) hcargWrP
  refine ⟨hWcr, hbcr, ?_, ?_, hAcr, ⟨Pcr, hPcr⟩⟩
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · exact hcargL a ha l hla
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · exact hcargF a ha l hla

set_option maxHeartbeats 3200000 in
/-- The bottom fact (`Hbot` of `TowerOk.of_stages`) of a **plain**
modeled rule: over any full frame-fitting value list, the canonical
iota left-hand side body (the recursor applied to the prefix
variables, the constructor residual's indices and the applied
constructor) and the rule right-hand side's instantiated body
interpret to the same value, and the body's annotations are truthful.
Derived by eliminating the checked `_model.iota_j` theorem's
inhabitant into the interpreted equation at the master frame. -/
theorem modeled_bottom_plain
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat) {ψ : Name → Nat}
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    -- the recursor, its public entry and its model
    {R : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    {ciR cim : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    (hRlps : ciR.toConstantVal.levelParams = lps)
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hClps : ciC.toConstantVal.levelParams = cvj.levelParams)
    -- the pinned equality former
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ'' cvt.type = some P ∧
      m₀.val thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- kernel kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    (htyStrip : (tyA.stripPis mI).isSome = true)
    (hrPmI : rP ≤ mI)
    (hplainLe : cnP ≤ rP)
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hCstripSome : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take rP)
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- kernel kit (public side)
    {rhsA : Expr} {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- the rule right-hand side's facts
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L)
    -- member and constructor type wf
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvj.type)
    (hICty : ∃ T, interpClosed V m₀.val env₀ ψ cvj.type = some T) :
    ∀ (xs : List V), xs.length = rP + cnF →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      (∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
          (fun i => xs.getD i SetTheory.empty)
          (Expr.mkAppN (.const R (lps.map .param))
            (fvsP ++ crest2.getAppArgs.drop cnP ++
              [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
                (fvsP.take cnP ++ xFvsP)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrest →
          interpExpr V m₀.val env₀ ψ (rP + cnF)
            (fun i => xs.getD i SetTheory.empty) e = some w) ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const R (lps.map .param))
          (fvsP ++ crest2.getAppArgs.drop cnP ++
            [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
              (fvsP.take cnP ++ xFvsP)])) := by
  intro xs hxs hpref
  -- ===== S0: the theorem-side master frame =====
  obtain ⟨hfvsInst, hfvsLen, hfvsShape⟩ :=
    openPisAtFvars_spec (rP + cnF) 0 hopen
  obtain ⟨hfvsWf, htbodyWf⟩ := openPisAtFvars_wf (rP + cnF) 0 hopen
    (WScoped.of_not_hasFvar hSw) hSb
    (Expr.LeavesBounded.of_not_hasFvar hSw)
  have hfvsW : ∀ a ∈ fvs, WScoped (rP + cnF) a := by
    intro a ha
    have := (hfvsWf a ha).1
    simpa using this
  have hfvsShapes : ∀ a ∈ fvs, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  have hspW : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvs xs := by
    refine FvarSpine_of_open hopen hxs (by omega) ?_
    intro k v hkv
    show xs.getD (0 + k) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hkv]
    rfl
  have hspWpre := FvarSpine.take rP hspW
  have hspWdrop := FvarSpine.drop rP hspW
  have hspWctorPre : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvs.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspW
    exact h
  have hspWctor := FvarSpine.append hspWctorPre hspWdrop
  have hfvsPreLen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvsLen]; omega
  have hfvsCLen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop,
      hfvsLen]
    omega
  -- ===== S0': the public frame and its walks =====
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw) hAty' hmemP
  -- the public constructor walk (parameters via the kernel pins)
  have hspC : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspP
    rwa [List.take_take, Nat.min_eq_left hplainLe] at h
  have hwsC : ∀ a ∈ fvsP.take cnP, WScoped (rP + cnF) a := fun a ha =>
    hwsP a (List.mem_of_mem_take ha)
  have hLsC : ∀ a ∈ fvsP.take cnP, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hFsC : ∀ a ∈ fvsP.take cnP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := fun a ha =>
    hΘP a (List.mem_of_mem_take ha)
  have hWc : WScoped (rP + cnF) cvj.type := WScoped.of_not_hasFvar hCw
  have hAc : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m₀ F hcinstP hdePars hspC hwsC
    hLsC hFsC hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcrEx⟩ := peel_walk hcinstP hspC hwsC hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  have hFcr : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hFsC a ha l hla
  have hLcr : Expr.LeavesBounded crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hLsC a ha l hla
  -- the public field walk
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  have hwsCrP : ∀ a ∈ fvsP.take cnP, WScoped rP a := by
    intro a ha
    have h := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcrRp⟩ := instPisAt_wscoped (D := rP) (fvsP.take cnP)
    hcinstP (WScoped.of_not_hasFvar hCw) hwsCrP
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf cnF rP hopenX hWcrRp
    hbcr hLcr
  have hspX : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) xFvsP (xs.drop rP) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_drop]; omega) (by omega) ?_
    intro j v hjv
    rw [List.getElem?_drop] at hjv
    show xs.getD (rP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsX : ∀ a ∈ xFvsP, WScoped (rP + cnF) a := fun a ha =>
    (hxWf a ha).1
  have hLsX : ∀ a ∈ xFvsP, Expr.LeavesBounded a := fun a ha =>
    (hxWf a ha).2.2
  have hmemX : ∀ (i : Nat) (a : Expr) (v : V),
      (xFvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.drop rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hit : i < cnF := by
      rcases Nat.lt_or_ge i cnF with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hix : i < xFvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvsP[i]? = some fvi :=
      ⟨xFvsP[i]'hix, List.getElem?_eq_getElem hix⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[rP + i]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show rP + i - rP = i from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (rP + i) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape i fvi hfvi
    have hWi : WScoped (rP + i) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWcrD' : WScoped (rP + cnF) crestP := hWcrRp.mono (by omega)
  obtain ⟨hfitXP, hΘX⟩ := self_walk hxInst hspX hwsX hWcrD' hbcr hLcr
    hFcr hAcr hmemX
  obtain ⟨-, hPcrest2Ex⟩ := peel_walk hxInst hspX hwsX hWcrD' hAcr
    ⟨Pcr, hPcr⟩ hmemX
  obtain ⟨Pcr2, hPcr2⟩ := hPcrest2Ex
  have hfitCfullP : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) crest2 :=
    TeleFitI.append hfitC hfitXP
  obtain ⟨hWcrest2, hbcrest2, hAcrest2, hlcrest2⟩ :=
    TeleFitI.rest_wf hfitCfullP hWc hCb hAc
  have hFcrest2 : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hFsC a ha l hla
      · exact hΘX a ha l hla
  have hLcrest2 : Expr.LeavesBounded crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hLsC a ha l hla
      · exact hLsX a ha l hla
  -- ===== S1: the membership packs across the frames =====
  -- the theorem prefix: memberships in the renamed member type's
  -- instantiated parameter domains
  obtain ⟨⟨bsTy, restTy⟩, htyStripSome⟩ :=
    Option.isSome_iff_exists.mp htyStrip
  obtain ⟨restTyPre, htyPreStrip⟩ :=
    Expr.stripPis_prefix rP (mI - rP)
      (by rw [show rP + (mI - rP) = mI from by omega]
          exact htyStripSome)
  obtain ⟨⟨dsPubR, restPubR⟩, hinstPubR⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvs.take rP)
        (by rw [hfvsPreLen, htyPreStrip]; rfl))
  have hiaWpre : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvs.take rP)
      (xs.take rP) :=
    InstArgs.of_fvarSpine hspWpre (fun a ha =>
      ⟨hfvsW a (List.mem_of_mem_take ha),
        (hfvsWf a (List.mem_of_mem_take ha)).2.1⟩)
  have hpackR := fit_mem_frames (φ := ψ) htyw htyb htyPreStrip
    hinstPubR hfvsPreLen hiaWpre hfitP
  have hstripRenPre := stripPis_renameConsts (f := f) rP htyPreStrip
  have hmemR : ∀ (k : Nat) (a : Expr) (v : V), rdoms[k]? = some a →
      (xs.take rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkr : k < rP := by
      rcases Nat.lt_or_ge k rP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hrinst, hfvsPreLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, (bsTy.take rP)[k]? = some b := by
      have := Expr.stripPis_length rP htyPreStrip
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis (fvs.take rP) hrinst
      (by rw [hfvsPreLen]; exact hstripRenPre)
    obtain ⟨-, hdsPub⟩ := instPisAt_stripPis (fvs.take rP) hinstPubR
      (by rw [hfvsPreLen]; exact htyPreStrip)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hb]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hpackR k _ v (hdsPub k b hb) hv
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvs.take rP).take k, ∃ i n t,
        x = .fvar i n t := fun x hx =>
      hfvsShapes x (List.mem_of_mem_take (List.mem_of_mem_take hx))
    rw [interp_instSeq_ren hro hshapes]
    exact hBi
  -- the constructor telescope: memberships in the renamed constructor
  -- type's instantiated domains (parameters and fields)
  obtain ⟨⟨bsC, cbody⟩, hCstripPair⟩ :=
    Option.isSome_iff_exists.mp hCstripSome
  obtain ⟨⟨dsPubC, restPubC⟩, hinstPubC⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvs.take cnP ++ fvs.drop rP)
        (by rw [hfvsCLen, hCstripPair]; rfl))
  have hiaWctor : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvs.take cnP ++ fvs.drop rP) (xs.take cnP ++ xs.drop rP) :=
    InstArgs.of_fvarSpine hspWctor (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact ⟨hfvsW a (List.mem_of_mem_take ha'),
          (hfvsWf a (List.mem_of_mem_take ha')).2.1⟩
      · exact ⟨hfvsW a (List.mem_of_mem_drop ha'),
          (hfvsWf a (List.mem_of_mem_drop ha')).2.1⟩)
  have hpackCF := fit_mem_frames (φ := ψ) hCw hCb hCstripPair
    hinstPubC hfvsCLen hiaWctor hfitCfullP
  have hstripRenC := stripPis_renameConsts (f := f) (cnP + cnF)
    hCstripPair
  have hmemC : ∀ (k : Nat) (a : Expr) (v : V), cdoms[k]? = some a →
      (xs.take cnP ++ xs.drop rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkc : k < cnP + cnF := by
      rcases Nat.lt_or_ge k (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hcinst, hfvsCLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, bsC[k]? = some b := by
      have := Expr.stripPis_length (cnP + cnF) hCstripPair
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis
      (fvs.take cnP ++ fvs.drop rP) hcinst
      (by rw [hfvsCLen]; exact hstripRenC)
    obtain ⟨-, hdsPub⟩ := instPisAt_stripPis
      (fvs.take cnP ++ fvs.drop rP) hinstPubC
      (by rw [hfvsCLen]; exact hCstripPair)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hb]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hpackCF k _ v (hdsPub k b hb) hv
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvs.take cnP ++ fvs.drop rP).take k,
        ∃ i n t, x = .fvar i n t := by
      intro x hx
      have hx' := List.mem_of_mem_take hx
      rcases List.mem_append.mp hx' with hx'' | hx''
      · exact hfvsShapes x (List.mem_of_mem_take hx'')
      · exact hfvsShapes x (List.mem_of_mem_drop hx'')
    rw [interp_instSeq_ren hro hshapes]
    exact hBi
  -- ===== S2: the theorem walk =====
  have hfvsInst' : Expr.instPisAt
      (fvs.take rP ++ fvs.drop rP) cvt.type =
      some (fvs.map Expr.fvarTypeD, tbody) := by
    rw [List.take_append_drop]
    exact hfvsInst
  obtain ⟨dsS1, midS, dsS2, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append _ _ hfvsInst'
  have hdsS1len : dsS1.length = rP := by
    rw [instPisAt_length _ hopS1, hfvsPreLen]
  obtain ⟨hdsS1eq, hdsS2eq⟩ : dsS1 = (fvs.take rP).map
      Expr.fvarTypeD ∧ dsS2 = (fvs.drop rP).map
      Expr.fvarTypeD := by
    have hmap : fvs.map Expr.fvarTypeD =
        (fvs.take rP).map Expr.fvarTypeD ++
        (fvs.drop rP).map Expr.fvarTypeD := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap] at hdsSplit
    exact List.append_inj hdsSplit.symm (by
      rw [hdsS1len, List.length_map, hfvsPreLen])
  subst hdsS1eq hdsS2eq
  have hWS : WScoped (rP + cnF) cvt.type :=
    WScoped.of_not_hasFvar hSw
  have hLS : Expr.LeavesBounded cvt.type :=
    Expr.LeavesBounded.of_not_hasFvar hSw
  have hFS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    FvarsOk.of_not_hasFvar hSw
  have hAS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    AnnotOk.closed_invariant hSw _ _ (hthm_annot ψ)
  obtain ⟨P, hPc, hPmem⟩ := hthm_mem ψ
  have hPI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type = some P := by
    rw [interp_closed_invariant hSw _ _]
    exact hPc
  -- the renamed member type's invariants
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  have hAtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) :=
    AnnotOk.closed_invariant htyRw _ _
      (AnnotOk.renameConsts hro tyA 0 (rho0 V) hAty)
  obtain ⟨Tty, hTtyc⟩ := hIty
  have hItyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) =
      some TR := by
    refine ⟨Tty, ?_⟩
    rw [interp_closed_invariant htyRw _ _]
    show interpClosed V m₀.val env₀ _ (tyA.renameConsts f) = some Tty
    unfold interpClosed
    rw [interp_renameConsts hro tyA 0 (rho0 V)]
    exact hTtyc
  -- stage 1: the prefix walk
  obtain ⟨hfitS1, hfitR1, hΘpre⟩ := pi_walk m₀ F hopS1 hrinst hdePre
    hspWpre (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    hWS hSb hLS hFS hAS
    (WScoped.of_not_hasFvar htyRw) htyRb
    (Expr.LeavesBounded.of_not_hasFvar htyRw)
    (FvarsOk.of_not_hasFvar htyRw) hAtyR
    ⟨P, hPI⟩ hItyR hmemR
  obtain ⟨Qmid, hQmidI, hQmidMem, hAmidS⟩ :=
    TeleFitI.elim hfitS1 hAS hPI hPmem
  obtain ⟨hWmidS, hbmidS, -, hleavesMidS⟩ :=
    TeleFitI.rest_wf hfitS1 hWS hSb hAS
  have hFmidS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact hΘpre a ha l hla
  have hLmidS : Expr.LeavesBounded midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- the renamed constructor's parameter walk to its mid residual
  obtain ⟨cdomsA, midC, cdomsB, hopC1, hopC2, hcdomsSplit⟩ :=
    instPisAt_append _ _ hcinst
  have hcdomsAlen : cdomsA.length = cnP := by
    rw [instPisAt_length _ hopC1, List.length_take, hfvsLen]
    omega
  have hcdomsBeq : cdoms.drop cnP = cdomsB := by
    rw [hcdomsSplit, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hCRw : (cvj.type.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]; exact hCw
  have hCRb : (cvj.type.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]; exact hCb
  have hACtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f) :=
    AnnotOk.closed_invariant hCRw _ _
      (AnnotOk.renameConsts hro cvj.type 0 (rho0 V) hACty)
  have hICtyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f) = some TR := by
    obtain ⟨TC, hTCc⟩ := hICty
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hCRw _ _]
    show interpClosed V m₀.val env₀ _ (cvj.type.renameConsts f) = some TC
    unfold interpClosed
    rw [interp_renameConsts hro cvj.type 0 (rho0 V)]
    exact hTCc
  obtain ⟨hfitC1, hImidC⟩ := peel_walk hopC1 hspWctorPre
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    (WScoped.of_not_hasFvar hCRw) hACtyR hICtyR
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      refine hmemC k a v ?_ ?_
      · rw [hcdomsSplit, List.getElem?_append_left (by omega)]
        exact ha
      · rw [List.getElem?_append_left
          (by rw [List.length_take]; omega)]
        exact hv)
  obtain ⟨hWmidC, hbmidC, hAmidC, hleavesMidC⟩ :=
    TeleFitI.rest_wf hfitC1 (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFmidC : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · refine hΘpre a ?_ l hla
      have heq : fvs.take cnP = (fvs.take rP).take cnP := by
        rw [List.take_take, Nat.min_eq_left hplainLe]
      rw [heq] at ha
      exact List.mem_of_mem_take ha
  have hLmidC : Expr.LeavesBounded midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- stage 2: the field walk
  obtain ⟨hfitS2, hfitR2, hΘx⟩ := pi_walk m₀ F hopS2
    (by rw [← hcdomsBeq] at hopC2; exact hopC2)
    hdeFld
    hspWdrop (fun a ha => hfvsW a (List.mem_of_mem_drop ha))
    hWmidS hbmidS hLmidS hFmidS hAmidS
    hWmidC hbmidC hLmidC hFmidC hAmidC
    ⟨Qmid, hQmidI⟩ hImidC
    (fun k a v ha hv => by
      refine hmemC (cnP + k) a v ?_ ?_
      · rw [List.getElem?_drop] at ha
        exact ha
      · rw [List.getElem?_append_right
          (by rw [List.length_take]; omega)]
        rw [List.length_take,
          show cnP + k - min cnP xs.length = k from by omega]
        exact hv)
  obtain ⟨Q, hQI, hQmem0, hAtbody⟩ :=
    TeleFitI.elim hfitS2 hAmidS hQmidI hQmidMem
  have hQmem : SpineFold V (m₀.val thmName ψ) xs ∈ˢ Q := by
    have h0 : SpineFold V (m₀.val thmName ψ)
        (xs.take rP ++ xs.drop rP) ∈ˢ Q := by
      rw [SpineFold_append]
      exact hQmem0
    rwa [List.take_append_drop] at h0
  -- ===== S3: the Eq collapse =====
  have htbodyEq : tbody = Expr.mkAppN (.const eqName [ℓA])
      [αS, lhsS, rhsS] := by
    have h0 := Expr.mkAppN_getApp tbody
    rw [hheadEq, hargs3] at h0
    exact h0.symm
  rw [htbodyEq] at hQI hAtbody
  obtain ⟨-, hcompsA, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hAtbody
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hQeq : Q = SpineFold V veq [vα, vl, vr] := by
    rw [hfoldQ] at hQI
    exact Option.some.inj hQI |>.symm
  have hveq : veq = eqVal V (Level.substFn ψ [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn ψ [uN] [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : Q = eqv vl vr := by
    rw [hQeq, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn ψ [uN] [ℓA]))
        [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hvlvr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- ===== S4: decompose the statement's left side =====
  have hlhsEq : lhsS = Expr.mkAppN (.const (f R) (lps.map .param))
      lhsS.getAppArgs := by
    have h0 := Expr.mkAppN_getApp lhsS
    rw [hlhead] at h0
    exact h0.symm
  have hAlhs : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    hcompsA lhsS (by simp)
  rw [hlhsEq] at hAlhs
  obtain ⟨-, hlargsA, vhead, lvals, hheadI, hspL, hchainL, hfoldL⟩ :=
    annotOk_spine_inv _ (.const (f R) (lps.map .param))
      (by
        intro h0
        rw [h0] at hlarity
        exact nomatch hlarity) hAlhs
  have hvlfold : vl = SpineFold V vhead lvals := by
    rw [← hlhsEq] at hfoldL
    rw [hfoldL] at hil
    exact Option.some.inj hil |>.symm
  -- the head is the recursor's value
  have hsubstψ : Level.substFn ψ lps (lps.map .param) = ψ :=
    funext (fun p => Level.substFn_map_param)
  have hcRi : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const (f R) (lps.map .param)) = some (m₀.val R ψ) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    rw [hsubstψ, hro.2.2 R]
  have hvhead : vhead = m₀.val R ψ := by
    rw [hcRi] at hheadI
    exact Option.some.inj hheadI |>.symm
  -- the equation body's component facts
  obtain ⟨hWtbody0, hbtbody0, htbodyL0⟩ := htbodyWf
  have hlhsMem : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWlhs : WScoped (rP + cnF) lhsS := by
    have h0 := hWtbody0.getAppArgs lhsS hlhsMem
    rwa [Nat.zero_add] at h0
  have hblhs : lhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hlhsMem
  obtain ⟨-, -, -, hleavesTbody⟩ := TeleFitI.rest_wf hfitS2 hWmidS hbmidS
    hAmidS
  have hFtbody : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tbody := by
    intro l hl
    rcases hleavesTbody l hl with hl' | ⟨a, ha, hla⟩
    · exact hFmidS l hl'
    · exact hΘx a ha l hla
  have hFlhs : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hlhsMem l hl)
      hFtbody
  have hLlhs : Expr.LeavesBounded lhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hlhsMem l hl)
  have hrhsMem : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWrhsS : WScoped (rP + cnF) rhsS := by
    have h0 := hWtbody0.getAppArgs rhsS hrhsMem
    rwa [Nat.zero_add] at h0
  have hbrhsS : rhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hrhsMem
  have hFrhsS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hrhsMem l hl)
      hFtbody
  have hLrhsS : Expr.LeavesBounded rhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hrhsMem l hl)
  have hArhsS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    hcompsA rhsS (by simp)
  -- the full renamed constructor fit and `cres`'s facts
  have hfitCfull : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f)
      (fvs.take cnP ++ fvs.drop rP) (xs.take cnP ++ xs.drop rP)
      cres := by
    exact TeleFitI.append hfitC1 hfitR2
  obtain ⟨hWcres, hbcres, hAcres, hleavesCres⟩ :=
    TeleFitI.rest_wf hfitCfull (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFcres : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · refine hΘpre a ?_ l hla
        have heq : fvs.take cnP = (fvs.take rP).take cnP := by
          rw [List.take_take, Nat.min_eq_left hplainLe]
        rw [heq] at ha
        exact List.mem_of_mem_take ha
      · exact hΘx a ha l hla
  have hLcres : Expr.LeavesBounded cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
      · exact (hfvsWf a (List.mem_of_mem_drop ha)).2.2 l hla
  -- the constructor body and both residuals' argument spines
  have hcbodyNF : cbody.hasFvar = false :=
    stripPis_body_hasFvar _ hCstripPair hCw
  have hcbodyBnd : cbody.looseBVarsBounded (cnP + cnF) = true := by
    have h0 := stripPis_body_bounded _ hCstripPair hCb
    simpa using h0
  have hcspine : cbody = Expr.mkAppN cbody.getAppFn cbody.getAppArgs :=
    (Expr.mkAppN_getApp cbody).symm
  have hfvsCShapes : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsShapes a (List.mem_of_mem_take ha)
    · exact hfvsShapes a (List.mem_of_mem_drop ha)
  obtain ⟨hcresEq0, -⟩ := instPisAt_stripPis
    (fvs.take cnP ++ fvs.drop rP) hcinst
    (by rw [hfvsCLen]; exact hstripRenC)
  have hcresEq' : cres = instSeq (fvs.take cnP ++ fvs.drop rP)
      (cnP + cnF - 1) (cbody.renameConsts f) := by
    rw [hcresEq0, hfvsCLen]
  have hheadRenNotApp : ∀ f' a',
      cbody.getAppFn.renameConsts f ≠ .app f' a' := by
    intro f' a' hcon
    cases hfn : cbody.getAppFn with
    | app g b => exact getAppFn_not_app cbody g b hfn
    | bvar _ => rw [hfn] at hcon; exact nomatch hcon
    | fvar _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | sort _ => rw [hfn] at hcon; exact nomatch hcon
    | const _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lam _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | forallE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | letE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lit _ => rw [hfn] at hcon; exact nomatch hcon
    | proj _ _ _ => rw [hfn] at hcon; exact nomatch hcon
  have hcresArgs : cres.getAppArgs = cbody.getAppArgs.map
      (fun e => instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (e.renameConsts f)) := by
    rw [hcresEq']
    calc (instSeq (fvs.take cnP ++ fvs.drop rP)
          (cnP + cnF - 1) (cbody.renameConsts f)).getAppArgs
        = (instSeq (fvs.take cnP ++ fvs.drop rP)
            (cnP + cnF - 1)
            (Expr.mkAppN (cbody.getAppFn.renameConsts f)
              (cbody.getAppArgs.map (·.renameConsts f)))).getAppArgs := by
          rw [← renameConsts_mkAppN, Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq (fvs.take cnP ++ fvs.drop rP)
            (cnP + cnF - 1) (cbody.getAppFn.renameConsts f))
            ((cbody.getAppArgs.map (·.renameConsts f)).map
              (instSeq (fvs.take cnP ++ fvs.drop rP)
                (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app _ _ hfvsCShapes hheadRenNotApp),
            List.map_map]
          simp [Function.comp]
  -- the public composed constructor walk and `crest2`'s spine
  have hpubC : Expr.instPisAt (fvsP.take cnP ++ xFvsP) cvj.type =
      some (cdomsP ++ xFvsP.map Expr.fvarTypeD, crest2) :=
    instPisAt_append_of (fvsP.take cnP) hcinstP hxInst
  have hfvsPXLen : (fvsP.take cnP ++ xFvsP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, hfvsPLen, hxLen]
    omega
  have hfvsPXShapes : ∀ a ∈ fvsP.take cnP ++ xFvsP,
      ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem
        (List.mem_of_mem_take ha)
      obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
      exact ⟨0 + j, nm, _, hsh⟩
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hxShape j a hja
      exact ⟨rP + j, nm, _, hsh⟩
  obtain ⟨hcrest2Eq0, -⟩ := instPisAt_stripPis
    (fvsP.take cnP ++ xFvsP) hpubC
    (by rw [hfvsPXLen]; exact hCstripPair)
  have hcrest2Eq : crest2 = instSeq (fvsP.take cnP ++ xFvsP)
      (cnP + cnF - 1) cbody := by
    rw [hcrest2Eq0, hfvsPXLen]
  have hcrest2Args : crest2.getAppArgs = cbody.getAppArgs.map
      (fun e => instSeq (fvsP.take cnP ++ xFvsP)
        (cnP + cnF - 1) e) := by
    rw [hcrest2Eq]
    calc (instSeq (fvsP.take cnP ++ xFvsP)
          (cnP + cnF - 1) cbody).getAppArgs
        = (instSeq (fvsP.take cnP ++ xFvsP)
            (cnP + cnF - 1)
            (Expr.mkAppN cbody.getAppFn cbody.getAppArgs)).getAppArgs := by
          rw [Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq (fvsP.take cnP ++ xFvsP)
            (cnP + cnF - 1) cbody.getAppFn)
            (cbody.getAppArgs.map
              (instSeq (fvsP.take cnP ++ xFvsP)
                (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app _ _ hfvsPXShapes
                (getAppFn_not_app _))]
          rfl
  -- ===== S4b: the argument values =====
  have hlvalsLen : lvals.length = mI + 1 := by
    rw [InterpSpine.length hspL, hlarity]
  obtain ⟨lastE, hlargsDecomp, hlastE⟩ :=
    take_concat_of_length (l := lhsS.getAppArgs) (n := mI) hlarity
  obtain ⟨vlast, hlvalsDecomp, hvlast⟩ :=
    take_concat_of_length (l := lvals) (n := mI) hlvalsLen
  have hlastEmaj : lastE =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP) := by
    have h0 : lhsS.getAppArgs.getLastD (.bvar 0) = lastE := by
      conv => lhs; rw [hlargsDecomp]
      rw [List.getLastD_concat]
    rw [← h0, hmaj]
  -- the prefix values are the frame values
  have hcbodyArgsLen : cbody.getAppArgs.length = cnP + (mI - rP) := by
    have h0 : cres.getAppArgs.length = cbody.getAppArgs.length := by
      rw [hcresArgs, List.length_map]
    rw [← h0, hclen]
  have hpreValsEq : lvals.take rP = xs.take rP := by
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i rP with hi | hi
    · obtain ⟨ei, hei⟩ : ∃ e, lhsS.getAppArgs[i]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨vi, hvi⟩ : ∃ v, lvals[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hint := InterpSpine.pointwise hspL i hei hvi
      have heifv : fvs[i]? = some ei := by
        have h0 := congrArg (·[i]?) hlpre
        simp only [List.getElem?_take_of_lt hi] at h0
        rw [← h0, hei]
      obtain ⟨nmi, hshi⟩ := hfvsShape i ei heifv
      rw [Nat.zero_add] at hshi
      rw [hshi] at hint
      simp only [interpExpr] at hint
      have hvix : vi = xs.getD i SetTheory.empty :=
        (Option.some.inj hint).symm
      rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
        hvi, hvix, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (l := xs) (i := i) (by omega)]
      rfl
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by rw [List.length_take]; omega)]
  -- `cres`'s per-argument facts
  have hcresArgW : ∀ e ∈ cres.getAppArgs, WScoped (rP + cnF) e :=
    fun e he => hWcres.getAppArgs e he
  have hcresArgB : ∀ e ∈ cres.getAppArgs,
      e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hbcres e he
  have hcresArgL : ∀ e ∈ cres.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLcres l (fvarLeaves_getAppArgs he l hl)
  have hcresArgF : ∀ e ∈ cres.getAppArgs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFcres
  have hcresSpineInv : cres.getAppArgs ≠ [] →
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN cres.getAppFn cres.getAppArgs) := by
    intro _
    rw [Expr.mkAppN_getApp]
    exact hAcres
  have hcresArgA : ∀ e ∈ cres.getAppArgs,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e := by
    intro e he
    have hne : cres.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ cres.getAppFn hne
      (hcresSpineInv hne)
    exact hargsA e he
  have hcresArgI : ∀ e ∈ cres.getAppArgs,
      ∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e = some w := by
    intro e he
    have hne : cres.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, -, vf, cvals, -, hspCres, -, -⟩ :=
      annotOk_spine_inv _ cres.getAppFn hne (hcresSpineInv hne)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem he
    obtain ⟨w, hw⟩ : ∃ w, cvals[j]? = some w := by
      have hlen := InterpSpine.length hspCres
      refine ⟨_, List.getElem?_eq_getElem ?_⟩
      rw [hlen]
      rcases Nat.lt_or_ge j cres.getAppArgs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj
        exact nomatch hj
    exact ⟨w, InterpSpine.pointwise hspCres j hj hw⟩
  -- lhsS's per-argument facts
  have hlargsW : ∀ e ∈ lhsS.getAppArgs, WScoped (rP + cnF) e :=
    fun e he => hWlhs.getAppArgs e he
  have hlargsB : ∀ e ∈ lhsS.getAppArgs, e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hblhs e he
  have hlargsL : ∀ e ∈ lhsS.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLlhs l (fvarLeaves_getAppArgs he l hl)
  have hlargsF : ∀ e ∈ lhsS.getAppArgs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFlhs
  -- the index values: statement's equal the public residual's
  have hpubSpine : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) :=
    FvarSpine.append hspC hspX
  have hiaPub : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) :=
    InstArgs.of_fvarSpine hpubSpine (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact ⟨hwsP a (List.mem_of_mem_take ha'),
          (hfvsPWf a (List.mem_of_mem_take ha')).2.1⟩
      · exact ⟨(hxWf a ha').1, (hxWf a ha').2.1⟩)
  have hidxVal : ∀ (j : Nat) (e2 : Expr) (v : V),
      (crest2.getAppArgs.drop cnP)[j]? = some e2 →
      (lvals.drop rP)[j]? = some v → j < mI - rP →
      interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e2 = some v := by
    intro j e2 v he2 hv hjlt
    -- the statement-side index argument and its value
    obtain ⟨eS, heS⟩ : ∃ e, lhsS.getAppArgs[rP + j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [List.getElem?_drop] at hv
    have hintS := InterpSpine.pointwise hspL (rP + j) heS hv
    -- the renamed residual's index argument
    obtain ⟨carg, hcarg⟩ : ∃ c, cbody.getAppArgs[cnP + j]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have heR : cres.getAppArgs[cnP + j]? = some
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          (carg.renameConsts f)) := by
      rw [hcresArgs, List.getElem?_map, hcarg]
      rfl
    have he2' : e2 = instSeq (fvsP.take cnP ++ xFvsP)
        (cnP + cnF - 1) carg := by
      rw [List.getElem?_drop, hcrest2Args, List.getElem?_map,
        hcarg] at he2
      exact (Option.some.inj he2).symm
    -- the kernel index pin identifies the two interpretations
    have hdej := DefEqListOk.pointwise hdeIdx j
      (a := eS) (b := instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (carg.renameConsts f))
      (by
        rw [List.getElem?_take_of_lt hjlt, List.getElem?_drop]
        exact heS)
      (by
        rw [List.getElem?_drop]
        exact heR)
    have heSmem : eS ∈ lhsS.getAppArgs := List.mem_of_getElem? heS
    have heRmem : instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (carg.renameConsts f) ∈ cres.getAppArgs :=
      List.mem_of_getElem? heR
    obtain ⟨wR, hwR⟩ := hcresArgI _ heRmem
    have hveq := isDefEqCore_sound m₀ F hdej
      (hlargsW eS heSmem) (hcresArgW _ heRmem)
      (hlargsB eS heSmem) (hcresArgB _ heRmem)
      (hlargsL eS heSmem) (hcresArgL _ heRmem)
      (hlargsF eS heSmem) (hcresArgF _ heRmem)
      (hlargsA eS heSmem) (hcresArgA _ heRmem)
      hintS hwR
    -- cross to the public residual's argument
    have hcargNF : carg.hasFvar = false :=
      hasFvar_getAppArgs hcbodyNF _ (List.mem_of_getElem? hcarg)
    have hcargBnd : carg.looseBVarsBounded (cnP + cnF) = true :=
      looseBVarsBounded_getAppArgs hcbodyBnd _
        (List.mem_of_getElem? hcarg)
    have hren : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          (carg.renameConsts f)) =
        interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          carg) :=
      interp_instSeq_ren hro hfvsCShapes
    have hframes : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP)
          ((fvs.take cnP ++ fvs.drop rP).length - 1) carg) =
        interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvsP.take cnP ++ xFvsP)
          ((fvsP.take cnP ++ xFvsP).length - 1) carg) :=
      interp_instSeq_frames hiaWctor hiaPub hcargNF
        (by rw [hfvsCLen]; exact hcargBnd)
    rw [hfvsCLen] at hframes
    rw [hfvsPXLen] at hframes
    rw [he2', ← hframes, ← hren, hwR]
    exact congrArg some hveq.symm
  -- ===== S4c: the major value =====
  have hsubstψC : Level.substFn ψ cvj.levelParams
      (cvj.levelParams.map .param) = ψ :=
    funext (fun p => Level.substFn_map_param)
  have hcCi : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const (f ctor) (cvj.levelParams.map .param)) =
      some (m₀.val ctor ψ) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hCmlps]; simp)]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from
      hCmlps]
    rw [hsubstψC, hro.2.2 ctor]
  have hcCpubI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const ctor (cvj.levelParams.map .param)) =
      some (m₀.val ctor ψ) := by
    simp only [interpExpr, hfC]
    rw [if_pos (by rw [hClps]; simp)]
    rw [show ciC.toConstantVal.levelParams = cvj.levelParams from
      hClps]
    rw [hsubstψC]
  have hctorSpineI : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvs.take cnP ++ fvs.drop rP) (xs.take cnP ++ xs.drop rP) :=
    InterpSpine_of_FvarSpine hspWctor
  have hmajI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lastE = some vlast :=
    InterpSpine.pointwise hspL mI hlastE hvlast
  have hvlastEq : vlast = SpineFold V (m₀.val ctor ψ)
      (xs.take cnP ++ xs.drop rP) := by
    rw [hlastEmaj] at hmajI
    rw [interp_mkAppN _ _ hcCi hctorSpineI] at hmajI
    exact (Option.some.inj hmajI).symm
  have hpubCtorSpineI : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) :=
    InterpSpine_of_FvarSpine hpubSpine
  have hctorAppI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
        (fvsP.take cnP ++ xFvsP)) = some vlast := by
    rw [interp_mkAppN _ _ hcCpubI hpubCtorSpineI]
    exact congrArg some hvlastEq.symm
  -- ===== S4d: the canonical body's spine =====
  have hseg1 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (lvals.take rP) := by
    rw [hpreValsEq]
    exact InterpSpine_of_FvarSpine hspP
  have hcrest2ArgsLen : crest2.getAppArgs.length = cnP + (mI - rP) := by
    rw [hcrest2Args, List.length_map, hcbodyArgsLen]
  have hseg2 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (crest2.getAppArgs.drop cnP)
      ((lvals.drop rP).take (mI - rP)) := by
    refine InterpSpine.of_pointwise ?_ ?_
    · rw [List.length_drop, hcrest2ArgsLen, List.length_take,
        List.length_drop, hlvalsLen]
      omega
    · intro j e v he hv
      have hjlt : j < mI - rP := by
        rcases Nat.lt_or_ge j (mI - rP) with h | h
        · exact h
        · rw [List.getElem?_eq_none
            (by rw [List.length_take]; omega)] at hv
          exact nomatch hv
      rw [List.getElem?_take_of_lt hjlt] at hv
      exact hidxVal j e v he hv hjlt
  have hseg3 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
        (fvsP.take cnP ++ xFvsP)] [vlast] := ⟨hctorAppI, trivial⟩
  have hspB : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP ++ crest2.getAppArgs.drop cnP ++
        [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
          (fvsP.take cnP ++ xFvsP)])
      (lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast]) :=
    InterpSpine.append (InterpSpine.append hseg1 hseg2) hseg3
  have hlvalsRebuild : lvals =
      lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast] := by
    conv =>
      lhs
      rw [hlvalsDecomp, show mI = rP + (mI - rP) from by omega,
        List.take_add]
  have hbLheadI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const R (lps.map .param)) = some (m₀.val R ψ) := by
    simp only [interpExpr, hfR]
    rw [if_pos (by rw [hRlps]; simp)]
    rw [show ciR.toConstantVal.levelParams = lps from hRlps]
    rw [hsubstψ]
  -- ===== S4e: the canonical body's truthful annotations =====
  have hAfvsP : ∀ a ∈ fvsP,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
    rw [hsh]
    simp [AnnotOk]
  have hAxFvs : ∀ a ∈ xFvsP,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, hsh⟩ := hxShape j a hja
    rw [hsh]
    simp [AnnotOk]
  have hcrest2SpineA : crest2.getAppArgs ≠ [] →
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN crest2.getAppFn crest2.getAppArgs) := by
    intro _
    rw [Expr.mkAppN_getApp]
    exact hAcrest2
  have hcrest2ArgA : ∀ e ∈ crest2.getAppArgs,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e := by
    intro e he
    have hne : crest2.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ crest2.getAppFn hne
      (hcrest2SpineA hne)
    exact hargsA e he
  -- the constructor value's typing chain, transferred from the
  -- statement's major
  have hAlastE : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) := by
    have h0 := hlargsA lastE (List.mem_of_getElem? hlastE)
    rwa [hlastEmaj] at h0
  have hchainCtor : ChainSlots V (m₀.val ctor ψ)
      (xs.take cnP ++ xs.drop rP) := by
    cases hlist : fvs.take cnP ++ fvs.drop rP with
    | nil =>
      have hvals0 : xs.take cnP ++ xs.drop rP = [] := by
        have h0 := hfvsCLen
        rw [hlist] at h0
        simp only [List.length_nil] at h0
        have hcnP : cnP = 0 := by omega
        have hcnF : cnF = 0 := by omega
        subst hcnP
        rw [List.take_zero, List.nil_append,
          List.drop_eq_nil_of_le (by omega)]
      rw [hvals0]
      trivial
    | cons c0 cr =>
      have hne : fvs.take cnP ++ fvs.drop rP ≠ [] := by
        rw [hlist]
        simp
      obtain ⟨-, -, vf, cvals, hvf, hspCv, hchainCv, -⟩ :=
        annotOk_spine_inv _
          (.const (f ctor) (cvj.levelParams.map .param)) hne hAlastE
      have hvfeq : vf = m₀.val ctor ψ := by
        rw [hcCi] at hvf
        exact (Option.some.inj hvf).symm
      have hcveq : cvals = xs.take cnP ++ xs.drop rP := by
        have h1 := InterpSpine.mapM_eq hspCv
        have h2 := InterpSpine.mapM_eq hctorSpineI
        rw [h1] at h2
        exact Option.some.inj h2
      rw [← hvfeq, ← hcveq]
      exact hchainCv
  obtain ⟨hActorApp, -⟩ := annotOk_spine (fvsP.take cnP ++ xFvsP)
    (.const ctor (cvj.levelParams.map .param))
    (by simp [AnnotOk]) hcCpubI
    (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact hAfvsP a (List.mem_of_mem_take ha')
      · exact hAxFvs a ha')
    hpubCtorSpineI hchainCtor
  -- assemble
  have hchainBL : ChainSlots V (m₀.val R ψ)
      (lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast]) := by
    rw [← hlvalsRebuild, ← hvhead]
    exact hchainL
  obtain ⟨hAbL, hbLI⟩ := annotOk_spine
    (fvsP ++ crest2.getAppArgs.drop cnP ++
      [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
        (fvsP.take cnP ++ xFvsP)])
    (.const R (lps.map .param))
    (by simp [AnnotOk]) hbLheadI
    (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · rcases List.mem_append.mp ha' with ha'' | ha''
        · exact hAfvsP a ha''
        · exact hcrest2ArgA a (List.mem_of_mem_drop ha'')
      · rcases List.mem_singleton.mp ha' with rfl
        exact hActorApp)
    hspB hchainBL
  have hbLvl : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const R (lps.map .param))
        (fvsP ++ crest2.getAppArgs.drop cnP ++
          [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
            (fvsP.take cnP ++ xFvsP)])) = some vl := by
    rw [hbLI, hvlfold, hvhead]
    exact congrArg some (congrArg _ hlvalsRebuild.symm)
  -- ===== S5: the right side is the applied rule =====
  have hWapp : ∀ (zs : List Expr) (h : Expr),
      WScoped (rP + cnF) h →
      (∀ x ∈ zs, WScoped (rP + cnF) x) →
      WScoped (rP + cnF) (Expr.mkAppN h zs) := by
    intro zs
    induction zs with
    | nil => intro h hh _; exact hh
    | cons x zs ih =>
      intro h hh hxs
      show WScoped _ (Expr.mkAppN (.app h x) zs)
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [WScoped]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hbapp : ∀ (zs : List Expr) (h : Expr),
      h.looseBVarsBounded 0 = true →
      (∀ x ∈ zs, x.looseBVarsBounded 0 = true) →
      (Expr.mkAppN h zs).looseBVarsBounded 0 = true := by
    intro zs
    induction zs with
    | nil => intro h hh _; exact hh
    | cons x zs ih =>
      intro h hh hxs
      show (Expr.mkAppN (.app h x) zs).looseBVarsBounded 0 = true
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hlapp : ∀ (zs : List Expr) (h : Expr) {l},
      l ∈ (Expr.mkAppN h zs).fvarLeaves →
      l ∈ h.fvarLeaves ∨ ∃ x ∈ zs, l ∈ x.fvarLeaves := by
    intro zs
    induction zs with
    | nil => intro h l hl; exact Or.inl hl
    | cons x zs ih =>
      intro h l hl
      rcases ih (.app h x) hl with hl' | ⟨y, hy, hly⟩
      · simp only [fvarLeaves, List.mem_append] at hl'
        rcases hl' with hl' | hl'
        · exact Or.inl hl'
        · exact Or.inr ⟨x, List.mem_cons_self, hl'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩
  -- the rule tower's walk at the public frame
  have hspPX : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
    have h := FvarSpine.append hspP hspX
    rwa [List.take_append_drop] at h
  have hWfull : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hwsP a ha
    · exact hwsX a ha
  have hΘfull : ∀ a ∈ fvsP ++ xFvsP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX a ha
  have hLfull : ∀ a ∈ fvsP ++ xFvsP, Expr.LeavesBounded a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact hLsX a ha
  have hArhsW : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ hArhs
  obtain ⟨L0, hL0c⟩ := hIrhs
  have hL0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  have hfitLam := lam_walk m₀ F hlinst hdeLam hspPX hWfull hΘfull
    hLfull (WScoped.of_not_hasFvar hrhsw) hrhsb
    (Expr.LeavesBounded.of_not_hasFvar hrhsw)
    (FvarsOk.of_not_hasFvar hrhsw) hArhsW ⟨L0, hL0⟩
  obtain ⟨Bf, hBfI, hBfold, hchainL2⟩ := TeleFitLam.fold hfitLam
    hArhsW hL0
  -- the applied renamed rule at the theorem frame
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hrhsw
  have hArhsRen : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (rhsA.renameConsts f) :=
    AnnotOk.closed_invariant hrhsRw _ _
      (AnnotOk.renameConsts hro rhsA 0 (rho0 V) hArhs)
  have hLren : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (rhsA.renameConsts f) = some L0 := by
    rw [interp_renameConsts hro]
    exact hL0
  have hfvsA : ∀ x ∈ fvs, AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) x := by
    intro x hx
    obtain ⟨i, n, t, rfl⟩ := hfvsShapes x hx
    simp [AnnotOk]
  obtain ⟨hAappF, hIappF⟩ := annotOk_spine fvs (rhsA.renameConsts f)
    hArhsRen hLren hfvsA (InterpSpine_of_FvarSpine hspW) hchainL2
  -- side conditions for the statement's right side
  have hΘfvs : ∀ a ∈ fvs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    rw [← List.take_append_drop rP fvs] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘpre a ha
    · exact hΘx a ha
  have hWappF : WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) :=
    hWapp fvs _ (WScoped.of_not_hasFvar hrhsRw) hfvsW
  have hbappF : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine hbapp fvs _ ?_ (FvarSpine.bounded hspW)
    rw [looseBVarsBounded_renameConsts]
    exact hrhsb
  have hLappF : Expr.LeavesBounded
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact (hfvsWf x hx).2.2 l hlx
  have hFappF : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact hΘfvs x hx l hlx
  have hvrFold : vr = SpineFold V L0 xs :=
    isDefEqCore_sound m₀ F hdeRhs hWrhsS hWappF hbrhsS hbappF hLrhsS
      hLappF hFrhsS hFappF hArhsS hAappF hir hIappF
  -- ===== S6: conclusion =====
  refine ⟨⟨vl, hbLvl, ?_⟩, hAbL⟩
  intro e hee
  rw [interp_erasedEq hee _ _, hBfI]
  refine congrArg some ?_
  rw [← hBfold, ← hvrFold, ← hvlvr]

set_option maxHeartbeats 1600000 in
/-- The full `RecRulesOk` clause tail of a plain rule, **parametric in
the bottom fact**.  Everything but the bottom is provenance-free: the
canonical decomposition computes from the kernel's own walks
(`ruleLhsParts_frameWf` / `ruleLhsParts_resolve`), the flat stage facts
come from the definitional domain pins (`modeled_stage`), and the
gluing is `TowerOk.of_stages` / `TowerOk.out`.  Both the modeled path
(`modeled_rule_eq_plain`, off the checked `_model.iota_j` theorem) and
the direct one (off the constructed values' fold equations) share
it. -/
theorem rule_eq_of_bottom
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    -- the rule and the stored recursor data
    {r : RecRule} {cv : ConstantVal} {R : Name} {lps : List Name}
    {tyA : Expr} {rP : Nat}
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (hfire : RecRule.fire r = .plain)
    (hrctor : RecRule.ctor r = ctor)
    (hrcp : RecRule.ctorParams r = cnP)
    (hrnf : RecRule.nfields r = cnF)
    (hrrhs : RecRule.rhs r = rhsA)
    (hcvty : cv.type = tyA)
    (hcvlps : cv.levelParams = lps)
    {ciR : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hplainLe : cnP ≤ rP)
    -- kernel kit (public side)
    {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    -- wf and resolution of the stored data
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∀ ψ : Name → Nat, ∃ L,
      interpClosed V m₀.val env₀ ψ rhsA = some L)
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ cvj.type = some T)
    (hTres : cv.type.constsResolve env₀ = true)
    (hCres : cvj.type.constsResolve env₀ = true)
    (Hbot : ∀ (ψ : Name → Nat) (xs : List V), xs.length = rP + cnF →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      (∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
          (fun i => xs.getD i SetTheory.empty)
          (Expr.mkAppN (.const R (lps.map .param))
            (fvsP ++ crest2.getAppArgs.drop cnP ++
              [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
                (fvsP.take cnP ++ xFvsP)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrest →
          interpExpr V m₀.val env₀ ψ (rP + cnF)
            (fun i => xs.getD i SetTheory.empty) e = some w) ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const R (lps.map .param))
          (fvsP ++ crest2.getAppArgs.drop cnP ++
            [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
              (fvsP.take cnP ++ xFvsP)]))) :
    ∃ fvms bL, ruleLhsParts R cv rP r cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = rP + RecRule.nfields r ∧
      (closeLamsAt fvms bL).constsResolve env₀ = true ∧
      ∀ ψ : Name → Nat,
        AnnotOk V m₀.val env₀ ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V m₀.val env₀ ψ (closeLamsAt fvms bL) =
            some Rv ∧
          interpClosed V m₀.val env₀ ψ (RecRule.rhs r) = some Rv := by
  -- spine data
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  have hspineLen : (fvsP ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPLen, hxLen]
  have hshSpine : ∀ a ∈ fvsP ++ xFvsP, ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
      exact ⟨0 + j, nm, _, hsh⟩
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hxShape j a hja
      exact ⟨rP + j, nm, _, hsh⟩
  -- the rule right-hand side's λ-tower shape
  have hstripSome := instLamsAt_stripLams_isSome _ hshSpine hlinst
  rw [hspineLen] at hstripSome
  obtain ⟨⟨rbs, rbody⟩, hstripR⟩ :=
    Option.isSome_iff_exists.mp hstripSome
  -- the canonical decomposition computes
  have hparts : ruleLhsParts R cv rP r cvj =
      some ((fvsP ++ xFvsP).zip (rbs.map (·.2.2)),
        Expr.mkAppN (.const R (cv.levelParams.map .param))
          (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
            [Expr.mkAppN (.const (RecRule.ctor r)
                (cvj.levelParams.map Level.param))
              (fvsP.take (RecRule.ctorParams r) ++ xFvsP)])) := by
    simp only [ruleLhsParts, hcvty, hopenP, hfire, ruleLhsAux, hrcp,
      hcinstP, hrnf, hopenX, hrrhs,
      show rhsA.stripLams (rP + cnF) = some (rbs, rbody) from hstripR]
  refine ⟨_, _, hparts, ?_⟩
  have hpinsVac : ∀ lvls pins, RecRule.fire r = .nested lvls pins →
      ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded rP = true := by
    intro lvls pins hcon
    rw [hfire] at hcon
    exact nomatch hcon
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts
    (by rw [hcvty]; exact htyw) (by rw [hcvty]; exact htyb) hCw hCb
    hpinsVac
  refine ⟨hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts (by rw [hfR]; rfl)
      (by rw [hrctor, hfC]; rfl) hTres hCres
      (fun lvls pins hcon => by
        rw [hfire] at hcon
        exact nomatch hcon)
  -- the semantic clause, per level assignment
  intro ψ
  have hctorPkg := ctor_pkg_plain (xFvsP := xFvsP) m₀ F hopenP htyw
    htyb (hAty ψ) hcinstP hdePars hplainLe hCw hCb (hACty ψ) (hICty ψ)
  have hstage := modeled_stage m₀ F hopenP htyw htyb (hAty ψ) (hIty ψ)
    hopenX hctorPkg hlinst hdeLam hrhsw hrhsb (hArhs ψ) (hIrhs ψ)
  -- frame bookkeeping for the tower recursion
  have hrbsLen : rbs.length = rP + cnF := Expr.stripLams_length _ hstripR
  have hzipFst : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).map Prod.fst =
      fvsP ++ xFvsP :=
    List.map_fst_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hzipSnd : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).map (·.2) =
      rbs.map (·.2.2) :=
    List.map_snd_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hfvmsLen : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).length =
      rP + cnF := by
    rw [List.length_zip, hspineLen, List.length_map, hrbsLen]
    simp
  -- the tower spec from the flat stage facts
  have htower := TowerOk.of_stages (cval := m₀.val) (env := env₀)
    (φ := ψ)
    (bL := Expr.mkAppN (.const R (cv.levelParams.map .param))
      (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
        [Expr.mkAppN (.const (RecRule.ctor r)
            (cvj.levelParams.map Level.param))
          (fvsP.take (RecRule.ctorParams r) ++ xFvsP)]))
    (lrest := lrest)
    (fvms := (fvsP ++ xFvsP).zip (rbs.map (·.2.2)))
    (ldoms := ldoms)
    (Ok := FramePref m₀.val env₀ ψ (fvsP ++ xFvsP))
    (Hty := by
      intro k xs fv m ld hxs hfv hld hOk
      have hfv' : (fvsP ++ xFvsP)[k]? = some fv := by
        have h0 := congrArg (·[k]?) hzipFst
        simp only [List.getElem?_map] at h0
        rw [← h0, hfv]
        rfl
      obtain ⟨A, h1, h2, h3, h4⟩ := hstage k xs fv ld hxs hfv' hld hOk
      exact ⟨A, h1, h2, h3, h4⟩)
    (Hbot := by
      intro xs hxs hOk
      rw [hfvmsLen] at hxs
      have h := Hbot ψ xs hxs hOk
      rw [hfvmsLen, hcvlps, hrcp, hrctor]
      exact h)
    ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))) 0 [] ldoms
    (RecRule.rhs r) (RecRule.rhs r)
    (by rw [Nat.zero_add])
    rfl rfl rfl
    (by
      intro j p hp
      have h0 := congrArg (·[j]?) hzipFst
      simp only [List.getElem?_map] at h0
      have hp1 : (fvsP ++ xFvsP)[j]? = some p.1 := by
        rw [← h0, hp]
        rfl
      rcases Nat.lt_or_ge j rP with hj | hj
      · rw [List.getElem?_append_left (by omega)] at hp1
        obtain ⟨nm, hsh⟩ := hfvsPShape j p.1 hp1
        rw [Nat.zero_add] at hsh
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add]
        exact hsh
      · rw [List.getElem?_append_right (by omega), hfvsPLen] at hp1
        obtain ⟨nm, hsh⟩ := hxShape (j - rP) p.1 hp1
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add, hsh]
        congr 1
        omega)
    (Expr.ErasedEq.rfl _)
    (by
      rw [hzipFst, hrrhs]
      exact hlinst)
    (by
      refine ⟨rbs, rbody, ?_, hzipSnd⟩
      rw [hfvmsLen, hrrhs]
      exact hstripR)
    (fun j v fv hjv _ => nomatch hjv)
  -- canonicalize the empty frame and consume the tower
  have hrho : (fun i => ([] : List V).getD i SetTheory.empty) =
      rho0 V := by
    funext i
    rfl
  rw [hrho] at htower
  obtain ⟨⟨Rv, hL, hR⟩, hAL⟩ := TowerOk.out htower hwf
    (by rw [hrrhs]; exact hArhs ψ)
  exact ⟨hAL, Rv, hL, hR⟩
set_option maxHeartbeats 1600000 in
/-- The full `RecRulesOk` clause tail of a **plain** modeled rule:
the canonical frame/body decomposition exists, is well-formed and
resolves, and at every level assignment the closed tower interprets
equal to the stored right-hand side.  Glues the syntactic halves
(`ruleLhsParts_frameWf` / `ruleLhsParts_resolve`) to the semantic
stage/bottom facts through `TowerOk.of_stages` and `TowerOk.out`. -/
theorem modeled_rule_eq_plain
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    -- the rule and the stored recursor data
    {r : RecRule} {cv : ConstantVal} {R : Name} {lps : List Name}
    {tyA : Expr} {mI rP : Nat}
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    (hfire : RecRule.fire r = .plain)
    (hrctor : RecRule.ctor r = ctor)
    (hrcp : RecRule.ctorParams r = cnP)
    (hrnf : RecRule.nfields r = cnF)
    (hrrhs : RecRule.rhs r = rhsA)
    (hcvty : cv.type = tyA)
    (hcvlps : cv.levelParams = lps)
    -- environment entries
    {ciR cim : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    (hRlps : ciR.toConstantVal.levelParams = lps)
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hClps : ciC.toConstantVal.levelParams = cvj.levelParams)
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ : Name → Nat, m₀.val eqName ψ = eqVal V ψ)
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ cvt.type = some P ∧
      m₀.val thmName ψ ∈ˢ P)
    (hthm_annot : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- kernel kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    (htyStrip : (tyA.stripPis mI).isSome = true)
    (hrPmI : rP ≤ mI)
    (hplainLe : cnP ≤ rP)
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hCstripSome : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take rP)
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- kernel kit (public side)
    {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- wf and resolution of the stored data
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∀ ψ : Name → Nat, ∃ L,
      interpClosed V m₀.val env₀ ψ rhsA = some L)
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ cvj.type = some T)
    (hTres : cv.type.constsResolve env₀ = true)
    (hCres : cvj.type.constsResolve env₀ = true) :
    ∃ fvms bL, ruleLhsParts R cv rP r cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = rP + RecRule.nfields r ∧
      (closeLamsAt fvms bL).constsResolve env₀ = true ∧
      ∀ ψ : Name → Nat,
        AnnotOk V m₀.val env₀ ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V m₀.val env₀ ψ (closeLamsAt fvms bL) =
            some Rv ∧
          interpClosed V m₀.val env₀ ψ (RecRule.rhs r) = some Rv := by
  refine rule_eq_of_bottom m₀ F hfire hrctor hrcp hrnf hrrhs hcvty hcvlps
    hfR hfC hplainLe hopenP hcinstP hdePars hopenX hlinst hdeLam hrhsw
    hrhsb hArhs hIrhs htyw htyb hAty hIty hCw hCb hACty hICty hTres hCres
    ?_
  intro ψ
  exact modeled_bottom_plain m₀ F hro hfR hRlps hfRm hRmlps
    hfCm hCmlps hfC hClps heqfind heqval hthm_mem hthm_annot hSw hSb
    htyStrip hrPmI hplainLe hopen hheadEq hargs3 hlhead hlarity hlpre
    hmaj hCstripSome hcinst hclen hdeIdx hrinst hdePre hdeFld hopenP
    hcinstP hdePars hopenX hlinst hdeLam hdeRhs hrhsw hrhsb (hArhs ψ)
    (hIrhs ψ) htyw htyb (hAty ψ) (hIty ψ) hCw hCb (hACty ψ) (hICty ψ)
    (ψ := ψ)

set_option maxHeartbeats 3200000 in
/-- The bottom fact (`Hbot` of `TowerOk.of_stages`) of a **nested**
modeled rule: as `modeled_bottom_plain`, with the constructor applied
at the stored level instantiations to the stored parameter
instantiations (no index tuple — nested-auxiliary recursors are
index-free), the parameter values flowing through the kernel's typed
pins. -/
theorem modeled_bottom_nested
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat) {ψ : Name → Nat}
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    (hcvp : ConstValParams m₀.val env₀)
    -- the recursor, its public entry and its model
    {R : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    {ciR cim : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    (hRlps : ciR.toConstantVal.levelParams = lps)
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hClps : ciC.toConstantVal.levelParams = cvj.levelParams)
    -- the pinned equality former
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ'' cvt.type = some P ∧
      m₀.val thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- the stored instantiations and the member type's major shape
    {lvls : List Level} {pins : List Expr} {Dn : Name}
    {preM : List (Name × Expr × BinderMeta)}
    {nmM : Name} {domM bodyM : Expr} {bmM : BinderMeta}
    (hmIrP : mI = rP)
    (hstripM : tyA.stripPis rP = some (preM, .forallE nmM domM bodyM bmM))
    (hdomFn : domM.getAppFn = .const Dn lvls)
    (hdomArgs : domM.getAppArgs = pins)
    (hpinsW : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    (hpinsLen : pins.length = cnP)
    (hpinsRen2 : ∀ p ∈ pins, Expr.ErasedEq
      ((p.renameConsts f).renameConsts f) (p.renameConsts f))
    -- kernel kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP))
    (hCstripSome : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hrinst : Expr.instPisAt (fvs.take rP)
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- kernel kit (public side)
    {rhsA : Expr} {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hcrest2Len : crest2.getAppArgs.length = cnP)
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstN : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (cdomsP, crestP))
    (htlP : TypedListOk F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- the rule right-hand side's facts
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L)
    -- member and constructor type wf
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ'' cvj.type = some T) :
    ∀ (xs : List V), xs.length = rP + cnF →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      (∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
          (fun i => xs.getD i SetTheory.empty)
          (Expr.mkAppN (.const R (lps.map .param))
            (fvsP ++ crest2.getAppArgs.drop cnP ++
              [Expr.mkAppN (.const ctor lvls)
                (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
                  xFvsP)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrest →
          interpExpr V m₀.val env₀ ψ (rP + cnF)
            (fun i => xs.getD i SetTheory.empty) e = some w) ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const R (lps.map .param))
          (fvsP ++ crest2.getAppArgs.drop cnP ++
            [Expr.mkAppN (.const ctor lvls)
              (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
                xFvsP)])) := by
  intro xs hxs hpref
  have hlen : xs.length ≤ rP + cnF := by omega
  have hge : rP ≤ xs.length := by omega
  obtain ⟨cty, hctyEq⟩ : ∃ c,
      c = cvj.type.instantiateLevelParams cvj.levelParams lvls :=
    ⟨_, rfl⟩
  rw [← hctyEq] at hcinstN
  have hCtw : cty.hasFvar = false := by
    rw [hctyEq, hasFvar_instantiateLevelParams]
    exact hCw
  have hCtb : cty.looseBVarsBounded 0 = true := by
    rw [hctyEq, looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hACt : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cty := by
    rw [hctyEq]
    exact AnnotOk.instLevels hcvp cvj.type 0 (rho0 V)
      (hACty (Level.substFn ψ cvj.levelParams lvls))
  have hICt : ∃ T, interpClosed V m₀.val env₀ ψ cty = some T := by
    obtain ⟨T, hT⟩ := hICty (Level.substFn ψ cvj.levelParams lvls)
    refine ⟨T, ?_⟩
    rw [hctyEq]
    unfold interpClosed
    rw [interp_instLevels hcvp cvj.type 0 (rho0 V)]
    exact hT
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the full recursor-prefix spine and its typing packages
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  have hIty' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA = some T := by
    obtain ⟨T, hT⟩ := hIty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant htyw _ _]
    exact hT
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw) hAty' hmemP
  obtain ⟨-, hPrestEx⟩ := peel_walk hfvsPInst hspP hwsP hWty hAty'
    hIty' hmemP
  obtain ⟨Prest, hPrest⟩ := hPrestEx
  obtain ⟨hWrest, hbrest, hArest, hlrest⟩ :=
    TeleFitI.rest_wf hfitP hWty htyb hAty'
  have hFrest : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) restP := by
    intro l hl
    rcases hlrest l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hΘP a ha l hla
  have hLrest : Expr.LeavesBounded restP := by
    intro l hl
    rcases hlrest l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact (hfvsPWf a ha).2.2 l hla
  -- the major premise's domain, instantiated at the prefix
  have hrestEq : restP = .forallE nmM
      (instSeq fvsP (rP - 1) domM)
      (instSeq fvsP (rP - 1 + 1) bodyM) bmM := by
    obtain ⟨h1, -⟩ := instPisAt_stripPis fvsP hfvsPInst
      (by rw [hfvsPLen]; exact hstripM)
    rw [h1, hfvsPLen, instSeq_forallE fvsP (rP - 1) nmM domM bodyM bmM
      (by rw [hfvsPLen]; omega)]
  -- the instantiated parameter spine and its typing packages
  have hdomEq : instSeq fvsP (rP - 1) domM =
      Expr.mkAppN (.const Dn lvls)
        (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) := by
    conv => lhs; rw [show domM = Expr.mkAppN domM.getAppFn
      domM.getAppArgs from (Expr.mkAppN_getApp domM).symm]
    rw [hdomFn, hdomArgs, Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _ (by rfl)]
    congr 1
    refine List.map_congr_left ?_
    intro p hp
    rw [Expr.instSpine_eq_instSeq]
  rw [hrestEq] at hArest hPrest hWrest hbrest hFrest hLrest
  have hAdomI : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (instSeq fvsP (rP - 1) domM) := by
    have h := hArest
    simp only [AnnotOk] at h
    exact h.1
  have hFdomI : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (instSeq fvsP (rP - 1) domM) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFrest
  have hLdomI : Expr.LeavesBounded (instSeq fvsP (rP - 1) domM) :=
    LeavesBounded.of_forallE_ty hLrest
  -- per-argument facts of the instantiated parameters
  have hcargW : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      WScoped (rP + cnF) a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact instSpine_WScoped (rP - 1)
      (WScoped.of_not_hasFvar (hpinsW p hp).1) hwsP
  have hcargB : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq,
      show rP - 1 = fvsP.length - 1 from by rw [hfvsPLen]]
    refine instSeq_bclosed ?_ ?_
    · intro x hx
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      obtain ⟨nm, hsh⟩ := hfvsPShape j x hj
      rw [hsh]
      rfl
    · rw [hfvsPLen]
      exact (hpinsW p hp).2
  have hcargL : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      Expr.LeavesBounded a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq]
    refine LeavesBounded_instSeq _ _ ?_ ?_
    · exact Expr.LeavesBounded.of_not_hasFvar (hpinsW p hp).1
    · intro x hx
      exact (hfvsPWf x hx).2.2
  have hcargF : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    refine FvarsOk.of_subset (fun l hl => ?_) hFdomI
    rw [hdomEq]
    refine fvarLeaves_getAppArgs ?_ l hl
    rw [Expr.getAppArgs_mkAppN,
      show (Expr.const Dn lvls).getAppArgs = [] from rfl,
      List.nil_append]
    exact ha
  have hcargA : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    have hne : pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ≠
        [] := by
      intro h0
      rw [h0] at ha
      exact nomatch ha
    have hAdom' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const Dn lvls)
          (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p))) := by
      rw [← hdomEq]
      exact hAdomI
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ (.const Dn lvls) hne
      hAdom'
    exact hargsA a ha
  -- walk the level-instantiated constructor type at the pins
  have hWct : WScoped (rP + cnF) cty := WScoped.of_not_hasFvar hCtw
  have hACt' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty :=
    AnnotOk.closed_invariant hCtw _ _ hACt
  have hICt' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty = some T := by
    obtain ⟨T, hT⟩ := hICt
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCtw _ _]
    exact hT
  obtain ⟨cvals, hfitC, hpackC, PcrEx⟩ := typed_walk m₀ F hcinstN htlP
    (fun a ha => ⟨hcargW a ha, hcargB a ha, hcargL a ha, hcargF a ha,
      hcargA a ha⟩)
    hWct hCtb (Expr.LeavesBounded.of_not_hasFvar hCtw)
    (FvarsOk.of_not_hasFvar hCtw) hACt' hICt'
  obtain ⟨Pcr, hPcr⟩ := PcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWct hCtb
    hACt'
  have hFcr : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · exact hcargF a ha l hla
  have hLcr : Expr.LeavesBounded crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · exact hcargL a ha l hla
  -- the public field walk
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  have hcargWrP : ∀ a ∈ pins.map (fun p => Expr.instSpine fvsP (rP - 1) p),
      WScoped rP a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine instSpine_WScoped (rP - 1)
      (WScoped.of_not_hasFvar (hpinsW p hp).1) ?_
    intro x hx
    have h := (hfvsPWf x hx).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcrRp⟩ := instPisAt_wscoped (D := rP)
    (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) hcinstN
    (WScoped.of_not_hasFvar hCtw) hcargWrP
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf cnF rP hopenX hWcrRp
    hbcr hLcr
  have hspX : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) xFvsP (xs.drop rP) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_drop]; omega) (by omega) ?_
    intro j v hjv
    rw [List.getElem?_drop] at hjv
    show xs.getD (rP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsX : ∀ a ∈ xFvsP, WScoped (rP + cnF) a := fun a ha =>
    (hxWf a ha).1
  have hLsX : ∀ a ∈ xFvsP, Expr.LeavesBounded a := fun a ha =>
    (hxWf a ha).2.2
  have hmemX : ∀ (i : Nat) (a : Expr) (v : V),
      (xFvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.drop rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hit : i < cnF := by
      rcases Nat.lt_or_ge i cnF with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hix : i < xFvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvsP[i]? = some fvi :=
      ⟨xFvsP[i]'hix, List.getElem?_eq_getElem hix⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[rP + i]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show rP + i - rP = i from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (rP + i) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape i fvi hfvi
    have hWi : WScoped (rP + i) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWcrD' : WScoped (rP + cnF) crestP := hWcrRp.mono (by omega)
  obtain ⟨hfitXP, hΘX⟩ := self_walk hxInst hspX hwsX hWcrD' hbcr hLcr
    hFcr hAcr hmemX
  obtain ⟨-, hPcrest2Ex⟩ := peel_walk hxInst hspX hwsX hWcrD' hAcr
    ⟨Pcr, hPcr⟩ hmemX
  obtain ⟨Pcr2, hPcr2⟩ := hPcrest2Ex
  have hfitCfullP : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++ xFvsP)
      (cvals ++ xs.drop rP) crest2 :=
    TeleFitI.append hfitC hfitXP
  obtain ⟨hWcrest2, hbcrest2, hAcrest2, hlcrest2⟩ :=
    TeleFitI.rest_wf hfitCfullP hWct hCtb hACt'
  have hFcrest2 : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hcargF a ha l hla
      · exact hΘX a ha l hla
  have hLcrest2 : Expr.LeavesBounded crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCtw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hcargL a ha l hla
      · exact hLsX a ha l hla
  -- ===== S0: the theorem-side master frame =====
  obtain ⟨hfvsInst, hfvsLen, hfvsShape⟩ :=
    openPisAtFvars_spec (rP + cnF) 0 hopen
  obtain ⟨hfvsWf, htbodyWf⟩ := openPisAtFvars_wf (rP + cnF) 0 hopen
    (WScoped.of_not_hasFvar hSw) hSb
    (Expr.LeavesBounded.of_not_hasFvar hSw)
  have hfvsW : ∀ a ∈ fvs, WScoped (rP + cnF) a := by
    intro a ha
    have := (hfvsWf a ha).1
    simpa using this
  have hfvsShapes : ∀ a ∈ fvs, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  have hspW : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvs xs := by
    refine FvarSpine_of_open hopen hxs (by omega) ?_
    intro k v hkv
    show xs.getD (0 + k) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hkv]
    rfl
  have hspWpre := FvarSpine.take rP hspW
  have hspWdrop := FvarSpine.drop rP hspW
  have hfvsPreLen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvsLen]; omega
  have htyStrip : (tyA.stripPis mI).isSome = true := by
    rw [hmIrP, hstripM]
    rfl
  -- ===== S1: the membership packs across the frames =====
  -- the theorem prefix: memberships in the renamed member type's
  -- instantiated parameter domains
  obtain ⟨⟨bsTy, restTy⟩, htyStripSome⟩ :=
    Option.isSome_iff_exists.mp htyStrip
  obtain ⟨restTyPre, htyPreStrip⟩ :=
    Expr.stripPis_prefix rP (mI - rP)
      (by rw [show rP + (mI - rP) = mI from by omega]
          exact htyStripSome)
  obtain ⟨⟨dsPubR, restPubR⟩, hinstPubR⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvs.take rP)
        (by rw [hfvsPreLen, htyPreStrip]; rfl))
  have hiaWpre : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvs.take rP)
      (xs.take rP) :=
    InstArgs.of_fvarSpine hspWpre (fun a ha =>
      ⟨hfvsW a (List.mem_of_mem_take ha),
        (hfvsWf a (List.mem_of_mem_take ha)).2.1⟩)
  have hpackR := fit_mem_frames (φ := ψ) htyw htyb htyPreStrip
    hinstPubR hfvsPreLen hiaWpre hfitP
  have hstripRenPre := stripPis_renameConsts (f := f) rP htyPreStrip
  have hmemR : ∀ (k : Nat) (a : Expr) (v : V), rdoms[k]? = some a →
      (xs.take rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkr : k < rP := by
      rcases Nat.lt_or_ge k rP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hrinst, hfvsPreLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, (bsTy.take rP)[k]? = some b := by
      have := Expr.stripPis_length rP htyPreStrip
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis (fvs.take rP) hrinst
      (by rw [hfvsPreLen]; exact hstripRenPre)
    obtain ⟨-, hdsPub⟩ := instPisAt_stripPis (fvs.take rP) hinstPubR
      (by rw [hfvsPreLen]; exact htyPreStrip)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hb]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hpackR k _ v (hdsPub k b hb) hv
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvs.take rP).take k, ∃ i n t,
        x = .fvar i n t := fun x hx =>
      hfvsShapes x (List.mem_of_mem_take (List.mem_of_mem_take hx))
    rw [interp_instSeq_ren hro hshapes]
    exact hBi
  -- ===== S2b: the instantiated parameters across the frames =====
  have hiaCP : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) cvals :=
    TeleFitI.toInstArgs hfitC
  have hcvalsLen : cvals.length = cnP := by
    have h := InstArgs.length hiaCP
    rw [List.length_map, hpinsLen] at h
    omega
  have hfvsTakeShapes : ∀ x ∈ fvs.take rP, ∃ i n t,
      x = Expr.fvar i n t := fun x hx =>
    hfvsShapes x (List.mem_of_mem_take hx)
  have hspinePairEE : ∀ (k : Nat) (a₁ a₂ : Expr),
      (fvs.take rP)[k]? = some a₁ → fvsP[k]? = some a₂ →
      Expr.ErasedEq a₁ a₂ := by
    intro k a₁ a₂ h₁ h₂
    have hk : k < rP := by
      rcases Nat.lt_or_ge k rP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hfvsPreLen]; omega)] at h₁
        exact nomatch h₁
    rw [List.getElem?_take_of_lt hk] at h₁
    obtain ⟨nm₁, hsh₁⟩ := hfvsShape k a₁ h₁
    obtain ⟨nm₂, hsh₂⟩ := hfvsPShape k a₂ h₂
    rw [Nat.zero_add] at hsh₁ hsh₂
    rw [hsh₁, hsh₂]
    exact rfl
  have hcargValR : ∀ (i : Nat) (pin : Expr) (v : V),
      pins[i]? = some pin → cvals[i]? = some v →
      interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty)
        (Expr.instSpine (fvs.take rP) (rP - 1)
          (pin.renameConsts f)) = some v := by
    intro i pin v hpin hv
    rw [Expr.instSpine_eq_instSeq,
      interp_instSeq_ren hro hfvsTakeShapes,
      interp_erasedEq (instSeq_erasedEq_args (fvs.take rP) fvsP
        (rP - 1) (Expr.ErasedEq.rfl pin) hspinePairEE
        (by rw [hfvsPreLen, hfvsPLen])) _ _]
    have h0 := InterpSpine.pointwise (InstArgs.toInterpSpine hiaCP) i
      (a := Expr.instSpine fvsP (rP - 1) pin)
      (by rw [List.getElem?_map, hpin]; rfl) hv
    rw [Expr.instSpine_eq_instSeq] at h0
    exact h0
  have hcargEEren : ∀ pin ∈ pins, Expr.ErasedEq
      ((Expr.instSpine fvsP (rP - 1) pin).renameConsts f)
      (Expr.instSpine (fvs.take rP) (rP - 1)
        (pin.renameConsts f)) := by
    intro pin hpin
    rw [Expr.instSpine_eq_instSeq, Expr.instSpine_eq_instSeq]
    refine Expr.ErasedEq.trans
      (instSeq_renameConsts (f := f) fvsP (rP - 1) ?_) ?_
    · intro a ha
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hfvsPShape j a hj
      rw [hsh]
      exact rfl
    · refine instSeq_erasedEq_args fvsP (fvs.take rP) (rP - 1)
        (Expr.ErasedEq.rfl _) ?_ (by rw [hfvsPreLen, hfvsPLen])
      intro k a₁ a₂ h₁ h₂
      exact Expr.ErasedEq.symm (hspinePairEE k a₂ a₁ h₂ h₁)
  have hcargAR : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    refine AnnotOk.erasedEq _ (hcargEEren pin hpin) _ _ ?_
    exact AnnotOk.renameConsts hro _ _ _
      (hcargA _ (List.mem_map_of_mem hpin))
  have hcargWR : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
      WScoped (rP + cnF) a := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    refine instSpine_WScoped (rP - 1)
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact (hpinsW pin hpin).1)) ?_
    intro x hx
    exact hfvsW x (List.mem_of_mem_take hx)
  have hcargBR : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq,
      show rP - 1 = (fvs.take rP).length - 1 from by rw [hfvsPreLen]]
    refine instSeq_bclosed ?_ ?_
    · intro x hx
      obtain ⟨i', n', t', hx'⟩ := hfvsTakeShapes x hx
      rw [hx']
      rfl
    · rw [hfvsPreLen, looseBVarsBounded_renameConsts]
      exact (hpinsW pin hpin).2
  obtain ⟨⟨bsC, cbody0⟩, hCstripPair⟩ :=
    Option.isSome_iff_exists.mp hCstripSome
  have hiaR : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty)
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      (cvals ++ xs.drop rP) := by
    refine InstArgs.append ?_ ?_
    · refine InstArgs.of_pointwise
        (by rw [List.length_map, hpinsLen, hcvalsLen]) ?_
      intro k a v ha hv
      have hkc : k < cnP := by
        rcases Nat.lt_or_ge k cnP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [hcvalsLen]; omega)] at hv
          exact nomatch hv
      obtain ⟨pin, hpin⟩ : ∃ p, pins[k]? = some p :=
        ⟨pins[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have ha' : a = Expr.instSpine (fvs.take rP) (rP - 1)
          (pin.renameConsts f) := by
        rw [List.getElem?_map, hpin] at ha
        exact (Option.some.inj ha).symm
      subst ha'
      exact ⟨hcargWR _ (List.mem_map_of_mem
          (List.mem_of_getElem? hpin)),
        hcargBR _ (List.mem_map_of_mem (List.mem_of_getElem? hpin)),
        hcargValR k pin v hpin hv⟩
    · exact InstArgs.of_fvarSpine hspWdrop (fun a ha =>
        ⟨hfvsW a (List.mem_of_mem_drop ha),
          (hfvsWf a (List.mem_of_mem_drop ha)).2.1⟩)
  have hspineRLen : (pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_map, hpinsLen,
      List.length_drop, hfvsLen]
    omega
  have hfitLvls : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++ xFvsP)
      (cvals ++ xs.drop rP) crest2 := by
    rw [← hctyEq]
    exact hfitCfullP
  have hswap := fit_mem_swap₂ (φ := ψ) hcvp hCw hCb hCstripPair hCps
    (ks₁ := cvj.levelParams) (us₁ := lvls)
    (fun p hp => rfl) hfitLvls hiaR hspineRLen
  have hstripI0 : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).stripPis (cnP + cnF)).isSome = true :=
    Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
      (cnP + cnF) (by rw [hCstripPair]; rfl)
  obtain ⟨⟨bsI, cbodyI⟩, hCstripI⟩ :=
    Option.isSome_iff_exists.mp hstripI0
  obtain ⟨hbodyIeq, hdomsIeq⟩ := stripPis_instantiateLevelParams_eq
    cvj.levelParams lvls _ hCstripPair hCstripI
  have hstripRenI := stripPis_renameConsts (f := f) (cnP + cnF)
    hCstripI
  have hEEargsR : ∀ x ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP, Expr.ErasedEq (x.renameConsts f) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp hx'
      rw [Expr.instSpine_eq_instSeq]
      refine Expr.ErasedEq.trans
        (instSeq_renameConsts (f := f) (fvs.take rP) (rP - 1) ?_) ?_
      · intro y hy
        obtain ⟨i', n', t', hy'⟩ := hfvsTakeShapes y hy
        rw [hy']
        exact rfl
      · exact instSeq_erasedEq (fvs.take rP) (rP - 1)
          (hpinsRen2 pin hpin)
    · obtain ⟨i', n', t', hx''⟩ :=
        hfvsShapes x (List.mem_of_mem_drop hx')
      rw [hx'']
      exact rfl
  have hmemC : ∀ (k : Nat) (a : Expr) (v : V), cdoms[k]? = some a →
      (cvals ++ xs.drop rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkc : k < cnP + cnF := by
      rcases Nat.lt_or_ge k (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hcinst, hspineRLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨bI, hbI⟩ : ∃ b, bsI[k]? = some b := by
      have := Expr.stripPis_length (cnP + cnF) hCstripI
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bC, hbC⟩ : ∃ b, bsC[k]? = some b := by
      have := Expr.stripPis_length (cnP + cnF) hCstripPair
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis _ hcinst
      (by rw [hspineRLen]; exact hstripRenI)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hbI]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hswap k bC v hbC hv
    refine ⟨B, ?_, hvB⟩
    have hbIdom : bI.2.1 =
        bC.2.1.instantiateLevelParams cvj.levelParams lvls :=
      hdomsIeq k bC bI hbC hbI
    dsimp only
    rw [hbIdom]
    have hEEtake : ∀ x ∈ (pins.map (fun p =>
        Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
        fvs.drop rP).take k, Expr.ErasedEq (x.renameConsts f) x :=
      fun x hx => hEEargsR x (List.mem_of_mem_take hx)
    have h1 := instSeq_renameConsts (f := f)
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP).take k) (k - 1)
      (X := bC.2.1.instantiateLevelParams cvj.levelParams lvls)
      hEEtake
    rw [← interp_erasedEq h1 _ _, interp_renameConsts hro _ _ _]
    exact hBi
  -- ===== S2: the theorem walk =====
  have hfvsInst' : Expr.instPisAt
      (fvs.take rP ++ fvs.drop rP) cvt.type =
      some (fvs.map Expr.fvarTypeD, tbody) := by
    rw [List.take_append_drop]
    exact hfvsInst
  obtain ⟨dsS1, midS, dsS2, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append _ _ hfvsInst'
  have hdsS1len : dsS1.length = rP := by
    rw [instPisAt_length _ hopS1, hfvsPreLen]
  obtain ⟨hdsS1eq, hdsS2eq⟩ : dsS1 = (fvs.take rP).map
      Expr.fvarTypeD ∧ dsS2 = (fvs.drop rP).map
      Expr.fvarTypeD := by
    have hmap : fvs.map Expr.fvarTypeD =
        (fvs.take rP).map Expr.fvarTypeD ++
        (fvs.drop rP).map Expr.fvarTypeD := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap] at hdsSplit
    exact List.append_inj hdsSplit.symm (by
      rw [hdsS1len, List.length_map, hfvsPreLen])
  subst hdsS1eq hdsS2eq
  have hWS : WScoped (rP + cnF) cvt.type :=
    WScoped.of_not_hasFvar hSw
  have hLS : Expr.LeavesBounded cvt.type :=
    Expr.LeavesBounded.of_not_hasFvar hSw
  have hFS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    FvarsOk.of_not_hasFvar hSw
  have hAS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    AnnotOk.closed_invariant hSw _ _ (hthm_annot ψ)
  obtain ⟨P, hPc, hPmem⟩ := hthm_mem ψ
  have hPI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type = some P := by
    rw [interp_closed_invariant hSw _ _]
    exact hPc
  -- the renamed member type's invariants
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  have hAtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) :=
    AnnotOk.closed_invariant htyRw _ _
      (AnnotOk.renameConsts hro tyA 0 (rho0 V) hAty)
  obtain ⟨Tty, hTtyc⟩ := hIty
  have hItyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) =
      some TR := by
    refine ⟨Tty, ?_⟩
    rw [interp_closed_invariant htyRw _ _]
    show interpClosed V m₀.val env₀ _ (tyA.renameConsts f) = some Tty
    unfold interpClosed
    rw [interp_renameConsts hro tyA 0 (rho0 V)]
    exact hTtyc
  -- stage 1: the prefix walk
  obtain ⟨hfitS1, hfitR1, hΘpre⟩ := pi_walk m₀ F hopS1 hrinst hdePre
    hspWpre (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    hWS hSb hLS hFS hAS
    (WScoped.of_not_hasFvar htyRw) htyRb
    (Expr.LeavesBounded.of_not_hasFvar htyRw)
    (FvarsOk.of_not_hasFvar htyRw) hAtyR
    ⟨P, hPI⟩ hItyR hmemR
  obtain ⟨Qmid, hQmidI, hQmidMem, hAmidS⟩ :=
    TeleFitI.elim hfitS1 hAS hPI hPmem
  obtain ⟨hWmidS, hbmidS, -, hleavesMidS⟩ :=
    TeleFitI.rest_wf hfitS1 hWS hSb hAS
  have hFmidS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact hΘpre a ha l hla
  have hLmidS : Expr.LeavesBounded midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- the renamed constructor's parameter walk to its mid residual
  obtain ⟨cdomsA, midC, cdomsB, hopC1, hopC2, hcdomsSplit⟩ :=
    instPisAt_append _ _ hcinst
  have hcdomsAlen : cdomsA.length = cnP := by
    rw [instPisAt_length _ hopC1, List.length_map, hpinsLen]
  have hcdomsBeq : cdoms.drop cnP = cdomsB := by
    rw [hcdomsSplit, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hCRw : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts, hasFvar_instantiateLevelParams]
    exact hCw
  have hCRb : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts,
      looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hACtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) := by
    refine AnnotOk.closed_invariant hCRw _ _ ?_
    refine AnnotOk.renameConsts hro _ 0 (rho0 V) ?_
    rw [← hctyEq]
    exact hACt
  have hICtyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some TR := by
    obtain ⟨TC, hTCc⟩ := hICt
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hCRw _ _]
    show interpClosed V m₀.val env₀ _ _ = some TC
    unfold interpClosed
    rw [interp_renameConsts hro _ 0 (rho0 V), ← hctyEq]
    exact hTCc
  obtain ⟨hfitC1, hImidC⟩ := expr_peel_walk hopC1
    (by
      refine InterpSpine.of_pointwise
        (by rw [List.length_map, hpinsLen, hcvalsLen]) ?_
      intro k a v ha hv
      have hkc : k < cnP := by
        rcases Nat.lt_or_ge k cnP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [hcvalsLen]; omega)] at hv
          exact nomatch hv
      obtain ⟨pin, hpin⟩ : ∃ p, pins[k]? = some p :=
        ⟨pins[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have ha' : a = Expr.instSpine (fvs.take rP) (rP - 1)
          (pin.renameConsts f) := by
        rw [List.getElem?_map, hpin] at ha
        exact (Option.some.inj ha).symm
      subst ha'
      exact hcargValR k pin v hpin hv)
    (fun a ha => ⟨hcargWR a ha, hcargBR a ha, hcargAR a ha⟩)
    (WScoped.of_not_hasFvar hCRw) hACtyR hICtyR
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      refine hmemC k a v ?_ ?_
      · rw [hcdomsSplit, List.getElem?_append_left (by omega)]
        exact ha
      · rw [List.getElem?_append_left (by rw [hcvalsLen]; omega)]
        exact hv)
  obtain ⟨hWmidC, hbmidC, hAmidC, hleavesMidC⟩ :=
    TeleFitI.rest_wf hfitC1 (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hcargFR : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    intro l hl
    rw [Expr.instSpine_eq_instSeq] at hl
    rcases fvarLeaves_instSeq _ _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact (hpinsW pin hpin).1)] at hl'
      cases hl'
    · exact hΘpre x hx l hlx
  have hcargLR : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
      Expr.LeavesBounded a := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    rw [Expr.instSpine_eq_instSeq]
    refine LeavesBounded_instSeq _ _ ?_ ?_
    · exact Expr.LeavesBounded.of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact (hpinsW pin hpin).1)
    · intro x hx
      exact (hfvsWf x (List.mem_of_mem_take hx)).2.2
  have hFmidC : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun l => xs.getD l SetTheory.empty) midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · exact hcargFR a ha l hla
  have hLmidC : Expr.LeavesBounded midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · exact hcargLR a ha l hla
  -- stage 2: the field walk
  obtain ⟨hfitS2, hfitR2, hΘx⟩ := pi_walk m₀ F hopS2
    (by rw [← hcdomsBeq] at hopC2; exact hopC2)
    hdeFld
    hspWdrop (fun a ha => hfvsW a (List.mem_of_mem_drop ha))
    hWmidS hbmidS hLmidS hFmidS hAmidS
    hWmidC hbmidC hLmidC hFmidC hAmidC
    ⟨Qmid, hQmidI⟩ hImidC
    (fun k a v ha hv => by
      refine hmemC (cnP + k) a v ?_ ?_
      · rw [List.getElem?_drop] at ha
        exact ha
      · rw [List.getElem?_append_right (by omega), hcvalsLen,
          show cnP + k - cnP = k from by omega]
        exact hv)
  obtain ⟨Q, hQI, hQmem0, hAtbody⟩ :=
    TeleFitI.elim hfitS2 hAmidS hQmidI hQmidMem
  have hQmem : SpineFold V (m₀.val thmName ψ) xs ∈ˢ Q := by
    have h0 : SpineFold V (m₀.val thmName ψ)
        (xs.take rP ++ xs.drop rP) ∈ˢ Q := by
      rw [SpineFold_append]
      exact hQmem0
    rwa [List.take_append_drop] at h0
  -- ===== S3: the Eq collapse =====
  have htbodyEq : tbody = Expr.mkAppN (.const eqName [ℓA])
      [αS, lhsS, rhsS] := by
    have h0 := Expr.mkAppN_getApp tbody
    rw [hheadEq, hargs3] at h0
    exact h0.symm
  rw [htbodyEq] at hQI hAtbody
  obtain ⟨-, hcompsA, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hAtbody
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hQeq : Q = SpineFold V veq [vα, vl, vr] := by
    rw [hfoldQ] at hQI
    exact Option.some.inj hQI |>.symm
  have hveq : veq = eqVal V (Level.substFn ψ [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn ψ [uN] [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : Q = eqv vl vr := by
    rw [hQeq, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn ψ [uN] [ℓA]))
        [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hvlvr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- ===== S4: decompose the statement's left side =====
  have hlhsEq : lhsS = Expr.mkAppN (.const (f R) (lps.map .param))
      lhsS.getAppArgs := by
    have h0 := Expr.mkAppN_getApp lhsS
    rw [hlhead] at h0
    exact h0.symm
  have hAlhs : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    hcompsA lhsS (by simp)
  rw [hlhsEq] at hAlhs
  obtain ⟨-, hlargsA, vhead, lvals, hheadI, hspL, hchainL, hfoldL⟩ :=
    annotOk_spine_inv _ (.const (f R) (lps.map .param))
      (by
        intro h0
        rw [h0] at hlarity
        exact nomatch hlarity) hAlhs
  have hvlfold : vl = SpineFold V vhead lvals := by
    rw [← hlhsEq] at hfoldL
    rw [hfoldL] at hil
    exact Option.some.inj hil |>.symm
  -- the head is the recursor's value
  have hsubstψ : Level.substFn ψ lps (lps.map .param) = ψ :=
    funext (fun p => Level.substFn_map_param)
  have hcRi : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const (f R) (lps.map .param)) = some (m₀.val R ψ) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    rw [hsubstψ, hro.2.2 R]
  have hvhead : vhead = m₀.val R ψ := by
    rw [hcRi] at hheadI
    exact Option.some.inj hheadI |>.symm
  -- the equation body's component facts
  obtain ⟨hWtbody0, hbtbody0, htbodyL0⟩ := htbodyWf
  have hlhsMem : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWlhs : WScoped (rP + cnF) lhsS := by
    have h0 := hWtbody0.getAppArgs lhsS hlhsMem
    rwa [Nat.zero_add] at h0
  have hblhs : lhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hlhsMem
  obtain ⟨-, -, -, hleavesTbody⟩ := TeleFitI.rest_wf hfitS2 hWmidS hbmidS
    hAmidS
  have hFtbody : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tbody := by
    intro l hl
    rcases hleavesTbody l hl with hl' | ⟨a, ha, hla⟩
    · exact hFmidS l hl'
    · exact hΘx a ha l hla
  have hFlhs : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hlhsMem l hl)
      hFtbody
  have hLlhs : Expr.LeavesBounded lhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hlhsMem l hl)
  have hrhsMem : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWrhsS : WScoped (rP + cnF) rhsS := by
    have h0 := hWtbody0.getAppArgs rhsS hrhsMem
    rwa [Nat.zero_add] at h0
  have hbrhsS : rhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hrhsMem
  have hFrhsS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hrhsMem l hl)
      hFtbody
  have hLrhsS : Expr.LeavesBounded rhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hrhsMem l hl)
  have hArhsS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    hcompsA rhsS (by simp)
  -- the full renamed constructor fit and `cres`'s facts
  have hfitCfull : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f)
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      (cvals ++ xs.drop rP) cres :=
    TeleFitI.append hfitC1 hfitR2
  obtain ⟨hWcres, hbcres, hAcres, hleavesCres⟩ :=
    TeleFitI.rest_wf hfitCfull (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFcres : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hcargFR a ha l hla
      · exact hΘx a ha l hla
  have hLcres : Expr.LeavesBounded cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hcargLR a ha l hla
      · exact (hfvsWf a (List.mem_of_mem_drop ha)).2.2 l hla
  -- ===== S4b: the argument values =====
  have hlvalsLen : lvals.length = mI + 1 := by
    rw [InterpSpine.length hspL, hlarity]
  obtain ⟨lastE, hlargsDecomp, hlastE⟩ :=
    take_concat_of_length (l := lhsS.getAppArgs) (n := mI) hlarity
  obtain ⟨vlast, hlvalsDecomp, hvlast⟩ :=
    take_concat_of_length (l := lvals) (n := mI) hlvalsLen
  have hlastEmaj : lastE =
      Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP) := by
    have h0 : lhsS.getAppArgs.getLastD (.bvar 0) = lastE := by
      conv => lhs; rw [hlargsDecomp]
      rw [List.getLastD_concat]
    rw [← h0, hmaj]
  have hpreValsEq : lvals.take rP = xs.take rP := by
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i rP with hi | hi
    · obtain ⟨ei, hei⟩ : ∃ e, lhsS.getAppArgs[i]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨vi, hvi⟩ : ∃ v, lvals[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hint := InterpSpine.pointwise hspL i hei hvi
      have heifv : fvs[i]? = some ei := by
        have h0 := congrArg (·[i]?) hlpre
        simp only [List.getElem?_take_of_lt hi] at h0
        rw [← h0, hei]
      obtain ⟨nmi, hshi⟩ := hfvsShape i ei heifv
      rw [Nat.zero_add] at hshi
      rw [hshi] at hint
      simp only [interpExpr] at hint
      have hvix : vi = xs.getD i SetTheory.empty :=
        (Option.some.inj hint).symm
      rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
        hvi, hvix, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (l := xs) (i := i) (by omega)]
      rfl
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by rw [List.length_take]; omega)]
  -- lhsS's per-argument facts
  have hlargsW : ∀ e ∈ lhsS.getAppArgs, WScoped (rP + cnF) e :=
    fun e he => hWlhs.getAppArgs e he
  have hlargsB : ∀ e ∈ lhsS.getAppArgs, e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hblhs e he
  have hlargsL : ∀ e ∈ lhsS.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLlhs l (fvarLeaves_getAppArgs he l hl)
  have hlargsF : ∀ e ∈ lhsS.getAppArgs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFlhs
  -- the index tuple is empty (nested rules are index-free)
  have hidxVal : ∀ (j : Nat) (e2 : Expr) (v : V),
      (crest2.getAppArgs.drop cnP)[j]? = some e2 →
      (lvals.drop rP)[j]? = some v → j < mI - rP →
      interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e2 = some v := by
    intro j e2 v _ _ hjlt
    exact absurd hjlt (by omega)
  -- ===== S4c: the major value =====
  have hmajI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lastE = some vlast :=
    InterpSpine.pointwise hspL mI hlastE hvlast
  rw [hlastEmaj] at hmajI
  obtain ⟨vh, hvh⟩ := interp_mkAppN_head_some _ _ hmajI
  have hlvlsLen : lvls.length = cimC.toConstantVal.levelParams.length := by
    revert hvh
    simp only [interpExpr, hfCm]
    split
    · next hcond =>
        intro _
        exact hcond
    · intro hvh
      exact nomatch hvh
  have hcCiN : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const (f ctor) lvls) =
      some (m₀.val ctor (Level.substFn ψ cvj.levelParams lvls)) := by
    simp only [interpExpr, hfCm]
    rw [if_pos hlvlsLen]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from
      hCmlps]
    rw [hro.2.2 ctor]
  have hcCpubIN : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const ctor lvls) =
      some (m₀.val ctor (Level.substFn ψ cvj.levelParams lvls)) := by
    simp only [interpExpr, hfC]
    rw [if_pos (by
      rw [hClps]
      rw [hCmlps] at hlvlsLen
      exact hlvlsLen)]
    rw [show ciC.toConstantVal.levelParams = cvj.levelParams from
      hClps]
  have hctorSpineI : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      (cvals ++ xs.drop rP) :=
    InstArgs.toInterpSpine hiaR
  have hvlastEq : vlast = SpineFold V
      (m₀.val ctor (Level.substFn ψ cvj.levelParams lvls))
      (cvals ++ xs.drop rP) := by
    rw [interp_mkAppN _ _ hcCiN hctorSpineI] at hmajI
    exact (Option.some.inj hmajI).symm
  have hpubCtorSpineI : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++ xFvsP)
      (cvals ++ xs.drop rP) :=
    TeleFitI.toInterpSpine hfitCfullP
  have hctorAppI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const ctor lvls)
        (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
          xFvsP)) = some vlast := by
    rw [interp_mkAppN _ _ hcCpubIN hpubCtorSpineI]
    exact congrArg some hvlastEq.symm
  -- ===== S4d: the canonical body's spine =====
  have hseg1 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (lvals.take rP) := by
    rw [hpreValsEq]
    exact InterpSpine_of_FvarSpine hspP
  have hcrest2ArgsLen : crest2.getAppArgs.length = cnP + (mI - rP) := by
    rw [hmIrP]
    simpa using hcrest2Len
  have hseg2 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (crest2.getAppArgs.drop cnP)
      ((lvals.drop rP).take (mI - rP)) := by
    refine InterpSpine.of_pointwise ?_ ?_
    · rw [List.length_drop, hcrest2ArgsLen, List.length_take,
        List.length_drop, hlvalsLen]
      omega
    · intro j e v he hv
      have hjlt : j < mI - rP := by
        rcases Nat.lt_or_ge j (mI - rP) with h | h
        · exact h
        · rw [List.getElem?_eq_none
            (by rw [List.length_take]; omega)] at hv
          exact nomatch hv
      rw [List.getElem?_take_of_lt hjlt] at hv
      exact hidxVal j e v he hv hjlt
  have hseg3 : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      [Expr.mkAppN (.const ctor lvls)
        (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
          xFvsP)] [vlast] := ⟨hctorAppI, trivial⟩
  have hspB : InterpSpine m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP ++ crest2.getAppArgs.drop cnP ++
        [Expr.mkAppN (.const ctor lvls)
          (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
            xFvsP)])
      (lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast]) :=
    InterpSpine.append (InterpSpine.append hseg1 hseg2) hseg3
  have hlvalsRebuild : lvals =
      lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast] := by
    conv =>
      lhs
      rw [hlvalsDecomp, show mI = rP + (mI - rP) from by omega,
        List.take_add]
  have hbLheadI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const R (lps.map .param)) = some (m₀.val R ψ) := by
    simp only [interpExpr, hfR]
    rw [if_pos (by rw [hRlps]; simp)]
    rw [show ciR.toConstantVal.levelParams = lps from hRlps]
    rw [hsubstψ]
  -- ===== S4e: the canonical body's truthful annotations =====
  have hAfvsP : ∀ a ∈ fvsP,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
    rw [hsh]
    simp [AnnotOk]
  have hAxFvs : ∀ a ∈ xFvsP,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, hsh⟩ := hxShape j a hja
    rw [hsh]
    simp [AnnotOk]
  have hcrest2SpineA : crest2.getAppArgs ≠ [] →
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN crest2.getAppFn crest2.getAppArgs) := by
    intro _
    rw [Expr.mkAppN_getApp]
    exact hAcrest2
  have hcrest2ArgA : ∀ e ∈ crest2.getAppArgs,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e := by
    intro e he
    have hne : crest2.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ crest2.getAppFn hne
      (hcrest2SpineA hne)
    exact hargsA e he
  -- the constructor value's typing chain, transferred from the
  -- statement's major
  have hAlastE : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)) := by
    have h0 := hlargsA lastE (List.mem_of_getElem? hlastE)
    rwa [hlastEmaj] at h0
  have hchainCtor : ChainSlots V
      (m₀.val ctor (Level.substFn ψ cvj.levelParams lvls))
      (cvals ++ xs.drop rP) := by
    cases hlist : pins.map (fun p =>
        Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
        fvs.drop rP with
    | nil =>
      have h0 := hspineRLen
      rw [hlist] at h0
      simp only [List.length_nil] at h0
      have hvals0 : cvals ++ xs.drop rP = [] := by
        rw [List.append_eq_nil_iff]
        constructor
        · rw [← List.length_eq_zero_iff, hcvalsLen]
          omega
        · rw [← List.length_eq_zero_iff, List.length_drop]
          omega
      rw [hvals0]
      trivial
    | cons c0 cr =>
      have hne : pins.map (fun p =>
          Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
          fvs.drop rP ≠ [] := by
        rw [hlist]
        simp
      obtain ⟨-, -, vf, cvalsE, hvf, hspCv, hchainCv, -⟩ :=
        annotOk_spine_inv _ (.const (f ctor) lvls) hne hAlastE
      have hvfeq : vf =
          m₀.val ctor (Level.substFn ψ cvj.levelParams lvls) := by
        rw [hcCiN] at hvf
        exact (Option.some.inj hvf).symm
      have hcveq : cvalsE = cvals ++ xs.drop rP :=
        InterpSpine.functional hspCv hctorSpineI
      rw [← hvfeq, ← hcveq]
      exact hchainCv
  obtain ⟨hActorApp, -⟩ := annotOk_spine
    (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++ xFvsP)
    (.const ctor lvls)
    (by simp [AnnotOk]) hcCpubIN
    (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact hcargA a ha'
      · exact hAxFvs a ha')
    hpubCtorSpineI hchainCtor
  -- assemble
  have hchainBL : ChainSlots V (m₀.val R ψ)
      (lvals.take rP ++ (lvals.drop rP).take (mI - rP) ++ [vlast]) := by
    rw [← hlvalsRebuild, ← hvhead]
    exact hchainL
  obtain ⟨hAbL, hbLI⟩ := annotOk_spine
    (fvsP ++ crest2.getAppArgs.drop cnP ++
      [Expr.mkAppN (.const ctor lvls)
        (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
          xFvsP)])
    (.const R (lps.map .param))
    (by simp [AnnotOk]) hbLheadI
    (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · rcases List.mem_append.mp ha' with ha'' | ha''
        · exact hAfvsP a ha''
        · exact hcrest2ArgA a (List.mem_of_mem_drop ha'')
      · rcases List.mem_singleton.mp ha' with rfl
        exact hActorApp)
    hspB hchainBL
  have hbLvl : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (.const R (lps.map .param))
        (fvsP ++ crest2.getAppArgs.drop cnP ++
          [Expr.mkAppN (.const ctor lvls)
            (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
              xFvsP)])) = some vl := by
    rw [hbLI, hvlfold, hvhead]
    exact congrArg some (congrArg _ hlvalsRebuild.symm)
  -- ===== S5: the right side is the applied rule =====
  have hWapp : ∀ (zs : List Expr) (h : Expr),
      WScoped (rP + cnF) h →
      (∀ x ∈ zs, WScoped (rP + cnF) x) →
      WScoped (rP + cnF) (Expr.mkAppN h zs) := by
    intro zs
    induction zs with
    | nil => intro h hh _; exact hh
    | cons x zs ih =>
      intro h hh hxs
      show WScoped _ (Expr.mkAppN (.app h x) zs)
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [WScoped]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hbapp : ∀ (zs : List Expr) (h : Expr),
      h.looseBVarsBounded 0 = true →
      (∀ x ∈ zs, x.looseBVarsBounded 0 = true) →
      (Expr.mkAppN h zs).looseBVarsBounded 0 = true := by
    intro zs
    induction zs with
    | nil => intro h hh _; exact hh
    | cons x zs ih =>
      intro h hh hxs
      show (Expr.mkAppN (.app h x) zs).looseBVarsBounded 0 = true
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hlapp : ∀ (zs : List Expr) (h : Expr) {l},
      l ∈ (Expr.mkAppN h zs).fvarLeaves →
      l ∈ h.fvarLeaves ∨ ∃ x ∈ zs, l ∈ x.fvarLeaves := by
    intro zs
    induction zs with
    | nil => intro h l hl; exact Or.inl hl
    | cons x zs ih =>
      intro h l hl
      rcases ih (.app h x) hl with hl' | ⟨y, hy, hly⟩
      · simp only [fvarLeaves, List.mem_append] at hl'
        rcases hl' with hl' | hl'
        · exact Or.inl hl'
        · exact Or.inr ⟨x, List.mem_cons_self, hl'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩
  -- the rule tower's walk at the public frame
  have hspPX : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
    have h := FvarSpine.append hspP hspX
    rwa [List.take_append_drop] at h
  have hWfull : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hwsP a ha
    · exact hwsX a ha
  have hΘfull : ∀ a ∈ fvsP ++ xFvsP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX a ha
  have hLfull : ∀ a ∈ fvsP ++ xFvsP, Expr.LeavesBounded a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact hLsX a ha
  have hArhsW : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ hArhs
  obtain ⟨L0, hL0c⟩ := hIrhs
  have hL0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  have hfitLam := lam_walk m₀ F hlinst hdeLam hspPX hWfull hΘfull
    hLfull (WScoped.of_not_hasFvar hrhsw) hrhsb
    (Expr.LeavesBounded.of_not_hasFvar hrhsw)
    (FvarsOk.of_not_hasFvar hrhsw) hArhsW ⟨L0, hL0⟩
  obtain ⟨Bf, hBfI, hBfold, hchainL2⟩ := TeleFitLam.fold hfitLam
    hArhsW hL0
  -- the applied renamed rule at the theorem frame
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hrhsw
  have hArhsRen : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (rhsA.renameConsts f) :=
    AnnotOk.closed_invariant hrhsRw _ _
      (AnnotOk.renameConsts hro rhsA 0 (rho0 V) hArhs)
  have hLren : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (rhsA.renameConsts f) = some L0 := by
    rw [interp_renameConsts hro]
    exact hL0
  have hfvsA : ∀ x ∈ fvs, AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) x := by
    intro x hx
    obtain ⟨i, n, t, rfl⟩ := hfvsShapes x hx
    simp [AnnotOk]
  obtain ⟨hAappF, hIappF⟩ := annotOk_spine fvs (rhsA.renameConsts f)
    hArhsRen hLren hfvsA (InterpSpine_of_FvarSpine hspW) hchainL2
  -- side conditions for the statement's right side
  have hΘfvs : ∀ a ∈ fvs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := by
    intro a ha
    rw [← List.take_append_drop rP fvs] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘpre a ha
    · exact hΘx a ha
  have hWappF : WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) :=
    hWapp fvs _ (WScoped.of_not_hasFvar hrhsRw) hfvsW
  have hbappF : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine hbapp fvs _ ?_ (FvarSpine.bounded hspW)
    rw [looseBVarsBounded_renameConsts]
    exact hrhsb
  have hLappF : Expr.LeavesBounded
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact (hfvsWf x hx).2.2 l hlx
  have hFappF : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact hΘfvs x hx l hlx
  have hvrFold : vr = SpineFold V L0 xs :=
    isDefEqCore_sound m₀ F hdeRhs hWrhsS hWappF hbrhsS hbappF hLrhsS
      hLappF hFrhsS hFappF hArhsS hAappF hir hIappF
  -- ===== S6: conclusion =====
  refine ⟨⟨vl, hbLvl, ?_⟩, hAbL⟩
  intro e hee
  rw [interp_erasedEq hee _ _, hBfI]
  refine congrArg some ?_
  rw [← hBfold, ← hvrFold, ← hvlvr]


/-- The `RecRulesOk` tail for a **nested** modeled rule: the canonical
frame/body decomposition computes, is well-formed and resolves, and for
every level assignment the closed tower interprets to the value of the
stored right-hand side.  Mirrors `modeled_rule_eq_plain` with the
constructor applied at the stored level instantiations to the stored
typed parameter pins. -/
theorem modeled_rule_eq_nested
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    (hcvp : ConstValParams m₀.val env₀)
    -- the rule and the stored recursor data
    {r : RecRule} {cv : ConstantVal} {R : Name} {lps : List Name}
    {tyA : Expr} {mI rP : Nat}
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr}
    {lvls : List Level} {pins : List Expr}
    (hfire : RecRule.fire r = .nested lvls pins)
    (hrctor : RecRule.ctor r = ctor)
    (hrcp : RecRule.ctorParams r = cnP)
    (hrnf : RecRule.nfields r = cnF)
    (hrrhs : RecRule.rhs r = rhsA)
    (hcvty : cv.type = tyA)
    (hcvlps : cv.levelParams = lps)
    -- environment entries
    {ciR cim : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    (hRlps : ciR.toConstantVal.levelParams = lps)
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hClps : ciC.toConstantVal.levelParams = cvj.levelParams)
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ : Name → Nat, m₀.val eqName ψ = eqVal V ψ)
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ cvt.type = some P ∧
      m₀.val thmName ψ ∈ˢ P)
    (hthm_annot : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- the stored instantiations and the member type's major shape
    {Dn : Name}
    {preM : List (Name × Expr × BinderMeta)}
    {nmM : Name} {domM bodyM : Expr} {bmM : BinderMeta}
    (hmIrP : mI = rP)
    (hstripM : tyA.stripPis rP = some (preM, .forallE nmM domM bodyM bmM))
    (hdomFn : domM.getAppFn = .const Dn lvls)
    (hdomArgs : domM.getAppArgs = pins)
    (hpinsW : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    (hpinsLen : pins.length = cnP)
    (hpinsRen2 : ∀ p ∈ pins, Expr.ErasedEq
      ((p.renameConsts f).renameConsts f) (p.renameConsts f))
    (hpinsRes : ∀ p ∈ pins, p.constsResolve env₀ = true)
    -- kernel kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP))
    (hCstripSome : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hrinst : Expr.instPisAt (fvs.take rP)
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- kernel kit (public side)
    {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hcrest2Len : crest2.getAppArgs.length = cnP)
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstN : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (cdomsP, crestP))
    (htlP : TypedListOk F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p)) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- wf and resolution of the stored data
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∀ ψ : Name → Nat, ∃ L,
      interpClosed V m₀.val env₀ ψ rhsA = some L)
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : ∀ ψ : Name → Nat,
      AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ cvj.type = some T)
    (hTres : cv.type.constsResolve env₀ = true)
    (hCres : cvj.type.constsResolve env₀ = true) :
    ∃ fvms bL, ruleLhsParts R cv rP r cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = rP + RecRule.nfields r ∧
      (closeLamsAt fvms bL).constsResolve env₀ = true ∧
      ∀ ψ : Name → Nat,
        AnnotOk V m₀.val env₀ ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V m₀.val env₀ ψ (closeLamsAt fvms bL) =
            some Rv ∧
          interpClosed V m₀.val env₀ ψ (RecRule.rhs r) = some Rv := by
  -- spine data
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  have hspineLen : (fvsP ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPLen, hxLen]
  have hshSpine : ∀ a ∈ fvsP ++ xFvsP, ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
      exact ⟨0 + j, nm, _, hsh⟩
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hxShape j a hja
      exact ⟨rP + j, nm, _, hsh⟩
  -- the rule right-hand side's λ-tower shape
  have hstripSome := instLamsAt_stripLams_isSome _ hshSpine hlinst
  rw [hspineLen] at hstripSome
  obtain ⟨⟨rbs, rbody⟩, hstripR⟩ :=
    Option.isSome_iff_exists.mp hstripSome
  -- the canonical decomposition computes
  have hparts : ruleLhsParts R cv rP r cvj =
      some ((fvsP ++ xFvsP).zip (rbs.map (·.2.2)),
        Expr.mkAppN (.const R (cv.levelParams.map .param))
          (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
            [Expr.mkAppN (.const (RecRule.ctor r) lvls)
              (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
                xFvsP)])) := by
    simp only [ruleLhsParts, hcvty, hopenP, hfire, ruleLhsAux,
      hcinstN, hrnf, hopenX, hrrhs,
      show rhsA.stripLams (rP + cnF) = some (rbs, rbody) from hstripR]
  refine ⟨_, _, hparts, ?_⟩
  have hpinsWf : ∀ lvls' pins', RecRule.fire r = .nested lvls' pins' →
      ∀ p ∈ pins', p.hasFvar = false ∧
        p.looseBVarsBounded rP = true := by
    intro lvls' pins' hcon
    rw [hfire] at hcon
    cases hcon
    exact hpinsW
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts
    (by rw [hcvty]; exact htyw) (by rw [hcvty]; exact htyb) hCw hCb
    hpinsWf
  refine ⟨hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts (by rw [hfR]; rfl)
      (by rw [hrctor, hfC]; rfl) hTres hCres
      (fun lvls' pins' hcon => by
        rw [hfire] at hcon
        cases hcon
        exact hpinsRes)
  -- the semantic clause, per level assignment
  intro ψ
  have hCtw : (cvj.type.instantiateLevelParams cvj.levelParams
      lvls).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hCw
  have hCtb : (cvj.type.instantiateLevelParams cvj.levelParams
      lvls).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hACt : AnnotOk V m₀.val env₀ ψ 0 (rho0 V)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) :=
    AnnotOk.instLevels hcvp cvj.type 0 (rho0 V)
      (hACty (Level.substFn ψ cvj.levelParams lvls))
  have hICt : ∃ T, interpClosed V m₀.val env₀ ψ
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some T := by
    obtain ⟨T, hT⟩ := hICty (Level.substFn ψ cvj.levelParams lvls)
    refine ⟨T, ?_⟩
    unfold interpClosed
    rw [interp_instLevels hcvp cvj.type 0 (rho0 V)]
    exact hT
  have hctorPkg := ctor_pkg_nested (xFvsP := xFvsP) m₀ F hopenP htyw
    htyb (hAty ψ) (hIty ψ) hstripM hdomFn hdomArgs hpinsW hcinstN
    htlP hCtw hCtb hACt hICt
  have hstage := modeled_stage m₀ F hopenP htyw htyb (hAty ψ) (hIty ψ)
    hopenX hctorPkg hlinst hdeLam hrhsw hrhsb (hArhs ψ) (hIrhs ψ)
  have hbot := modeled_bottom_nested m₀ F hro hcvp hfR hRlps hfRm
    hRmlps hfCm hCmlps hfC hClps heqfind heqval hthm_mem hthm_annot
    hSw hSb hmIrP hstripM hdomFn hdomArgs hpinsW hpinsLen hpinsRen2
    hopen hheadEq hargs3 hlhead hlarity hlpre hmaj hCstripSome hCps
    hcinst hclen hrinst hdePre hdeFld hcrest2Len hopenP hcinstN htlP
    hopenX hlinst hdeLam hdeRhs hrhsw hrhsb (hArhs ψ) (hIrhs ψ) htyw
    htyb (hAty ψ) (hIty ψ) hCw hCb hACty hICty
  -- frame bookkeeping for the tower recursion
  have hrbsLen : rbs.length = rP + cnF := Expr.stripLams_length _ hstripR
  have hzipFst : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).map Prod.fst =
      fvsP ++ xFvsP :=
    List.map_fst_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hzipSnd : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).map (·.2) =
      rbs.map (·.2.2) :=
    List.map_snd_zip (by
      rw [hspineLen, List.length_map, hrbsLen]
      omega)
  have hfvmsLen : ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))).length =
      rP + cnF := by
    rw [List.length_zip, hspineLen, List.length_map, hrbsLen]
    simp
  -- the tower spec from the flat stage facts
  have htower := TowerOk.of_stages (cval := m₀.val) (env := env₀)
    (φ := ψ)
    (bL := Expr.mkAppN (.const R (cv.levelParams.map .param))
      (fvsP ++ crest2.getAppArgs.drop (RecRule.ctorParams r) ++
        [Expr.mkAppN (.const (RecRule.ctor r) lvls)
          (pins.map (fun p => Expr.instSpine fvsP (rP - 1) p) ++
            xFvsP)]))
    (lrest := lrest)
    (fvms := (fvsP ++ xFvsP).zip (rbs.map (·.2.2)))
    (ldoms := ldoms)
    (Ok := FramePref m₀.val env₀ ψ (fvsP ++ xFvsP))
    (Hty := by
      intro k xs fv m ld hxs hfv hld hOk
      have hfv' : (fvsP ++ xFvsP)[k]? = some fv := by
        have h0 := congrArg (·[k]?) hzipFst
        simp only [List.getElem?_map] at h0
        rw [← h0, hfv]
        rfl
      obtain ⟨A, h1, h2, h3, h4⟩ := hstage k xs fv ld hxs hfv' hld hOk
      exact ⟨A, h1, h2, h3, h4⟩)
    (Hbot := by
      intro xs hxs hOk
      rw [hfvmsLen] at hxs
      have h := hbot xs hxs hOk
      rw [hfvmsLen, hcvlps, hrcp, hrctor]
      exact h)
    ((fvsP ++ xFvsP).zip (rbs.map (·.2.2))) 0 [] ldoms
    (RecRule.rhs r) (RecRule.rhs r)
    (by rw [Nat.zero_add])
    rfl rfl rfl
    (by
      intro j p hp
      have h0 := congrArg (·[j]?) hzipFst
      simp only [List.getElem?_map] at h0
      have hp1 : (fvsP ++ xFvsP)[j]? = some p.1 := by
        rw [← h0, hp]
        rfl
      rcases Nat.lt_or_ge j rP with hj | hj
      · rw [List.getElem?_append_left (by omega)] at hp1
        obtain ⟨nm, hsh⟩ := hfvsPShape j p.1 hp1
        rw [Nat.zero_add] at hsh
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add]
        exact hsh
      · rw [List.getElem?_append_right (by omega), hfvsPLen] at hp1
        obtain ⟨nm, hsh⟩ := hxShape (j - rP) p.1 hp1
        refine ⟨nm, Expr.fvarTypeD p.1, ?_⟩
        rw [Nat.zero_add, hsh]
        congr 1
        omega)
    (Expr.ErasedEq.rfl _)
    (by
      rw [hzipFst, hrrhs]
      exact hlinst)
    (by
      refine ⟨rbs, rbody, ?_, hzipSnd⟩
      rw [hfvmsLen, hrrhs]
      exact hstripR)
    (fun j v fv hjv _ => nomatch hjv)
  -- canonicalize the empty frame and consume the tower
  have hrho : (fun i => ([] : List V).getD i SetTheory.empty) =
      rho0 V := by
    funext i
    rfl
  rw [hrho] at htower
  obtain ⟨⟨Rv, hL, hR⟩, hAL⟩ := TowerOk.out htower hwf
    (by rw [hrrhs]; exact hArhs ψ)
  exact ⟨hAL, Rv, hL, hR⟩

end Setlec
