module

public import ConLeche.Verify.EnvExt.ScOps

public section

/-!
# Env extension, part 3: the fuel-free readers agree

Every fuel-free reader of the environment the knot's bodies call
(`Kernel/CoreDefs.lean`, `Kernel/PropRead.lean`) answers the same in two
environments that `Agree` on a scope, at a scoped argument — and what
it returns is scoped.  These are the leaves of the body walk
(`EnvExt/Bodies*.lean`): each site of the audit (DESIGN.md, ENVEXT) is
one lemma here.
-/

namespace ConLeche.EnvExt

open ConLeche

theorem sc_default {N : Name → Prop} : Sc N (default : Expr) := trivial

/-- The head of a scoped term is scoped. -/
theorem head_const_N {N : Name → Prop} {e : Expr} (he : Sc N e) {n : Name} {us : List Level}
    (h : e.getAppFn = .const n us) : N n := by
  have := sc_getAppFn he; rw [h] at this; exact sc_const.mp this

namespace Agree

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
include H

/-! ## Kind S: the head constant -/

theorem isCtorApp_eq {e : Expr} (he : Sc N e) : isCtorApp E₂ e = isCtorApp E₁ e := by
  unfold isCtorApp
  split
  · rename_i n us h; rw [H.find (head_const_N he h)]
  · rfl

theorem unfoldDefinition_eq {e : Expr} (he : Sc N e) :
    unfoldDefinition E₂ e = unfoldDefinition E₁ e := by
  unfold unfoldDefinition
  split
  · rename_i n us h; rw [H.find (head_const_N he h)]
  · rfl

theorem unfoldDefinition_sc {e r : Expr} (he : Sc N e) (h : unfoldDefinition E₁ e = some r) :
    Sc N r := by
  unfold unfoldDefinition at h
  split at h
  · rename_i n us hfn
    split at h
    · rename_i cv value hint hfind
      split at h
      · cases h
        have hc := H.closed (head_const_N he hfn) hfind
        simp only [CiSc] at hc
        exact sc_mkAppN (sc_instantiateLevelParams _ _ _ hc.2) (sc_getAppArgs he)
      · cases h
    · cases h
  · cases h

theorem unfoldableHead_eq {e : Expr} (he : Sc N e) :
    unfoldableHead E₂ e = unfoldableHead E₁ e := by
  unfold unfoldableHead
  split
  · rename_i n us h; rw [H.find (head_const_N he h)]
  · rfl

theorem headHint_eq {e : Expr} (he : Sc N e) : headHint E₂ e = headHint E₁ e := by
  unfold headHint
  split
  · rename_i n us h; rw [H.find (head_const_N he h)]
  · rfl

theorem natOpStored_eq {c : Name} (hc : N c) : natOpStored E₂ c = natOpStored E₁ c := by
  unfold natOpStored; rw [H.find hc]

theorem etaCtorShape_eq {e : Expr} (he : Sc N e) :
    etaCtorShape E₂ e = etaCtorShape E₁ e := by
  unfold etaCtorShape
  split
  · rename_i n us h; rw [H.find (head_const_N he h)]
  · rfl

/-! ## Kind F: the fixed names -/

theorem isUnitLikeTy_eq (e : Expr) : isUnitLikeTy E₂ e = isUnitLikeTy E₁ e := by
  unfold isUnitLikeTy
  split
  · rw [H.find H.fixed_punit, H.find H.fixed_punitRec]
  · rfl

theorem natLitSupported_eq : natLitSupported E₂ = natLitSupported E₁ := by
  unfold natLitSupported
  rw [H.find H.fixed_nat, H.find H.fixed_natZero, H.find H.fixed_natSucc]

theorem strLitSupported_eq : strLitSupported E₂ = strLitSupported E₁ := by
  unfold strLitSupported
  rw [H.natLitSupported_eq, H.find H.fixed_string, H.find H.fixed_stringOfList,
    H.find H.fixed_list, H.find H.fixed_listNil, H.find H.fixed_listCons,
    H.find H.fixed_char, H.find H.fixed_charOfNat]

theorem litToCtorIfNat_eq (e : Expr) : litToCtorIfNat E₂ e = litToCtorIfNat E₁ e := by
  unfold litToCtorIfNat
  split
  · rw [H.natLitSupported_eq]
  · rfl

theorem litToCtorIfNat_sc {e : Expr} (he : Sc N e) : Sc N (litToCtorIfNat E₁ e) := by
  unfold litToCtorIfNat
  split
  · split
    · exact sc_natLitToConstructor H _
    · exact sc_lit
  · exact he

theorem andRescueSlots_eq (ctor : Name) (nP : Nat) (ust : List Level) :
    andRescueSlots E₂ ctor nP ust = andRescueSlots E₁ ctor nP ust := by
  unfold andRescueSlots andRescueSlotsOf
  have : E₂.findProj? andName = E₁.findProj? andName := by
    funext i; unfold Env.findProj?; rw [H.find H.fixed_andTable]
  rw [this]

/-! ## Kind D: the derived names -/

theorem towerSlotsAll_eq {T : Name} (hT : N T) (nF : Nat) :
    towerSlotsAll E₂ T nF = towerSlotsAll E₁ T nF := by
  unfold towerSlotsAll
  simp only [H.findProj? hT]

theorem recSlotsAll_eq {T : Name} (hT : N T) (nF : Nat) :
    recSlotsAll E₂ T nF = recSlotsAll E₁ T nF := by
  unfold recSlotsAll
  congr 1; funext j; rw [H.find (H.projFn j hT)]

theorem etaProjs_eq {T : Name} (hT : N T) (us : List Level) (targs : List Expr) (b : Expr)
    (nF : Nat) : etaProjs E₂ T us targs b nF = etaProjs E₁ T us targs b nF := by
  unfold etaProjs; rw [H.towerSlotsAll_eq hT]

theorem etaProjs_sc {T : Name} (hT : N T) {us : List Level} {targs : List Expr} {b : Expr}
    {nF : Nat} (htargs : ∀ a ∈ targs, Sc N a) (hb : Sc N b) :
    ∀ x ∈ etaProjs E₁ T us targs b nF, Sc N x := by
  unfold etaProjs
  split
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact sc_proj.mpr ⟨hT, hb⟩
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact sc_mkAppN (sc_const.mpr (H.projFn j hT))
      (sc_mem_append htargs (by simpa using hb))

theorem etaFabArgsE_eq {T : Name} (hT : N T) (us : List Level) (targs : List Expr)
    (b : Expr) (nF : Nat) :
    etaFabArgsE E₂ T us targs b nF = etaFabArgsE E₁ T us targs b nF := by
  unfold etaFabArgsE; rw [H.etaProjs_eq hT]

theorem etaFabArgsE_sc {T : Name} (hT : N T) {us : List Level} {targs : List Expr}
    {b : Expr} {nF : Nat} (htargs : ∀ a ∈ targs, Sc N a) (hb : Sc N b) :
    ∀ x ∈ etaFabArgsE E₁ T us targs b nF, Sc N x := by
  unfold etaFabArgsE
  exact sc_mem_append htargs (H.etaProjs_sc hT htargs hb)

/-! ## Kind C: stored data read back -/


/-- A projection-table entry read at a scoped structure name has a
scoped body. -/
theorem findProj?_sc {T : Name} (hT : N T) {i : Nat} {entry : ProjEntry}
    (h : E₁.findProj? T i = some entry) : Sc N entry.body := by
  unfold Env.findProj? at h
  split at h
  · rename_i tbl hfind
    split at h
    · cases h
      have hc := H.closed (H.table hT) hfind
      simp only [CiSc] at hc
      show Sc N (tbl.bodies.getD i default)
      rw [Array.getD_eq_getD_getElem?]
      cases hb : tbl.bodies[i]? with
      | none => exact sc_default
      | some b => exact hc b (by simpa using Array.mem_of_getElem? hb)
    · cases h
  · cases h

theorem typeAt_sc {T : Name} (hT : N T) {i : Nat} {entry : ProjEntry}
    (h : E₁.findProj? T i = some entry) (us : List Level) {targs : List Expr} {pe : Expr}
    (htargs : ∀ a ∈ targs, Sc N a) (hpe : Sc N pe) : Sc N (entry.typeAt us targs pe) := by
  unfold ProjEntry.typeAt
  refine sc_instantiateList _ _ _ ?_ (sc_instantiateLevelParams _ _ _ (H.findProj?_sc hT h))
  intro v hv
  simp only [List.mem_cons, List.mem_reverse] at hv
  rcases hv with rfl | hv
  · exact hpe
  · exact htargs v hv

/-- A stored constant's type is scoped. -/
theorem stored_type_sc {n : Name} (hn : N n) {ci : ConstantInfo} (h : E₁.find? n = some ci) :
    Sc N ci.toConstantVal.type := by
  have hc := H.closed hn h
  cases ci <;> simp only [CiSc, ConstantInfo.toConstantVal] at hc ⊢ <;>
    first | exact hc | exact hc.1 | exact sc_sort

/-- A stored constant's type, level-instantiated, is scoped. -/
theorem const_type_sc {n : Name} (hn : N n) {ci : ConstantInfo} (h : E₁.find? n = some ci)
    (ks : List Name) (us : List Level) :
    Sc N (ci.toConstantVal.type.instantiateLevelParams ks us) :=
  sc_instantiateLevelParams _ _ _ (H.stored_type_sc hn h)

/-! ## The head-symbol readers (`Kernel/PropRead.lean`) -/

theorem headTypePW_eq {e : Expr} (he : Sc N e) (n : Nat) :
    headTypePW E₂.find? e n = headTypePW E₁.find? e n := by
  unfold headTypePW
  split
  · rename_i I us; rw [H.find (sc_const.mp he)]
  · rfl
  · rfl

theorem typeSortPW_eq {T : Expr} (hT : Sc N T) :
    typeSortPW E₂.find? T = typeSortPW E₁.find? T := by
  unfold typeSortPW
  split
  · rfl
  · rfl
  · exact H.headTypePW_eq (sc_getAppFn hT) _

theorem headProofPW_eq {e : Expr} (he : Sc N e) :
    headProofPW E₂.find? e = headProofPW E₁.find? e := by
  unfold headProofPW
  split
  · rename_i c us
    have hc : N c := sc_const.mp he
    rw [H.find hc]
    cases hf : E₁.find? c with
    | none => rfl
    | some ci =>
      simp only
      rw [H.typeSortPW_eq (H.stored_type_sc hc hf)]
  · rename_i idx ty; exact H.typeSortPW_eq (sc_fvar.mp he)
  all_goals rfl

theorem proofPW_eq {a : Expr} (ha : Sc N a) : proofPW E₂.find? a = proofPW E₁.find? a := by
  unfold proofPW
  split
  · rfl
  · exact H.headProofPW_eq (sc_getAppFn ha)

theorem notProofFast_eq {a : Expr} (ha : Sc N a) :
    notProofFast E₂.find? a = notProofFast E₁.find? a := by
  unfold notProofFast; rw [H.proofPW_eq ha]

theorem isProofFast_eq {a : Expr} (ha : Sc N a) :
    isProofFast E₂.find? a = isProofFast E₁.find? a := by
  unfold isProofFast; rw [H.proofPW_eq ha]

end Agree

theorem recFireComparands_sc {N : Name → Prop} {rl : RecRule} (hrl : RuleSc N rl) (lps : List Name)
    (us : List Level) (cvjLps : List Name) {args : List Expr} (hargs : ∀ a ∈ args, Sc N a)
    (rP : Nat) : ∀ x ∈ (recFireComparands rl lps us cvjLps args rP).2, Sc N x := by
  unfold recFireComparands
  split
  · rename_i lvls pins hfire
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact sc_instSpine (sc_mem_take hargs)
      (sc_instantiateLevelParams _ _ _ (hrl.2.2 lvls pins hfire p hp))
  · exact sc_mem_take hargs


end ConLeche.EnvExt
