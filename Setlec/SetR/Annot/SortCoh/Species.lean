import Setlec.SetR.Annot.SortCoh.ThetaRel

/-!
# Species suppliers (the preservation families, `EnvWF`-backed)

The `Q`-free species discharged from the landed Verify-tier
preservation batteries: the subject package (`SubjInv`) and the
cross-pairing travel along core steps, unfoldings, nat fires and
projection fires by leaf-subset monotonicity plus the
scoped/bounded preservation lemmas.  The `Q`-parametric species
remain named hypotheses (they discharge at the consumer's concrete
`Q`).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-- Cross-pairing restricts along a left-side leaf subset. -/
theorem PairedLeaves.sub_left {a a' c : Expr}
    (hsub : ∀ l ∈ a'.fvarLeaves, l ∈ a.fvarLeaves)
    (hp : PairedLeaves a c) : PairedLeaves a' c := by
  intro l hl l' hl' heq
  refine hp l ?_ l' ?_ heq
  · rcases List.mem_append.mp hl with h | h
    · exact List.mem_append.2 (Or.inl (hsub _ h))
    · exact List.mem_append.2 (Or.inr h)
  · rcases List.mem_append.mp hl' with h | h
    · exact List.mem_append.2 (Or.inl (hsub _ h))
    · exact List.mem_append.2 (Or.inr h)

/-- Leaf-annotation bounds restrict along a leaf subset. -/
theorem LeavesBounded.sub {a a' : Expr}
    (hsub : ∀ l ∈ a'.fvarLeaves, l ∈ a.fvarLeaves)
    (hL : Expr.LeavesBounded a) : Expr.LeavesBounded a' :=
  fun l hl => hL l (hsub l hl)

/-- The subject package travels along a leaf-subset-preserving,
scoped/bounded-preserving step. -/
theorem SubjInv.step {d : Nat} {e e' : Expr}
    (hw : Expr.WScoped d e') (hb : e'.looseBVarsBounded 0 = true)
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
    (hI : SubjInv d e) : SubjInv d e' :=
  ⟨hw, hb, LeavesBounded.sub hsub hI.2.2.1, fun l hl l' hl' heq =>
    hI.2.2.2 l (by
      rcases List.mem_append.mp hl with h | h <;>
        exact List.mem_append.2 (Or.inl (hsub _ h)))
      l' (by
        rcases List.mem_append.mp hl' with h | h <;>
          exact List.mem_append.2 (Or.inl (hsub _ h))) heq⟩

/-- `LeavesSubCoreF`, supplied. -/
theorem leavesSubCoreF_of (henv : EnvWF env) :
    LeavesSubCoreF μ env :=
  fun h => Setlec.whnfCore_leaves (mode := μ) henv _ h

/-- `InvPreserveCoreF`, supplied. -/
theorem invPreserveCoreF_of (henv : EnvWF env) :
    InvPreserveCoreF μ env := by
  intro f d e e' h hI
  exact SubjInv.step
    (Setlec.whnfCore_WScoped (mode := μ) henv f h hI.1)
    (Setlec.whnfCore_looseBVars (mode := μ) henv f h hI.2.1)
    (Setlec.whnfCore_leaves (mode := μ) henv f h) hI

/-- `InvPreserveDeltaF`, supplied. -/
theorem invPreserveDeltaF_of (henv : EnvWF env) :
    InvPreserveDeltaF env := by
  intro d e e' h hI
  obtain ⟨hb, hw⟩ := unfoldDefinition_pres henv h hI.2.1 hI.1
  exact SubjInv.step hw hb
    (Setlec.unfoldDefinition_leaves henv h) hI

/-- `InvPreserveNatF`, supplied. -/
theorem invPreserveNatF_of (_henv : EnvWF env) :
    InvPreserveNatF μ env := by
  intro f d e e' h hI
  rw [Setlec.reduceNat_fold] at h
  have hsh := Setlec.reduceNat_inv (mode := μ) h
  refine SubjInv.step ?_ ?_ ?_ hI
  · exact Setlec.Expr.WScoped.of_not_hasFvar (by
      rcases hsh with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl)
  · rcases hsh with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
  · intro l hl
    exfalso
    rcases hsh with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
      simp [Setlec.Expr.fvarLeaves] at hl

/-- `PairedPreserveCoreF`, supplied. -/
theorem pairedPreserveCoreF_of (henv : EnvWF env) :
    PairedPreserveCoreF μ env :=
  fun h hp => PairedLeaves.sub_left
    (Setlec.whnfCore_leaves (mode := μ) henv _ h) hp

/-- `PairedPreserveDeltaF`, supplied. -/
theorem pairedPreserveDeltaF_of (henv : EnvWF env) :
    PairedPreserveDeltaF env :=
  fun h hp => PairedLeaves.sub_left
    (Setlec.unfoldDefinition_leaves henv h) hp

/-- `PairedPreserveNatF`, supplied. -/
theorem pairedPreserveNatF_of (_henv : EnvWF env) :
    PairedPreserveNatF μ env := by
  intro f d e e' c h hp
  rw [Setlec.reduceNat_fold] at h
  have hsh := Setlec.reduceNat_inv (mode := μ) h
  refine PairedLeaves.sub_left ?_ hp
  intro l hl
  exfalso
  rcases hsh with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
    simp [Setlec.Expr.fvarLeaves] at hl

/-- `StoredWF`, supplied (values are `fvar`-free, hence leaf-nil
and vacuously leaf-bounded). -/
theorem storedWF_of (henv : EnvWF env) : StoredWF env := by
  intro n cv value hfind
  rcases hfind with ⟨hint, hf⟩ | hf
  · obtain ⟨-, -, -, -, hval, -⟩ := henv _ (Setlec.find?_mem hf)
    obtain ⟨hvc, -, -, hvb⟩ := hval cv value hint rfl
    refine ⟨Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hvc, hvb,
      ?_⟩
    intro l hl
    rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hvc] at hl
    exact absurd hl List.not_mem_nil
  · obtain ⟨-, -, -, -, -, -, hval⟩ := henv _ (Setlec.find?_mem hf)
    obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
    refine ⟨Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hvc, hvb,
      ?_⟩
    intro l hl
    rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hvc] at hl
    exact absurd hl List.not_mem_nil

/-- The projection-scrutinee literal conversion preserves the
closedness package and shrinks leaves into the input's. -/
theorem projLit_pres (henv : EnvWF env) {g dd : Nat} {w e₃ : Expr}
    (h : Setlec.projLitToCtorP μ env g dd w = .ok e₃)
    (hb : w.looseBVarsBounded 0 = true)
    (hw : Expr.WScoped dd w) :
    e₃.looseBVarsBounded 0 = true ∧ Expr.WScoped dd e₃ ∧
      ∀ l ∈ e₃.fvarLeaves, l ∈ w.fvarLeaves := by
  rcases Setlec.projLitToCtorP_inv (mode := μ) h with
    rfl | ⟨s, rfl, hsupp, hred⟩
  · exact ⟨hb, hw, fun l hl => hl⟩
  · have hb₃ : e₃.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars (mode := μ) henv g hred
        (strLitToConstructor_bounded s)
    have hfv₃ : e₃.hasFvar = false :=
      whnf_closed_out_fvarfree henv
        (strLitToConstructor_not_hasFvar s) hred
    refine ⟨hb₃, Setlec.Expr.WScoped.of_not_hasFvar hfv₃, ?_⟩
    intro l hl
    rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv₃] at hl
    exact absurd hl List.not_mem_nil

/-- The fired field's leaves sit inside the scrutinee's (facts-free
chain through the conversion rows). -/
theorem projFire_field_leaves (henv : EnvWF env)
    {g d i nP : Nat} {e w e₃ h' : Expr}
    (hwf : whnf μ env g d e = .ok w)
    (hlit : Setlec.projLitToCtorP μ env g d w = .ok e₃)
    (hilt : nP + i < e₃.getAppArgs.length)
    (hred : whnfCore μ env g d
      (e₃.getAppArgs.getD (nP + i) (.bvar 0)) = .ok h') :
    ∀ l ∈ h'.fvarLeaves, l ∈ e.fvarLeaves := by
  intro l hl
  have hl₃ : l ∈ e₃.fvarLeaves :=
    Setlec.fvarLeaves_getAppArgs (Setlec.getD_mem hilt) _
      (Setlec.whnfCore_leaves (mode := μ) henv g hred _ hl)
  have hlw : l ∈ w.fvarLeaves := by
    rcases Setlec.projLitToCtorP_inv (mode := μ) hlit with
      rfl | ⟨s, rfl, hsupp, hred'⟩
    · exact hl₃
    · exfalso
      have := Setlec.whnf_leaves (mode := μ) henv g hred' _ hl₃
      rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (strLitToConstructor_not_hasFvar s)] at this
      exact absurd this List.not_mem_nil
  exact Setlec.whnf_leaves (mode := μ) henv g hwf _ hlw

/-- The fired-field extraction under the projection fire, packaged:
facts and leaf inclusion for `h'` from the scrutinee's. -/
theorem projFire_field_pres (henv : EnvWF env)
    {g d i : Nat} {e w e₃ h' : Expr} {entry : Setlec.ProjEntry}
    (hwf : whnf μ env g d e = .ok w)
    (hlit : Setlec.projLitToCtorP μ env g d w = .ok e₃)
    (hi : i < entry.numFields)
    (hlen : e₃.getAppArgs.length
      = entry.numParams + entry.numFields)
    (hred : whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h')
    (hb : e.looseBVarsBounded 0 = true)
    (hw : Expr.WScoped d e) :
    h'.looseBVarsBounded 0 = true ∧ Expr.WScoped d h' ∧
      ∀ l ∈ h'.fvarLeaves, l ∈ e.fvarLeaves := by
  have hbw := Setlec.whnf_looseBVars (mode := μ) henv g hwf hb
  have hww := Setlec.whnf_WScoped (mode := μ) henv g hwf hw
  obtain ⟨hb₃, hw₃, hl₃⟩ := projLit_pres henv hlit hbw hww
  have hilt : entry.numParams + i < e₃.getAppArgs.length := by
    omega
  have hbf : (e₃.getAppArgs.getD (entry.numParams + i)
      (.bvar 0)).looseBVarsBounded 0 = true :=
    Setlec.looseBVarsBounded_getAppArgs hb₃ _
      (Setlec.getD_mem hilt)
  have hwf' : Expr.WScoped d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) :=
    Setlec.Expr.WScoped.getAppArgs hw₃ _ (Setlec.getD_mem hilt)
  exact ⟨Setlec.whnfCore_looseBVars (mode := μ) henv g hred hbf,
    Setlec.whnfCore_WScoped (mode := μ) henv g hred hwf',
    projFire_field_leaves henv hwf hlit hilt hred⟩

/-- `InvPreserveProjFireF`, supplied. -/
theorem invPreserveProjFireF_of (henv : EnvWF env) :
    InvPreserveProjFireF μ env := by
  intro g d i sn e w e₃ h' entry us as hwf hlit hfn hf hnat hi
    hlen hred hI
  obtain ⟨hwHd, hwArgs⟩ := wScoped_mkAppN_parts hI.1
  obtain ⟨hbHd, hbArgs⟩ := looseBVarsBounded_mkAppN_parts hI.2.1
  have hwE : Expr.WScoped d e := by
    simpa only [Expr.WScoped] using hwHd
  have hbE : e.looseBVarsBounded 0 = true := by
    simpa only [Setlec.Expr.looseBVarsBounded] using hbHd
  obtain ⟨hbH, hwH, hlH⟩ := projFire_field_pres henv hwf hlit hi
    hlen hred hbE hwE
  refine SubjInv.step
    (Setlec.Expr.WScoped.mkAppN hwH hwArgs)
    (Setlec.looseBVarsBounded_mkAppN hbH hbArgs) ?_ hI
  intro l hl
  rcases fvarLeaves_mkAppN hl with hlh | ⟨x, hx, hlx⟩
  · exact mem_fvarLeaves_mkAppN_head (by
      show l ∈ (Expr.proj sn i e).fvarLeaves
      simpa only [Setlec.Expr.fvarLeaves] using hlH l hlh)
  · exact mem_fvarLeaves_mkAppN_arg hx hlx

/-- `PairedPreserveProjFireF`, supplied. -/
theorem pairedPreserveProjFireF_of (henv : EnvWF env) :
    PairedPreserveProjFireF μ env := by
  intro g d i sn e w e₃ h' c entry us as hwf hlit hfn hf hnat hi
    hlen hred hp
  have hsub : ∀ l ∈ (Setlec.Expr.mkAppN h' as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN (.proj sn i e) as).fvarLeaves := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with hlh | ⟨x, hx, hlx⟩
    · refine mem_fvarLeaves_mkAppN_head ?_
      show l ∈ (Expr.proj sn i e).fvarLeaves
      have := projFire_field_leaves henv hwf hlit
        (by omega : entry.numParams + i
          < e₃.getAppArgs.length) hred l hlh
      simpa only [Setlec.Expr.fvarLeaves] using this
    · exact mem_fvarLeaves_mkAppN_arg hx hlx
  exact PairedLeaves.sub_left hsub hp

end Discharge

end Setlec.SetR.Interp2
