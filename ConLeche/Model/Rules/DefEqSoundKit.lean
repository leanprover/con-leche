module

public import ConLeche.Model.Rules.Motive
public import ConLeche.Model.Inductives.StructIntro
import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
public import ConLeche.Semantics.DefEqStep
public import ConLeche.Semantics.Hoist

public section

/-!
# The definitional-equality soundness kit (task #305, lane S-defeq)

The plumbing the per-rule lemmas of `Model/Rules/DefEqSound.lean`
share: the frame/grading splitters at each node shape, the two `Nat`
constant readings, and `projAV`'s congruence.  Everything here is a
TRANSPLANT of an argument that lives today in `Model/Steps/*`
(`DefEq.lean`'s `hoist_*` and `denoteMeta_nat*Const`,
`ProjAVKit.lean`'s `projAV` family) — restated at the rules tier's
`Frame`/`Graded` vocabulary, so that no `Model/Rules` module imports a
file stated over runs.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The frame splitters -/

theorem Frame.app_fn {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d f := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.app_arg {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.proj_arg {d : Nat} {s : Name} {i : Nat} {e : Expr}
    (h : Frame d (.proj s i e)) : Frame d e := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded] at hb
  exact ⟨hw, hb, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

/-- The opened body's frame, at an arbitrary (well-framed) domain —
`binder_congr`'s `hLo₁`/`hLo₂` plus its two scoping arguments. -/
theorem Frame.open_body {d : Nat} {ty' bd : Expr} (hty' : Frame d ty')
    (hwb : Expr.WScoped d bd) (hbb : bd.looseBVarsBounded 1 = true)
    (hLb : Expr.LeavesBounded bd) :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  refine ⟨Expr.WScoped.instantiate1 hty'.1 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 bd 0 hbb, ?_⟩
  intro l hl
  rcases ConLeche.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
  · exact hLb l h2
  · rw [ConLeche.Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hty'.2.1
    · exact hty'.2.2 l h3

theorem Frame.forallE_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.forallE ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.forallE_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.forallE ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.lam_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.lam ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.lam_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.lam ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.of_not_hasFvar {d : Nat} {e : Expr} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) : Frame d e :=
  ⟨Expr.WScoped.of_not_hasFvar hf, hb, Expr.LeavesBounded.of_not_hasFvar hf⟩

/-! ## The grading splitters — `Steps/DefEq.lean`'s `hoist_*`, at
`Graded` -/

theorem Graded.app {Δa : List AnnotTerm} {f a : AnnotTerm}
    (h : Graded V Δa (.app f a)) :
    Graded V Δa f ∧ Graded V Δa a := by
  refine ⟨fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).1, ?_⟩,
    fun ρ hρ => ⟨((WellDenoted_app V ρ f a) ▸ (h ρ hρ).1).2.1, ?_⟩⟩
  · exact ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).1
  · exact ((AnnotValid_app V ρ f a) ▸ (h ρ hρ).2).2

theorem Graded.fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.fst e)) : Graded V Δa e := fun ρ hρ =>
  ⟨((WellDenoted_fst V ρ e) ▸ (h ρ hρ).1).1,
    (AnnotValid_fst V ρ e) ▸ (h ρ hρ).2⟩

theorem Graded.snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.snd e)) : Graded V Δa e := fun ρ hρ =>
  ⟨((WellDenoted_snd V ρ e) ▸ (h ρ hρ).1).1,
    (AnnotValid_snd V ρ e) ▸ (h ρ hρ).2⟩

/-- `hoist_pi` (`Steps/DefEq.lean:141`) at `Graded`. -/
theorem Graded.pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : Graded V Δa (.pi u v A B)) :
    Graded V Δa A ∧ Graded V (A :: Δa) B := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_pi V _ u v A B) ▸
      (h _ (Sat_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- `hoist_lam` (`Steps/DefEq.lean:155`) at `Graded`. -/
theorem Graded.lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : Graded V Δa (.lam v A b)) :
    Graded V Δa A ∧ Graded V (A :: Δa) b := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_lam V _ v A b) ▸
      (h _ (Sat_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

/-- The head transport of a hoisted grading, at `Graded`. -/
theorem Graded.head_congr {Δa : List AnnotTerm} {A B e : AnnotTerm}
    (heq : ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ A = interp V ρ B)
    (h : Graded V (B :: Δa) e) : Graded V (A :: Δa) e :=
  fun ρ hρ => h ρ (Sat.head_congr heq hρ)

/-! ## The two `Nat` constant readings (`Steps/DefEq.lean:99`, `:119`) -/

/-- `Nat.zero`, in the validated reading. -/
theorem denoteMeta_natZeroConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natZeroName [])
      = some (acval ConLeche.natZeroName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? ConLeche.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h2
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [ConLeche.natZeroOk] at h2
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- `Nat.succ`, in the validated reading. -/
theorem denoteMeta_natSuccConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natSuccName [])
      = some (acval ConLeche.natSuccName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? ConLeche.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h3
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [ConLeche.natSuccOk] at h3
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- The opened body's reading does not see the domain annotation
(`binder_congr`'s `hva₁'`). -/
theorem denoteMeta_open_rename {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {bd ty ty' : Expr} {ba : AnnotTerm}
    (h : denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty))
      = some ba) :
    denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty'))
      = some ba := by
  rw [denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl bd)
    (show Expr.ErasedEq (.fvar d ty') (.fvar d ty) from rfl))]
  exact h

/-! ## The constant congruence (`Steps/DefEq.lean:844`) -/

/-- The same constant at level-equivalent instantiations has one
validated reading. -/
theorem acval_const_congr' {m : EnvModel V env} (hap : AcvalParams m)
    {d : Nat} {n : Name} {us us' : List Level} {aa ba : AnnotTerm}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denoteMeta m.acval env φ d (.const n us) = some aa)
    (hdb : denoteMeta m.acval env φ d (.const n us') = some ba) :
    aa = ba := by
  rw [denoteMeta] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine hap n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-! ## `projAV` at equal-valued subjects (`Steps/ProjAVKit.lean`) -/

theorem WellDenoted_projAV_hoist' :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (projAV i e) → WellDenoted V σ e
  | 0, e, σ, h => ((WellDenoted_fst V σ e) ▸ h).1
  | i + 1, e, σ, h =>
    ((WellDenoted_snd V σ e) ▸
      (WellDenoted_projAV_hoist' (i := i) (e := .snd e) h)).1

theorem AnnotValid_projAV_hoist' :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ (projAV i e) → AnnotValid V σ e
  | 0, e, σ, h => (AnnotValid_fst V σ e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValid_snd V σ e) ▸
      (AnnotValid_projAV_hoist' (i := i) (e := .snd e) h)

theorem Graded.projAV {Δa : List AnnotTerm} {i : Nat} {e : AnnotTerm}
    (h : Graded V Δa (ConLeche.Semantics.projAV i e)) : Graded V Δa e :=
  fun ρ hρ =>
    ⟨WellDenoted_projAV_hoist' (h ρ hρ).1, AnnotValid_projAV_hoist' (h ρ hρ).2⟩

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp_projAV_congr' {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') :
    interp V σ (projAV i e) = interp V σ (projAV i e') := by
  rw [projAV_interp, projAV_interp, heq]

end ConLeche.Model.Rules
