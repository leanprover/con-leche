module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Inductives.StructIntro
import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.PropRead
import ConLeche.Model.IOLicense
import ConLeche.Model.Annot.BitClosed
import ConLeche.Verify.PinnedShapes
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but
not `@[expose]`d, so the `cases`-then-`rfl` steps of the squash-regime
facts below cannot see the reduct.  `import all` restores that view
HERE only — the transplant of `Model/Steps/IrrelFast.lean`, which
carries the same escape for the same reason. -/
import all ConLeche.Kernel.PropWhen
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

/-! ## Spine readings and gradings (`Steps/Stuck.lean:129`,
`Steps/IotaGate.lean:72`) -/

/-- The head of a graded spine is graded. -/
theorem wellDenotedV_mkAppN_head {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {f : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN f as) → WellDenotedV V ρ f
  | [], _, h => h
  | a :: as, f, h => by
    have h' : WellDenotedV V ρ (.app f a) := wellDenotedV_mkAppN_head as h
    exact ⟨((WellDenoted_app V ρ f a) ▸ h'.1).1,
      ((AnnotValid_app V ρ f a) ▸ h'.2).1⟩

/-- A read spine has the length of its source. -/
theorem ReadSpine.length {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) : as.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A spine that reads splits into a head reading and a `ReadSpine`. -/
theorem denoteMeta_mkAppN_inv {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : AnnotTerm},
    denoteMeta acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denoteMeta acval env φ d f = some fa ∧
      ReadSpine acval env φ d as vs ∧ ea = AnnotTerm.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denoteMeta_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

/-! ## The stored constant's package (`Steps/IotaRows.lean:200`) -/

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and framed (closed, so the frames are free). -/
theorem constType_pkg {m : EnvModel V env} (hct : ConstTy m φ)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hnt : ci.isTowerEntry = false) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : AnnotTerm,
      (∀ d : Nat, denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hnt hlen
  have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denoteMeta_depth_of_closed m.acval_closed hnf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnf hbd hta 1 k)
      hta,
    hok, hmem, hnf, hbd⟩

/-! ## The proof-irrelevance fast arm (`Steps/IrrelFast.lean:67-419`)

The whole squash-regime licence, transplanted: the `V`-level facts,
the type former's `.pi` chain, and `prf_of_isProofFast` itself, with
`ConstType` read as the rules tier's `ConstTy`. -/

/-! ## 1. The squash-regime facts, V level -/

/-- Every application of `pt` is `pt` (`app_pt`, folded along a spine). -/
theorem foldl_app_pt' {ρ : Nat → V} : ∀ (as : List AnnotTerm),
    as.foldl (fun r a => app r (interp V ρ a)) (pt : V) = pt
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' as

/-- A spine on a `pt`-valued head interprets to `pt`. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : AnnotTerm}
    (hf : interp V ρ f = pt) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = pt := by
  rw [interp_mkAppN, hf]
  exact foldl_app_pt' as

/-- The kernel's "definitely `Prop`" test on a datum is the ∀-φ uniform
version of the claims' zero side: the bit is `0` at every valuation
(the dual of `pwBit_ne_zero_of_isNever`). -/
theorem pwBit_eq_zero_of_isProp {pw : PropWhen}
    (h : pw.isProp = true) (φ : Name → Nat) : pwBit φ pw = 0 := by
  rw [eq_of_beq h]
  simp [pwBit]

/-- **Exactness**: `pw.isProp` is *the* datum that is zero at every
valuation — `isNever_iff_forall_pwBit_ne_zero`'s mirror. -/
theorem alwaysZero_iff_forall_pwBit_eq_zero {pw : PropWhen} :
    pw.isProp = true ↔ ∀ φ : Name → Nat, pwBit φ pw = 0 := by
  constructor
  · exact pwBit_eq_zero_of_isProp
  · intro h
    cases pw with
    | never => exact absurd (h (fun _ => 0)) (by simp [pwBit])
    | ifAllZero ps =>
      cases ps with
      | nil => rfl
      | cons n ps =>
        have := h (fun _ => 1)
        simp [pwBit] at this

/-- A level whose zero-ness datum is always-zero evaluates to `0`. -/
theorem eval_eq_zero_of_isProp {u : Level}
    (h : (Level.zeronessOf u).isProp = true) (φ : Name → Nat) :
    Level.eval φ u = 0 := by
  have := pwBit_eq_zero_of_isProp h φ
  rw [pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound] at this
  exact beq_iff_eq.mp this

/-- **THE FENCE.**  At a nonzero bit the product reading is a graph set
with two distinct members: a `prf` verdict read off a datum that is
not always-zero would equate them.  So the fast "yes" is exactly the
always-zero datum, model-class-wide. -/
theorem irrel_fast_fence :
    ∃ (A : V) (B : V → V) (f g : V),
      f ∈ˢ piR 1 A B ∧ g ∈ˢ piR 1 A B ∧ f ≠ g := by
  refine ⟨truthVal True, fun _ => univZero,
    lamR 1 (truthVal True) (fun _ => truthVal False),
    lamR 1 (truthVal True) (fun _ => truthVal True), ?_, ?_, ?_⟩
  · exact lamR_mem fun _ _ => truthVal_mem_univZero False
  · exact lamR_mem fun _ _ => truthVal_mem_univZero True
  · intro h
    have h1 : app (lamR 1 (truthVal True) (fun _ => (truthVal False : V))) (pt : V)
        = app (lamR 1 (truthVal True) (fun _ => (truthVal True : V))) (pt : V) :=
      congrArg (fun z => app z (pt : V)) h
    rw [app_lamR_pos (by decide) (pt_mem_truthVal trivial),
      app_lamR_pos (by decide) (pt_mem_truthVal trivial)] at h1
    have : (pt : V) ∈ˢ (truthVal False : V) := h1 ▸ pt_mem_truthVal trivial
    exact (mem_truthVal.mp this).1

/-! ## 2. The type former's telescope: a `.pi` chain at nonzero bits -/

/-- The reading's first `n` heads are `.pi` nodes at nonzero regime
bits, and the residual is `.sort u` — the reading of a type former's
stored type `∀ p⃗, Sort u` whose binders the reader checked to be
`.never`. -/
@[expose] def NeverChain : Nat → Nat → AnnotTerm → Prop
  | 0, u, e => e = .sort u
  | n + 1, u, e =>
    match e with
    | .pi _ v _ B => v ≠ 0 ∧ NeverChain n u B
    | _ => False

theorem neverChain_succ_inv {n u : Nat} {e : AnnotTerm}
    (h : NeverChain (n + 1) u e) :
    ∃ w v A B, e = .pi w v A B ∧ v ≠ 0 ∧ NeverChain n u B := by
  match e with
  | .pi w v A B => exact ⟨w, v, A, B, rfl, h.1, h.2⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

/-- Substitution preserves the chain (`inst` maps `.pi` to `.pi` and
`.sort` to itself). -/
theorem NeverChain.inst : ∀ {n u : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    NeverChain n u e → NeverChain n u (e.inst a k) := by
  intro n
  induction n with
  | zero => intro u e a k h; subst h; rfl
  | succ n ih =>
    intro u e a k h
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv h
    exact ⟨hv, ih a (k + 1) hB⟩

/-- **A `.never`-peeled telescope reads to a chain**: each binder's bit
is nonzero (`pwBit_ne_zero_of_isNever`), the residual sort evaluates. -/
theorem neverChain_of_peel {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {T : Expr} {u : Level} {ta : AnnotTerm},
      T.peelNeverPis n = some (.sort u) →
      denoteMeta acval env φ d T = some ta →
      NeverChain n (Level.eval φ u) ta := by
  intro n
  induction n with
  | zero =>
    intro d T u ta hp hd
    obtain rfl := Expr.peelNeverPis_zero_inv hp
    rw [denoteMeta] at hd
    exact (Option.some.inj hd).symm
  | succ n ih =>
    intro d T u ta hp hd
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv hp
    obtain ⟨tA, tB, -, htB, rfl⟩ := denoteMeta_forallE_inv hd
    exact ⟨pwBit_ne_zero_of_isNever hnev φ,
      ih (Expr.peelNeverPis_instantiate1 n _ 0 hb) htB⟩

/-- **A type former's application lands in its result universe.**  The
walk along the chain: at every slot the bit is nonzero, so the
argument's membership in the domain is `io_domain_transfer` from the
applied spine's own hereditary app slot — no certificate anywhere. -/
theorem spine_mem_univ_of_neverChain {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {u : Nat},
      NeverChain vs.length u Ta →
      WellDenotedV V ρ Ta → WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ (univ u : V) := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f u hch _ _ hf
    obtain rfl : Ta = .sort u := hch
    exact hf
  | cons a vs ih =>
    intro Ta f u hch hokT hokS hf
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv hch
    have hokApp : WellDenotedV V ρ (.app f a) := wellDenotedV_mkAppN_head vs hokS
    have hoka : WellDenotedV V ρ a :=
      ⟨((WellDenoted_app V ρ f a) ▸ hokApp.1).2.1,
        ((AnnotValid_app V ρ f a) ▸ hokApp.2).2⟩
    have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
      fun y hy =>
        ⟨((WellDenoted_pi V ρ w v A B) ▸ hokT.1).2 y hy,
          ((AnnotValid_pi V ρ w v A B) ▸ hokT.2).2.1 y hy⟩
    have hf' : interp V ρ f
        ∈ˢ piR v (interp V ρ A) (fun x => interp V (cons x ρ) B) := hf
    have hmem : interp V ρ a ∈ˢ interp V ρ A := by
      obtain ⟨v', A', B', hslot, ha, -⟩ :=
        ((WellDenoted_app V ρ f a) ▸ hokApp.1).2.2
      exact io_domain_transfer hv hslot ha hf'
    have hokB' : WellDenotedV V ρ (B.inst a) :=
      (WellDenotedV_inst0 hoka).mpr (hokB _ hmem)
    have hfa : interp V ρ (.app f a) ∈ˢ interp V ρ (B.inst a) := by
      rw [interp_app, interp_inst0]
      exact app_mem_piR_pos hv hf' hmem
    exact ih (NeverChain.inst a 0 hB) hokB' hokS hfa

/-- The reading of a type-former application `T = hd b⃗` lands in
`univ 0` once the head's type reads to a chain of `b⃗`'s length ending
in `Sort 0`, the head inhabits it, and both readings are graded. -/
theorem mem_univ_zero_of_spine {acval : Name → (Name → Nat) → AnnotTerm}
    {ρ : Nat → V} {d : Nat} {T hd : Expr} {Ta fa taH : AnnotTerm}
    (hfn : T.getAppFn = hd)
    (hTa : denoteMeta acval env φ d T = some Ta)
    (hfa : denoteMeta acval env φ d hd = some fa)
    (hchain : NeverChain T.getAppArgs.length 0 taH)
    (hokH : WellDenotedV V ρ taH) (hokT : WellDenotedV V ρ Ta)
    (hmem : interp V ρ fa ∈ˢ interp V ρ taH) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  rw [← ConLeche.Expr.mkAppN_getApp T, hfn] at hTa
  obtain ⟨fa', vs, hfa', hsp, rfl⟩ := denoteMeta_mkAppN_inv hTa
  rw [hfa] at hfa'
  obtain rfl := Option.some.inj hfa'
  rw [hsp.length] at hchain
  exact spine_mem_univ_of_neverChain vs hchain hokH hokT hmem

/-- **A constant-headed type former's application** (`I b⃗`, `I` stored
with type `∀ p⃗, Sort u`, every binder `.never`, `u` zero at the use's
levels) lands in `univ 0`: `ConstType` supplies `I`'s membership in
its instantiated stored type and that type's grading; the chain is
read off the stored syntax at the composed valuation. -/
theorem typeFormer_mem_univ_zero {m : EnvModel V env}
    (hct : ConstTy m φ) {ρ : Nat → V} {d : Nat} {T : Expr}
    {I : Name} {us : List Level} {ci : ConstantInfo} {u : Level} {Ta : AnnotTerm}
    (hfn : T.getAppFn = .const I us) (hfI : env.find? I = some ci)
    (hnt : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpeel : ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
      some (.sort u))
    (hz : Level.eval (Level.substFn φ ci.toConstantVal.levelParams us) u = 0)
    (hTa : denoteMeta m.acval env φ d T = some Ta) (hokT : WellDenotedV V ρ Ta) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  obtain ⟨taI, htaI, hokI, hmemI, -, -⟩ := constType_pkg hct hfI hnt hlen
  have htaI' := htaI d
  rw [denotePInstLevels] at htaI'
  have hchain := neverChain_of_peel (env := env) T.getAppArgs.length hpeel htaI'
  rw [hz] at hchain
  exact mem_univ_zero_of_spine hfn hTa (denoteMeta_const hfI hlen) hchain
    (hokI ρ) hokT (hmemI ρ)

/-! ## 3. The kernel-shaped licence -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN : ∀ (as : List Expr) (f : Expr)
    (l : Nat × Expr), l ∈ f.fvarLeaves →
    l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h =>
    mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, h])

/-- A leaf of a term's head is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn' {a hd : Expr} {l : Nat × Expr}
    (h : a.getAppFn = hd) (hl : l ∈ hd.fvarLeaves) : l ∈ a.fvarLeaves := by
  rw [← ConLeche.Expr.mkAppN_getApp a, h]
  exact mem_fvarLeaves_mkAppN _ _ _ hl

/-- The leaf of a term's head fvar is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn {a ty : Expr} {idx : Nat}
    (h : a.getAppFn = .fvar idx ty) : (idx, ty) ∈ a.fvarLeaves :=
  mem_fvarLeaves_of_getAppFn' h (by simp [Expr.fvarLeaves])

/-- The leaves of an fvar's type are leaves of the fvar. -/
theorem mem_fvarLeaves_of_ty {ty : Expr} {idx : Nat}
    {l : Nat × Expr} (h : l ∈ ty.fvarLeaves) :
    l ∈ (Expr.fvar idx ty).fvarLeaves := by
  simp [Expr.fvarLeaves, h]

/-- **A term whose validated data say "proof" is `pt`.**  The
head-symbol case split of `isProofFast`, each case closed by the
squash-regime licence (a ∀-typed head, a λ) or the one graph-regime
step (a type-former-typed head). -/
theorem prf_of_isProofFast {m : EnvModel V env} (hct : ConstTy m φ)
    {d : Nat} {a : Expr} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (h : isProofFast env.find? a = true)
    (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨pw, hpw, hprop⟩ := isProofFast_inv env.find? h
  rcases proofPW_some_inv env.find? hpw with
    ⟨ty, bd, mb, rfl, rfl⟩ | ⟨-, hhead⟩
  · -- a λ: its datum is the body's type's sort, at bit `0`
    obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hda
    rw [interp_lam, pwBit_eq_zero_of_isProp hprop, lamR_zero]
  -- an application spine: the head decides
  have hspine := hda
  rw [← ConLeche.Expr.mkAppN_getApp a] at hspine
  obtain ⟨fa, vs, hfa, -, rfl⟩ := denoteMeta_mkAppN_inv hspine
  refine interp_mkAppN_pt ?_ vs
  rcases headProofPW_some_inv env.find? hhead with
    ⟨c, us, ci, hfn, hf, hnt, hlen, pw0, hty, rfl⟩ |
    ⟨idx, ty, hfn, hty⟩ | rfl
  · -- a constant head: the stored type decides
    rw [hfn, denoteMeta_const hf hlen] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨ta, hta, hokT, hmem, hnf, -⟩ := constType_pkg hct hf hnt hlen
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, hT, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idx, ty', u, hfnT, -, -⟩
    · -- ∀-typed: the squash product
      have hta' := hta d
      rw [hT, ConLeche.Expr.instantiateLevelParams] at hta'
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv hta'
      have hbit : pwBit φ (Level.substPW ci.toConstantVal.levelParams us mb.pw)
          = 0 := pwBit_eq_zero_of_isProp hprop φ
      have hm := hmem ρ
      rw [interp_pi, hbit] at hm
      exact eq_pt_of_mem_piR_zero hm
    · -- `Sort`-typed: never a proof
      exact absurd hprop (by simp)
    · -- a type-former application: the graph-regime step
      have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hfI)
      have hdefU : (Level.zeronessOf u).paramsDefined
          ciI.toConstantVal.levelParams = true := by
        obtain ⟨bs, hbs⟩ := Expr.stripPis_of_peelNeverPis _ hpeel
        have := ConLeche.Expr.allLevelParamsDefined_stripPis_body _ hbs hwf.2.1
        exact ConLeche.Level.zeronessOf_paramsDefined
          (by simpa [ConLeche.Expr.allLevelParamsDefined] using this)
      have hcomp := ConLeche.Level.substPW_comp
        (ks := ci.toConstantVal.levelParams) (us := us) hlenI hdefU
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams
          (us'.map (Level.subst ci.toConstantVal.levelParams us))) u = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [hcomp, pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have hT : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).getAppFn =
          .const I (us'.map (Level.subst ci.toConstantVal.levelParams us)) := by
        rw [ConLeche.Expr.getAppFn_instantiateLevelParams, hfnT]
        rfl
      have hpeel' : ciI.toConstantVal.type.peelNeverPis
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us).getAppArgs.length =
          some (.sort u) := by
        rw [ConLeche.Expr.getAppArgs_instantiateLevelParams, List.length_map]
        exact hpeel
      have huniv := typeFormer_mem_univ_zero hct hT hfI hntI
        (by rw [List.length_map]; exact hlenI) hpeel' hz (hta d) (hokT ρ)
      exact mem_univ_zero huniv (hmem ρ)
    · -- an fvar-headed stored type: stored types are closed
      exact absurd (ConLeche.Expr.hasFvar_of_getAppFn_fvar hfnT)
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams] at hnf; simp [hnf])
  · -- an fvar head: the context supplies the membership
    rw [hfn, denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨-, -, tya, Aa, htya, hAa, heq, hokT⟩ :=
      hCa.2 _ (mem_fvarLeaves_of_getAppFn hfn)
    have hx : interp V ρ (.bvar (d - 1 - idx)) ∈ˢ interp V ρ tya := by
      rw [interp_bvar, heq ρ hρ]
      exact hρ _ _ hAa
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, rfl, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idy, tyy, u, hfnT, hpeel, rfl⟩
    · -- ∀-typed: the squash product
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv htya
      rw [interp_pi, pwBit_eq_zero_of_isProp hprop] at hx
      exact eq_pt_of_mem_piR_zero hx
    · exact absurd hprop (by simp)
    · -- a constant-headed type former: the graph-regime step
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams us') u
          = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have huniv := typeFormer_mem_univ_zero hct hfnT hfI hntI hlenI hpeel hz
        htya (hokT ρ hρ)
      exact mem_univ_zero huniv hx
    · -- an fvar-headed type former (`h : motive n`): the head's type
      -- is in the context too
      obtain ⟨-, -, tyyA, Ay, htyy, hAy, heqy, hokY⟩ :=
        hCa.2 _ (mem_fvarLeaves_of_getAppFn' hfn
          (mem_fvarLeaves_of_ty (idx := idx)
            (mem_fvarLeaves_of_getAppFn hfnT)))
      have hy : interp V ρ (.bvar (d - 1 - idy)) ∈ˢ interp V ρ tyyA := by
        rw [interp_bvar, heqy ρ hρ]
        exact hρ _ _ hAy
      have hchain := neverChain_of_peel (env := env) (acval := m.acval)
        ty.getAppArgs.length hpeel htyy
      rw [eval_eq_zero_of_isProp hprop φ] at hchain
      have huniv := mem_univ_zero_of_spine hfnT htya (denoteMeta_fvar _ _ _ _)
        hchain (hokY ρ hρ) (hokT ρ hρ) hy
      exact mem_univ_zero huniv hx
  · -- a sort, a ∀, a literal: never a proof
    exact absurd hprop (by simp)



/-! ## The ∀-chain guard and the fit's un-instantiation
(`Steps/CapsRows.lean:73-182`, `:452`) -/

/-- The reading's first `n` heads are `.pi` nodes. -/
@[expose] def PiChain : Nat → AnnotTerm → Prop
  | 0, _ => True
  | n + 1, e =>
    match e with
    | .pi _ _ _ B => PiChain n B
    | _ => False

@[simp] theorem piChain_zero (e : AnnotTerm) : PiChain 0 e := trivial

@[simp] theorem piChain_succ_pi {n u v : Nat} {A B : AnnotTerm} :
    PiChain (n + 1) (.pi u v A B) = PiChain n B := rfl

theorem piChain_succ_inv {n : Nat} {e : AnnotTerm} (h : PiChain (n + 1) e) :
    ∃ u v A B, e = .pi u v A B ∧ PiChain n B := by
  match e with
  | .pi u v A B => exact ⟨u, v, A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

theorem PiChain.inst : ∀ {n : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    PiChain n e → PiChain n (e.inst a k) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro e a k h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact ih a (k + 1) hB

/-- **A syntactic ∀-telescope reads to a ∀-chain.** -/
theorem piChain_of_stripPis {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {ea : AnnotTerm},
      (e.stripPis n).isSome = true →
      denoteMeta acval env φ d e = some ea → PiChain n ea := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; trivial
  | succ n ih =>
    intro d e ea hs hd
    match e, hs with
    | .bvar _, hs => exact nomatch hs
    | .fvar _ _, hs => exact nomatch hs
    | .sort _, hs => exact nomatch hs
    | .const _ _, hs => exact nomatch hs
    | .app _ _, hs => exact nomatch hs
    | .lam _ _ _, hs => exact nomatch hs
    | .letE _ _ _, hs => exact nomatch hs
    | .lit _, hs => exact nomatch hs
    | .proj _ _ _, hs => exact nomatch hs
    | .forallE ty bd mb, hs =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hd
      simp only [ConLeche.Expr.stripPis, Option.isSome_map] at hs
      exact ih (ConLeche.Expr.stripPis_instantiate1_isSome n 0 hs) hba

theorem teleFit_nil_inv {ρ : Nat → V} {T : AnnotTerm} {rest : V}
    (h : TeleFit V ρ T [] rest) : rest = interp V ρ T := by
  cases h; rfl

/-- **The fit un-instantiates, under the ∀-chain guard.** -/
theorem teleFit_of_inst {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V ρ (E.inst aa k) L rest →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    obtain rfl : rest = interp V ρ (E.inst aa k) := teleFit_nil_inv h
    rw [interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi] at h
    cases h with
    | cons hmem hfit =>
      refine .cons (by rwa [interp_inst] at hmem) ?_
      have hrec := ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit
      rw [shiftE_succ_cons] at hrec
      rw [cons_instE]
      exact hrec

theorem teleFit_of_inst0 {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V ρ (E.inst aa) L rest) :
    TeleFit V (cons (interp V ρ aa) ρ) E L rest := by
  have := teleFit_of_inst hpc h
  rwa [shiftE_zero_zero, instE_zero] at this

/-- **The rules tier's bridge**: the motive `CertsSem` concludes the
substitution-peeling fit `TeleFitPA` (`certs_telePA`'s currency) while
the capability laws `EtaLaw`/`UnitLaw` consume the value-level
`TeleFit`.  Under the ∀-chain guard — which every call site holds from
the family's `stripPis` conjunct — the two agree: `TeleFitPA` peels
`B.inst a` where `TeleFit` extends the environment, and
`teleFit_of_inst0` is exactly that exchange.  (Without the guard the
PA fit is strictly stronger: it can walk through a `.bvar 0` body,
`teleFit_bvar_stuck`.) -/
theorem teleFit_of_PA {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {T rest : AnnotTerm},
      PiChain as.length T → TeleFitPA V ρ T as rest →
      TeleFit V ρ T (as.map (interp V ρ)) (interp V ρ rest) := by
  intro as
  induction as with
  | nil =>
    intro T rest _ h
    cases h
    exact .nil
  | cons a as ih =>
    intro T rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    cases h with
    | cons hmem htail =>
      refine .cons hmem ?_
      exact teleFit_of_inst0 (by simpa using hB)
        (ih (PiChain.inst a 0 hB) htail)

/-! ## Spine frames and gradings (`Steps/Stuck.lean:171`, `:194`) -/

/-- Every argument of a graded application spine is graded, and so is
its head. -/
theorem Graded.mkAppN {Δa : List AnnotTerm} :
    ∀ (asa : List AnnotTerm) {fa : AnnotTerm},
      Graded V Δa (AnnotTerm.mkAppN fa asa) →
      Graded V Δa fa ∧ ∀ x ∈ asa, Graded V Δa x := by
  intro asa
  induction asa with
  | nil => intro fa h; exact ⟨h, by simp⟩
  | cons a as ih =>
    intro fa h
    obtain ⟨happ, hrest⟩ := ih (fa := .app fa a) h
    refine ⟨fun ρ hρ => ⟨?_, ?_⟩, ?_⟩
    · exact ((WellDenoted_app V ρ fa a) ▸ (happ ρ hρ).1).1
    · exact ((AnnotValid_app V ρ fa a) ▸ (happ ρ hρ).2).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact fun ρ hρ =>
          ⟨((WellDenoted_app V ρ fa x) ▸ (happ ρ hρ).1).2.1,
            ((AnnotValid_app V ρ fa x) ▸ (happ ρ hρ).2).2⟩
      · exact hrest x hx'

/-- The frame and context of every argument of a spine. -/
theorem Frame.getAppArgs {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {a : Expr} (hf : Frame d a)
    (hC : CtxOk m φ d Δa a) :
    ∀ x ∈ a.getAppArgs, Frame d x ∧ CtxOk m φ d Δa x := fun x hx =>
  ⟨⟨hf.1.getAppArgs x hx, ConLeche.looseBVarsBounded_getAppArgs hf.2.1 x hx,
      fun l hl => hf.2.2 l (ConLeche.fvarLeaves_getAppArgs hx l hl)⟩,
    hC.of_subset (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)⟩


/-! ## The spine kit, completed (`Steps/CapsRows.lean:324-446`) -/

theorem ReadSpine.take {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ n, ReadSpine acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using ReadSpine.nil
  | @cons a v as vs ha _ ih =>
    intro n
    cases n with
    | zero => exact ReadSpine.nil
    | succ n => exact ReadSpine.cons ha (ih n)

theorem ReadSpine.drop {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ n, ReadSpine acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using ReadSpine.nil
  | @cons a v as vs ha htl ih =>
    intro n
    cases n with
    | zero => exact ReadSpine.cons ha htl
    | succ n => exact ih n

theorem ReadSpine.append {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {as bs : List Expr} {vs ws : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs)
    (h2 : ReadSpine acval env φ d bs ws) :
    ReadSpine acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => exact h2
  | cons ha _ ih => exact ReadSpine.cons ha ih

/-- A mapped spine reads pointwise. -/
theorem ReadSpine.map_list {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {g : Nat → Expr} {G : Nat → AnnotTerm} :
    ∀ l : List Nat, (∀ j ∈ l, denoteMeta acval env φ d (g j) = some (G j)) →
      ReadSpine acval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact ReadSpine.nil
  | cons x xs ih =>
    intro h
    exact ReadSpine.cons (h x (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- **The application spine reads, constructing direction.** -/
theorem denoteMeta_mkAppN {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {as : List Expr} {vs : List AnnotTerm}
    (h : ReadSpine acval env φ d as vs) :
    ∀ {f : Expr} {fa : AnnotTerm}, denoteMeta acval env φ d f = some fa →
      denoteMeta acval env φ d (Expr.mkAppN f as)
        = some (AnnotTerm.mkAppN fa vs) := by
  induction h with
  | nil => intro f fa hf; exact hf
  | cons ha _ ih =>
    intro f fa hf
    exact ih (by rw [denoteMeta_app, hf, ha]; rfl)

/-- A `TeleFit` plus the type's grading yields the applied spine's
grading and its residual membership. -/
theorem wellDenotedV_mkAppN_of_fit {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {σ : Nat → V} {rest : V},
      WellDenotedV V σ Ta → WellDenotedV V ρ f →
      (∀ x ∈ vs, WellDenotedV V ρ x) →
      interp V ρ f ∈ˢ interp V σ Ta →
      TeleFit V σ Ta (vs.map (interp V ρ)) rest →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) ∧
        interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f σ rest _ hf _ hmem hfit
    obtain rfl : rest = interp V σ Ta := teleFit_nil_inv hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f σ rest hokT hf hoks hmem hfit
    simp only [List.map_cons] at hfit
    cases hfit with
    | @cons _ u v A B _ _ _ hx hfit' =>
      have hokA : WellDenotedV V σ A :=
        ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).1,
          ((AnnotValid_pi V σ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp V σ A → WellDenotedV V (cons y σ) B :=
        fun y hy =>
          ⟨((WellDenoted_pi V σ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp V σ A →
          interp V (cons y σ) B ∈ˢ (univZero : V) :=
        ((AnnotValid_pi V σ u v A B) ▸ hokT.2).2.2
      rw [interp_pi] at hmem
      have hokx : WellDenotedV V ρ x := hoks x List.mem_cons_self
      have hstep : WellDenotedV V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨hf.1, hokx.1, v, interp V σ A,
            (fun y => interp V (cons y σ) B), hmem, hx, hfib⟩
        · rw [AnnotValid_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp V ρ (.app f x)
          ∈ˢ interp V (cons (interp V ρ x) σ) B := by
        rw [interp_app]
        exact app_mem_piR hmem hx hfib
      exact ih (hokB _ hx) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'

/-- A ∀-chain of a list's length peels along it. -/
theorem peelPis_of_piChain : ∀ (as : List AnnotTerm) {T : AnnotTerm},
    PiChain as.length T →
      ∃ rest, ConLeche.Model.AnnotTerm.peelPis T as = some rest
  | [], T, _ => ⟨T, rfl⟩
  | a :: as, T, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv h
    exact peelPis_of_piChain as (PiChain.inst a 0 hB)

/-! ## The tower entry's reading (`Steps/TowerKit.lean:46`, `:173`) -/

/-- The clause at a stored entry: the uniform iterated projection. -/
theorem denoteMeta_proj_tower {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : AnnotTerm}
    (hfe : env.findProj? s i = some entry)
    (he : denoteMeta acval env φ d e = some ia) :
    denoteMeta acval env φ d (.proj s i e)
      = some (projAV (i + entry.off) ia) := by
  rw [denoteMeta_proj, he]
  show (match env.findProj? s i with
    | some entry => some (projAV (i + entry.off) ia)
    | none => AnnotTerm.projPair? i ia)
      = some (projAV (i + entry.off) ia)
  rw [hfe]

/-- A stored tower entry's body telescope is closed. -/
theorem towerEntry_tele_closed (hwf : ConLeche.EnvWF env) {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    (us : List Level) :
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).hasFvar = false ∧
    (ConLeche.projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).looseBVarsBounded 0
      = true := by
  rw [ConLeche.projTele_hasFvar, ConLeche.projTele_looseBVarsBounded,
    Nat.zero_add]
  exact ⟨ConLeche.projEntry_body_hasFvar hwf hfe us,
    ConLeche.projEntry_body_looseBVars hwf hfe us⟩

/-- **The body telescope's reading is depth-free.** -/
theorem towerEntry_tele_at_depth {m : EnvModel V env} {T : Name} {i : Nat}
    {entry : ProjEntry} (hfe : env.findProj? T i = some entry)
    {us : List Level} {Ta : AnnotTerm}
    (hTa : denoteMeta m.acval env φ 0
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) :
    (∀ d : Nat, denoteMeta m.acval env φ d
      (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta) ∧
    ∀ k : Nat, Ta.liftN 1 k = Ta := by
  obtain ⟨hnf, hb⟩ := towerEntry_tele_closed m.wf hfe us
  have hcl : ∀ k : Nat, Ta.liftN 1 k = Ta := fun k =>
    denoteMeta_closed m.acval_erase m.cval_closed hnf hb hTa 1 k
  exact ⟨denoteMeta_depth_of_closed m.acval_closed hnf hcl hTa, hcl⟩

/-! ## The two proof-irrelevance sides (`Steps/Irrel.lean:71`, `:119`)

`prop_side_pt`/`unit_side_pt` at the motives: the run premises become
the rule's `InferSemIO`/`RedSem` derivations, and the inferred type's
frames — which the run lemmas `inferTypeIO_WScoped`/`_looseBVars`/
`_fvarLeaves` supplied there — are now the motives' own conclusions. -/

/-- A term whose type's type reduces to a zero-equivalent sort
interprets to `pt`. -/
theorem prop_side_pt' {m : EnvModel V env} {d : Nat} {a ta tta : Expr}
    {u : Level} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSem m φ d tta (.sort u))
    (hu0 : Level.isEquiv u .zero = some true)
    (hfa : Frame d a) (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : Graded V Δa aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨hfta, hsub1, taa, htaa, hoktaa, hmemA⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub1
  obtain ⟨hftta, hsub2, ttaa, httaa, hokttaa, hmemT⟩ :=
    htta hfta hCta htaa hoktaa
  have hCtta : CtxOk m φ d Δa tta := hCta.of_subset hsub2
  obtain ⟨-, -, sa, hsa, -, heq⟩ := hu hftta hCtta httaa hokttaa
  rw [denoteMeta_sort] at hsa
  obtain rfl : sa = AnnotTerm.sort (u.eval φ) := (Option.some.inj hsa).symm
  have h0 : Level.eval φ u = 0 := ConLeche.Level.isEquiv_sound hu0 φ
  have hT := hmemT ρ hρ
  rw [heq ρ hρ, interp_sort, h0] at hT
  exact mem_univ_zero hT (hmemA ρ hρ)

/-- A term whose type reduces to a unit-like type interprets to `pt`:
`isUnitLikeTy` accepts only the pinned `PUnit`, whose `interp` is
`unitSet = {pt}`. -/
theorem unit_side_pt' {m : EnvModel V env} {d : Nat} {a ta wta : Expr}
    {Δa : List AnnotTerm} {aa : AnnotTerm}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hu : ConLeche.isUnitLikeTy env wta = true)
    (hfa : Frame d a) (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (hokA : Graded V Δa aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨hfta, hsub1, taa, htaa, hoktaa, hmemA⟩ := hta hfa hCa hda hokA
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub1
  obtain ⟨-, -, wtaa, hwtaa, -, heqW⟩ := hwta hfta hCta htaa hoktaa
  obtain ⟨us, rfl, hfind⟩ :=
    ConLeche.Verify.unitLike_eq_punit m.basis_pinned hu
  rw [denoteMeta, hfind] at hwtaa
  dsimp only at hwtaa
  split at hwtaa
  case isFalse => exact nomatch hwtaa
  case isTrue hlen =>
  obtain rfl : wtaa = m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us) :=
    (Option.some.inj hwtaa).symm
  have hpin : m.cvalE ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = ConLeche.Term.punitT
        (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN) :=
    (m.basis_pinned ConLeche.punitName _ hfind (by decide)).2 _ _ rfl
  have hleaf : m.acval ConLeche.punitName
      (Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us)
      = .const .punit
        [Level.substFn φ ConLeche.punitA.toConstantVal.levelParams us
          ConLeche.uN] :=
    erase_eq_const (by rw [m.acval_erase, hpin]; rfl)
  have hmem := hmemA ρ hρ
  rw [heqW ρ hρ, hleaf, interp_const] at hmem
  exact mem_unitSet hmem

end ConLeche.Model.Rules
