import Setlec.SetP.InstallP
import Setlec.SetP.Step2.NatP
import Setlec.SetBase.NatFrag
import Setlec.SetBase.DeclRun

/-!
# The structural-`Nat` recurrences, established at `interp2` from run
certificates (task #161, literal tier)

The literal tier's wall (`Step2/NatP.lean`) is exactly one law wide:
the stored operations' recurrences at `interp2`.  This file builds the
recorded resumption route — **establishment from run certificates**:
`DeclDefnR` records one `isDefEqCore` run per substituted equation
(`NatEqsRunR`, the H1 exposure), and `DefEqClaims2P` at the
pre-insertion environment converts each run into an `interp2` equality
at the two-variable `Nat` context.  The v1 route (`NatEqsR`'s `DefEq`
+ `DefEq.sound`) is *not* transferable — its soundness lives at the
collapse currency only (the wall record's finding 2).

What the conversion costs beyond v1: `DefEqClaims2P` demands the
compared readings **graded** (`AnnotOkP` under `Sat2`), which the
collapse-lane `DefEqClaimsR` never did.  The grading of an equation
side — an application spine over stored `Nat`-operation heads,
`Nat.zero`/`Nat.succ`, and two `Nat` free variables — is assembled
here from the environment invariant alone:

* argument memberships from `Sat2` and `NatHeadsP`;
* head memberships from `mem_typeP` at the **pinned** operation types
  (`natOpTyPinned`), whose `denoteP` readings compute to two-step
  `.pi` spines over the `Nat` leaf;
* fibre facts at *unknown* regime bits from `type_okP`'s
  `AnnotValidV` — `app_mem_piR`'s `hB0` premise is exactly the
  validity `pi` clause, so **no bit positivity is ever needed**
  (the doctrine holds: bits are never taken from a metatheorem, and
  here they are not taken at all).

The layers: the two-variable context kit; the graded-argument walk
(`NatArgP`); the head packages (`NatBinHeadP`/`NatUnHeadP`) and their
pinned-type establishment; the per-equation conversion; the crossing
to the install's extension (`denoteP_substConst0`); and the field
suppliers (`natOpsP_install` bespoke at the operation's own install,
`natOpsP_cons_fresh` at every other fresh cons).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## Level plumbing -/

/-- The ground-composition identity: substituting nothing reads the
assignment itself. -/
theorem substFn_nil (ψ : Name → Nat) : Level.substFn ψ [] [] = ψ :=
  funext fun _ => rfl

/-! ## The two-variable `Nat` context -/

/-- The `Nat` leaf at an assignment (every structural-`Nat` head is
stored level-monomorphically, so the spelling is the plain
assignment). -/
def natAP {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) :
    AVExpr :=
  m.acval Setlec.natName ψ

/-- The stored `Nat`'s interpretation. -/
noncomputable def natSP {env : Env} (m : EnvS2Core V env)
    (ψ : Name → Nat) (ρ : Nat → V) : V :=
  interp2 V ρ (natAP m ψ)

/-- A leaf's interpretation does not read the environment
(`acval_interp2_closed` at the core carrier). -/
theorem acval_interp2_closedC (m : EnvS2Core V env) (n : Name)
    (ψ : Name → Nat) (ρ ρ' : Nat → V) :
    interp2 V ρ (m.acval n ψ) = interp2 V ρ' (m.acval n ψ) :=
  interp2_closed V
    (by rw [m.acval_erase]; exact m.cval_closed n ψ) ρ ρ'

/-- The `Nat` leaf's interpretation does not read the environment. -/
theorem natAP_interp2_closed (m : EnvS2Core V env) (ψ : Name → Nat)
    (ρ ρ' : Nat → V) :
    interp2 V ρ (natAP m ψ) = interp2 V ρ' (natAP m ψ) :=
  acval_interp2_closedC m _ ψ ρ ρ'

/-- The stored `Nat`'s interpretation does not read the
environment. -/
theorem natSP_closed (m : EnvS2Core V env) (ψ : Name → Nat)
    (ρ ρ' : Nat → V) : natSP m ψ ρ = natSP m ψ ρ' :=
  acval_interp2_closedC m _ ψ ρ ρ'

/-- The two-variable context: both slots are the `Nat` leaf. -/
def natCtx2 {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) :
    List AVExpr :=
  [natAP m ψ, natAP m ψ]

/-- Two `Nat` members satisfy the two-variable context (`sat_two`'s P
mirror; the slot readings collapse by leaf closedness). -/
theorem sat2_natCtx2 (m : EnvS2Core V env) {ψ : Name → Nat}
    {ρ : Nat → V} {x y : V}
    (hx : x ∈ˢ natSP m ψ ρ) (hy : y ∈ˢ natSP m ψ ρ) :
    Sat2 V (natCtx2 m ψ) (cons y (cons x ρ)) := by
  intro i Aa hi
  match i with
  | 0 =>
    obtain rfl : natAP m ψ = Aa := by simpa [natCtx2] using hi
    show y ∈ˢ interp2 V _ (natAP m ψ)
    rw [natAP_interp2_closed m ψ _ ρ]
    exact hy
  | 1 =>
    obtain rfl : natAP m ψ = Aa := by simpa [natCtx2] using hi
    show x ∈ˢ interp2 V _ (natAP m ψ)
    rw [natAP_interp2_closed m ψ _ ρ]
    exact hx
  | n + 2 => simp [natCtx2] at hi

/-- Conversely, a satisfying valuation of the two-variable context has
`Nat` members in both slots. -/
theorem sat2_natCtx2_inv (m : EnvS2Core V env) {ψ : Name → Nat}
    {ρ : Nat → V} (hρ : Sat2 V (natCtx2 m ψ) ρ) :
    ρ 0 ∈ˢ natSP m ψ ρ ∧ ρ 1 ∈ˢ natSP m ψ ρ := by
  have h0 := hρ 0 (natAP m ψ) (by simp [natCtx2])
  have h1 := hρ 1 (natAP m ψ) (by simp [natCtx2])
  rw [natAP_interp2_closed m ψ _ ρ] at h0
  rw [natAP_interp2_closed m ψ _ ρ] at h1
  exact ⟨h0, h1⟩

/-! ## The graded-argument walk

A `Nat`-valued fragment term at the two-variable context: it reads,
its reading is graded, and its interpretation is a stored-`Nat`
member.  The intro lemmas below are the fragment's typing rules; the
head packages that drive the application rules follow. -/

/-- A graded `Nat`-valued argument. -/
def NatArgP (m : EnvS2Core V env) (ψ : Name → Nat) (e : Expr) :
    Prop :=
  ∃ ea, denoteP m.acval env ψ 2 e = some ea ∧
    ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ →
      AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ natSP m ψ ρ

/-- The first equation variable (`fvar 0`). -/
theorem natArgP_var0 (m : EnvS2Core V env) (ψ : Name → Nat)
    (n : Name) : NatArgP m ψ (.fvar 0 n (.const Setlec.natName [])) := by
  refine ⟨.bvar 1, denoteP_fvar _ 2 0 n _, fun ρ hρ => ?_⟩
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [interp2_bvar]
  exact (sat2_natCtx2_inv m hρ).2

/-- The second equation variable (`fvar 1`). -/
theorem natArgP_var1 (m : EnvS2Core V env) (ψ : Name → Nat)
    (n : Name) : NatArgP m ψ (.fvar 1 n (.const Setlec.natName [])) := by
  refine ⟨.bvar 0, denoteP_fvar _ 2 1 n _, fun ρ hρ => ?_⟩
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [interp2_bvar]
  exact (sat2_natCtx2_inv m hρ).1

/-- `Nat.zero`. -/
theorem natArgP_zero (m : EnvS2Core V env) {ψ : Name → Nat}
    (hnh : NatHeadsP m ψ) (hval : AcvalValidP m)
    (hs : natLitSupported env = true) :
    NatArgP m ψ (.const Setlec.natZeroName []) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hlpZ' : (Setlec.ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
      = [] := hlpZ
  have hzl : denoteP m.acval env ψ 2 (.const Setlec.natZeroName [])
      = some (m.acval Setlec.natZeroName (Level.substFn ψ
          (Setlec.ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          [])) :=
    denoteP_const hfZ (by simp [hlpZ'])
  rw [hlpZ'] at hzl
  refine ⟨m.acval Setlec.natZeroName (Level.substFn ψ [] []), hzl,
    fun ρ hρ => ?_⟩
  refine ⟨⟨m.acval_ok2 _ _ ρ, hval _ _ ρ⟩, ?_⟩
  have h := (hnh hs ρ).1
  rwa [show natSP m ψ ρ
      = interp2 V ρ (m.acval Setlec.natName (Level.substFn ψ [] []))
    from by rw [substFn_nil]; rfl]

/-- `Nat.succ` applied to a graded argument. -/
theorem natArgP_succ (m : EnvS2Core V env) {ψ : Name → Nat}
    (hnh : NatHeadsP m ψ) (hval : AcvalValidP m)
    (hs : natLitSupported env = true) {t : Expr}
    (ht : NatArgP m ψ t) :
    NatArgP m ψ (.app (.const Setlec.natSuccName []) t) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  obtain ⟨ta, hta, htg⟩ := ht
  have hlpS' : (Setlec.ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
      = [] := hlpS
  have hsl : denoteP m.acval env ψ 2 (.const Setlec.natSuccName [])
      = some (m.acval Setlec.natSuccName (Level.substFn ψ
          (Setlec.ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
          [])) :=
    denoteP_const hfS (by simp [hlpS'])
  rw [hlpS'] at hsl
  refine ⟨.app (m.acval Setlec.natSuccName (Level.substFn ψ [] [])) ta,
    by rw [denoteP_app, hsl, hta]; rfl, fun ρ hρ => ?_⟩
  obtain ⟨⟨htok, htv⟩, htm⟩ := htg ρ hρ
  have hsucc := (hnh hs ρ).2
  have hnatEq : interp2 V ρ (m.acval Setlec.natName (Level.substFn ψ [] []))
      = natSP m ψ ρ := by rw [substFn_nil]; rfl
  rw [hnatEq] at hsucc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [AnnotOk2_app]
    exact ⟨m.acval_ok2 _ _ ρ, htok,
      1, natSP m ψ ρ, fun _ => natSP m ψ ρ, hsucc, htm,
      fun h => absurd h Nat.one_ne_zero⟩
  · rw [AnnotValidV_app]
    exact ⟨hval _ _ ρ, htv⟩
  · rw [interp2_app]
    exact app_mem_piR_pos Nat.one_ne_zero hsucc htm

/-! ## The head packages

What a fragment application rule needs of its head: the head reads to
a graded `AVExpr` whose interpretation sits in a (one- or two-step)
`piR` over the stored `Nat`, with the validity fibre facts at each
step — at *whatever* regime bits the stored annotation carries.
`app_mem_piR` consumes exactly this, so no bit positivity appears. -/

/-- A binary head over the pinned `Nat`, with codomain set `codS`. -/
def NatBinHeadP (m : EnvS2Core V env) (ψ : Name → Nat) (f : Expr)
    (codS : (Nat → V) → V) : Prop :=
  ∃ fa, denoteP m.acval env ψ 2 f = some fa ∧
    ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ →
      AnnotOkP V ρ fa ∧
      ∃ b₁ b₂ : Nat,
        interp2 V ρ fa ∈ˢ piR b₁ (natSP m ψ ρ)
          (fun _ => piR b₂ (natSP m ψ ρ) (fun _ => codS ρ)) ∧
        (b₁ = 0 → ∀ x, x ∈ˢ natSP m ψ ρ →
          piR b₂ (natSP m ψ ρ) (fun _ => codS ρ) ∈ˢ (univZero : V)) ∧
        (b₂ = 0 → ∀ x, x ∈ˢ natSP m ψ ρ → codS ρ ∈ˢ (univZero : V))

/-- A unary head over the pinned `Nat`, with codomain set `codS`. -/
def NatUnHeadP (m : EnvS2Core V env) (ψ : Name → Nat) (f : Expr)
    (codS : (Nat → V) → V) : Prop :=
  ∃ fa, denoteP m.acval env ψ 2 f = some fa ∧
    ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ →
      AnnotOkP V ρ fa ∧
      ∃ b₁ : Nat,
        interp2 V ρ fa ∈ˢ piR b₁ (natSP m ψ ρ) (fun _ => codS ρ) ∧
        (b₁ = 0 → ∀ x, x ∈ˢ natSP m ψ ρ → codS ρ ∈ˢ (univZero : V))

/-- **The binary application rule**: a binary head applied to two
graded arguments reads, is graded, and lands in the codomain set. -/
theorem natBinHeadP_app (m : EnvS2Core V env) {ψ : Name → Nat}
    {f x y : Expr} {codS : (Nat → V) → V}
    (hh : NatBinHeadP m ψ f codS) (hx : NatArgP m ψ x)
    (hy : NatArgP m ψ y) :
    ∃ ea, denoteP m.acval env ψ 2 (.app (.app f x) y) = some ea ∧
      ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ →
        AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ codS ρ := by
  obtain ⟨fa, hfa, hfg⟩ := hh
  obtain ⟨xa, hxa, hxg⟩ := hx
  obtain ⟨ya, hya, hyg⟩ := hy
  refine ⟨.app (.app fa xa) ya,
    by rw [denoteP_app, denoteP_app, hfa, hxa, hya]; rfl,
    fun ρ hρ => ?_⟩
  obtain ⟨⟨hfok, hfv⟩, b₁, b₂, hfm, hB1, hB2⟩ := hfg ρ hρ
  obtain ⟨⟨hxok, hxv⟩, hxm⟩ := hxg ρ hρ
  obtain ⟨⟨hyok, hyv⟩, hym⟩ := hyg ρ hρ
  -- the inner application's membership, at whatever bit
  have hinner : SetTheory.app (interp2 V ρ fa) (interp2 V ρ xa)
      ∈ˢ piR b₂ (natSP m ψ ρ) (fun _ => codS ρ) :=
    app_mem_piR hfm hxm hB1
  have houter : SetTheory.app
      (SetTheory.app (interp2 V ρ fa) (interp2 V ρ xa))
      (interp2 V ρ ya) ∈ˢ codS ρ :=
    app_mem_piR hinner hym hB2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [AnnotOk2_app]
    refine ⟨?_, hyok, b₂, natSP m ψ ρ, fun _ => codS ρ, ?_, hym, ?_⟩
    · rw [AnnotOk2_app]
      exact ⟨hfok, hxok, b₁, natSP m ψ ρ,
        fun _ => piR b₂ (natSP m ψ ρ) (fun _ => codS ρ), hfm, hxm,
        fun hz => hB1 hz⟩
    · rw [interp2_app]
      exact hinner
    · intro hz z hz'
      exact hB2 hz z hz'
  · rw [AnnotValidV_app, AnnotValidV_app]
    exact ⟨⟨hfv, hxv⟩, hyv⟩
  · rw [interp2_app, interp2_app]
    exact houter

/-- **The unary application rule.** -/
theorem natUnHeadP_app (m : EnvS2Core V env) {ψ : Name → Nat}
    {f x : Expr} {codS : (Nat → V) → V}
    (hh : NatUnHeadP m ψ f codS) (hx : NatArgP m ψ x) :
    ∃ ea, denoteP m.acval env ψ 2 (.app f x) = some ea ∧
      ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ →
        AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ codS ρ := by
  obtain ⟨fa, hfa, hfg⟩ := hh
  obtain ⟨xa, hxa, hxg⟩ := hx
  refine ⟨.app fa xa, by rw [denoteP_app, hfa, hxa]; rfl,
    fun ρ hρ => ?_⟩
  obtain ⟨⟨hfok, hfv⟩, b₁, hfm, hB1⟩ := hfg ρ hρ
  obtain ⟨⟨hxok, hxv⟩, hxm⟩ := hxg ρ hρ
  have happ : SetTheory.app (interp2 V ρ fa) (interp2 V ρ xa)
      ∈ˢ codS ρ := app_mem_piR hfm hxm hB1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [AnnotOk2_app]
    exact ⟨hfok, hxok, b₁, natSP m ψ ρ, fun _ => codS ρ, hfm, hxm,
      fun hz => hB1 hz⟩
  · rw [AnnotValidV_app]
    exact ⟨hfv, hxv⟩
  · rw [interp2_app]
    exact happ

/-! ## The pinned operation types, shape and reading

`natOpTyPinned` pins an operation's stored type syntactically; its
`denoteP` reading therefore computes to a two-step (binary) or
one-step (unary) `.pi` spine over the `Nat` leaf, at whatever regime
bits the stored annotation carries. -/

/-- The pinned binary type's syntactic shape (the `natOpTyPinned`
else-branch, unpacked). -/
theorem natOpTyPinned_shape_bin {env' : Env} {c : Name} {ty : Expr}
    (hnu : ¬(c = Setlec.natPredName ∨ c = Setlec.natLog2Name))
    (h : Setlec.natOpTyPinned env' c ty = true) :
    ∃ n₁ n₂ mb₁ mb₂ cod,
      ty = .forallE n₁ (.const Setlec.natName [])
        (.forallE n₂ (.const Setlec.natName []) cod mb₂) mb₁ ∧
      ((c = Setlec.natBeqName ∨ c = Setlec.natBleName) →
        cod = .const Setlec.boolName [] ∧
        ∃ ci, env'.find? Setlec.boolName = some ci ∧
          ci.toConstantVal.levelParams = []) ∧
      (¬(c = Setlec.natBeqName ∨ c = Setlec.natBleName) →
        cod = .const Setlec.natName []) := by
  unfold Setlec.natOpTyPinned at h
  split at h
  · next hc =>
    exfalso
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    exact hnu hc
  · split at h
    · next a dom b dom2 body mb2 mb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hcod⟩ := h
      unfold Setlec.natOpCod at hcod
      refine ⟨a, b, mb, mb2, body, rfl, ?_, ?_⟩
      all_goals split at hcod
      · intro _
        simp only [Bool.and_eq_true, beq_iff_eq] at hcod
        obtain ⟨rfl, hstore⟩ := hcod
        refine ⟨rfl, ?_⟩
        revert hstore
        cases hf : env'.find? Setlec.boolName with
        | none => intro hh; exact nomatch hh
        | some ci =>
          intro hh
          simp only [Bool.and_eq_true] at hh
          exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using hh.1⟩
      · next hcb =>
        intro hc
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
        exact hcb hc
      · next hcb =>
        intro hn
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
        exact hn hcb
      · intro _
        exact beq_iff_eq.mp hcod
    · exact nomatch h

/-- The pinned unary type's syntactic shape. -/
theorem natOpTyPinned_shape_un {env' : Env} {c : Name} {ty : Expr}
    (hu : c = Setlec.natPredName ∨ c = Setlec.natLog2Name)
    (h : Setlec.natOpTyPinned env' c ty = true) :
    ∃ n₁ mb₁, ty = .forallE n₁ (.const Setlec.natName [])
      (.const Setlec.natName []) mb₁ := by
  unfold Setlec.natOpTyPinned at h
  split at h
  · split at h
    · next a dom body mb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hcod⟩ := h
      unfold Setlec.natOpCod at hcod
      split at hcod
      · next hcb =>
        exfalso
        rcases hu with rfl | rfl <;> exact absurd hcb (by decide)
      · exact ⟨a, mb, by rw [beq_iff_eq.mp hcod]⟩
    · exact nomatch h
  · next hc =>
    exfalso
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    exact hc hu

/-! ## Reading the pinned types -/

/-- A stored level-monomorphic constant reads to its leaf at the plain
assignment. -/
theorem denoteP_levelless_const {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat} {d : Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    denoteP acval env ψ d (.const n []) = some (acval n ψ) := by
  have h : denoteP acval env ψ d (.const n [])
      = some (acval n (Level.substFn ψ ci.toConstantVal.levelParams []))
    := denoteP_const hf (by simp [hlp])
  rw [hlp, substFn_nil] at h
  exact h

/-- The pinned binary operation type's reading: a two-step `.pi` over
the `Nat` leaf and the codomain leaf, at the stored regime bits. -/
theorem denoteP_pinnedBinTy (m : EnvS2Core V env) (ψ : Name → Nat)
    {n₁ n₂ : Name} {mb₁ mb₂ : Setlec.BinderMeta} {codN : Name}
    {ciN codCi : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = []) :
    denoteP m.acval env ψ 0
        (.forallE n₁ (.const Setlec.natName [])
          (.forallE n₂ (.const Setlec.natName []) (.const codN []) mb₂)
          mb₁)
      = some (.pi 0 (pwBit ψ mb₁.pw) (m.acval Setlec.natName ψ)
          (.pi 0 (pwBit ψ mb₂.pw) (m.acval Setlec.natName ψ)
            (m.acval codN ψ))) := by
  rw [denoteP_forallE, denoteP_levelless_const hfN hlpN]
  rw [show (Expr.forallE n₂ (.const Setlec.natName [])
        (.const codN []) mb₂).instantiate1
        (.fvar 0 n₁ (.const Setlec.natName []))
      = Expr.forallE n₂ (.const Setlec.natName []) (.const codN []) mb₂
    from Setlec.Expr.instantiate1_eq_self
      (by simp [Setlec.Expr.looseBVarsBounded])]
  rw [denoteP_forallE, denoteP_levelless_const hfN hlpN]
  rw [show (Expr.const codN ([] : List Setlec.Level)).instantiate1
        (.fvar 1 n₂ (.const Setlec.natName []))
      = Expr.const codN [] from Setlec.Expr.instantiate1_eq_self
      (by simp [Setlec.Expr.looseBVarsBounded])]
  rw [denoteP_levelless_const hcodF hcodLp]
  rfl

/-- The pinned unary operation type's reading. -/
theorem denoteP_pinnedUnTy (m : EnvS2Core V env) (ψ : Name → Nat)
    {n₁ : Name} {mb₁ : Setlec.BinderMeta}
    {ciN : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denoteP m.acval env ψ 0
        (.forallE n₁ (.const Setlec.natName [])
          (.const Setlec.natName []) mb₁)
      = some (.pi 0 (pwBit ψ mb₁.pw) (m.acval Setlec.natName ψ)
          (m.acval Setlec.natName ψ)) := by
  rw [denoteP_forallE, denoteP_levelless_const hfN hlpN]
  rw [show (Expr.const Setlec.natName ([] : List Setlec.Level)).instantiate1
        (.fvar 0 n₁ (.const Setlec.natName []))
      = Expr.const Setlec.natName [] from Setlec.Expr.instantiate1_eq_self
      (by simp [Setlec.Expr.looseBVarsBounded])]
  rw [denoteP_levelless_const hfN hlpN]
  rfl

/-! ## Head packages from parts -/

/-- **The binary head package, from its parts**: a graded reading, a
membership in the (two-step, leaf-component) pinned product's reading,
and the product reading's own grading. -/
theorem natBinHeadP_of_parts (m : EnvS2Core V env) {ψ : Name → Nat}
    {f : Expr} {fa : AVExpr} {b₁ b₂ : Nat} {codN : Name}
    (hfa : denoteP m.acval env ψ 2 f = some fa)
    (hok : ∀ ρ : Nat → V, AnnotOkP V ρ fa)
    (hmem : ∀ ρ : Nat → V, interp2 V ρ fa ∈ˢ interp2 V ρ
      (.pi 0 b₁ (m.acval Setlec.natName ψ)
        (.pi 0 b₂ (m.acval Setlec.natName ψ) (m.acval codN ψ))))
    (htok : ∀ ρ : Nat → V, AnnotOkP V ρ
      ((.pi 0 b₁ (m.acval Setlec.natName ψ)
        (.pi 0 b₂ (m.acval Setlec.natName ψ) (m.acval codN ψ)))
        : AVExpr)) :
    NatBinHeadP m ψ f (fun ρ => interp2 V ρ (m.acval codN ψ)) := by
  refine ⟨fa, hfa, fun ρ _ => ⟨hok ρ, b₁, b₂, ?_, ?_, ?_⟩⟩
  · -- the membership, with the fibres closed off
    have h := hmem ρ
    rw [interp2_pi] at h
    have hfib : (fun x => interp2 V (cons x ρ)
          ((.pi 0 b₂ (m.acval Setlec.natName ψ) (m.acval codN ψ))
            : AVExpr))
        = fun _ => piR b₂ (natSP m ψ ρ)
            (fun _ => interp2 V ρ (m.acval codN ψ)) := by
      funext x
      rw [interp2_pi]
      congr 1
      · exact acval_interp2_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp2_closedC m _ ψ _ ρ
    rw [hfib] at h
    exact h
  · -- the outer fibre fact, from validity
    intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValidV_pi] at hv
    have h := hv.2.2 hz x hx
    rw [show interp2 V (cons x ρ)
          ((.pi 0 b₂ (m.acval Setlec.natName ψ) (m.acval codN ψ))
            : AVExpr)
        = piR b₂ (natSP m ψ ρ)
            (fun _ => interp2 V ρ (m.acval codN ψ)) from by
      rw [interp2_pi]
      congr 1
      · exact acval_interp2_closedC m _ ψ _ ρ
      · funext y
        exact acval_interp2_closedC m _ ψ _ ρ] at h
    exact h
  · -- the inner fibre fact, from validity one binder in
    intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValidV_pi] at hv
    have hinner := hv.2.1 x hx
    rw [AnnotValidV_pi] at hinner
    have h := hinner.2.2 hz x
      (by rw [acval_interp2_closedC m _ ψ (cons x ρ) ρ]; exact hx)
    rwa [acval_interp2_closedC m _ ψ _ ρ] at h

/-- **The unary head package, from its parts.** -/
theorem natUnHeadP_of_parts (m : EnvS2Core V env) {ψ : Name → Nat}
    {f : Expr} {fa : AVExpr} {b₁ : Nat} {codN : Name}
    (hfa : denoteP m.acval env ψ 2 f = some fa)
    (hok : ∀ ρ : Nat → V, AnnotOkP V ρ fa)
    (hmem : ∀ ρ : Nat → V, interp2 V ρ fa ∈ˢ interp2 V ρ
      (.pi 0 b₁ (m.acval Setlec.natName ψ) (m.acval codN ψ)))
    (htok : ∀ ρ : Nat → V, AnnotOkP V ρ
      ((.pi 0 b₁ (m.acval Setlec.natName ψ) (m.acval codN ψ))
        : AVExpr)) :
    NatUnHeadP m ψ f (fun ρ => interp2 V ρ (m.acval codN ψ)) := by
  refine ⟨fa, hfa, fun ρ _ => ⟨hok ρ, b₁, ?_, ?_⟩⟩
  · have h := hmem ρ
    rw [interp2_pi] at h
    have hfib : (fun x => interp2 V (cons x ρ) (m.acval codN ψ))
        = fun _ => interp2 V ρ (m.acval codN ψ) := by
      funext x
      exact acval_interp2_closedC m _ ψ _ ρ
    rw [hfib] at h
    exact h
  · intro hz x hx
    have hv := (htok ρ).2
    rw [AnnotValidV_pi] at hv
    have h := hv.2.2 hz x hx
    rwa [acval_interp2_closedC m _ ψ _ ρ] at h

/-! ## Head packages from the environment invariant

A stored operation with a pinned type gets its head package from
`mem_typeP` (the leaf inhabits its type's reading) and `type_okP` (the
reading is graded — which is where the fibre facts at the unknown
regime bits come from). -/

/-- **A stored pinned binary head.** -/
theorem natBinHeadP_of_stored (mp : EnvS2PM V μ env) {ψ : Name → Nat}
    {o : Name} {cvo : ConstantVal} {vo : Expr}
    {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (hlp : cvo.levelParams = [])
    {n₁ n₂ : Name} {mb₁ mb₂ : Setlec.BinderMeta} {codN : Name}
    (hty : cvo.type = .forallE n₁ (.const Setlec.natName [])
      (.forallE n₂ (.const Setlec.natName []) (.const codN []) mb₂)
      mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = []) :
    NatBinHeadP mp.base2 ψ (.const o [])
      (fun ρ => interp2 V ρ (mp.base2.acval codN ψ)) := by
  have hmemE := Setlec.SetR.Env.find?_mem hf
  have hnm : cvo.name = o := Setlec.SetR.Env.find?_name hf
  have hta : denoteP mp.base2.acval env ψ 0
      (ConstantInfo.defnInfo cvo vo ho).toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval Setlec.natName ψ)
          (.pi 0 (pwBit ψ mb₂.pw) (mp.base2.acval Setlec.natName ψ)
            (mp.base2.acval codN ψ))) := by
    show denoteP mp.base2.acval env ψ 0 cvo.type = _
    rw [hty]
    exact denoteP_pinnedBinTy mp.base2 ψ hfN hlpN hcodF hcodLp
  refine natBinHeadP_of_parts mp.base2
    (denoteP_levelless_const hf (show (ConstantInfo.defnInfo cvo vo
      ho).toConstantVal.levelParams = [] from hlp))
    (fun ρ => ⟨mp.base2.acval_ok2 _ _ ρ, mp.acval_validV _ _ ρ⟩)
    (fun ρ => ?_) (fun ρ => mp.type_okP _ hmemE ψ _ hta ρ)
  have h := mp.mem_typeP _ hmemE ψ _ hta ρ
  rwa [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at h

/-- **A stored pinned unary head.** -/
theorem natUnHeadP_of_stored (mp : EnvS2PM V μ env) {ψ : Name → Nat}
    {o : Name} {cvo : ConstantVal} {vo : Expr}
    {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (hlp : cvo.levelParams = [])
    {n₁ : Name} {mb₁ : Setlec.BinderMeta}
    (hty : cvo.type = .forallE n₁ (.const Setlec.natName [])
      (.const Setlec.natName []) mb₁)
    {ciN : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    NatUnHeadP mp.base2 ψ (.const o [])
      (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName ψ)) := by
  have hmemE := Setlec.SetR.Env.find?_mem hf
  have hnm : cvo.name = o := Setlec.SetR.Env.find?_name hf
  have hta : denoteP mp.base2.acval env ψ 0
      (ConstantInfo.defnInfo cvo vo ho).toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval Setlec.natName ψ)
          (mp.base2.acval Setlec.natName ψ)) := by
    show denoteP mp.base2.acval env ψ 0 cvo.type = _
    rw [hty]
    exact denoteP_pinnedUnTy mp.base2 ψ hfN hlpN
  refine natUnHeadP_of_parts mp.base2
    (denoteP_levelless_const hf (show (ConstantInfo.defnInfo cvo vo
      ho).toConstantVal.levelParams = [] from hlp))
    (fun ρ => ⟨mp.base2.acval_ok2 _ _ ρ, mp.acval_validV _ _ ρ⟩)
    (fun ρ => ?_) (fun ρ => mp.type_okP _ hmemE ψ _ hta ρ)
  have h := mp.mem_typeP _ hmemE ψ _ hta ρ
  rwa [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at h

/-! ## The two-variable context discipline, and the conversion -/

/-- The `Nat`-leaved sides satisfy `CtxOkP` at the two-variable
context. -/
theorem ctxOkP_natCtx2 (m : EnvS2Core V env) {ψ : Name → Nat}
    (hval : AcvalValidP m) {ciN : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {e : Expr}
    (hleaf : ∀ l ∈ e.fvarLeaves, l.1 < 2 ∧
      l.2.2 = .const Setlec.natName []) :
    CtxOkP m ψ 2 (natCtx2 m ψ) e := by
  refine ⟨rfl, fun l hl => ?_⟩
  obtain ⟨hlt, hty⟩ := hleaf l hl
  refine ⟨hlt, by rw [hty]; trivial, natAP m ψ, natAP m ψ,
    by rw [hty]; exact denoteP_levelless_const hfN hlpN, ?_, ?_, ?_⟩
  · show (natCtx2 m ψ)[2 - 1 - l.1]? = some (natAP m ψ)
    obtain h01 | h01 : l.1 = 0 ∨ l.1 = 1 := by omega
    · rw [h01]; rfl
    · rw [h01]; rfl
  · intro ρ _
    exact natAP_interp2_closed m ψ ρ _
  · intro ρ _
    exact ⟨m.acval_ok2 _ _ ρ, hval _ _ ρ⟩

/-- **One substituted equation, converted**: the recorded run plus both
sides' packages give the two-variable `interp2` equality — the exact
law shape `NatOpsP` stores.  `DefEqClaims2P` does the work; the frames
come from the v1 fragment machinery, the gradings from the packages,
the context from `ctxOkP_natCtx2`. -/
theorem natEqLawP_of_run (mp : EnvS2PM V μ env) {ψ : Name → Nat}
    {F : Nat} (hde : DefEqClaims2P μ mp.base2 ψ F)
    {ciN : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {lhs rhs : Expr} {la ra : AVExpr}
    (hrun : Setlec.isDefEqCore μ env F 2 lhs rhs = .ok true)
    (hwl : Expr.WScoped 2 lhs) (hbl : lhs.looseBVarsBounded 0 = true)
    (hLl : Expr.LeavesBounded lhs)
    (hll : ∀ l ∈ lhs.fvarLeaves, l.1 < 2 ∧
      l.2.2 = .const Setlec.natName [])
    (hwr : Expr.WScoped 2 rhs) (hbr : rhs.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded rhs)
    (hlr : ∀ l ∈ rhs.fvarLeaves, l.1 < 2 ∧
      l.2.2 = .const Setlec.natName [])
    (hla : denoteP mp.base2.acval env ψ 2 lhs = some la)
    (hga : ∀ ρ : Nat → V, Sat2 V (natCtx2 mp.base2 ψ) ρ →
      AnnotOkP V ρ la)
    (hra : denoteP mp.base2.acval env ψ 2 rhs = some ra)
    (hgr : ∀ ρ : Nat → V, Sat2 V (natCtx2 mp.base2 ψ) ρ →
      AnnotOkP V ρ ra) :
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp2 V ρ (mp.base2.acval Setlec.natName ψ) →
      y ∈ˢ interp2 V ρ (mp.base2.acval Setlec.natName ψ) →
      interp2 V (cons y (cons x ρ)) la
        = interp2 V (cons y (cons x ρ)) ra := by
  intro ρ x y hx hy
  have hρ : Sat2 V (natCtx2 mp.base2 ψ) (cons y (cons x ρ)) :=
    sat2_natCtx2 mp.base2 hx hy
  exact hde hrun hwl hbl hLl hwr hbr hLr
    (ctxOkP_natCtx2 mp.base2 mp.acvalValidP hfN hlpN hll)
    (ctxOkP_natCtx2 mp.base2 mp.acvalValidP hfN hlpN hlr)
    hla hra hga hgr (cons y (cons x ρ)) hρ

/-! ## The crossing: substituted readings at the prefix are raw
readings at the extension (`denote_substConst0`'s P mirror) -/

/-- **The substitution crossing for the install's own constant**: on
the shallow fragment, reading in the extended environment under the
extended valuation is reading the substituted expression in the old
one. -/
theorem denoteP_substConst0 {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat} {c₀ : ConstantInfo} {c : Name} {v : Expr}
    {A : (Name → Nat) → AVExpr}
    (hname : c₀.name = c) (hfresh : env.find? c = none)
    (hlp : c₀.toConstantVal.levelParams = [])
    (hacl : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (acval n ψ').liftN 1 k = acval n ψ')
    (hAcl : ∀ k : Nat, (A ψ).liftN 1 k = A ψ)
    (hv : denoteP acval env ψ 0 v = some (A ψ))
    (hvf : v.hasFvar = false) :
    ∀ (d : Nat) (e : Expr), shallowE e = true →
      denoteP (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d e
        = denoteP acval env ψ d (Expr.substConst0 c v e) := by
  intro d e
  induction e with
  | sort u =>
    intro _
    show denoteP (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d (.sort u)
      = denoteP acval env ψ d (.sort u)
    rw [denoteP_sort, denoteP_sort]
  | fvar idx n ty =>
    intro _
    show denoteP (acvalWith acval c A) ⟨c₀ :: env.consts⟩ ψ d
        (.fvar idx n ty) = denoteP acval env ψ d (.fvar idx n ty)
    rw [denoteP_fvar, denoteP_fvar]
  | const n us =>
    intro _
    by_cases hn : n = c
    · subst hn
      by_cases hus : us = []
      · subst hus
        rw [show Expr.substConst0 n v (.const n []) = v from by
          rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
        have hfc : (⟨c₀ :: env.consts⟩ : Env).find? n = some c₀ := by
          rw [Setlec.Env.find?_cons, if_pos hname]
        have h1 : denoteP (acvalWith acval n A) ⟨c₀ :: env.consts⟩ ψ d
            (.const n []) = some (acvalWith acval n A n ψ) :=
          denoteP_levelless_const hfc hlp
        rw [h1, show acvalWith acval n A n = A from acvalWith_self]
        exact (denoteP_depth_of_closed hacl hvf hAcl hv d).symm
      · rw [show Expr.substConst0 n v (.const n us) = .const n us from
          by rw [Expr.substConst0, if_neg (fun h => hus h.2)]]
        rw [denoteP, denoteP]
        rw [show (⟨c₀ :: env.consts⟩ : Env).find? n = some c₀ from by
          rw [Setlec.Env.find?_cons, if_pos hname], hfresh]
        dsimp only
        rw [if_neg (by rw [hlp]; simpa using hus)]
    · rw [show Expr.substConst0 c v (.const n us) = .const n us from by
        rw [Expr.substConst0, if_neg (fun h => hn h.1)]]
      rw [denoteP, denoteP]
      rw [show (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n from by
        rw [Setlec.Env.find?_cons,
          if_neg (fun hh => hn (hh.symm.trans hname))]]
      cases hf : env.find? n with
      | none => rfl
      | some ci =>
        dsimp only
        rw [show acvalWith acval c A n = acval n from acvalWith_ne hn]
  | app f a ihf iha =>
    intro hfr
    simp only [shallowE, Bool.and_eq_true] at hfr
    rw [show Expr.substConst0 c v (.app f a)
      = .app (Expr.substConst0 c v f) (Expr.substConst0 c v a) from
      rfl]
    rw [denoteP_app, denoteP_app, ihf hfr.1, iha hfr.2]
  | bvar _ => intro hfr; simp [shallowE] at hfr
  | lam _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | forallE _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | letE _ _ _ _ => intro hfr; simp [shallowE] at hfr
  | proj _ _ _ => intro hfr; simp [shallowE] at hfr
  | lit _ => intro hfr; simp [shallowE] at hfr

/-! ## `Nat`-codomain applications are graded arguments -/

/-- A binary head with `Nat` codomain applied to two graded arguments
is a graded argument. -/
theorem natArgP_of_bin (m : EnvS2Core V env) {ψ : Name → Nat}
    {f x y : Expr}
    (hh : NatBinHeadP m ψ f
      (fun ρ => interp2 V ρ (m.acval Setlec.natName ψ)))
    (hx : NatArgP m ψ x) (hy : NatArgP m ψ y) :
    NatArgP m ψ (.app (.app f x) y) :=
  natBinHeadP_app m hh hx hy

/-- A unary head with `Nat` codomain applied to a graded argument is a
graded argument. -/
theorem natArgP_of_un (m : EnvS2Core V env) {ψ : Name → Nat}
    {f x : Expr}
    (hh : NatUnHeadP m ψ f
      (fun ρ => interp2 V ρ (m.acval Setlec.natName ψ)))
    (hx : NatArgP m ψ x) :
    NatArgP m ψ (.app f x) :=
  natUnHeadP_app m hh hx

/-- A graded argument's package, forgetting the membership — the shape
`natEqLawP_of_run`'s grading premises take. -/
theorem NatArgP.package (m : EnvS2Core V env) {ψ : Name → Nat}
    {e : Expr} (h : NatArgP m ψ e) :
    ∃ ea, denoteP m.acval env ψ 2 e = some ea ∧
      ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ → AnnotOkP V ρ ea := by
  obtain ⟨ea, hea, hg⟩ := h
  exact ⟨ea, hea, fun ρ hρ => (hg ρ hρ).1⟩

/-- A `Bool`-codomain application's package (comparison sides): the
membership in the codomain is dropped, the grading kept. -/
theorem natBinHeadP_app_package (m : EnvS2Core V env) {ψ : Name → Nat}
    {f x y : Expr} {codS : (Nat → V) → V}
    (hh : NatBinHeadP m ψ f codS) (hx : NatArgP m ψ x)
    (hy : NatArgP m ψ y) :
    ∃ ea, denoteP m.acval env ψ 2 (.app (.app f x) y) = some ea ∧
      ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ → AnnotOkP V ρ ea := by
  obtain ⟨ea, hea, hg⟩ := natBinHeadP_app m hh hx hy
  exact ⟨ea, hea, fun ρ hρ => (hg ρ hρ).1⟩

/-- A stored level-monomorphic constant's package (the comparison
right-hand sides' `Bool` constructors). -/
theorem natConstP_package (m : EnvS2Core V env) {ψ : Name → Nat}
    (hval : AcvalValidP m) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    ∃ ea, denoteP m.acval env ψ 2 (.const n []) = some ea ∧
      ∀ ρ : Nat → V, Sat2 V (natCtx2 m ψ) ρ → AnnotOkP V ρ ea :=
  ⟨m.acval n ψ, denoteP_levelless_const hf hlp,
    fun ρ _ => ⟨m.acval_ok2 _ _ ρ, hval _ _ ρ⟩⟩

/-! ## Descending the extension's storedness facts -/

/-- `natOpStoredOk` at a fresh cons, for a name other than the head,
descends to the prefix (the pinned-type conjunct stays at the
extension — its shape is env-free, and its `Bool`-codomain storedness
conjunct is descended separately by the caller). -/
theorem natOpStoredOk_descend {c₀ : ConstantInfo} {n : Name}
    (hne : n ≠ c₀.name)
    (hok : Setlec.natOpStoredOk ⟨c₀ :: env.consts⟩ n = true) :
    ∃ cvn vn hn, env.find? n = some (.defnInfo cvn vn hn) ∧
      cvn.levelParams = [] ∧
      Setlec.natOpTyPinned ⟨c₀ :: env.consts⟩ n cvn.type = true := by
  unfold Setlec.natOpStoredOk at hok
  cases hf2 : (⟨c₀ :: env.consts⟩ : Env).find? n with
  | none => rw [hf2] at hok; exact nomatch hok
  | some ci =>
    rw [hf2] at hok
    cases ci with
    | defnInfo cvn vn hn =>
      simp only [Bool.and_eq_true] at hok
      have hfE : env.find? n = some (.defnInfo cvn vn hn) := by
        rw [Setlec.Env.find?_cons] at hf2
        split at hf2
        · next heq => exact absurd heq.symm hne
        · exact hf2
      exact ⟨cvn, vn, hn, hfE,
        by simpa [List.isEmpty_iff] using hok.1, hok.2⟩
    | _ => exact nomatch hok

/-! ## The field's suppliers -/

/-- The pinned codomain's name: `Bool` for the comparisons, `Nat`
otherwise. -/
def natOpCodN (c : Name) : Name :=
  if c = Setlec.natBeqName ∨ c = Setlec.natBleName then Setlec.boolName
  else Setlec.natName

/-- Fragment terms mention only stored constants (the raw sides; the
head `c` must itself be stored). -/
theorem constsBound_of_natFragOk {c : Name}
    (hc : (env.find? c).isSome = true)
    (hnat : (env.find? Setlec.natName).isSome = true) :
    ∀ {e : Expr}, Setlec.TTVerify.natFragOk env c e = true →
      ConstsBound env e := by
  intro e
  induction e with
  | sort u => intro _; unfold ConstsBound; trivial
  | fvar idx n ty =>
    intro h
    simp only [Setlec.TTVerify.natFragOk, Bool.and_eq_true,
      beq_iff_eq] at h
    unfold ConstsBound
    rw [h.2]
    unfold ConstsBound
    exact hnat
  | const n us =>
    intro h
    unfold ConstsBound
    simp only [Setlec.TTVerify.natFragOk, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, -⟩ | h
    · exact hc
    · revert h
      cases env.find? n with
      | none => intro h; exact nomatch h
      | some ci => intro _; rfl
  | app f a ihf iha =>
    intro h
    simp only [Setlec.TTVerify.natFragOk, Bool.and_eq_true] at h
    unfold ConstsBound
    exact ⟨ihf h.1, iha h.2⟩
  | bvar _ => intro h; simp [Setlec.TTVerify.natFragOk] at h
  | lam _ _ _ _ => intro h; simp [Setlec.TTVerify.natFragOk] at h
  | forallE _ _ _ _ => intro h; simp [Setlec.TTVerify.natFragOk] at h
  | letE _ _ _ _ => intro h; simp [Setlec.TTVerify.natFragOk] at h
  | proj _ _ _ => intro h; simp [Setlec.TTVerify.natFragOk] at h
  | lit _ => intro h; simp [Setlec.TTVerify.natFragOk] at h

/-- The raw sides of a stored operation's recurrences are in the
fragment, from the guard alone. -/
theorem natOpEquations_frag_of_guard {c : Name}
    (hg : natOpGuard env c = true) :
    ∀ eq ∈ Setlec.natOpEquations 0 c,
      Setlec.TTVerify.natFragOk env c eq.1 = true ∧
        Setlec.TTVerify.natFragOk env c eq.2 = true := by
  obtain ⟨hN, hz, hs, hdeps, hbool⟩ :=
    Setlec.TTVerify.natOpGuard_stored hg
  refine Setlec.TTVerify.natOpEquations_frag hz hs
    (fun n hn _ => hdeps n hn) (fun hc => (hbool (by
      rcases hc with rfl | rfl <;> simp)).1)
    (fun hc => (hbool (by rcases hc with rfl | rfl <;> simp)).2)

/-- **The per-operation crossing at a fresh cons**: an operation
stored in the prefix keeps its `NatOpsP` entry at the extension. -/
theorem natOpsP_entry_cons (mp : EnvS2PM V μ env) {φ : Name → Nat}
    (hprev : NatOpsP mp.base2 φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    {c : Name} (hcN : c ∈ Setlec.natOpNames) (hne : c ≠ c₀.name)
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (hf₂ : (⟨c₀ :: env.consts⟩ : Env).find? c
      = some (.defnInfo cv' v' hint')) :
    natOpGuard (⟨c₀ :: env.consts⟩ : Env) c = true ∧
    ∀ eq ∈ Setlec.natOpEquations 0 c, ∃ L R,
      denoteP m₂.acval ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
      denoteP m₂.acval ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
        y ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
        interp2 V (cons y (cons x ρ)) L
          = interp2 V (cons y (cons x ρ)) R := by
  have hfE : env.find? c = some (.defnInfo cv' v' hint') := by
    rw [Setlec.Env.find?_cons] at hf₂
    split at hf₂
    · next heq => exact absurd heq.symm hne
    · exact hf₂
  obtain ⟨hg, hlaws⟩ := hprev c hcN cv' v' hint' hfE
  -- the stored heads are not the fresh cons
  obtain ⟨hN, -, -, -, -⟩ := Setlec.TTVerify.natOpGuard_stored hg
  obtain ⟨ciN, hfN, -⟩ := Setlec.TTVerify.storedNoLevels_exists hN
  have hnatne : Setlec.natName ≠ c₀.name := fun hh => by
    rw [hh, hfresh] at hfN
    exact nomatch hfN
  have hcb : ∀ eq ∈ Setlec.natOpEquations 0 c,
      ConstsBound env eq.1 ∧ ConstsBound env eq.2 := by
    intro eq hq
    obtain ⟨h1, h2⟩ := natOpEquations_frag_of_guard hg eq hq
    exact ⟨constsBound_of_natFragOk (by simp [hfE]) (by simp [hfN]) h1,
      constsBound_of_natFragOk (by simp [hfE]) (by simp [hfN]) h2⟩
  refine ⟨Setlec.TTVerify.natOpGuard_cons hfresh hg, fun eq hq => ?_⟩
  obtain ⟨L, R, hL, hR, hlaw⟩ := hlaws eq hq
  refine ⟨L, R, ?_, ?_, ?_⟩
  · rw [hac]
    exact denoteP_cons_fresh_mono hfresh φ 2 eq.1 (hcb eq hq).1 hL
  · rw [hac]
    exact denoteP_cons_fresh_mono hfresh φ 2 eq.2 (hcb eq hq).2 hR
  · intro ρ x y hx hy
    rw [hac, show acvalWith mp.base2.acval c₀.name A Setlec.natName
        = mp.base2.acval Setlec.natName from acvalWith_ne hnatne]
      at hx hy
    exact hlaw ρ x y hx hy

/-- **`NatOpsP` at a fresh non-operation cons** — every value-kind
step except the operation's own install discharges its obligation
here.  The disjunctive premise: either the cons is not a definition at
all, or its name is not an operation name. -/
theorem natOpsP_cons_fresh (mp : EnvS2PM V μ env) {φ : Name → Nat}
    (hprev : NatOpsP mp.base2 φ)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnothead : (∀ cv v hint, c₀ ≠ .defnInfo cv v hint) ∨
      c₀.name ∉ Setlec.natOpNames)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    NatOpsP m₂ φ := by
  intro c hcN cv' v' hint' hf₂
  by_cases hne : c = c₀.name
  · subst hne
    rw [Setlec.Env.find?_cons_self] at hf₂
    rcases hnothead with hnd | hnn
    · exact absurd (Option.some.inj hf₂) (hnd cv' v' hint')
    · exact absurd hcN hnn
  · exact natOpsP_entry_cons mp hprev hfresh m₂ hac hcN hne hf₂

/-- **The installing operation's own head packages**, from the
harvest's facts: the annotated value's reading, grading and membership
at the declared type's reading, plus the type's pin.  Splits by the
operation's arity and codomain, concluding both forms
`natOpsP_install` takes. -/
theorem natSelfHeadP_install (mp : EnvS2PM V μ env) {φ : Name → Nat}
    {c : Name} (hcmem : c ∈ Setlec.natOpNames)
    {lps : List Name} {type' value' : Expr} {hint : ReducibilityHint}
    (hfresh : env.find? c = none)
    (hpin : Setlec.natOpTyPinned
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env)
      c type' = true)
    (hs : natLitSupported env = true)
    {Ta : (Name → Nat) → AVExpr}
    (hTa : ∀ ψ, denoteP mp.base2.acval env ψ 0 type' = some (Ta ψ))
    (hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkP V ρ (Ta ψ))
    {A : (Name → Nat) → AVExpr}
    (hA2 : ∀ ψ, denoteP mp.base2.acval env ψ 2 value' = some (A ψ))
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkP V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (Ta ψ)) :
    (c ≠ Setlec.natPredName →
      NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval (natOpCodN c) φ))) ∧
    (c = Setlec.natPredName →
      NatUnHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ))) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN0,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hlpN : (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams
      = [] := hlpN0
  constructor
  · -- the binary head
    intro hcp
    have hnu : ¬(c = Setlec.natPredName ∨ c = Setlec.natLog2Name) := by
      rintro (rfl | rfl)
      · exact hcp rfl
      · exact absurd hcmem (by decide)
    obtain ⟨n₁, n₂, mb₁, mb₂, cod, hty, hcmp, hncmp⟩ :=
      natOpTyPinned_shape_bin hnu hpin
    by_cases hccmp : c = Setlec.natBeqName ∨ c = Setlec.natBleName
    · -- `Bool` codomain
      obtain ⟨rfl, ci₂, hfB₂, hlpB₂⟩ := hcmp hccmp
      have hBne : Setlec.boolName ≠ c :=
        Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcmem
      have hfB : env.find? Setlec.boolName = some ci₂ := by
        rw [Setlec.Env.find?_cons] at hfB₂
        split at hfB₂
        · next heq =>
          exact absurd (heq.symm.trans (show (ConstantInfo.defnInfo
            ⟨c, lps, type'⟩ value' hint).name = c from rfl)) hBne
        · exact hfB₂
      have hTshape := denoteP_pinnedBinTy (codN := Setlec.boolName)
        (n₁ := n₁) (n₂ := n₂) (mb₁ := mb₁) (mb₂ := mb₂)
        mp.base2 φ hfN hlpN hfB hlpB₂
      rw [← hty] at hTshape
      obtain heq : Ta φ = _ :=
        Option.some.inj ((hTa φ).symm.trans hTshape)
      have hres := natBinHeadP_of_parts mp.base2 (hA2 φ)
        (fun ρ => hAok φ ρ)
        (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)
      rwa [show natOpCodN c = Setlec.boolName from by
        unfold natOpCodN; rw [if_pos hccmp]]
    · -- `Nat` codomain
      obtain rfl := hncmp hccmp
      have hTshape := denoteP_pinnedBinTy (codN := Setlec.natName)
        (n₁ := n₁) (n₂ := n₂) (mb₁ := mb₁) (mb₂ := mb₂)
        mp.base2 φ hfN hlpN hfN hlpN
      rw [← hty] at hTshape
      obtain heq : Ta φ = _ :=
        Option.some.inj ((hTa φ).symm.trans hTshape)
      have hres := natBinHeadP_of_parts mp.base2 (hA2 φ)
        (fun ρ => hAok φ ρ)
        (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)
      rwa [show natOpCodN c = Setlec.natName from by
        unfold natOpCodN; rw [if_neg hccmp]]
  · -- the unary head (`pred`)
    intro hcp
    obtain ⟨n₁, mb₁, hty⟩ :=
      natOpTyPinned_shape_un (Or.inl hcp) hpin
    have hTshape := denoteP_pinnedUnTy mp.base2 φ hfN hlpN
      (n₁ := n₁) (mb₁ := mb₁)
    rw [← hty] at hTshape
    obtain heq : Ta φ = _ :=
      Option.some.inj ((hTa φ).symm.trans hTshape)
    exact natUnHeadP_of_parts mp.base2 (hA2 φ) (fun ρ => hAok φ ρ)
      (fun ρ => heq ▸ hmemA φ ρ) (fun ρ => heq ▸ hTok φ ρ)

/-- **`NatOpsP` at the operation's own install** — the run-certificate
conversion, end to end: the recorded `isDefEqCore` runs on the
substituted recurrences (`NatEqsRunR`) become `interp2` equalities
through `DefEqClaims2P` at the pre-insertion environment, and the
substitution crossing (`denoteP_substConst0`) restates them as the raw
equations' readings at the extension. -/
theorem natOpsP_install (mp : EnvS2PM V μ env) {φ : Name → Nat}
    {F : Nat} (hde : DefEqClaims2P μ mp.base2 φ F)
    (hprev : NatOpsP mp.base2 φ)
    {c : Name} {lps : List Name} {type' value' : Expr}
    {hint : ReducibilityHint}
    (hcmem : c ∈ Setlec.natOpNames)
    (hfresh : env.find? c = none)
    (hlpcv : lps = [])
    (hs : natLitSupported env = true)
    (hg2 : natOpGuard
      (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env) c
      = true)
    (hdepsOk : (Setlec.natOpDeps c).all
      (Setlec.natOpStoredOk
        (⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩ : Env))
      = true)
    (hruns : NatEqsRunR μ F env
      ((Setlec.natOpEquations 0 c).map fun eq =>
        (Expr.substConst0 c value' eq.1,
         Expr.substConst0 c value' eq.2)))
    {A : (Name → Nat) → AVExpr}
    (hA : ∀ ψ, denoteP mp.base2.acval env ψ 0 value' = some (A ψ))
    (hAcl : ∀ ψ k, (A ψ).liftN 1 k = A ψ)
    (hvf' : value'.hasFvar = false)
    (hbv' : value'.looseBVarsBounded 0 = true)
    (hSelfBin : c ≠ Setlec.natPredName →
      NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval (natOpCodN c) φ)))
    (hSelfUn : c = Setlec.natPredName →
      NatUnHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)))
    (m₂ : EnvS2Core V
      ⟨.defnInfo ⟨c, lps, type'⟩ value' hint :: env.consts⟩)
    (hac : m₂.acval
      = acvalWith mp.base2.acval c A) :
    NatOpsP m₂ φ := by
  intro cq hcqN cv' v' hint' hf₂
  have hname0 : (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
      hint).name = c := rfl
  by_cases hne : cq = c
  case neg =>
    exact natOpsP_entry_cons mp hprev
      (c₀ := .defnInfo ⟨c, lps, type'⟩ value' hint)
      (show env.find? (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name = none from hfresh) m₂
      (show m₂.acval = acvalWith mp.base2.acval
        (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value' hint).name A
        from hac) hcqN
      (show cq ≠ (ConstantInfo.defnInfo ⟨c, lps, type'⟩ value'
        hint).name from hne) hf₂
  subst hne
  refine ⟨hg2, fun eq hq => ?_⟩
  obtain ⟨e1, e2⟩ := eq
  -- the shared preamble: storedness at the prefix, fragments, frames
  have hnh : NatHeadsP mp.base2 φ := mp.nat_heads φ
  have hvalV : AcvalValidP mp.base2 := mp.acvalValidP
  obtain ⟨hN₂, hz₂, hs₂, hdeps₂, hbool₂⟩ :=
    Setlec.TTVerify.natOpGuard_stored hg2
  have tr : ∀ {n : Name}, n ≠ cq →
      Setlec.TTVerify.storedNoLevels
        (⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ : Env) n →
      Setlec.TTVerify.storedNoLevels env n := fun hne h =>
    Setlec.TTVerify.storedNoLevels_of_cons
      (ci := .defnInfo ⟨cq, lps, type'⟩ value' hint) rfl hne h
  have hnz : Setlec.natZeroName ≠ cq :=
    Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcqN
  have hns : Setlec.natSuccName ≠ cq :=
    Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcqN
  have hnN : Setlec.natName ≠ cq :=
    Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcqN
  have hnT : Setlec.boolTrueName ≠ cq :=
    Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcqN
  have hnF : Setlec.boolFalseName ≠ cq :=
    Setlec.TTVerify.ne_of_mem_natOpNames (by decide) hcqN
  obtain ⟨hfr1, hfr2⟩ := Setlec.TTVerify.natOpEquations_frag
    (env := env) (c := cq) (tr hnz hz₂) (tr hns hs₂)
    (fun n hn hne => tr hne (hdeps₂ n hn))
    (fun hc => tr hnT (hbool₂ (by rcases hc with rfl | rfl <;> simp)).1)
    (fun hc => tr hnF (hbool₂ (by rcases hc with rfl | rfl <;> simp)).2)
    (e1, e2) hq
  have hden : ∀ ψ : Name → Nat,
      ∃ V0, denote mp.base.cval env ψ 0 value' = some V0 :=
    fun ψ => ⟨(A ψ).erase,
      denoteP_erase mp.base_erase 0 value' (hA ψ)⟩
  obtain ⟨hw1, hb1, hL1, hleaf1⟩ :=
    Setlec.TTVerify.natFrag_subst_syntax hvf' hbv' hfr1
  obtain ⟨hw2, hb2, hL2, hleaf2⟩ :=
    Setlec.TTVerify.natFrag_subst_syntax hvf' hbv' hfr2
  have hrun := hruns _ (List.mem_map.mpr ⟨(e1, e2), hq, rfl⟩)
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN0,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  have hlpN : (ConstantInfo.indInfo cvN caps).toConstantVal.levelParams
      = [] := hlpN0
  -- the crossing and the membership conversion, shared
  have hcross : ∀ (e : Expr), shallowE e = true →
      ∀ {ea : AVExpr},
      denoteP mp.base2.acval env φ 2 (Expr.substConst0 cq value' e)
        = some ea →
      denoteP m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2 e
        = some ea := by
    intro e hsh ea h
    rw [hac, denoteP_substConst0 (c₀ := .defnInfo ⟨cq, lps, type'⟩
        value' hint)
        (show (ConstantInfo.defnInfo ⟨cq, lps, type'⟩ value'
          hint).name = cq from rfl)
        hfresh hlpcv mp.base2.acval_closed (hAcl φ)
        (hA φ) hvf' 2 e hsh]
    exact h
  have hnatne : Setlec.natName ≠
      (ConstantInfo.defnInfo ⟨cq, lps, type'⟩ value' hint).name := hnN
  have hmemc : ∀ (ρ : Nat → V) (x : V),
      x ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
      x ∈ˢ interp2 V ρ (mp.base2.acval Setlec.natName φ) := by
    intro ρ x hx
    rw [hac] at hx
    rwa [show acvalWith mp.base2.acval cq A Setlec.natName
        = mp.base2.acval Setlec.natName from acvalWith_ne hnN] at hx
  -- stored dependency heads (the pinned types via `hdepsOk`)
  have hdepBin : ∀ o ∈ Setlec.natOpDeps cq, o ≠ cq →
      ¬(o = Setlec.natBeqName ∨ o = Setlec.natBleName) →
      ¬(o = Setlec.natPredName ∨ o = Setlec.natLog2Name) →
      NatBinHeadP mp.base2 φ (.const o [])
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
    intro o ho hone honcmp honun
    obtain ⟨cvo, vo, hino, hfo, hlpo, hpino⟩ :=
      natOpStoredOk_descend (c₀ := .defnInfo ⟨cq, lps, type'⟩ value'
        hint) hone (List.all_eq_true.mp hdepsOk o (by simpa using ho))
    obtain ⟨n₁, n₂, mb₁, mb₂, cod, hty, -, hcodN⟩ :=
      natOpTyPinned_shape_bin honun hpino
    exact natBinHeadP_of_stored (ψ := φ) mp hfo hlpo
      (by rw [hty, hcodN honcmp]) hfN hlpN hfN hlpN
  have hdepUn : ∀ o ∈ Setlec.natOpDeps cq, o ≠ cq →
      (o = Setlec.natPredName ∨ o = Setlec.natLog2Name) →
      NatUnHeadP mp.base2 φ (.const o [])
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
    intro o ho hone houn
    obtain ⟨cvo, vo, hino, hfo, hlpo, hpino⟩ :=
      natOpStoredOk_descend (c₀ := .defnInfo ⟨cq, lps, type'⟩ value'
        hint) hone (List.all_eq_true.mp hdepsOk o (by simpa using ho))
    obtain ⟨n₁, mb₁, hty⟩ := natOpTyPinned_shape_un houn hpino
    exact natUnHeadP_of_stored (ψ := φ) mp hfo hlpo hty hfN hlpN
  -- one equation, packaged: the shared closing move
  have close : ∀ {la ra : AVExpr},
      denoteP mp.base2.acval env φ 2
        (Expr.substConst0 cq value' e1) = some la →
      (∀ ρ : Nat → V, Sat2 V (natCtx2 mp.base2 φ) ρ →
        AnnotOkP V ρ la) →
      denoteP mp.base2.acval env φ 2
        (Expr.substConst0 cq value' e2) = some ra →
      (∀ ρ : Nat → V, Sat2 V (natCtx2 mp.base2 φ) ρ →
        AnnotOkP V ρ ra) →
      ∃ L R, denoteP m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2
          e1 = some L ∧
        denoteP m₂.acval
          ⟨.defnInfo ⟨cq, lps, type'⟩ value' hint :: env.consts⟩ φ 2
          e2 = some R ∧
        ∀ (ρ : Nat → V) (x y : V),
          x ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
          y ∈ˢ interp2 V ρ (m₂.acval Setlec.natName φ) →
          interp2 V (cons y (cons x ρ)) L
            = interp2 V (cons y (cons x ρ)) R := by
    intro la ra hla hga hra hgr
    refine ⟨la, ra,
      hcross e1 (Setlec.TTVerify.shallowE_of_natFragOk hfr1) hla,
      hcross e2 (Setlec.TTVerify.shallowE_of_natFragOk hfr2) hra,
      fun ρ x y hx hy => ?_⟩
    exact natEqLawP_of_run mp hde hfN hlpN hrun hw1 hb1 hL1 hleaf1
      hw2 hb2 hL2 hleaf2 hla hga hra hgr ρ x y (hmemc ρ x hx)
      (hmemc ρ y hy)
  -- the per-operation equation analysis
  clear hf₂ hcqN
  rcases (show cq = Setlec.natPredName ∨ cq = Setlec.natAddName ∨
      cq = Setlec.natSubName ∨ cq = Setlec.natMulName ∨
      cq = Setlec.natPowName ∨ cq = Setlec.natBeqName ∨
      cq = Setlec.natBleName from by
    simpa [Setlec.natOpNames] using hcmem) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `Nat.pred`
    have hun : NatUnHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) :=
      hSelfUn rfl
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- pred 0 = 0
      obtain ⟨la, hla, hga⟩ := NatArgP.package mp.base2
        (natArgP_of_un mp.base2 hun hz)
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2 hz
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- pred (succ x) = x
      obtain ⟨la, hla, hga⟩ := NatArgP.package mp.base2
        (natArgP_of_un mp.base2 hun
          (natArgP_succ mp.base2 hnh hvalV hs hvx))
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.add`
    have hbin : NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN Setlec.natAddName = Setlec.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- add x 0 = x
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- add x (succ y) = succ (add x y)
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        hvx (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2
        (natArgP_succ mp.base2 hnh hvalV hs
          (natArgP_of_bin mp.base2 hbin hvx hvy))
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.sub`
    have hbin : NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN Setlec.natSubName = Setlec.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hpred := hdepUn Setlec.natPredName (by decide) (by decide)
      (Or.inl rfl)
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- sub x 0 = x
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2 hvx
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- sub x (succ y) = pred (sub x y)
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        hvx (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2
        (natArgP_of_un mp.base2 hpred
          (natArgP_of_bin mp.base2 hbin hvx hvy))
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.mul`
    have hbin : NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN Setlec.natMulName = Setlec.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hadd := hdepBin Setlec.natAddName (by decide) (by decide)
      (by decide) (by decide)
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- mul x 0 = 0
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2 hz
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- mul x (succ y) = add (mul x y) x
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        hvx (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2
        (natArgP_of_bin mp.base2 hadd
          (natArgP_of_bin mp.base2 hbin hvx hvy) hvx)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.pow`
    have hbin : NatBinHeadP mp.base2 φ value'
        (fun ρ => interp2 V ρ (mp.base2.acval Setlec.natName φ)) := by
      have h := hSelfBin (by decide)
      simpa only [show natOpCodN Setlec.natPowName = Setlec.natName
        from by unfold natOpCodN; rw [if_neg (by decide)]] using h
    have hmul := hdepBin Setlec.natMulName (by decide) (by decide)
      (by decide) (by decide)
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- pow x 0 = 1
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hz
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2
        (natArgP_succ mp.base2 hnh hvalV hs hz)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- pow x (succ y) = mul (pow x y) x
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        hvx (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ := NatArgP.package mp.base2
        (natArgP_of_bin mp.base2 hmul
          (natArgP_of_bin mp.base2 hbin hvx hvy) hvx)
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.beq`
    have hbin := hSelfBin (by decide)
    obtain ⟨ciT, hfT, hlpT⟩ := Setlec.TTVerify.storedNoLevels_exists
      (tr hnT (hbool₂ (by decide)).1)
    obtain ⟨ciF, hfF, hlpF⟩ := Setlec.TTVerify.storedNoLevels_exists
      (tr hnF (hbool₂ (by decide)).2)
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- beq 0 0 = true
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hz hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConstP_package mp.base2 hvalV hfT hlpT
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq 0 (succ y) = false
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        hz (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natConstP_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq (succ x) 0 = false
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        (natArgP_succ mp.base2 hnh hvalV hs hvx) hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConstP_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- beq (succ x) (succ y) = beq x y
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        (natArgP_succ mp.base2 hnh hvalV hs hvx)
        (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hvy
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
  · -- `Nat.ble`
    have hbin := hSelfBin (by decide)
    obtain ⟨ciT, hfT, hlpT⟩ := Setlec.TTVerify.storedNoLevels_exists
      (tr hnT (hbool₂ (by decide)).1)
    obtain ⟨ciF, hfF, hlpF⟩ := Setlec.TTVerify.storedNoLevels_exists
      (tr hnF (hbool₂ (by decide)).2)
    have hvx := natArgP_var0 mp.base2 φ (.str .anonymous "x")
    have hvy := natArgP_var1 mp.base2 φ (.str .anonymous "y")
    have hz := natArgP_zero mp.base2 hnh hvalV hs
    simp +decide [Setlec.natOpEquations] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- ble 0 y = true
      obtain ⟨la, hla, hga⟩ :=
        natBinHeadP_app_package mp.base2 hbin hz hvy
      obtain ⟨ra, hra, hgr⟩ :=
        natConstP_package mp.base2 hvalV hfT hlpT
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- ble (succ x) 0 = false
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        (natArgP_succ mp.base2 hnh hvalV hs hvx) hz
      obtain ⟨ra, hra, hgr⟩ :=
        natConstP_package mp.base2 hvalV hfF hlpF
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra
    · -- ble (succ x) (succ y) = ble x y
      obtain ⟨la, hla, hga⟩ := natBinHeadP_app_package mp.base2 hbin
        (natArgP_succ mp.base2 hnh hvalV hs hvx)
        (natArgP_succ mp.base2 hnh hvalV hs hvy)
      obtain ⟨ra, hra, hgr⟩ :=
        natBinHeadP_app_package mp.base2 hbin hvx hvy
      refine close ?_ hga ?_ hgr
      · simpa +decide [Expr.substConst0] using hla
      · simpa +decide [Expr.substConst0] using hra

end Setlec.SetR.Interp2
