import Setlec.TTVerify.NatOpPin
import Setlec.Verify.DivModInv

/-!
# The `Nat.div`/`Nat.mod` characterization pin

`DivModPinTT`, the second obligation `DeclDefnTT` left behind.

`checkDivModCerts` checks each vendored certificate exactly like a
theorem declaration over an *opened* four-variable telescope
(`x`, `y`, and one `fvar` per `ble`-guard hypothesis), in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value.  So the bridge's job is:

1. turn a successful run into a derivation in the closed four-entry
   context `[H₂, H₁, Nat, Nat]` — `InferClaimsTT` at depth `4`, then
   `DefEqClaimsTT` against the pinned equation, then `EnvTT.eq_law` to
   read the resulting `Eq` spine as the layer's `eqE`;
2. move that derivation to the caller's arbitrary context and
   arguments.

Step 2 takes the **object-level route** the substitution file asks for:
four `lam`s close the derivation, `weakenTail` puts it in the caller's
context, and four `app`s instantiate it — the `app` rule's own
`B.inst a` performs every substitution in the type.  `HasType.instN`
is never used here.

> **The inert type slot pays for the guards.**  A clause's hypothesis
> is handed to us as `Deq Δ (ble y x) true`, but the certificate wants
> an *inhabitant* of the stored `Eq` spine.  `Deq.toHasType` retypes a
> derivation at **any** type slot, so the guard converts with no
> unique-typing argument anywhere: pick the slot the law wants.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The fragment's constants, denoted -/

/-- A constant of the certificate fragment denotes to the install's
valuation — the operation itself through its substituted stored value,
every other constant through the environment. -/
def DMDen {env : Env} (m : EnvTT env) (c : Name) (value' : Expr)
    (φ : Name → Nat) (n : Name) : Prop :=
  ∀ d, denote m.cval env φ d (Expr.substConst0 c value' (.const n []))
    = some (cvalAt m.cval env c value' n φ)

/-- The operation's own constant. -/
theorem DMDen.self {env : Env} {m : EnvTT env} {c : Name} {value' : Expr}
    {φ : Name → Nat} {V : VExpr}
    (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false)
    (hvb : value'.looseBVarsBounded 0 = true) :
    DMDen m c value' φ c := by
  intro d
  rw [show Expr.substConst0 c value' (.const c []) = value' from by
    rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
  rw [denote_depth_closed m.cval_closed hvf hvb d, hv, cvalAt_self hv]

/-- Any other stored constant. -/
theorem DMDen.other {env : Env} {m : EnvTT env} {c : Name} {value' : Expr}
    {φ : Name → Nat} {n : Name} {ci : ConstantInfo} (hne : n ≠ c)
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    DMDen m c value' φ n := by
  intro d
  rw [show Expr.substConst0 c value' (.const n []) = .const n [] from by
    rw [Expr.substConst0, if_neg (fun hh => hne hh.1)]]
  rw [denote_const_nolevels m φ hf hlp d, cvalAt_ne hne]

/-! ## The pinned operations, typed

`natOpStoredOk` pins each dependency's type to `Nat → Nat → Nat` or
`Nat → Nat → Bool` (`Nat → Nat` for the unary pair).  The guard checks
that shape so the *reduction* rules may assume it; the bridge reads the
same shape as the typing that lets a clause's spines be formed at all.
-/

/-- The pinned codomain of an operation, as a term. -/
def dmCodV {env : Env} (m : EnvTT env) (φ : Name → Nat) (n : Name) : VExpr :=
  if n = natBeqName ∨ n = natBleName then m.cval boolName φ
  else m.cval natName φ

/-- The pinned codomain is a bare constant, so no instantiation ever
enters it. -/
theorem natOpCod_shape {env : Env} {n : Name} {e : Expr}
    (h : natOpCod env n e = true) : ∃ bn, e = .const bn [] := by
  unfold natOpCod at h
  by_cases hb : (decide (n = natBeqName) || decide (n = natBleName)) = true
  · rw [if_pos hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨boolName, h.1⟩
  · rw [if_neg hb] at h
    simp only [beq_iff_eq] at h
    exact ⟨natName, h⟩

/-- `natOpCod`, denoted. -/
theorem denote_natOpCod {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {e : Expr} (h : natOpCod env n e = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) (d : Nat) :
    denote m.cval env φ d e = some (dmCodV m φ n) := by
  unfold natOpCod at h
  by_cases hb : (decide (n = natBeqName) || decide (n = natBleName)) = true
  · rw [if_pos hb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hbool⟩ := h
    rw [dmCodV, if_pos (by simpa using hb)]
    revert hbool
    split
    · next ci hf =>
      intro hbool
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hbool
      exact denote_const_nolevels m φ hf hbool.1 d
    · intro hbool; exact nomatch hbool
  · rw [if_neg hb] at h
    simp only [beq_iff_eq] at h
    subst h
    rw [dmCodV, if_neg (by simpa using hb)]
    exact denote_const_nolevels m φ hfN hlpN d

/-- A pinned binary operation's type, denoted. -/
theorem denote_natOpTy2 {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {ty : Expr}
    (hnot : ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true))
    (h : natOpTyPinned env n ty = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denote m.cval env φ 0 ty
      = some (.pi (m.cval natName φ)
        (.pi (m.cval natName φ) (dmCodV m φ n))) := by
  unfold natOpTyPinned at h
  rw [if_neg hnot] at h
  revert h
  match ty with
  | .forallE nm dom (.forallE nm2 dom2 body mb2) mb => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
  | .forallE _ _ (.bvar _) _ | .forallE _ _ (.fvar _ _ _) _
  | .forallE _ _ (.sort _) _ | .forallE _ _ (.const _ _) _
  | .forallE _ _ (.app _ _) _ | .forallE _ _ (.lam _ _ _ _) _
  | .forallE _ _ (.letE _ _ _ _) _ | .forallE _ _ (.lit _) _
  | .forallE _ _ (.proj _ _ _) _ =>
    intro h; exact nomatch h
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hcod⟩ := h
  obtain ⟨bn, rfl⟩ := natOpCod_shape hcod
  have hN : ∀ d, denote m.cval env φ d (.const natName [])
      = some (m.cval natName φ) := fun d =>
    denote_const_nolevels m φ hfN hlpN d
  simp only [denote_forallE, hN, Expr.instantiate1,
    denote_natOpCod m φ hcod hfN hlpN]

/-- A pinned unary operation's type, denoted. -/
theorem denote_natOpTy1 {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {ty : Expr}
    (hnot : (decide (n = natPredName) || decide (n = natLog2Name)) = true)
    (h : natOpTyPinned env n ty = true)
    {ciN : ConstantInfo} (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = []) :
    denote m.cval env φ 0 ty
      = some (.pi (m.cval natName φ) (dmCodV m φ n)) := by
  unfold natOpTyPinned at h
  rw [if_pos hnot] at h
  revert h
  match ty with
  | .forallE nm dom body mb => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hcod⟩ := h
  obtain ⟨bn, rfl⟩ := natOpCod_shape hcod
  have hN : ∀ d, denote m.cval env φ d (.const natName [])
      = some (m.cval natName φ) := fun d =>
    denote_const_nolevels m φ hfN hlpN d
  simp only [denote_forallE, hN, Expr.instantiate1,
    denote_natOpCod m φ hcod hfN hlpN]

/-! ## One certificate, extracted

The transpose of `divModCert_extract`: annotate, infer, compare — with
`InferClaimsTT` and `DefEqClaimsTT` where the model has
`inferTypeCore_sound` and `isDefEqCore_sound`, and the same three
containment lemmas carrying the frames across the two walks. -/

/-- Annotation only shrinks the leaf closure, so a context
correspondence survives it. -/
theorem CtxOk.annotate {env : Env} {cval : TConstVal} {φ : Name → Nat}
    {F d : Nat} {Δ : List VExpr} {e e' : Expr}
    (hann : annotateCore env F d e = .ok e') (hw : Expr.WScoped d e)
    (hb : e.looseBVarsBounded 0 = true)
    (h : CtxOk cval env φ d Δ e) : CtxOk cval env φ d Δ e' :=
  ⟨h.1, fun l hl => h.2 l (annotateCore_leaves_sub F e hann hw hb l hl)⟩

/-- **One certificate, extracted.**  A successful run inhabits the
pinned equation's denotation in the frame's own context. -/
theorem cert_extractT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {F : Nat} {A0 eqS appliedA tp : Expr} {Δ : List VExpr} {E : VExpr}
    (hw : Expr.WScoped 4 A0) (hb : A0.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded A0) (hC : CtxOk m.cval env φ 4 Δ A0)
    (hwE : Expr.WScoped 4 eqS) (hbE : eqS.looseBVarsBounded 0 = true)
    (hLE : Expr.LeavesBounded eqS) (hCE : CtxOk m.cval env φ 4 Δ eqS)
    (hE : denote m.cval env φ 4 eqS = some E)
    (hann : annotateCore env F 4 A0 = .ok appliedA)
    (hinf : inferTypeCore env F 4 appliedA = .ok tp)
    (hde : isDefEqCore env F 4 tp eqS = .ok true) :
    ∃ v, HasType Δ v E := by
  have hsub := annotateCore_leaves_sub F _ hann hw hb
  have hwA : Expr.WScoped 4 appliedA := annotateCore_WScoped F _ hann hw
  have hbA : appliedA.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F _ hann hb
  have hLA : Expr.LeavesBounded appliedA := fun l hl => hL l (hsub l hl)
  have hCA : CtxOk m.cval env φ 4 Δ appliedA := CtxOk.annotate hann hw hb hC
  obtain ⟨-, -, ihd, ihi⟩ := checkClaimsTT m φ F
  obtain ⟨v, tv, -, htv, hvT⟩ := ihi hinf hwA hbA hLA hCA
  have hleaf := inferTypeCore_fvarLeaves m.wf F hinf hwA
  have hdeq := ihd hde (inferTypeCore_WScoped m.wf F hinf hwA)
    (inferTypeCore_looseBVars m.wf F hinf hwA hbA hLA)
    (fun l hl => hLA l (hleaf l hl)) hwE hbE hLE
    ⟨hC.1, fun l hl => hCA.2 l (hleaf l hl)⟩ hCE htv hE
  exact ⟨v, HasType.conv hvT (hdeq.toHasType tv)⟩

/-! ## The frame

`CtxOk` fixes the context up to the *denotations of the checker's own
`fvar` annotations*, so the frame's context is forced: the two `Nat`
variables, then each hypothesis type denoted at the depth its binder
sits at.  Nothing here is a choice. -/

/-- The certificate frame's context, from the depth-`2` denotations of
the hypothesis types. -/
def dmCtx4 (natV H1 H2 : VExpr) : List VExpr :=
  [VExpr.liftN 1 H2 0, H1, natV, natV]

/-- Two fresh entries at the context head. -/
theorem HasType.weaken2 {Γ : List VExpr} {e A : VExpr} (X Y : VExpr)
    (h : HasType Γ e A) :
    HasType (X :: Y :: Γ) (VExpr.liftN 2 e 0) (VExpr.liftN 2 A 0) :=
  h.weakenN (.zero [X, Y] rfl)

section Frame

variable {env : Env} {m : EnvTT env} {φ : Name → Nat} {c : Name}
  {value' : Expr} {V : VExpr} {natV H1 H2 : VExpr}

/-- The frame's two `Nat` variables, typed. -/
theorem dmCtx4_x (hcl : VExpr.Closed natV) :
    HasType (dmCtx4 natV H1 H2) (.bvar (4 - 1 - 0)) natV := by
  have := HasType.bvar (Γ := dmCtx4 natV H1 H2) (i := 3) (A := natV)
    (by simp [dmCtx4])
  rwa [VExpr.liftN_eq_self_of_closed hcl _ 0] at this

theorem dmCtx4_y (hcl : VExpr.Closed natV) :
    HasType (dmCtx4 natV H1 H2) (.bvar (4 - 1 - 1)) natV := by
  have := HasType.bvar (Γ := dmCtx4 natV H1 H2) (i := 2) (A := natV)
    (by simp [dmCtx4])
  rwa [VExpr.liftN_eq_self_of_closed hcl _ 0] at this

theorem dmCtx4_h1 :
    HasType (dmCtx4 natV H1 H2) (.bvar (4 - 1 - 2)) (VExpr.liftN 2 H1 0) :=
  HasType.bvar (Γ := dmCtx4 natV H1 H2) (i := 1) (A := H1) (by simp [dmCtx4])

theorem dmCtx4_h2 :
    HasType (dmCtx4 natV H1 H2) (.bvar (4 - 1 - 3)) (VExpr.liftN 2 H2 0) := by
  have := HasType.bvar (Γ := dmCtx4 natV H1 H2) (i := 0)
    (A := VExpr.liftN 1 H2 0) (by simp [dmCtx4])
  rwa [VExpr.liftN_liftN_absorb H2 (Nat.le_refl 0) (Nat.zero_le _) 1] at this

/-- A fragment expression's depth-`4` denotation is its depth-`2` one,
two lifts up. -/
theorem denote4_of_denote2 {e : Expr} {W : VExpr}
    (hfb : Expr.fvarsBelow 2 e)
    (h : denote m.cval env φ 2 e = some W) :
    denote m.cval env φ 4 e = some (VExpr.liftN 2 W 0) := by
  have h3 : denote m.cval env φ 3 e = some (VExpr.liftN 1 W 0) := by
    rw [denote_weaken_top m.cval_closed hfb, h]; rfl
  rw [show (4 : Nat) = 3 + 1 from rfl,
    denote_weaken_top m.cval_closed (Expr.fvarsBelow_mono (by omega) hfb), h3]
  simp only [Option.map_some]
  rw [VExpr.liftN_liftN_absorb W (Nat.le_refl 0) (Nat.zero_le _) 1]

/-- The four frame conditions the claims ask for, at the certificate's
depth. -/
def Frames4 {env : Env} (m : EnvTT env) (φ : Name → Nat) (Δ : List VExpr)
    (e : Expr) : Prop :=
  Expr.WScoped 4 e ∧ e.looseBVarsBounded 0 = true ∧
  Expr.LeavesBounded e ∧ CtxOk m.cval env φ 4 Δ e

variable {Δ : List VExpr}

theorem Frames4.app {f a : Expr} (hf : Frames4 m φ Δ f)
    (ha : Frames4 m φ Δ a) : Frames4 m φ Δ (.app f a) := by
  refine ⟨by simp only [Expr.WScoped]; exact ⟨hf.1, ha.1⟩,
    by simp [Expr.looseBVarsBounded, hf.2.1, ha.2.1],
    ?_, CtxOk.app hf.2.2.2 ha.2.2.2⟩
  intro l hl
  rw [Expr.fvarLeaves] at hl
  rcases List.mem_append.mp hl with h' | h'
  · exact hf.2.2.1 l h'
  · exact ha.2.2.1 l h'

theorem Frames4.closed (hlen : Δ.length = 4) {e : Expr}
    (hcf : e.hasFvar = false) (hcb : e.looseBVarsBounded 0 = true) :
    Frames4 m φ Δ e :=
  ⟨Expr.WScoped.of_not_hasFvar hcf, hcb,
    Expr.LeavesBounded.of_not_hasFvar hcf,
    ⟨hlen, fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hcf] at hl
      exact nomatch hl⟩⟩

theorem Frames4.fvar (hlen : Δ.length = 4) {i : Nat} {n : Name} {ty : Expr}
    {T : VExpr} (hi : i < 4) (htyw : Expr.WScoped i ty)
    (hty : Frames4 m φ Δ ty) (hfb : Expr.fvarsBelow i ty)
    (hdT : denote m.cval env φ 4 ty = some T)
    (hT : HasType Δ (.bvar (4 - 1 - i)) T) :
    Frames4 m φ Δ (.fvar i n ty) := by
  refine ⟨by simp only [Expr.WScoped]; exact ⟨hi, htyw⟩, rfl, ?_,
    ⟨hlen, ?_⟩⟩
  · intro l hl
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact hty.2.1
    · exact hty.2.2.1 l hl'
  · intro l hl
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨hi, hfb, T, hdT, hT⟩
    · exact hty.2.2.2.2 l hl'

end Frame

/-! ## A clause, in the caller's context

The two extractions differ only in how many hypothesis binders the
frame carries.  Both end at `Deq.close4` / `Deq.close3`, whose
conclusion is `close2`'s: the proof binders leave no trace. -/

section Clause

variable {env : Env} {m : EnvTT env} {φ ψ : Name → Nat} {c : Name}
  {value' : Expr} {V : VExpr} {F : Nat} {ciN : ConstantInfo}

/-- **The guard's verdict, as an inhabitant.**  `Deq.toHasType` re-slots
the equation at whatever type the stored `Eq` law wants — no
unique-typing argument enters. -/
theorem hyp_inhabited (hEq : env.find? eqName = some eqA)
    {Γ : List VExpr} {B a b : VExpr}
    (hB : HasType Γ B (.sort (ψ uNT))) (ha : HasType Γ a B)
    (hb : HasType Γ b B) (h : Deq Γ a b) :
    HasType Γ .prf (VExpr.mkAppN (m.cval eqName ψ) [B, a, b]) :=
  HasType.conv (h.toHasType B)
    (((m.eq_law hEq ψ Γ B a b hB ha hb).symm).toHasType (.eqE B a b))

/-- The frame facts of a fragment statement, at both depths the frame
needs them. -/
theorem frag_frames (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false) (hvb : value'.looseBVarsBounded 0 = true)
    (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    {H1 H2 : VExpr} {e : Expr} (hfe : natFragOk env c e = true) :
    Expr.WScoped 2 (Expr.substConst0 c value' e) ∧
    Expr.fvarsBelow 2 (Expr.substConst0 c value' e) ∧
    Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (Expr.substConst0 c value' e) ∧
    ∃ w, denote m.cval env φ 2 (Expr.substConst0 c value' e) = some w := by
  have hxT : HasType [m.cval natName φ, m.cval natName φ]
      (.bvar (2 - 1 - 0)) (m.cval natName φ) := by
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 1) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  have hyT : HasType [m.cval natName φ, m.cval natName φ]
      (.bvar (2 - 1 - 1)) (m.cval natName φ) := by
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 0) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  obtain ⟨hw2, -, -, -, w, hd2⟩ :=
    natFrag_subst_facts m φ hvf hvb hv (Nat.le_refl 2) rfl hxT hyT hfN hlpN
      _ hfe
  obtain ⟨hw4, hb4, hL4, hC4, -⟩ :=
    natFrag_subst_facts m φ hvf hvb hv (by omega)
      (show (dmCtx4 (m.cval natName φ) H1 H2).length = 4 from rfl)
      (dmCtx4_x (m.cval_closed natName φ)) (dmCtx4_y (m.cval_closed natName φ))
      hfN hlpN _ hfe
  exact ⟨hw2, hw2.fvarsBelow, ⟨hw4, hb4, hL4, hC4⟩, w, hd2⟩

/-- The vendored proof is closed — the two guard conjuncts the frame
needs. -/
theorem certGuard_proof {hyps : List Expr} {eqE proof : Expr}
    (h : divModCertGuard env c value' hyps eqE proof = true) :
    (Expr.substConstAll c value' proof).hasFvar = false ∧
    (Expr.substConstAll c value' proof).looseBVarsBounded 0 = true := by
  unfold divModCertGuard at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.1.1⟩

/-- **A two-hypothesis clause, in the caller's context.** -/
theorem clause2T (m : EnvTT env) (φ : Name → Nat)
    (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false) (hvb : value'.looseBVarsBounded 0 = true)
    (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hEq : env.find? eqName = some eqA)
    {h1 h2 eqE proof : Expr}
    (hf1 : natFragOk env c h1 = true) (hf2 : natFragOk env c h2 = true)
    (hfE : natFragOk env c eqE = true)
    (hrun : CertRunFacts env F c value' ([h1, h2], eqE) proof)
    {H1 H2 A L R : VExpr}
    (hH1 : denote m.cval env φ 2 (Expr.substConst0 c value' h1) = some H1)
    (hH2 : denote m.cval env φ 2 (Expr.substConst0 c value' h2) = some H2)
    (hEE : denote m.cval env φ 2 (Expr.substConst0 c value' eqE)
      = some (VExpr.mkAppN (m.cval eqName ψ) [A, L, R]))
    (hAT : HasType [m.cval natName φ, m.cval natName φ] A (.sort (ψ uNT)))
    (hLT : HasType [m.cval natName φ, m.cval natName φ] L A)
    (hRT : HasType [m.cval natName φ, m.cval natName φ] R A)
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ))
    (hp1 : HasType Γ .prf ((H1.inst x 1).inst y))
    (hp2 : HasType Γ .prf ((H2.inst x 1).inst y)) :
    Deq Γ ((L.inst x 1).inst y) ((R.inst x 1).inst y) := by
  obtain ⟨hguard, appliedA, tp, hann, hinf, hde⟩ := hrun
  obtain ⟨hpf, hpb⟩ := certGuard_proof hguard
  obtain ⟨hw1_2, hfb1, hF1, -⟩ :=
    frag_frames (H1 := H1) (H2 := H2) hv hvf hvb hfN hlpN hf1
  obtain ⟨hw2_2, hfb2, hF2, -⟩ :=
    frag_frames (H1 := H1) (H2 := H2) hv hvf hvb hfN hlpN hf2
  obtain ⟨-, hfbE, hFE, -⟩ :=
    frag_frames (H1 := H1) (H2 := H2) hv hvf hvb hfN hlpN hfE
  have hN4 : denote m.cval env φ 4 (.const natName [])
      = some (m.cval natName φ) := denote_const_nolevels m φ hfN hlpN 4
  have hFnat : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (.const natName []) := Frames4.closed rfl rfl rfl
  have hFx : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (.fvar 0 (.str .anonymous "x") (.const natName [])) :=
    Frames4.fvar rfl (by omega) (by simp [Expr.WScoped]) hFnat trivial hN4
      (dmCtx4_x (m.cval_closed natName φ))
  have hFy : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (.fvar 1 (.str .anonymous "y") (.const natName [])) :=
    Frames4.fvar rfl (by omega) (by simp [Expr.WScoped]) hFnat trivial hN4
      (dmCtx4_y (m.cval_closed natName φ))
  have hFh1 : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (.fvar 2 (.str .anonymous "h1") (Expr.substConst0 c value' h1)) :=
    Frames4.fvar rfl (by omega) hw1_2 hF1 hfb1
      (denote4_of_denote2 hfb1 hH1) dmCtx4_h1
  have hFh2 : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (.fvar 3 (.str .anonymous "h2") (Expr.substConst0 c value' h2)) :=
    Frames4.fvar rfl (by omega) (Expr.WScoped.mono (by omega) hw2_2) hF2
      (Expr.fvarsBelow_mono (by omega) hfb2)
      (denote4_of_denote2 hfb2 hH2) dmCtx4_h2
  have hFA : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H2)
      (divModCertApplied (Expr.substConstAll c value' proof)
        ([h1, h2].map (Expr.substConst0 c value'))) :=
    ((((Frames4.closed rfl hpf hpb).app hFx).app hFy).app hFh1).app hFh2
  obtain ⟨v, hvT⟩ := cert_extractT m φ hFA.1 hFA.2.1 hFA.2.2.1 hFA.2.2.2
    hFE.1 hFE.2.1 hFE.2.2.1 hFE.2.2.2 (denote4_of_denote2 hfbE hEE)
    hann hinf hde
  -- the `Eq` spine, read as the layer's equation
  have hlaw := m.eq_law hEq ψ (dmCtx4 (m.cval natName φ) H1 H2)
    (VExpr.liftN 2 A 0) (VExpr.liftN 2 L 0) (VExpr.liftN 2 R 0)
    (HasType.weaken2 _ _ hAT) (HasType.weaken2 _ _ hLT)
    (HasType.weaken2 _ _ hRT)
  rw [show VExpr.mkAppN (m.cval eqName ψ)
        [VExpr.liftN 2 A 0, VExpr.liftN 2 L 0, VExpr.liftN 2 R 0]
      = VExpr.liftN 2 (VExpr.mkAppN (m.cval eqName ψ) [A, L, R]) 0 from by
    simp [VExpr.mkAppN,
      VExpr.liftN_eq_self_of_closed (m.cval_closed eqName ψ)]] at hlaw
  have hfin : HasType (dmCtx4 (m.cval natName φ) H1 H2) .prf
      (VExpr.liftN 2 (.eqE A L R) 0) :=
    (Deq.intro (HasType.conv hvT (hlaw.toHasType (VExpr.liftN 2 A 0)))).toHasType
      (VExpr.liftN 2 A 0)
  exact Deq.close4 (m.cval_closed natName φ) hfin hx hy hp1 hp2


/-- **A one-hypothesis clause.**  The checker runs it at depth `4` too,
so the frame is still four entries: the unused binder is given the used
hypothesis's type and inhabited by the same proof. -/
theorem clause1T (m : EnvTT env) (φ : Name → Nat)
    (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false) (hvb : value'.looseBVarsBounded 0 = true)
    (hfN : env.find? natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hEq : env.find? eqName = some eqA)
    {h1 eqE proof : Expr}
    (hf1 : natFragOk env c h1 = true) (hfE : natFragOk env c eqE = true)
    (hrun : CertRunFacts env F c value' ([h1], eqE) proof)
    {H1 A L R : VExpr}
    (hH1 : denote m.cval env φ 2 (Expr.substConst0 c value' h1) = some H1)
    (hEE : denote m.cval env φ 2 (Expr.substConst0 c value' eqE)
      = some (VExpr.mkAppN (m.cval eqName ψ) [A, L, R]))
    (hAT : HasType [m.cval natName φ, m.cval natName φ] A (.sort (ψ uNT)))
    (hLT : HasType [m.cval natName φ, m.cval natName φ] L A)
    (hRT : HasType [m.cval natName φ, m.cval natName φ] R A)
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ))
    (hp1 : HasType Γ .prf ((H1.inst x 1).inst y)) :
    Deq Γ ((L.inst x 1).inst y) ((R.inst x 1).inst y) := by
  obtain ⟨hguard, appliedA, tp, hann, hinf, hde⟩ := hrun
  obtain ⟨hpf, hpb⟩ := certGuard_proof hguard
  obtain ⟨hw1_2, hfb1, hF1, -⟩ :=
    frag_frames (H1 := H1) (H2 := H1) hv hvf hvb hfN hlpN hf1
  obtain ⟨-, hfbE, hFE, -⟩ :=
    frag_frames (H1 := H1) (H2 := H1) hv hvf hvb hfN hlpN hfE
  have hN4 : denote m.cval env φ 4 (.const natName [])
      = some (m.cval natName φ) := denote_const_nolevels m φ hfN hlpN 4
  have hFnat : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H1)
      (.const natName []) := Frames4.closed rfl rfl rfl
  have hFx : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H1)
      (.fvar 0 (.str .anonymous "x") (.const natName [])) :=
    Frames4.fvar rfl (by omega) (by simp [Expr.WScoped]) hFnat trivial hN4
      (dmCtx4_x (m.cval_closed natName φ))
  have hFy : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H1)
      (.fvar 1 (.str .anonymous "y") (.const natName [])) :=
    Frames4.fvar rfl (by omega) (by simp [Expr.WScoped]) hFnat trivial hN4
      (dmCtx4_y (m.cval_closed natName φ))
  have hFh1 : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H1)
      (.fvar 2 (.str .anonymous "h1") (Expr.substConst0 c value' h1)) :=
    Frames4.fvar rfl (by omega) hw1_2 hF1 hfb1
      (denote4_of_denote2 hfb1 hH1) dmCtx4_h1
  have hFA : Frames4 m φ (dmCtx4 (m.cval natName φ) H1 H1)
      (divModCertApplied (Expr.substConstAll c value' proof)
        ([h1].map (Expr.substConst0 c value'))) :=
    (((Frames4.closed rfl hpf hpb).app hFx).app hFy).app hFh1
  obtain ⟨v, hvT⟩ := cert_extractT m φ hFA.1 hFA.2.1 hFA.2.2.1 hFA.2.2.2
    hFE.1 hFE.2.1 hFE.2.2.1 hFE.2.2.2 (denote4_of_denote2 hfbE hEE)
    hann hinf hde
  have hlaw := m.eq_law hEq ψ (dmCtx4 (m.cval natName φ) H1 H1)
    (VExpr.liftN 2 A 0) (VExpr.liftN 2 L 0) (VExpr.liftN 2 R 0)
    (HasType.weaken2 _ _ hAT) (HasType.weaken2 _ _ hLT)
    (HasType.weaken2 _ _ hRT)
  rw [show VExpr.mkAppN (m.cval eqName ψ)
        [VExpr.liftN 2 A 0, VExpr.liftN 2 L 0, VExpr.liftN 2 R 0]
      = VExpr.liftN 2 (VExpr.mkAppN (m.cval eqName ψ) [A, L, R]) 0 from by
    simp [VExpr.mkAppN,
      VExpr.liftN_eq_self_of_closed (m.cval_closed eqName ψ)]] at hlaw
  have hfin : HasType (dmCtx4 (m.cval natName φ) H1 H1) .prf
      (VExpr.liftN 2 (.eqE A L R) 0) :=
    (Deq.intro (HasType.conv hvT (hlaw.toHasType (VExpr.liftN 2 A 0)))).toHasType
      (VExpr.liftN 2 A 0)
  exact Deq.close4 (m.cval_closed natName φ) hfin hx hy hp1 hp1

end Clause

end Setlec.TTVerify
