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

-- The clause assemblies rewrite with a fixed four-lemma instantiation
-- set; which of the four fires depends on the clause's shape, so some
-- are unused in some clauses.  Same practice as the basis installs.
set_option linter.unusedSimpArgs false

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


/-! ## Reading the guards

`divModEnvGuard` is checked in the *extended* environment; every
constant it pins is distinct from the operation being installed
(`natDivModNames_ne_env`), so each fact transfers down — except the
operation's own entry, which is the install's business and comes from
the declaration's own key. -/

/-- `natOpCod` reads the environment only at `boolName`. -/
theorem natOpCod_cons {env : Env} {ci : ConstantInfo}
    (hne : ci.name ≠ boolName) {n : Name} {e : Expr} :
    natOpCod ⟨ci :: env.consts⟩ n e = natOpCod env n e := by
  unfold natOpCod
  split
  · rw [Env.find?_cons, if_neg hne]
  · rfl

theorem natOpTyPinned_cons {env : Env} {ci : ConstantInfo}
    (hne : ci.name ≠ boolName) {n : Name} {ty : Expr} :
    natOpTyPinned ⟨ci :: env.consts⟩ n ty = natOpTyPinned env n ty := by
  unfold natOpTyPinned
  split <;> split <;> simp [natOpCod_cons hne]

theorem natOpStoredOk_cons {env : Env} {ci : ConstantInfo} {n : Name}
    (hneB : ci.name ≠ boolName) (hne : ci.name ≠ n)
    (h : natOpStoredOk ⟨ci :: env.consts⟩ n = true) :
    natOpStoredOk env n = true := by
  unfold natOpStoredOk at h ⊢
  rw [Env.find?_cons, if_neg hne] at h
  simpa only [natOpTyPinned_cons hneB] using h

/-- A stored constant's find?, from `storedNoLevels`. -/
theorem storedNoLevels_find {env : Env} {n : Name}
    (h : storedNoLevels env n) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] :=
  storedNoLevels_exists h

/-! ## Spines

Every side of every clause is a spine over the pinned constants, and
each needs three things at once: membership of the fragment, its
denotation, and its typing.  One inductive carries all three, so a
clause's obligations are discharged by *building the spine* rather than
by three separate walks. -/

/-- A spine over pinned constants: `e` denotes to `W`, which is typed
by `A` in the frame. -/
inductive DMSpine {env : Env} (m : EnvTT env) (φ : Name → Nat) (c : Name)
    (value' : Expr) : Expr → VExpr → VExpr → Prop
  | fvar0 (n : Name) :
      DMSpine m φ c value' (.fvar 0 n (.const natName []))
        (.bvar 1) (m.cval natName φ)
  | fvar1 (n : Name) :
      DMSpine m φ c value' (.fvar 1 n (.const natName []))
        (.bvar 0) (m.cval natName φ)
  | const {n : Name} {A : VExpr} (hfrag : natFragOk env c (.const n []) = true)
      (hd : DMDen m c value' φ n)
      (hT : ∀ Δ : List VExpr, HasType Δ (cvalAt m.cval env c value' n φ) A) :
      DMSpine m φ c value' (.const n [])
        (cvalAt m.cval env c value' n φ) A
  | app {f a : Expr} {F Wa A B : VExpr} (hB : VExpr.Closed B)
      (hf : DMSpine m φ c value' f F (.pi A B))
      (ha : DMSpine m φ c value' a Wa A) :
      DMSpine m φ c value' (.app f a) (.app F Wa) B

section Spine

variable {env : Env} {m : EnvTT env} {φ : Name → Nat} {c : Name}
  {value' : Expr}

/-- **A spine, eliminated.**  Fragment membership, denotation and
typing, from the one derivation. -/
theorem DMSpine.sound {e : Expr} {W A : VExpr}
    (h : DMSpine m φ c value' e W A) :
    natFragOk env c e = true ∧
    denote m.cval env φ 2 (Expr.substConst0 c value' e) = some W ∧
    HasType [m.cval natName φ, m.cval natName φ] W A := by
  induction h with
  | fvar0 n =>
    refine ⟨by simp [natFragOk], by
      rw [show Expr.substConst0 c value' (Expr.fvar 0 n (.const natName []))
        = Expr.fvar 0 n (.const natName []) from rfl, denote_fvar], ?_⟩
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 1) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  | fvar1 n =>
    refine ⟨by simp [natFragOk], by
      rw [show Expr.substConst0 c value' (Expr.fvar 1 n (.const natName []))
        = Expr.fvar 1 n (.const natName []) from rfl, denote_fvar], ?_⟩
    have := HasType.bvar (Γ := [m.cval natName φ, m.cval natName φ])
      (i := 0) (A := m.cval natName φ) (by simp)
    rwa [VExpr.liftN_eq_self_of_closed (m.cval_closed natName φ) _ 0] at this
  | const hfrag hd hT => exact ⟨hfrag, hd 2, hT _⟩
  | app hB _ _ ihf iha =>
    obtain ⟨hff, hdf, hTf⟩ := ihf
    obtain ⟨hfa, hda, hTa⟩ := iha
    refine ⟨by simp [natFragOk, hff, hfa], ?_, ?_⟩
    · rw [show Expr.substConst0 c value' (.app _ _)
        = .app (Expr.substConst0 c value' _) (Expr.substConst0 c value' _)
        from rfl, denote_app, hdf, hda]
    · have := HasType.app hTf hTa
      rwa [VExpr.inst_eq_self_of_closed hB] at this

/-- The constants the certificate statements are built from, as spines
— read off the guards once and consumed by all nine assemblies.

The list is `natOpDeps c` plus the two `Nat` constructors, the two
`Bool` constructors and the pinned equality, which is exactly what
`divModEnvGuard` checks.  **The guard's list and the assemblies' list
are the same list**, the div/mod repeat of the `natOpEquations`
alignment. -/
structure DMBase {env : Env} (m : EnvTT env) (φ : Name → Nat) (c : Name)
    (value' : Expr) : Prop where
  /-- A binary pinned operation. -/
  op2 : ∀ n ∈ c :: natOpDeps c,
    ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true) →
    DMSpine m φ c value' (.const n []) (cvalAt m.cval env c value' n φ)
      (.pi (m.cval natName φ) (.pi (m.cval natName φ) (dmCodV m φ n)))
  /-- A unary pinned operation (`pred`, `log2`). -/
  op1 : ∀ n ∈ c :: natOpDeps c,
    (decide (n = natPredName) || decide (n = natLog2Name)) = true →
    DMSpine m φ c value' (.const n []) (cvalAt m.cval env c value' n φ)
      (.pi (m.cval natName φ) (dmCodV m φ n))
  /-- `Nat.zero`. -/
  zero : DMSpine m φ c value' (.const natZeroName [])
    (cvalAt m.cval env c value' natZeroName φ) (m.cval natName φ)
  /-- `Nat.succ`. -/
  succ : DMSpine m φ c value' (.const natSuccName [])
    (cvalAt m.cval env c value' natSuccName φ)
    (.pi (m.cval natName φ) (m.cval natName φ))
  /-- `Bool.true`. -/
  btrue : DMSpine m φ c value' (.const boolTrueName [])
    (cvalAt m.cval env c value' boolTrueName φ) (m.cval boolName φ)
  /-- `Bool.false`. -/
  bfalse : DMSpine m φ c value' (.const boolFalseName [])
    (cvalAt m.cval env c value' boolFalseName φ) (m.cval boolName φ)
  /-- `Nat` as a type. -/
  natTy : DMSpine m φ c value' (.const natName []) (m.cval natName φ) (.sort 1)
  /-- `Bool` as a type. -/
  boolTy : DMSpine m φ c value' (.const boolName []) (m.cval boolName φ)
    (.sort 1)
  /-- The pinned equality is stored, so its spines denote. -/
  eqStored : env.find? eqName = some eqA
  /-- The stored value denotes, and is closed. -/
  val : ∃ V, denoteClosed m.cval env φ value' = some V
  valFvar : value'.hasFvar = false
  valBnd : value'.looseBVarsBounded 0 = true
  /-- `Nat` is stored level-monomorphically. -/
  natStored : ∃ ci, env.find? natName = some ci ∧
    ci.toConstantVal.levelParams = []

section Assembly

variable {env : Env} {m : EnvTT env} {φ : Name → Nat} {c : Name}
  {value' : Expr}

/-- The level assignment the certificate statements read `Eq` at. -/
def psiEq1 (φ : Name → Nat) : Name → Nat :=
  Level.substFn φ eqA.toConstantVal.levelParams [.succ .zero]

theorem psiEq1_uNT (φ : Name → Nat) : psiEq1 φ uNT = 1 := rfl

/-- A pinned-equality statement: its fragment membership and its
denotation, from the three spines it is built from. -/
theorem dmEqStmt (hb : DMBase m φ c value')
    {tyE lhs rhs : Expr} {TA L R : VExpr}
    (hA : DMSpine m φ c value' tyE TA (.sort 1))
    (hL : DMSpine m φ c value' lhs L TA)
    (hR : DMSpine m φ c value' rhs R TA) :
    natFragOk env c
      (.app (.app (.app (.const eqName [.succ .zero]) tyE) lhs) rhs) = true ∧
    denote m.cval env φ 2 (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero]) tyE) lhs) rhs))
      = some (VExpr.mkAppN (m.cval eqName (psiEq1 φ)) [TA, L, R]) := by
  obtain ⟨hfA, hdA, -⟩ := hA.sound
  obtain ⟨hfL, hdL, -⟩ := hL.sound
  obtain ⟨hfR, hdR, -⟩ := hR.sound
  have hfEq : natFragOk env c (.const eqName [.succ .zero]) = true := by
    simp only [natFragOk, Bool.or_eq_true]
    exact Or.inr (by rw [hb.eqStored]; simp [eqA, ConstantInfo.toConstantVal])
  have hdEq : denote m.cval env φ 2
      (Expr.substConst0 c value' (.const eqName [.succ .zero]))
      = some (m.cval eqName (psiEq1 φ)) := by
    rw [show Expr.substConst0 c value' (.const eqName [.succ .zero])
      = .const eqName [.succ .zero] from by
        rw [Expr.substConst0, if_neg (fun hh => nomatch hh.2)]]
    rw [denote_const, hb.eqStored]
    exact if_pos rfl
  refine ⟨by
    simp only [natFragOk, Bool.and_eq_true]
    exact ⟨⟨⟨hfEq, hfA⟩, hfL⟩, hfR⟩, ?_⟩
  rw [show Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero]) tyE) lhs) rhs)
    = .app (.app (.app (Expr.substConst0 c value' (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' tyE)) (Expr.substConst0 c value' lhs))
        (Expr.substConst0 c value' rhs) from rfl]
  rw [denote_app, denote_app, denote_app, hdEq, hdA, hdL, hdR]
  rfl



/-! ### Spine builders -/

theorem dmCodV_closed (m : EnvTT env) (φ : Name → Nat) (n : Name) :
    VExpr.Closed (dmCodV m φ n) := by
  unfold dmCodV; split <;> exact m.cval_closed _ φ

theorem dmCodV_nat {n : Name} (h : ¬ (n = natBeqName ∨ n = natBleName)) :
    dmCodV m φ n = m.cval natName φ := by rw [dmCodV, if_neg h]

theorem dmCodV_bool {n : Name} (h : n = natBeqName ∨ n = natBleName) :
    dmCodV m φ n = m.cval boolName φ := by rw [dmCodV, if_pos h]

theorem dmSucc (hb : DMBase m φ c value') {a : Expr} {A : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.const natSuccName []) a)
      (.app (cvalAt m.cval env c value' natSuccName φ) A)
      (m.cval natName φ) :=
  DMSpine.app (m.cval_closed natName φ) hb.succ ha

theorem dmOp2 (hb : DMBase m φ c value') {n : Name} (hn : n ∈ c :: natOpDeps c)
    (hnot : ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true))
    {a b : Expr} {A B : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ))
    (hbb : DMSpine m φ c value' b B (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.app (.const n []) a) b)
      (.app (.app (cvalAt m.cval env c value' n φ) A) B) (dmCodV m φ n) :=
  DMSpine.app (dmCodV_closed m φ n)
    (DMSpine.app ⟨m.cval_closed natName φ,
      VExpr.bvarsBelow.mono (by omega) (dmCodV_closed m φ n)⟩
      (hb.op2 n hn hnot) ha) hbb

theorem dmOp1 (hb : DMBase m φ c value') {n : Name} (hn : n ∈ c :: natOpDeps c)
    (hyes : (decide (n = natPredName) || decide (n = natLog2Name)) = true)
    {a : Expr} {A : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.const n []) a)
      (.app (cvalAt m.cval env c value' n φ) A) (dmCodV m φ n) :=
  DMSpine.app (dmCodV_closed m φ n) (hb.op1 n hn hyes) ha


/-- A binary `Nat`-valued pinned operation, as a spine. -/
theorem dmN (m : EnvTT env) (hb : DMBase m φ c value') (n : Name)
    (hn : n ∈ c :: natOpDeps c)
    (h1 : ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true))
    (h2 : ¬ (n = natBeqName ∨ n = natBleName))
    {a b : Expr} {A B : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ))
    (hbb : DMSpine m φ c value' b B (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.app (.const n []) a) b)
      (.app (.app (cvalAt m.cval env c value' n φ) A) B) (m.cval natName φ) :=
  dmCodV_nat h2 ▸ dmOp2 hb hn h1 ha hbb

/-- The `Bool`-valued comparison `Nat.ble`, as a spine. -/
theorem dmB (m : EnvTT env) (hb : DMBase m φ c value') (n : Name)
    (hn : n ∈ c :: natOpDeps c)
    (h1 : ¬ ((decide (n = natPredName) || decide (n = natLog2Name)) = true))
    (h2 : n = natBeqName ∨ n = natBleName)
    {a b : Expr} {A B : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ))
    (hbb : DMSpine m φ c value' b B (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.app (.const n []) a) b)
      (.app (.app (cvalAt m.cval env c value' n φ) A) B) (m.cval boolName φ) :=
  dmCodV_bool h2 ▸ dmOp2 hb hn h1 ha hbb

/-- A unary pinned operation (`Nat.log2`), as a spine. -/
theorem dmU (m : EnvTT env) (hb : DMBase m φ c value') (n : Name)
    (hn : n ∈ c :: natOpDeps c)
    (h1 : (decide (n = natPredName) || decide (n = natLog2Name)) = true)
    (h2 : ¬ (n = natBeqName ∨ n = natBleName))
    {a : Expr} {A : VExpr}
    (ha : DMSpine m φ c value' a A (m.cval natName φ)) :
    DMSpine m φ c value' (.app (.const n []) a)
      (.app (cvalAt m.cval env c value' n φ) A) (m.cval natName φ) :=
  dmCodV_nat h2 ▸ dmOp1 hb hn h1 ha

/-! ### The two-variable instantiation, computed -/

theorem inst2_app (f a x y : VExpr) :
    ((VExpr.app f a).inst x 1).inst y
      = .app ((f.inst x 1).inst y) ((a.inst x 1).inst y) := rfl

theorem inst2_closed {e : VExpr} (h : VExpr.Closed e) (x y : VExpr) :
    (e.inst x 1).inst y = e := by
  rw [VExpr.inst_eq_self_of_closed h, VExpr.inst_eq_self_of_closed h]

theorem inst2_bvar1 (x y : VExpr) : ((VExpr.bvar 1).inst x 1).inst y = x := by
  rw [show ((VExpr.bvar 1).inst x 1) = VExpr.liftN 1 x 0 from by
    simp [VExpr.inst]]
  rw [VExpr.inst_liftN_absorb x (Nat.le_refl 0) (Nat.le_refl 0) y,
    VExpr.liftN_zero]

theorem inst2_bvar0 (x y : VExpr) : ((VExpr.bvar 0).inst x 1).inst y = y := by
  rw [show ((VExpr.bvar 0).inst x 1) = VExpr.bvar 0 from by simp [VExpr.inst]]
  simp [VExpr.inst, VExpr.liftN_zero]

theorem inst2_mkAppN3 {f A L R : VExpr} (hf : VExpr.Closed f) (x y : VExpr) :
    ((VExpr.mkAppN f [A, L, R]).inst x 1).inst y
      = VExpr.mkAppN f [(A.inst x 1).inst y, (L.inst x 1).inst y,
        (R.inst x 1).inst y] := by
  simp only [VExpr.mkAppN, inst2_app, inst2_closed hf]


/-- The install's valuation is closed at every name. -/
theorem cvalAt_closed (m : EnvTT env) {φ : Name → Nat} {c : Name}
    {value' : Expr} (hb : DMBase m φ c value') (n : Name) :
    VExpr.Closed (cvalAt m.cval env c value' n φ) := by
  obtain ⟨V, hv⟩ := hb.val
  unfold cvalAt
  split
  · simp only [hv, Option.getD_some]
    exact denote_closed m.cval_closed hb.valFvar hb.valBnd hv
  · exact m.cval_closed _ φ

theorem inst2_cvalAt (m : EnvTT env) {φ : Name → Nat} {c : Name}
    {value' : Expr} (hb : DMBase m φ c value') (n : Name) (x y : VExpr) :
    ((cvalAt m.cval env c value' n φ).inst x 1).inst y
      = cvalAt m.cval env c value' n φ :=
  inst2_closed (cvalAt_closed m hb n) x y

/-! ### The clause drivers

One per hypothesis count.  Everything specific to an operation is in
the spines handed in; the driver is the same walk for all nine. -/

/-- **A one-guard clause of `DivModClausesTT`.** -/
theorem dmClause1 (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ c value')
    {gl gr lhs rhs proof : Expr} {GL GR L R : VExpr}
    (hgl : DMSpine m φ c value' gl GL (m.cval boolName φ))
    (hgr : DMSpine m φ c value' gr GR (m.cval boolName φ))
    (hL : DMSpine m φ c value' lhs L (m.cval natName φ))
    (hR : DMSpine m φ c value' rhs R (m.cval natName φ))
    (hrun : CertRunFacts env F c value'
      ([.app (.app (.app (.const eqName [.succ .zero]) (.const boolName []))
          gl) gr],
        .app (.app (.app (.const eqName [.succ .zero]) (.const natName []))
          lhs) rhs) proof)
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ))
    (hguard : Deq Γ ((GL.inst x 1).inst y) ((GR.inst x 1).inst y)) :
    Deq Γ ((L.inst x 1).inst y) ((R.inst x 1).inst y) := by
  obtain ⟨V, hv⟩ := hb.val
  obtain ⟨ciN, hfN, hlpN⟩ := hb.natStored
  have hvf := hb.valFvar
  have hvb := hb.valBnd
  obtain ⟨hf1, hd1⟩ := dmEqStmt hb hb.boolTy hgl hgr
  obtain ⟨hfE, hdE⟩ := dmEqStmt hb hb.natTy hL hR
  have hBool : HasType Γ (m.cval boolName φ) (.sort (psiEq1 φ uNT)) := by
    have := HasType.close2 (m.cval_closed natName φ) (by trivial)
      hb.boolTy.sound.2.2 hx hy
    rwa [inst2_closed (m.cval_closed boolName φ)] at this
  have hp1 : HasType Γ .prf
      ((VExpr.mkAppN (m.cval eqName (psiEq1 φ)) [m.cval boolName φ, GL, GR]).inst
        x 1 |>.inst y) := by
    rw [inst2_mkAppN3 (m.cval_closed eqName (psiEq1 φ)),
      inst2_closed (m.cval_closed boolName φ)]
    exact hyp_inhabited hb.eqStored hBool
      (HasType.close2 (m.cval_closed natName φ) (m.cval_closed boolName φ)
        hgl.sound.2.2 hx hy)
      (HasType.close2 (m.cval_closed natName φ) (m.cval_closed boolName φ)
        hgr.sound.2.2 hx hy) hguard
  exact clause1T m φ hv hvf hvb hfN hlpN hb.eqStored hf1 hfE hrun hd1 hdE
    hb.natTy.sound.2.2 hL.sound.2.2 hR.sound.2.2 hx hy hp1

/-- **A two-guard clause of `DivModClausesTT`** — only `Nat.div` and
`Nat.mod` have one. -/
theorem dmClause2 (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ c value')
    {gl gr gl2 gr2 lhs rhs proof : Expr} {GL GR GL2 GR2 L R : VExpr}
    (hgl : DMSpine m φ c value' gl GL (m.cval boolName φ))
    (hgr : DMSpine m φ c value' gr GR (m.cval boolName φ))
    (hgl2 : DMSpine m φ c value' gl2 GL2 (m.cval boolName φ))
    (hgr2 : DMSpine m φ c value' gr2 GR2 (m.cval boolName φ))
    (hL : DMSpine m φ c value' lhs L (m.cval natName φ))
    (hR : DMSpine m φ c value' rhs R (m.cval natName φ))
    (hrun : CertRunFacts env F c value'
      ([.app (.app (.app (.const eqName [.succ .zero]) (.const boolName []))
          gl) gr,
        .app (.app (.app (.const eqName [.succ .zero]) (.const boolName []))
          gl2) gr2],
        .app (.app (.app (.const eqName [.succ .zero]) (.const natName []))
          lhs) rhs) proof)
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ))
    (hguard : Deq Γ ((GL.inst x 1).inst y) ((GR.inst x 1).inst y))
    (hguard2 : Deq Γ ((GL2.inst x 1).inst y) ((GR2.inst x 1).inst y)) :
    Deq Γ ((L.inst x 1).inst y) ((R.inst x 1).inst y) := by
  obtain ⟨V, hv⟩ := hb.val
  obtain ⟨ciN, hfN, hlpN⟩ := hb.natStored
  have hvf := hb.valFvar
  have hvb := hb.valBnd
  obtain ⟨hf1, hd1⟩ := dmEqStmt hb hb.boolTy hgl hgr
  obtain ⟨hf2, hd2⟩ := dmEqStmt hb hb.boolTy hgl2 hgr2
  obtain ⟨hfE, hdE⟩ := dmEqStmt hb hb.natTy hL hR
  have hBool : HasType Γ (m.cval boolName φ) (.sort (psiEq1 φ uNT)) := by
    have := HasType.close2 (m.cval_closed natName φ) (by trivial)
      hb.boolTy.sound.2.2 hx hy
    rwa [inst2_closed (m.cval_closed boolName φ)] at this
  have mk : ∀ {gL gR : VExpr},
      HasType [m.cval natName φ, m.cval natName φ] gL (m.cval boolName φ) →
      HasType [m.cval natName φ, m.cval natName φ] gR (m.cval boolName φ) →
      Deq Γ ((gL.inst x 1).inst y) ((gR.inst x 1).inst y) →
      HasType Γ .prf
        ((VExpr.mkAppN (m.cval eqName (psiEq1 φ))
          [m.cval boolName φ, gL, gR]).inst x 1 |>.inst y) := by
    intro gL gR hgL hgR hg
    rw [inst2_mkAppN3 (m.cval_closed eqName (psiEq1 φ)),
      inst2_closed (m.cval_closed boolName φ)]
    exact hyp_inhabited hb.eqStored hBool
      (HasType.close2 (m.cval_closed natName φ) (m.cval_closed boolName φ)
        hgL hx hy)
      (HasType.close2 (m.cval_closed natName φ) (m.cval_closed boolName φ)
        hgR hx hy) hg
  exact clause2T m φ hv hvf hvb hfN hlpN hb.eqStored hf1 hf2 hfE hrun hd1 hd2
    hdE hb.natTy.sound.2.2 hL.sound.2.2 hR.sound.2.2 hx hy
    (mk hgl.sound.2.2 hgr.sound.2.2 hguard)
    (mk hgl2.sound.2.2 hgr2.sound.2.2 hguard2)


/-! ### The nine operations

Each assembly is: build the spines its statements are made of, split
the certificate run, and hand both to a driver.  Nothing else. -/

/-- `natGcd`. -/
theorem dmGcd (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natGcdName value')
    (hruns : CertRuns (CertRunFacts env F natGcdName value')
      (divModCertStmts natGcdName) (divModCertProofs natGcdName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natGcdName value') natGcdName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natGcdName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natGcdName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.btrue (dmN m hb natGcdName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natGcdName (by decide) (by decide) (by decide) (dmN m hb natModName (by decide) (by decide) (by decide) (sy) (sx)) (sx)) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.bfalse (dmN m hb natGcdName (by decide) (by decide) (by decide) (sx) (sy)) (sy) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natShiftLeft`. -/
theorem dmShl (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natShiftLeftName value')
    (hruns : CertRuns (CertRunFacts env F natShiftLeftName value')
      (divModCertStmts natShiftLeftName) (divModCertProofs natShiftLeftName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natShiftLeftName value') natShiftLeftName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natShiftLeftName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natShiftLeftName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.btrue (dmN m hb natShiftLeftName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natShiftLeftName (by decide) (by decide) (by decide) (dmN m hb natMulName (by decide) (by decide) (by decide) (s2) (sx)) (dmN m hb natSubName (by decide) (by decide) (by decide) (sy) (s1))) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.bfalse (dmN m hb natShiftLeftName (by decide) (by decide) (by decide) (sx) (sy)) (sx) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natShiftRight`. -/
theorem dmShr (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natShiftRightName value')
    (hruns : CertRuns (CertRunFacts env F natShiftRightName value')
      (divModCertStmts natShiftRightName) (divModCertProofs natShiftRightName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natShiftRightName value') natShiftRightName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natShiftRightName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natShiftRightName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.btrue (dmN m hb natShiftRightName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natDivName (by decide) (by decide) (by decide) (dmN m hb natShiftRightName (by decide) (by decide) (by decide) (sx) (dmN m hb natSubName (by decide) (by decide) (by decide) (sy) (s1))) (s2)) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.bfalse (dmN m hb natShiftRightName (by decide) (by decide) (by decide) (sx) (sy)) (sx) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natLog2`. -/
theorem dmLog2 (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natLog2Name value')
    (hruns : CertRuns (CertRunFacts env F natLog2Name value')
      (divModCertStmts natLog2Name) (divModCertProofs natLog2Name))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natLog2Name value') natLog2Name φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natLog2Name)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natLog2Name)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s2) (sx)) hb.btrue (dmU m hb natLog2Name (by decide) (by decide) (by decide) (sx)) (dmSucc hb (dmU m hb natLog2Name (by decide) (by decide) (by decide) (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (s2)))) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s2) (sx)) hb.bfalse (dmU m hb natLog2Name (by decide) (by decide) (by decide) (sx)) (hb.zero) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natLand`. -/
theorem dmLand (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natLandName value')
    (hruns : CertRuns (CertRunFacts env F natLandName value')
      (divModCertStmts natLandName) (divModCertProofs natLandName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natLandName value') natLandName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natLandName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natLandName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.btrue (dmN m hb natLandName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natAddName (by decide) (by decide) (by decide) (dmN m hb natMulName (by decide) (by decide) (by decide) (s2) (dmN m hb natLandName (by decide) (by decide) (by decide) (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natDivName (by decide) (by decide) (by decide) (sy) (s2)))) (dmN m hb natMulName (by decide) (by decide) (by decide) (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natModName (by decide) (by decide) (by decide) (sy) (s2)))) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.bfalse (dmN m hb natLandName (by decide) (by decide) (by decide) (sx) (sy)) (hb.zero) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natLor`. -/
theorem dmLor (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natLorName value')
    (hruns : CertRuns (CertRunFacts env F natLorName value')
      (divModCertStmts natLorName) (divModCertProofs natLorName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natLorName value') natLorName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natLorName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natLorName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.btrue (dmN m hb natLorName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natAddName (by decide) (by decide) (by decide) (dmN m hb natMulName (by decide) (by decide) (by decide) (s2) (dmN m hb natLorName (by decide) (by decide) (by decide) (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natDivName (by decide) (by decide) (by decide) (sy) (s2)))) (dmN m hb natSubName (by decide) (by decide) (by decide) (dmN m hb natAddName (by decide) (by decide) (by decide) (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natModName (by decide) (by decide) (by decide) (sy) (s2))) (dmN m hb natMulName (by decide) (by decide) (by decide) (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natModName (by decide) (by decide) (by decide) (sy) (s2))))) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.bfalse (dmN m hb natLorName (by decide) (by decide) (by decide) (sx) (sy)) (sy) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natXor`. -/
theorem dmXor (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natXorName value')
    (hruns : CertRuns (CertRunFacts env F natXorName value')
      (divModCertStmts natXorName) (divModCertProofs natXorName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natXorName value') natXorName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natXorName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natXorName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  refine ⟨?_, ?_⟩
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.btrue (dmN m hb natXorName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natAddName (by decide) (by decide) (by decide) (dmN m hb natMulName (by decide) (by decide) (by decide) (s2) (dmN m hb natXorName (by decide) (by decide) (by decide) (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natDivName (by decide) (by decide) (by decide) (sy) (s2)))) (dmN m hb natModName (by decide) (by decide) (by decide) (dmN m hb natAddName (by decide) (by decide) (by decide) (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (s2)) (dmN m hb natModName (by decide) (by decide) (by decide) (sy) (s2))) (s2))) hr1 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sx)) hb.bfalse (dmN m hb natXorName (by decide) (by decide) (by decide) (sx) (sy)) (sy) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natDiv`. -/
theorem dmDiv (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natDivName value')
    (hruns : CertRuns (CertRunFacts env F natDivName value')
      (divModCertStmts natDivName) (divModCertProofs natDivName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natDivName value') natDivName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natDivName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natDivName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  cases hruns with
  | cons hr3 hruns =>
  refine ⟨?_, ?_, ?_⟩
  · intro hg hg2
    have := dmClause2 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (sy) (sx)) hb.btrue (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.btrue (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (sy)) (dmSucc hb (dmN m hb natDivName (by decide) (by decide) (by decide) (dmN m hb natSubName (by decide) (by decide) (by decide) (sx) (sy)) (sy))) hr1
      hx hy (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg) (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg2)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (sy) (sx)) hb.bfalse (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (sy)) (hb.zero) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.bfalse (dmN m hb natDivName (by decide) (by decide) (by decide) (sx) (sy)) (hb.zero) hr3 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb,
      reduceIte] using this

/-- `natMod`. -/
theorem dmMod (m : EnvTT env) (φ : Name → Nat) {F : Nat}
    (hb : DMBase m φ natModName value')
    (hruns : CertRuns (CertRunFacts env F natModName value')
      (divModCertStmts natModName) (divModCertProofs natModName))
    {Γ : List VExpr} {x y : VExpr}
    (hx : HasType Γ x (m.cval natName φ))
    (hy : HasType Γ y (m.cval natName φ)) :
    DivModClausesTT (cvalAt m.cval env natModName value') natModName φ Γ x y := by
  have sx := DMSpine.fvar0 (m := m) (φ := φ) (c := natModName)
    (value' := value') (.str .anonymous "x")
  have sy := DMSpine.fvar1 (m := m) (φ := φ) (c := natModName)
    (value' := value') (.str .anonymous "y")
  have s1 := dmSucc hb hb.zero
  have s2 := dmSucc hb s1
  cases hruns with
  | cons hr1 hruns =>
  cases hruns with
  | cons hr2 hruns =>
  cases hruns with
  | cons hr3 hruns =>
  refine ⟨?_, ?_, ?_⟩
  · intro hg hg2
    have := dmClause2 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (sy) (sx)) hb.btrue (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.btrue (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (sy)) (dmN m hb natModName (by decide) (by decide) (by decide) (dmN m hb natSubName (by decide) (by decide) (by decide) (sx) (sy)) (sy)) hr1
      hx hy (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg) (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg2)
    rw [if_neg (by decide : ¬ (natModName = natDivName))]
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (sy) (sx)) hb.bfalse (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (sy)) (sx) hr2 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    rw [if_neg (by decide : ¬ (natModName = natDivName))]
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb] using this
  · intro hg
    have := dmClause1 m φ hb (dmB m hb natBleName (by decide) (by decide) (by decide) (s1) (sy)) hb.bfalse (dmN m hb natModName (by decide) (by decide) (by decide) (sx) (sy)) (sx) hr3 hx hy
      (by simp only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb]; exact hg)
    rw [if_neg (by decide : ¬ (natModName = natDivName))]
    simpa only [inst2_app, inst2_bvar1, inst2_bvar0, inst2_cvalAt m hb] using this


/-! ## `DMBase`, from the install's guards -/

/-- A stored constant other than the operation, as a spine. -/
theorem dmConstOther (m : EnvTT env) {n : Name} {ci : ConstantInfo} {A : VExpr}
    (hne : n ≠ c) (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = [])
    (hty : denoteClosed m.cval env φ ci.toConstantVal.type = some A) :
    DMSpine m φ c value' (.const n []) (cvalAt m.cval env c value' n φ) A :=
  DMSpine.const
    (natFragOk_const (by unfold storedNoLevels; rw [hf]; simp [hlp]))
    (DMDen.other hne hf hlp)
    (fun Δ => by rw [cvalAt_ne hne]; exact cval_hasType m hf φ hty)

/-- The operation itself, as a spine — typed by its own declaration
key rather than by the environment, since it is not stored yet. -/
theorem dmConstSelf (m : EnvTT env) {V A : VExpr}
    (hv : denoteClosed m.cval env φ value' = some V)
    (hvf : value'.hasFvar = false) (hvb : value'.looseBVarsBounded 0 = true)
    (hVA : HasType [] V A) :
    DMSpine m φ c value' (.const c []) (cvalAt m.cval env c value' c φ) A :=
  DMSpine.const natFragOk_self (DMDen.self hv hvf hvb)
    (fun Δ => by rw [cvalAt_self hv]; exact HasType.weakenNil hVA Δ)

/-- Build the spine base from the pinned environment guard, the
declaration's own key, and freshness. -/
theorem dmBase_of_guard {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {cv : ConstantVal} {value' : Expr} {hint : ReducibilityHint} {V T : VExpr}
    (hc : cv.name ∈ natDivModNames)
    (hvf : value'.hasFvar = false) (hvb : value'.looseBVarsBounded 0 = true)
    (hv : denoteClosed m.cval env φ value' = some V)
    (hTd : denoteClosed m.cval env φ cv.type = some T)
    (hVT : HasType [] V T)
    (hguard : divModEnvGuard ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩
      cv.name = true) :
    DMBase m φ cv.name value' := by
  obtain ⟨hcN, hcZ, hcS, hcB, hcBT, hcBF, hcEq, hcBle, -, -, -⟩ :=
    natDivModNames_ne_env hc
  obtain ⟨hng, hdeps, hEq2, hbT2, hbF2⟩ := divModEnvGuard_inv hguard
  have fdown : ∀ {n : Name} {cj : ConstantInfo}, cv.name ≠ n →
      Env.find? ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ n = some cj →
      env.find? n = some cj := by
    intro n cj hne h
    rwa [Env.find?_cons,
      if_neg (show ¬ (ConstantInfo.name (.defnInfo cv value' hint) = n) from
        hne)] at h
  -- `Nat`, `Nat.zero`, `Nat.succ`
  obtain ⟨ciN, hfN2, hlpN, htyN⟩ := natOpGuard_natTy hng
  obtain ⟨ciZ, hfZ2, hlpZ, htyZ⟩ := natOpGuard_zeroTy hng
  obtain ⟨ciS, nmS, mbS, hfS2, hlpS, htyS⟩ := natOpGuard_succTy hng
  have hfN := fdown hcN hfN2
  have hfZ := fdown hcZ hfZ2
  have hfS := fdown hcS hfS2
  -- the `Bool` type, hidden in `Nat.ble`'s pinned type
  have hbleDep : natBleName ∈ natOpDeps cv.name := by
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hbleOk : natOpStoredOk env natBleName = true :=
    natOpStoredOk_cons (ci := .defnInfo cv value' hint) hcB hcBle
      (List.all_eq_true.mp hdeps _ hbleDep)
  obtain ⟨cvB, vB, hintB, hfBle, hpinBle⟩ := natOpStoredOk_tyPinned hbleOk
  obtain ⟨ciB, hfB, hlpB, htyB⟩ := natOpTyPinned_boolFacts hpinBle
  -- the `Bool` constructors
  obtain ⟨ciT, hfT2, htyT⟩ := hbT2
  obtain ⟨ciF, hfF2, htyF⟩ := hbF2
  have hfT := fdown hcBT hfT2
  have hfF := fdown hcBF hfF2
  have hlpT : ciT.toConstantVal.levelParams = [] := by
    have := natOpGuard_stored hng
    have h := (this.2.2.2.2 (by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr (List.contains_iff_mem.mpr hc))).1
    unfold storedNoLevels at h
    rw [hfT2] at h
    simpa [List.isEmpty_iff] using h
  have hlpF : ciF.toConstantVal.levelParams = [] := by
    have := natOpGuard_stored hng
    have h := (this.2.2.2.2 (by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr (List.contains_iff_mem.mpr hc))).2
    unfold storedNoLevels at h
    rw [hfF2] at h
    simpa [List.isEmpty_iff] using h
  -- denotations of the pinned types
  have hdN : denoteClosed m.cval env φ ciN.toConstantVal.type
      = some (.sort 1) := by rw [denoteClosed, htyN, denote_sort]; rfl
  have hdB : denoteClosed m.cval env φ ciB.toConstantVal.type
      = some (.sort 1) := by rw [denoteClosed, htyB, denote_sort]; rfl
  have hNc : ∀ d, denote m.cval env φ d (.const natName [])
      = some (m.cval natName φ) := fun d =>
    denote_const_nolevels m φ hfN hlpN d
  have hdZ : denoteClosed m.cval env φ ciZ.toConstantVal.type
      = some (m.cval natName φ) := by rw [denoteClosed, htyZ]; exact hNc 0
  have hdS : denoteClosed m.cval env φ ciS.toConstantVal.type
      = some (.pi (m.cval natName φ) (m.cval natName φ)) := by
    rw [denoteClosed, htyS]
    simp only [denote_forallE, hNc, Expr.instantiate1]
  have hdT : denoteClosed m.cval env φ ciT.toConstantVal.type
      = some (m.cval boolName φ) := by
    rw [denoteClosed, htyT]
    exact denote_const_nolevels m φ hfB hlpB 0
  have hdF : denoteClosed m.cval env φ ciF.toConstantVal.type
      = some (m.cval boolName φ) := by
    rw [denoteClosed, htyF]
    exact denote_const_nolevels m φ hfB hlpB 0
  refine
    { op2 := ?_, op1 := ?_,
      zero := dmConstOther m (Ne.symm hcZ) hfZ hlpZ hdZ,
      succ := dmConstOther m (Ne.symm hcS) hfS hlpS hdS,
      btrue := dmConstOther m (Ne.symm hcBT) hfT hlpT hdT,
      bfalse := dmConstOther m (Ne.symm hcBF) hfF hlpF hdF,
      natTy := ?_, boolTy := ?_,
      eqStored := fdown hcEq hEq2,
      val := ⟨V, hv⟩, valFvar := hvf, valBnd := hvb,
      natStored := ⟨ciN, hfN, hlpN⟩ }
  · -- binary operations
    intro n hn hnot
    by_cases hnc : n = cv.name
    · subst hnc
      refine dmConstSelf m hv hvf hvb ?_
      obtain rfl : T = .pi (m.cval natName φ)
          (.pi (m.cval natName φ) (dmCodV m φ cv.name)) := by
        have hpin : natOpTyPinned env cv.name cv.type = true := by
          have hst := List.all_eq_true.mp hdeps cv.name (by
            simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
              or_false] at hc
            rcases hc with h | h | h | h | h | h | h | h | h <;>
              rw [h] <;> decide)
          obtain ⟨cvn, vn, hintn, hfn, hpinn⟩ := natOpStoredOk_tyPinned hst
          rw [Env.find?_cons,
            if_pos (show ConstantInfo.name (.defnInfo cv value' hint)
              = cv.name from rfl)] at hfn
          obtain rfl : cv = cvn := by
            injection Option.some.inj hfn with h1 _ _
          simpa only [natOpTyPinned_cons (ci := .defnInfo cv value' hint) hcB]
            using hpinn
        rw [denoteClosed] at hTd
        rw [denote_natOpTy2 m φ hnot hpin hfN hlpN] at hTd
        exact (Option.some.inj hTd).symm
      exact hVT
    · have hn' : n ∈ natOpDeps cv.name := by
        rcases List.mem_cons.mp hn with h | h
        · exact absurd h hnc
        · exact h
      have hst : natOpStoredOk env n :=
        natOpStoredOk_cons (ci := .defnInfo cv value' hint) hcB
          (fun hh => hnc hh.symm) (List.all_eq_true.mp hdeps _ hn')
      obtain ⟨cvn, vn, hintn, hfn, hpinn⟩ := natOpStoredOk_tyPinned hst
      refine dmConstOther m hnc hfn ?_ ?_
      · unfold natOpStoredOk at hst
        rw [hfn] at hst
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hst
        exact hst.1
      · rw [denoteClosed]
        exact denote_natOpTy2 m φ hnot hpinn hfN hlpN
  · -- unary operations
    intro n hn hyes
    by_cases hnc : n = cv.name
    · subst hnc
      refine dmConstSelf m hv hvf hvb ?_
      obtain rfl : T = .pi (m.cval natName φ) (dmCodV m φ cv.name) := by
        have hpin : natOpTyPinned env cv.name cv.type = true := by
          have hst := List.all_eq_true.mp hdeps cv.name (by
            simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
              or_false] at hc
            rcases hc with h | h | h | h | h | h | h | h | h <;>
              rw [h] <;> decide)
          obtain ⟨cvn, vn, hintn, hfn, hpinn⟩ := natOpStoredOk_tyPinned hst
          rw [Env.find?_cons,
            if_pos (show ConstantInfo.name (.defnInfo cv value' hint)
              = cv.name from rfl)] at hfn
          obtain rfl : cv = cvn := by
            injection Option.some.inj hfn with h1 _ _
          simpa only [natOpTyPinned_cons (ci := .defnInfo cv value' hint) hcB]
            using hpinn
        rw [denoteClosed] at hTd
        rw [denote_natOpTy1 m φ hyes hpin hfN hlpN] at hTd
        exact (Option.some.inj hTd).symm
      exact hVT
    · have hn' : n ∈ natOpDeps cv.name := by
        rcases List.mem_cons.mp hn with h | h
        · exact absurd h hnc
        · exact h
      have hst : natOpStoredOk env n :=
        natOpStoredOk_cons (ci := .defnInfo cv value' hint) hcB
          (fun hh => hnc hh.symm) (List.all_eq_true.mp hdeps _ hn')
      obtain ⟨cvn, vn, hintn, hfn, hpinn⟩ := natOpStoredOk_tyPinned hst
      refine dmConstOther m hnc hfn ?_ ?_
      · unfold natOpStoredOk at hst
        rw [hfn] at hst
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hst
        exact hst.1
      · rw [denoteClosed]
        exact denote_natOpTy1 m φ hyes hpinn hfN hlpN
  · have h := dmConstOther (A := VExpr.sort 1) (value' := value') m
      (Ne.symm hcN) hfN hlpN hdN
    rwa [cvalAt_ne (Ne.symm hcN)] at h
  · have h := dmConstOther (A := VExpr.sort 1) (value' := value') m
      (Ne.symm hcB) hfB hlpB hdB
    rwa [cvalAt_ne (Ne.symm hcB)] at h


/-! ## The assembly

`checkDivModPin`'s inversion, the `DMBase` construction, and one of the
nine assemblies. -/

/-- **`DivModPinTT`.**  The pinned operation satisfies its guarded
characterisation at every pair of `Nat`s, in every context. -/
theorem divModPinTT : DivModPinTT F := by
  intro env m cv value value' hint hmem hfresh _hannv hvf hvb hkey hpin
  obtain ⟨hEnvG, cv2, value2, hint2, hfind2, -, -, hcerts⟩ :=
    checkDivModPin_inv hpin
  rw [Env.find?_cons,
    if_pos (show ConstantInfo.name (.defnInfo cv value' hint) = cv.name from
      rfl)] at hfind2
  obtain ⟨rfl, rfl⟩ : cv = cv2 ∧ value' = value2 := by
    injection Option.some.inj hfind2 with h1 h2 _
    exact ⟨h1, h2⟩
  refine ⟨(divModEnvGuard_inv hEnvG).1, ?_⟩
  intro φ Δ x y hx hy
  obtain ⟨hcN, -, -, -, -, -, -, -, -, -, -⟩ := natDivModNames_ne_env hmem
  rw [cvalAt_ne (Ne.symm hcN)] at hx hy
  obtain ⟨V, T, hv, hT, hVT⟩ := hkey φ
  have hb := dmBase_of_guard m φ hmem hvf hvb hv hT hVT hEnvG
  have hruns := checkDivModCerts_inv hcerts
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h <;>
    rw [h] at hb hruns ⊢
  · exact dmDiv m φ hb hruns hx hy
  · exact dmMod m φ hb hruns hx hy
  · exact dmGcd m φ hb hruns hx hy
  · exact dmLand m φ hb hruns hx hy
  · exact dmLor m φ hb hruns hx hy
  · exact dmXor m φ hb hruns hx hy
  · exact dmShl m φ hb hruns hx hy
  · exact dmShr m φ hb hruns hx hy
  · exact dmLog2 m φ hb hruns hx hy


/-- **`DeclDefnTT`, closed.**  Both `Nat` pins are discharged, so the
definition case of `checkDecl` carries no hypotheses. -/
theorem declDefnTT_closed : DeclDefnTT F := declDefnTT natOpPinTT divModPinTT

end Assembly

end Spine

end Setlec.TTVerify
