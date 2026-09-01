import Setlec.SetR.Interp2.NatWfP
import Setlec.SetR.DivModPin

/-!
# The WF-recursive operations' clauses, established at `interp2` from
the pin certificates (task #161, literal tier — the divmod leg, part 3)

`DivModPin.lean` extracts `DivModV`'s clauses from the checker's
`checkDivModCerts` verdict at the collapse currency.  This file is its
mirror at the validated-annotation currency, and the shape is the one
`NatEqsP.lean` established for the structural recurrences:
**establishment from run certificates**.  The certificate's three runs
(`annotateCore`/`inferTypeCore`/`isDefEqCore` at depth 4, unpacked by
the currency-free `checkDivModCerts_inv`) are converted by
`InferClaims2P`/`DefEqClaims2P` at the pre-insertion environment into
"the statement's interpretation is inhabited", and the pinned `Eq`
law turns inhabited into equal.

Everything `V`-free in `DivModPin.lean` is reused as it stands
(`dmFragOk`, `dmEvalV`, `dmLeavesOk` and its lemmas,
`fvarLeaves_substConst0`, `divModCertApplied_mem1`/`2`, the applied
forms' frame lemmas, the pinned-type inversions).  What is genuinely
new here is the **grading**: `CtxOkP`, `InferClaims2P` and
`DefEqClaims2P` all demand `AnnotOkP` of what they compare, and
`CtxOkR` demanded nothing of the sort.  So the statements' fragment
gets a graded walk (`dmNatFragP`), built the way `NatEqsP.lean`'s
`NatArgP` walk is: argument memberships from the frame, head
memberships from `mem_typeP` at the pinned types, and the fibre facts
at *unknown* regime bits from `type_okP`'s `AnnotValidV` — so no bit
positivity is taken anywhere.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## Value-level head packages

What a fragment application rule needs of a head, at the value level:
a membership in a one- or two-step `piR` over the frame's `Nat`, with
`app_mem_piR`'s fibre premise at each step.  The bits are whatever the
stored annotation carries. -/

/-- A binary head over the frame's `Nat`, with codomain set `codS`. -/
def DmBinV (natS codS f : V) : Prop :=
  ∃ b₁ b₂ : Nat,
    f ∈ˢ piR b₁ natS (fun _ => piR b₂ natS (fun _ => codS)) ∧
    (b₁ = 0 → ∀ x, x ∈ˢ natS →
      piR b₂ natS (fun _ => codS) ∈ˢ (univZero : V)) ∧
    (b₂ = 0 → ∀ x, x ∈ˢ natS → codS ∈ˢ (univZero : V))

/-- A unary head over the frame's `Nat`. -/
def DmUnV (natS codS f : V) : Prop :=
  ∃ b₁ : Nat, f ∈ˢ piR b₁ natS (fun _ => codS) ∧
    (b₁ = 0 → ∀ x, x ∈ˢ natS → codS ∈ˢ (univZero : V))

/-- The binary rule, at the value level. -/
theorem DmBinV.app {natS codS f x y : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) (hy : y ∈ˢ natS) :
    SetTheory.app (SetTheory.app f x) y ∈ˢ codS := by
  obtain ⟨b₁, b₂, hm, hB1, hB2⟩ := h
  have hinner : SetTheory.app f x ∈ˢ piR b₂ natS (fun _ => codS) :=
    app_mem_piR hm hx hB1
  exact app_mem_piR hinner hy hB2

/-- The unary rule. -/
theorem DmUnV.app {natS codS f x : V} (h : DmUnV natS codS f)
    (hx : x ∈ˢ natS) : SetTheory.app f x ∈ˢ codS := by
  obtain ⟨b₁, hm, hB1⟩ := h
  exact app_mem_piR hm hx hB1

/-- The `AnnotOk2` witness a binary head's first application needs. -/
theorem DmBinV.ok1 {natS codS f x : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) {ρ : Nat → V} {fa xa : AVExpr}
    (hfa : AnnotOk2 V ρ fa) (hxa : AnnotOk2 V ρ xa)
    (hf : interp2 V ρ fa = f) (hxv : interp2 V ρ xa = x) :
    AnnotOk2 V ρ (.app fa xa) := by
  obtain ⟨b₁, b₂, hm, hB1, -⟩ := h
  rw [AnnotOk2_app]
  exact ⟨hfa, hxa, b₁, natS, fun _ => piR b₂ natS (fun _ => codS),
    by rw [hf]; exact hm, by rw [hxv]; exact hx, hB1⟩

/-- …and its second. -/
theorem DmBinV.ok2 {natS codS f x y : V} (h : DmBinV natS codS f)
    (hx : x ∈ˢ natS) (hy : y ∈ˢ natS) {ρ : Nat → V}
    {fa xa ya : AVExpr}
    (hfa : AnnotOk2 V ρ fa) (hxa : AnnotOk2 V ρ xa)
    (hya : AnnotOk2 V ρ ya)
    (hf : interp2 V ρ fa = f) (hxv : interp2 V ρ xa = x)
    (hyv : interp2 V ρ ya = y) :
    AnnotOk2 V ρ (.app (.app fa xa) ya) := by
  have hok1 := DmBinV.ok1 h hx hfa hxa hf hxv
  obtain ⟨b₁, b₂, hm, hB1, hB2⟩ := h
  rw [AnnotOk2_app]
  refine ⟨hok1, hya, b₂, natS, fun _ => codS, ?_,
    by rw [hyv]; exact hy, hB2⟩
  rw [interp2_app, hf, hxv]
  have hinner : SetTheory.app f x ∈ˢ piR b₂ natS (fun _ => codS) :=
    app_mem_piR hm hx hB1
  exact hinner

/-- The unary head's `AnnotOk2` witness. -/
theorem DmUnV.ok1 {natS codS f x : V} (h : DmUnV natS codS f)
    (hx : x ∈ˢ natS) {ρ : Nat → V} {fa xa : AVExpr}
    (hfa : AnnotOk2 V ρ fa) (hxa : AnnotOk2 V ρ xa)
    (hf : interp2 V ρ fa = f) (hxv : interp2 V ρ xa = x) :
    AnnotOk2 V ρ (.app fa xa) := by
  obtain ⟨b₁, hm, hB1⟩ := h
  rw [AnnotOk2_app]
  exact ⟨hfa, hxa, b₁, natS, fun _ => codS, by rw [hf]; exact hm,
    by rw [hxv]; exact hx, hB1⟩

/-! ## The head packages, from the environment invariant

`mem_typeP` at a pinned operation type gives the membership;
`type_okP`'s `AnnotValidV` gives the fibre facts.  (These are
`NatEqsP.lean`'s `natBinHeadP_of_stored`/`natUnHeadP_of_stored` with
the two-variable context stripped off — the certificate frame is a
different context, and the packages never read one.) -/

/-- **A stored pinned binary head, at the value level.** -/
theorem dmBinV_of_stored (mp : EnvS2PM V μ env) (ψ : Name → Nat)
    {o : Name} {cvo : ConstantVal} {vo : Expr} {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (_hlp : cvo.levelParams = [])
    {n₁ n₂ : Name} {mb₁ mb₂ : Setlec.BinderMeta} {codN : Name}
    (hty : cvo.type = .forallE n₁ (.const Setlec.natName [])
      (.forallE n₂ (.const Setlec.natName []) (.const codN []) mb₂)
      mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = [])
    (ρ : Nat → V) :
    DmBinV (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (mp.base2.acval codN ψ))
      (interp2 V ρ (mp.base2.acval o ψ)) := by
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
  have hmem := mp.mem_typeP _ hmemE ψ _ hta ρ
  rw [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at hmem
  have htok := mp.type_okP _ hmemE ψ _ hta ρ
  refine ⟨pwBit ψ mb₁.pw, pwBit ψ mb₂.pw, ?_, ?_, ?_⟩
  · rw [interp2_pi] at hmem
    rw [show (fun x => interp2 V (cons x ρ)
          ((.pi 0 (pwBit ψ mb₂.pw) (mp.base2.acval Setlec.natName ψ)
            (mp.base2.acval codN ψ)) : AVExpr))
        = fun _ => piR (pwBit ψ mb₂.pw)
            (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
            (fun _ => interp2 V ρ (mp.base2.acval codN ψ)) from by
      funext x
      rw [interp2_pi]
      congr 1
      · exact acval_interp2_closedC mp.base2 _ ψ _ ρ
      · funext y
        exact acval_interp2_closedC mp.base2 _ ψ _ ρ] at hmem
    exact hmem
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValidV_pi] at hv
    have h := hv.2.2 hz x hx
    rw [show interp2 V (cons x ρ)
          ((.pi 0 (pwBit ψ mb₂.pw) (mp.base2.acval Setlec.natName ψ)
            (mp.base2.acval codN ψ)) : AVExpr)
        = piR (pwBit ψ mb₂.pw)
            (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
            (fun _ => interp2 V ρ (mp.base2.acval codN ψ)) from by
      rw [interp2_pi]
      congr 1
      · exact acval_interp2_closedC mp.base2 _ ψ _ ρ
      · funext y
        exact acval_interp2_closedC mp.base2 _ ψ _ ρ] at h
    exact h
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValidV_pi] at hv
    have hinner := hv.2.1 x hx
    rw [AnnotValidV_pi] at hinner
    have h := hinner.2.2 hz x
      (by rw [acval_interp2_closedC mp.base2 _ ψ (cons x ρ) ρ]; exact hx)
    rwa [acval_interp2_closedC mp.base2 _ ψ _ ρ] at h

/-- **A stored pinned unary head, at the value level.** -/
theorem dmUnV_of_stored (mp : EnvS2PM V μ env) (ψ : Name → Nat)
    {o : Name} {cvo : ConstantVal} {vo : Expr} {ho : ReducibilityHint}
    (hf : env.find? o = some (.defnInfo cvo vo ho))
    (_hlp : cvo.levelParams = [])
    {n₁ : Name} {mb₁ : Setlec.BinderMeta} {codN : Name}
    (hty : cvo.type = .forallE n₁ (.const Setlec.natName [])
      (.const codN []) mb₁)
    {ciN codCi : ConstantInfo}
    (hfN : env.find? Setlec.natName = some ciN)
    (hlpN : ciN.toConstantVal.levelParams = [])
    (hcodF : env.find? codN = some codCi)
    (hcodLp : codCi.toConstantVal.levelParams = [])
    (ρ : Nat → V) :
    DmUnV (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (mp.base2.acval codN ψ))
      (interp2 V ρ (mp.base2.acval o ψ)) := by
  have hmemE := Setlec.SetR.Env.find?_mem hf
  have hnm : cvo.name = o := Setlec.SetR.Env.find?_name hf
  have hta : denoteP mp.base2.acval env ψ 0
      (ConstantInfo.defnInfo cvo vo ho).toConstantVal.type
      = some (.pi 0 (pwBit ψ mb₁.pw) (mp.base2.acval Setlec.natName ψ)
          (mp.base2.acval codN ψ)) := by
    show denoteP mp.base2.acval env ψ 0 cvo.type = _
    rw [hty, denoteP_forallE, denoteP_levelless_const hfN hlpN]
    rw [show (Expr.const codN ([] : List Setlec.Level)).instantiate1
          (.fvar 0 n₁ (.const Setlec.natName []))
        = Expr.const codN [] from Setlec.Expr.instantiate1_eq_self
        (by simp [Setlec.Expr.looseBVarsBounded])]
    rw [denoteP_levelless_const hcodF hcodLp]
    rfl
  have hmem := mp.mem_typeP _ hmemE ψ _ hta ρ
  rw [show (ConstantInfo.defnInfo cvo vo ho).name = o from hnm] at hmem
  have htok := mp.type_okP _ hmemE ψ _ hta ρ
  refine ⟨pwBit ψ mb₁.pw, ?_, ?_⟩
  · rw [interp2_pi] at hmem
    rw [show (fun x => interp2 V (cons x ρ)
          (mp.base2.acval codN ψ))
        = fun _ => interp2 V ρ (mp.base2.acval codN ψ) from by
      funext x
      exact acval_interp2_closedC mp.base2 _ ψ _ ρ] at hmem
    exact hmem
  · intro hz x hx
    have hv := htok.2
    rw [AnnotValidV_pi] at hv
    have h := hv.2.2 hz x hx
    rwa [acval_interp2_closedC mp.base2 _ ψ _ ρ] at h

/-! ## The statements' `Nat`-valued fragment, and its graded walk

`dmFragOk` (v1) is the loose grammar: it does not record which heads
are unary and which binary, because v1 never needs to *type* a
subterm.  The P side does — a grading is a typing derivation — so the
walk below runs on the tighter grammar `dmNatFrag`, which is what the
certificate statements' `Nat`-valued sides actually are: the two frame
variables, `Nat.zero`, and saturated applications of the listed
unary/binary heads.  Membership of a concrete statement side in this
grammar is `by decide`. -/

/-- The `Nat`-valued statement fragment. -/
def dmNatFrag (bins uns : List Name) : Expr → Bool
  | .app (.app (.const n us) a) b =>
      bins.contains n && us.isEmpty &&
        dmNatFrag bins uns a && dmNatFrag bins uns b
  | .app (.const n us) a =>
      uns.contains n && us.isEmpty && dmNatFrag bins uns a
  | .const n us => (n == Setlec.natZeroName) && us.isEmpty
  | .fvar i nm ty =>
      ((i == 0 && nm == Name.anonymous.str "x") ||
        (i == 1 && nm == Name.anonymous.str "y")) &&
        ty == Expr.const Setlec.natName []
  | _ => false

/-- **The graded walk.**  A `Nat`-valued statement fragment reads, and
at every valuation putting the two frame variables in the frame's
`Nat` its reading is graded, its value is in `Nat`, and that value is
the `dmEvalV` chain `DivModClausesV` is written in.

The valuation is quantified *inside* the reading, because the P claims
grade at every valuation satisfying the telescope, not at one. -/
theorem dmNatFragP {m : EnvS2Core V env} {ψ : Name → Nat}
    {c : Name} {A : (Name → Nat) → AVExpr} {value' : Expr}
    {bins uns : List Name} {d : Nat} {natS : V}
    (hread : ∀ n ∈ Setlec.natZeroName :: (bins ++ uns), ∀ d' : Nat,
      denoteP m.acval env ψ d' (Expr.substConst0 c value' (.const n []))
        = some (acvalWith m.acval c A n ψ))
    (hleafOk : ∀ (n : Name) (ρ : Nat → V),
      AnnotOkP V ρ (acvalWith m.acval c A n ψ))
    (hbin : ∀ n ∈ bins, ∀ ρ : Nat → V,
      DmBinV natS natS (interp2 V ρ (acvalWith m.acval c A n ψ)))
    (hun : ∀ n ∈ uns, ∀ ρ : Nat → V,
      DmUnV natS natS (interp2 V ρ (acvalWith m.acval c A n ψ)))
    (hzero : ∀ ρ : Nat → V,
      interp2 V ρ (acvalWith m.acval c A Setlec.natZeroName ψ) ∈ˢ natS) :
    ∀ e : Expr, dmNatFrag bins uns e = true →
      ∃ ea, denoteP m.acval env ψ d
          (Expr.substConst0 c value' e) = some ea ∧
        ∀ ρ : Nat → V, ρ (d - 1 - 0) ∈ˢ natS → ρ (d - 1 - 1) ∈ˢ natS →
          AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ natS ∧
          interp2 V ρ ea = dmEvalV V
            (fun n => interp2 V ρ (acvalWith m.acval c A n ψ))
            (ρ (d - 1 - 0)) (ρ (d - 1 - 1)) e
  | .app (.app (.const n us) a) b, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hn, rfl⟩, ha⟩, hb⟩ := h
    have hnm : n ∈ bins := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hfa⟩ := dmNatFragP hread hleafOk hbin hun hzero a ha
    obtain ⟨ba, hdb, hfb⟩ := dmNatFragP hread hleafOk hbin hun hzero b hb
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (.app (acvalWith m.acval c A n ψ) aa) ba, ?_,
      fun ρ hx hy => ?_⟩
    · show denoteP m.acval env ψ d
        (.app (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) (Expr.substConst0 c value' b))
        = _
      rw [denoteP_app, denoteP_app, hdn, hda, hdb]
      rfl
    · obtain ⟨hoka, hma, hea⟩ := hfa ρ hx hy
      obtain ⟨hokb, hmb, heb⟩ := hfb ρ hx hy
      refine ⟨⟨DmBinV.ok2 (hbin n hnm ρ) hma hmb (hleafOk n ρ).1
          hoka.1 hokb.1 rfl rfl rfl,
          by rw [AnnotValidV_app, AnnotValidV_app]
             exact ⟨⟨(hleafOk n ρ).2, hoka.2⟩, hokb.2⟩⟩, ?_, ?_⟩
      · rw [interp2_app, interp2_app]
        exact DmBinV.app (hbin n hnm ρ) hma hmb
      · rw [interp2_app, interp2_app, hea, heb]
        rfl
  | .app (.const n us) a, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨hn, rfl⟩, ha⟩ := h
    have hnm : n ∈ uns := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hfa⟩ := dmNatFragP hread hleafOk hbin hun hzero a ha
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (acvalWith m.acval c A n ψ) aa, ?_, fun ρ hx hy => ?_⟩
    · show denoteP m.acval env ψ d
        (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) = _
      rw [denoteP_app, hdn, hda]
      rfl
    · obtain ⟨hoka, hma, hea⟩ := hfa ρ hx hy
      refine ⟨⟨DmUnV.ok1 (hun n hnm ρ) hma (hleafOk n ρ).1 hoka.1 rfl
          rfl,
          by rw [AnnotValidV_app]; exact ⟨(hleafOk n ρ).2, hoka.2⟩⟩,
        ?_, ?_⟩
      · rw [interp2_app]
        exact DmUnV.app (hun n hnm ρ) hma
      · rw [interp2_app, hea]
        rfl
  | .const n us, h => by
    simp only [dmNatFrag, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, hread _ (by simp) d,
      fun ρ _ _ => ⟨hleafOk _ ρ, hzero ρ, rfl⟩⟩
  | .fvar i nm ty, h => by
    simp only [dmNatFrag, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨.bvar (d - 1 - 0), ?_, fun ρ hx hy => ?_⟩
      · show denoteP m.acval env ψ d
          (.fvar 0 (Name.anonymous.str "x")
            (.const Setlec.natName [])) = _
        rw [denoteP_fvar]
      · exact ⟨⟨by simp, by simp⟩, by rw [interp2_bvar]; exact hx,
          by rw [interp2_bvar]; rfl⟩
    · refine ⟨.bvar (d - 1 - 1), ?_, fun ρ hx hy => ?_⟩
      · show denoteP m.acval env ψ d
          (.fvar 1 (Name.anonymous.str "y")
            (.const Setlec.natName [])) = _
        rw [denoteP_fvar]
      · exact ⟨⟨by simp, by simp⟩, by rw [interp2_bvar]; exact hy,
          by rw [interp2_bvar]; rfl⟩
  | .bvar _, h | .sort _, h | .lam _ _ _ _, h | .letE _ _ _ _, h
  | .forallE _ _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp [dmNatFrag] at h

/-! ## One certificate, converted

`certValueS`'s mirror.  The run's three components become, in order:
the annotated applied proof keeps the frame (currency-free), the
`InferClaims2P` row gives its reading's membership in the inferred
type's, and the `DefEqClaims2P` row identifies that type with the
pinned statement — so the statement's interpretation is inhabited.

Two premises v1 does not have, both the grading tax: the statement's
reading must be graded (`DefEqClaims2P` compares graded readings), and
the applied proof must *read* at all (v1's `InferClaimsR` concluded
existence; the P claim takes the reading as a premise, so the reads
bundle supplies it). -/

/-- **One certificate, extracted at `interp2`.** -/
theorem certValueP {F : Nat} (mp : EnvS2PM V μ env) (ψ : Name → Nat)
    (hacc : ∀ {d : Nat} {e t : Expr},
      Setlec.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteP mp.base2.acval env ψ d e = some ea)
    (hreads : InferReadsP mp.base2 μ ψ F)
    (hinfC : InferClaims2P μ mp.base2 ψ F)
    (hdeC : DefEqClaims2P μ mp.base2 ψ F)
    {c : Name} {annVal : Expr} {st : List Expr × Expr} {proof : Expr}
    (hfacts : CertRunFacts μ env F c annVal st proof)
    {Δa : List AVExpr}
    (hW : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hB : (divModCertApplied (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))).looseBVarsBounded 0
      = true)
    (hL : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hCA : CtxOkP mp.base2 ψ 4 Δa (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))))
    (hWE : Expr.WScoped 4 (Expr.substConst0 c annVal st.2))
    (hBE : (Expr.substConst0 c annVal st.2).looseBVarsBounded 0 = true)
    (hLE : Expr.LeavesBounded (Expr.substConst0 c annVal st.2))
    (hCE : CtxOkP mp.base2 ψ 4 Δa (Expr.substConst0 c annVal st.2))
    {vE : AVExpr}
    (hvE : denoteP mp.base2.acval env ψ 4
      (Expr.substConst0 c annVal st.2) = some vE)
    (hokE : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vE)
    (ρ : Nat → V) (hsat : Sat2 V Δa ρ) :
    ∃ w : V, w ∈ˢ interp2 V ρ vE := by
  obtain ⟨-, appliedA, tp, hann, hinf, hde⟩ := hfacts
  -- the annotated applied proof keeps the frame
  have hWA : Expr.WScoped 4 appliedA :=
    Setlec.annotateCore_WScoped F _ hann hW
  have hBA : appliedA.looseBVarsBounded 0 = true :=
    Setlec.annotateCore_looseBVars F _ hann hB
  have hsub := Setlec.annotateCore_leaves_sub F _ hann hW hB
  have hLA : Expr.LeavesBounded appliedA := fun l hl => hL l (hsub l hl)
  have hCA' : CtxOkP mp.base2 ψ 4 Δa appliedA := hCA.of_subset hsub
  -- the readings
  obtain ⟨ea, hea⟩ := hacc hinf hWA hBA hLA
  obtain ⟨ta, hta⟩ :=
    hreads hinf hWA hBA hLA (LeafReadsP.of_ctxOkP hCA') hea
  obtain ⟨-, hokT, hmem⟩ := hinfC hinf hWA hBA hLA hCA' hea hta
  -- the inferred type's frame
  have hWtp : Expr.WScoped 4 tp :=
    Setlec.inferTypeCore_WScoped mp.base2.base.wf F hinf hWA
  have hBtp : tp.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars mp.base2.base.wf F hinf hWA hBA hLA
  have hLtp : Expr.LeavesBounded tp := fun l hl =>
    hLA l (Setlec.inferTypeCore_fvarLeaves mp.base2.base.wf F hinf hWA
      l hl)
  have hCtp : CtxOkP mp.base2 ψ 4 Δa tp :=
    hCA'.of_subset
      (Setlec.inferTypeCore_fvarLeaves mp.base2.base.wf F hinf hWA)
  -- the defeq run identifies the inferred type with the statement
  have heq := hdeC hde hWtp hBtp hLtp hWE hBE hLE hCtp hCE hta hvE
    hokT hokE ρ hsat
  exact ⟨interp2 V ρ ea, by rw [← heq]; exact hmem ρ hsat⟩

/-! ## The frame's leaf discipline

`CtxOkR.pinnedCtxLift`'s mirror.  `CtxOkP` is slack in the same way
`CtxOkR` is — it asks for the leaf annotation's *reading* to agree with
the entry read one telescope deeper, not for entry equality — so a
hypothesis slot may carry its type's reading at the depth the type is
*stated*, with the depth-4 reading its lift.  The P side adds the
grading conjunct, which is supplied at the depth-4 reading and
transported by the same equation. -/

/-- Two weakenings, composed. -/
theorem denotePLift {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (acval n ψ').liftN 1 k = acval n ψ')
    {d n : Nat} {e : Expr} {W : AVExpr} (hw : Expr.WScoped d e)
    (h : denoteP acval env ψ d e = some W) :
    denoteP acval env ψ (d + n) e = some (W.liftN n 0) := by
  induction n with
  | zero => rw [Nat.add_zero, h, AVExpr.liftN_zero]
  | succ n ih =>
    rw [show d + (n + 1) = (d + n) + 1 from rfl,
      denoteP_weaken_top hacl (hw.mono (by omega)), ih]
    simp only [Option.map_some]
    rw [AVExpr.liftN_liftN, Nat.add_comm 1 n]

/-- **The certificate frame's leaf discipline, in the lift-carrying
form.** -/
theorem ctxOkP_pinnedLift {m : EnvS2Core V env} {ψ : Name → Nat}
    {d : Nat} {Δa : List AVExpr} {e : Expr}
    (hlen : Δa.length = d)
    (hslot : ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
      ∃ tya, denoteP m.acval env ψ d l.2.2 = some tya ∧
        tya = (Δa.getD (d - 1 - l.1) default).liftN (d - l.1) 0 ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya) :
    CtxOkP m ψ d Δa e := by
  refine ⟨hlen, fun l hl => ?_⟩
  obtain ⟨hlt, hfb, tya, hden, heq, hok⟩ := hslot l hl
  have hidx : d - 1 - l.1 < Δa.length := by rw [hlen]; omega
  have hget : Δa[d - 1 - l.1]?
      = some (Δa.getD (d - 1 - l.1) default) := by
    rw [List.getD, List.getElem?_eq_getElem hidx]
    rfl
  refine ⟨hlt, hfb, tya, _, hden, hget, fun ρ _ => ?_, hok⟩
  rw [heq, interp2_liftN]
  congr 1
  funext j
  simp only [shiftE]
  rw [if_neg (by omega)]
  congr 1
  omega

/-! ## The pinned `Eq` spine, read and graded -/

/-- The pinned `Eq` spine's reading (`denote_eqSpine`'s mirror): the
head carries `Eq.{1}`, whose level argument is not `[]`, so the
operation substitution leaves it alone. -/
theorem denoteP_eqSpine {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat} {c : Name} {value' : Expr}
    (hEq : env.find? eqName = some eqA) {A a b : Expr}
    {Aa aa ba : AVExpr} {d : Nat}
    (hA : denoteP acval env ψ d (Expr.substConst0 c value' A)
      = some Aa)
    (ha : denoteP acval env ψ d (Expr.substConst0 c value' a)
      = some aa)
    (hb : denoteP acval env ψ d (Expr.substConst0 c value' b)
      = some ba) :
    denoteP acval env ψ d (Expr.substConst0 c value'
        (.app (.app (.app (.const eqName [.succ .zero]) A) a) b))
      = some (.app (.app (.app (acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) Aa) aa)
          ba) := by
  have hhead : denoteP acval env ψ d
      (Expr.substConst0 c value' (.const eqName [.succ .zero]))
      = some (acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) := by
    rw [show Expr.substConst0 c value' (.const eqName [.succ .zero])
        = .const eqName [.succ .zero] from by
      simp only [Expr.substConst0]
      rw [if_neg (by rintro ⟨-, hh⟩; exact nomatch hh)]]
    exact denoteP_const hEq rfl
  show denoteP acval env ψ d
      (.app (.app (.app (Expr.substConst0 c value'
        (.const eqName [.succ .zero]))
        (Expr.substConst0 c value' A)) (Expr.substConst0 c value' a))
        (Expr.substConst0 c value' b)) = _
  rw [denoteP_app, denoteP_app, denoteP_app, hhead, hA, ha, hb]
  rfl

/-- The `Eq.{1}` level assignment sends `u` to `1`. -/
theorem eqSubstP_uN (ψ : Name → Nat) :
    Level.substFn ψ eqA.toConstantVal.levelParams [Level.zero.succ] uN
      = 1 := rfl

/-! ## The head names a certificate block reads -/

/-- The extension's valuation: the pinned operation at its own name
(through the annotated stored value), every dependency at its
storage. -/
def dmLeaf {env : Env} (m : EnvS2Core V env) (c : Name)
    (A : (Name → Nat) → AVExpr) (ψ : Name → Nat) (n : Name) : AVExpr :=
  acvalWith m.acval c A n ψ

/-- The binary heads the statements apply: the recurrence dependencies
minus the guard's `Nat.ble` and the unary `Nat.pred`/`Nat.log2`. -/
def dmBinNames (c : Name) : List Name :=
  (Setlec.natOpDeps c).filter fun n =>
    n != Setlec.natBleName && n != Setlec.natPredName &&
      n != Setlec.natLog2Name

/-- The unary heads: `Nat.succ`, plus the operation itself when it is
`Nat.log2`. -/
def dmUnNames (c : Name) : List Name :=
  if c = Setlec.natLog2Name then [Setlec.natSuccName, Setlec.natLog2Name]
  else [Setlec.natSuccName]

/-- Every head a certificate block mentions. -/
def dmHeadNames (c : Name) : List Name :=
  Setlec.natName :: Setlec.boolName :: Setlec.natZeroName ::
    Setlec.natBleName :: Setlec.boolTrueName ::
    Setlec.boolFalseName :: (dmBinNames c ++ dmUnNames c)

/-- The walk's head list sits inside the frame's. -/
theorem mem_dmHeadNames {c n : Name}
    (h : n ∈ Setlec.natZeroName :: (dmBinNames c ++ dmUnNames c)) :
    n ∈ dmHeadNames c := by
  simp only [dmHeadNames, List.mem_cons] at h ⊢
  rcases h with rfl | h
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-! ## The statements' syntactic obligations, from the grammar

A `dmNatFrag` term has only the two frame variables as leaves, both at
`Nat`, and no bound variables at all — so every syntactic side
condition the frame asks for is a consequence of the grammar, not a
`by decide` at each call site. -/

/-- A frame variable is well-scoped at any depth above its index. -/
theorem dmFvarWScoped {d i : Nat} {n : Name} {ty : Expr} (hi : i < d)
    (hty : Expr.WScoped i ty) : Expr.WScoped d (Expr.fvar i n ty) := by
  simp only [Expr.WScoped]
  exact ⟨hi, hty⟩

theorem dmNatFrag_syntax {bins uns : List Name} :
    ∀ e : Expr, dmNatFrag bins uns e = true →
      dmLeavesOk e = true ∧ e.looseBVarsBounded 0 = true ∧
      ∀ d : Nat, 2 ≤ d → Expr.WScoped d e
  | .app (.app (.const n us) a) b, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨-, rfl⟩, ha⟩, hb⟩ := h
    obtain ⟨hla, hba, hwa⟩ := dmNatFrag_syntax a ha
    obtain ⟨hlb, hbb, hwb⟩ := dmNatFrag_syntax b hb
    refine ⟨?_, ?_, fun d hd =>
      dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar (e := .const n []) rfl)
        (hwa d hd)) (hwb d hd)⟩
    · simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
        List.all_append, Bool.and_eq_true]
      exact ⟨hla, hlb⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨⟨trivial, hba⟩, hbb⟩
  | .app (.const n us) a, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨-, rfl⟩, ha⟩ := h
    obtain ⟨hla, hba, hwa⟩ := dmNatFrag_syntax a ha
    refine ⟨?_, ?_, fun d hd =>
      dmApp_wscoped (Expr.WScoped.of_not_hasFvar (e := .const n []) rfl)
        (hwa d hd)⟩
    · simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append]
      exact hla
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨trivial, hba⟩
  | .const n us, h => by
    simp only [dmNatFrag, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl, fun _ _ =>
      Expr.WScoped.of_not_hasFvar
        (e := .const Setlec.natZeroName []) rfl⟩
  | .fvar i nm ty, h => by
    simp only [dmNatFrag, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl,
        fun d hd => dmFvarWScoped (by omega)
          (Expr.WScoped.of_not_hasFvar
            (e := .const Setlec.natName []) rfl)⟩
    · exact ⟨by simp [dmLeavesOk, Expr.fvarLeaves], rfl,
        fun d hd => dmFvarWScoped (by omega)
          (Expr.WScoped.of_not_hasFvar
            (e := .const Setlec.natName []) rfl)⟩
  | .bvar _, h | .sort _, h | .lam _ _ _ _, h | .letE _ _ _ _, h
  | .forallE _ _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp [dmNatFrag] at h

/-- Scoping survives the operation substitution (the `WScoped` twin of
`wscopedB_substConst0`; `substConst0` rewrites `const` nodes and
recurses only through applications). -/
theorem wscoped_substConst0 {c : Name} {v : Expr}
    (hv : v.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, Expr.WScoped d e →
      Expr.WScoped d (Expr.substConst0 c v e)
  | .const n us, d, _ => by
    simp only [Expr.substConst0]
    split
    · exact Expr.WScoped.of_not_hasFvar hv
    · exact Expr.WScoped.of_not_hasFvar (e := .const n us) rfl
  | .app f a, d, hw => by
    simp only [Expr.WScoped] at hw
    exact dmApp_wscoped (wscoped_substConst0 hv f hw.1)
      (wscoped_substConst0 hv a hw.2)
  | .bvar _, _, hw | .fvar _ _ _, _, hw | .sort _, _, hw
  | .lit _, _, hw | .lam _ _ _ _, _, hw | .forallE _ _ _ _, _, hw
  | .letE _ _ _ _, _, hw | .proj _ _ _, _, hw => hw

/-! ## The certificate frame

Everything the nine clause blocks are read against, at one assignment:
the extension's valuation with its closedness and grading, the frame's
`Nat` and `Bool` as universes, the statements' heads as functions on
`Nat`, and the pinned `Eq`.  This is `dmFrameS`'s existential tuple as
a structure. -/

/-- **The div/mod certificate frame at `interp2`.** -/
structure DmFrameP {env : Env} (mp : EnvS2PM V μ env) (c : Name)
    (A : (Name → Nat) → AVExpr) (value' : Expr) (ψ : Name → Nat) :
    Prop where
  /-- the pinned `Eq` is stored -/
  eqStored : env.find? eqName = some eqA
  /-- neither pinned type name is the operation being installed -/
  natNe : Setlec.natName ≠ c
  boolNe : Setlec.boolName ≠ c
  /-- the annotated stored value's reading, at every depth -/
  selfRead : ∀ d : Nat,
    denoteP mp.base2.acval env ψ d value' = some (A ψ)
  /-- the annotated value is closed -/
  valueNoFvar : value'.hasFvar = false
  valueBounded : value'.looseBVarsBounded 0 = true
  /-- every head the statements read is the operation itself or is
  stored level-monomorphically -/
  stored : ∀ n ∈ dmHeadNames c, n = c ∨ (n ≠ c ∧ ∃ ci,
    env.find? n = some ci ∧ ci.toConstantVal.levelParams = [])
  /-- the extension's leaves are graded and closed -/
  leafOk : ∀ (n : Name) (ρ : Nat → V),
    AnnotOkP V ρ (dmLeaf mp.base2 c A ψ n)
  leafClosed : ∀ (n : Name) (ρ ρ' : Nat → V),
    interp2 V ρ (dmLeaf mp.base2 c A ψ n)
      = interp2 V ρ' (dmLeaf mp.base2 c A ψ n)
  /-- the frame's two types are universes -/
  natU : ∀ ρ : Nat → V,
    interp2 V ρ (mp.base2.acval Setlec.natName ψ) ∈ˢ (univ 1 : V)
  boolU : ∀ ρ : Nat → V,
    interp2 V ρ (mp.base2.acval Setlec.boolName ψ) ∈ˢ (univ 1 : V)
  /-- the statements' heads are functions on the frame's `Nat` -/
  binHead : ∀ n ∈ dmBinNames c, ∀ ρ : Nat → V,
    DmBinV (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (dmLeaf mp.base2 c A ψ n))
  unHead : ∀ n ∈ dmUnNames c, ∀ ρ : Nat → V,
    DmUnV (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (dmLeaf mp.base2 c A ψ n))
  /-- …and the guard's `Nat.ble` is one into `Bool` -/
  bleHead : ∀ ρ : Nat → V,
    DmBinV (interp2 V ρ (mp.base2.acval Setlec.natName ψ))
      (interp2 V ρ (mp.base2.acval Setlec.boolName ψ))
      (interp2 V ρ (dmLeaf mp.base2 c A ψ Setlec.natBleName))
  /-- the constructors inhabit their types -/
  zeroMem : ∀ ρ : Nat → V,
    interp2 V ρ (dmLeaf mp.base2 c A ψ Setlec.natZeroName)
      ∈ˢ interp2 V ρ (mp.base2.acval Setlec.natName ψ)
  boolCtorMem : ∀ bn : Name,
    bn = Setlec.boolTrueName ∨ bn = Setlec.boolFalseName →
    ∀ ρ : Nat → V, interp2 V ρ (dmLeaf mp.base2 c A ψ bn)
      ∈ˢ interp2 V ρ (mp.base2.acval Setlec.boolName ψ)

namespace DmFrameP

variable {mp : EnvS2PM V μ env} {c : Name} {A : (Name → Nat) → AVExpr}
variable {value' : Expr} {ψ : Name → Nat}

/-- **A head reads to its leaf**, at every depth: the operation itself
through the substitution, a dependency through its storage. -/
theorem read (fr : DmFrameP mp c A value' ψ) {n : Name}
    (hn : n ∈ dmHeadNames c) (d : Nat) :
    denoteP mp.base2.acval env ψ d
        (Expr.substConst0 c value' (.const n []))
      = some (dmLeaf mp.base2 c A ψ n) := by
  rcases fr.stored n hn with rfl | ⟨hne, ci, hf, hlp⟩
  · rw [show Expr.substConst0 n value' (.const n []) = value' from by
      rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]]
    rw [fr.selfRead d, dmLeaf,
      show acvalWith mp.base2.acval n A n = A from acvalWith_self]
  · rw [show Expr.substConst0 c value' (.const n []) = .const n []
      from by
      rw [Expr.substConst0, if_neg (fun hh => hne hh.1)]]
    rw [denoteP_levelless_const hf hlp, dmLeaf,
      show acvalWith mp.base2.acval c A n = mp.base2.acval n
        from acvalWith_ne hne]

/-- The `Nat` leaf is not moved by the extension. -/
theorem natLeaf (fr : DmFrameP mp c A value' ψ) :
    dmLeaf mp.base2 c A ψ Setlec.natName
      = mp.base2.acval Setlec.natName ψ := by
  rw [dmLeaf, show acvalWith mp.base2.acval c A Setlec.natName
    = mp.base2.acval Setlec.natName from acvalWith_ne fr.natNe]

/-- Nor is the `Bool` leaf. -/
theorem boolLeaf (fr : DmFrameP mp c A value' ψ) :
    dmLeaf mp.base2 c A ψ Setlec.boolName
      = mp.base2.acval Setlec.boolName ψ := by
  rw [dmLeaf, show acvalWith mp.base2.acval c A Setlec.boolName
    = mp.base2.acval Setlec.boolName from acvalWith_ne fr.boolNe]

end DmFrameP

/-! ## The statement's equation, at a satisfied frame

`dmCertEq1S`/`dmCertEq2S`'s content, with the two hypothesis-slot
shapes factored out: what the certificate delivers depends on the
*frame* being satisfied, not on how many hypotheses it took to satisfy
it.  The caller supplies the four-entry telescope with its two `Nat`
slots at the bottom, the applied proof's frame conditions, and a
satisfying valuation. -/

/-- The frame's `Nat` leaf reads. -/
theorem DmFrameP.readNat {mp : EnvS2PM V μ env} {c : Name}
    {A : (Name → Nat) → AVExpr} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrameP mp c A value' ψ) (d : Nat) :
    denoteP mp.base2.acval env ψ d (Expr.const Setlec.natName [])
      = some (mp.base2.acval Setlec.natName ψ) := by
  rcases fr.stored Setlec.natName (by simp [dmHeadNames]) with
    hc | ⟨-, ci, hf, hlp⟩
  · exact absurd hc fr.natNe
  · exact denoteP_levelless_const hf hlp

/-- The frame's `Bool` leaf reads. -/
theorem DmFrameP.readBool {mp : EnvS2PM V μ env} {c : Name}
    {A : (Name → Nat) → AVExpr} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrameP mp c A value' ψ) (d : Nat) :
    denoteP mp.base2.acval env ψ d (Expr.const Setlec.boolName [])
      = some (mp.base2.acval Setlec.boolName ψ) := by
  rcases fr.stored Setlec.boolName (by simp [dmHeadNames]) with
    hc | ⟨-, ci, hf, hlp⟩
  · exact absurd hc fr.boolNe
  · exact denoteP_levelless_const hf hlp

/-- A `dmLeavesOk` term's leaves are the two `Nat` slots, so the frame
discipline is free for it. -/
theorem dmCtxOkP_natLeaves {mp : EnvS2PM V μ env} {c : Name}
    {A : (Name → Nat) → AVExpr} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrameP mp c A value' ψ) {Δa : List AVExpr}
    (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval Setlec.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval Setlec.natName ψ)
    {e : Expr} (he : dmLeavesOk e = true) :
    CtxOkP mp.base2 ψ 4 Δa (Expr.substConst0 c value' e) := by
  have hself : ∀ k : Nat,
      (mp.base2.acval Setlec.natName ψ).liftN k 0
        = mp.base2.acval Setlec.natName ψ := fun k =>
    AVExpr.liftN_eq_self _
      (by rw [mp.base2.acval_erase]
          exact mp.base2.base.cval_closed Setlec.natName ψ) k
  refine ctxOkP_pinnedLift hlen (fun l hl => ?_)
  rw [fvarLeaves_substConst0 (n := c) fr.valueNoFvar e] at hl
  rcases dmLeavesOk_mem he hl with rfl | rfl
  · refine ⟨by omega, trivial, _, fr.readNat 4, ?_,
      fun ρ _ => ⟨mp.base2.acval_ok2 _ _ ρ, mp.acval_validV _ _ ρ⟩⟩
    show mp.base2.acval Setlec.natName ψ
      = (Δa.getD 3 default).liftN 4 0
    rw [h3, hself 4]
  · refine ⟨by omega, trivial, _, fr.readNat 4, ?_,
      fun ρ _ => ⟨mp.base2.acval_ok2 _ _ ρ, mp.acval_validV _ _ ρ⟩⟩
    show mp.base2.acval Setlec.natName ψ
      = (Δa.getD 2 default).liftN 3 0
    rw [h2, hself 3]

/-- The frame's two `Nat` slots, read off satisfaction. -/
theorem dmSat_slots {mp : EnvS2PM V μ env} {ψ : Name → Nat}
    {Δa : List AVExpr} (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval Setlec.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval Setlec.natName ψ)
    {ρ : Nat → V} (hsat : Sat2 V Δa ρ) (ρ₀ : Nat → V) :
    ρ 3 ∈ˢ interp2 V ρ₀ (mp.base2.acval Setlec.natName ψ) ∧
      ρ 2 ∈ˢ interp2 V ρ₀ (mp.base2.acval Setlec.natName ψ) := by
  have hg : ∀ i : Nat, i < 4 →
      Δa[i]? = some (Δa.getD i default) := by
    intro i hi
    rw [List.getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    rfl
  have e3 := hsat 3 _ (by rw [hg 3 (by omega), h3])
  have e2 := hsat 2 _ (by rw [hg 2 (by omega), h2])
  rw [acval_interp2_closedC mp.base2 _ ψ _ ρ₀] at e3 e2
  exact ⟨e3, e2⟩

/-- **The certificate's equation, at a satisfied frame.**  The
statement's two sides are `Nat`-valued fragments; how the frame's
hypothesis slots came to be satisfied is the caller's business. -/
theorem dmStmtEqP {F : Nat} {mp : EnvS2PM V μ env} {c : Name}
    {A : (Name → Nat) → AVExpr} {value' : Expr} {ψ : Name → Nat}
    (fr : DmFrameP mp c A value' ψ) (heqlaw : EqLawP mp.base2)
    (hacc : ∀ {d : Nat} {e t : Expr},
      Setlec.inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteP mp.base2.acval env ψ d e = some ea)
    (hreads : InferReadsP mp.base2 μ ψ F)
    (hinfC : InferClaims2P μ mp.base2 ψ F)
    (hdeC : DefEqClaims2P μ mp.base2 ψ F)
    {hyps : List Expr} {lhs rhs proof : Expr}
    (hfacts : CertRunFacts μ env F c value'
      (hyps, .app (.app (.app (.const eqName [.succ .zero])
        (.const Setlec.natName [])) lhs) rhs) proof)
    (hlhs : dmNatFrag (dmBinNames c) (dmUnNames c) lhs = true)
    (hrhs : dmNatFrag (dmBinNames c) (dmUnNames c) rhs = true)
    {Δa : List AVExpr} (hlen : Δa.length = 4)
    (h3 : Δa.getD 3 default = mp.base2.acval Setlec.natName ψ)
    (h2 : Δa.getD 2 default = mp.base2.acval Setlec.natName ψ)
    (hWA : Expr.WScoped 4 (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (hBA : (divModCertApplied (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))).looseBVarsBounded 0
      = true)
    (hLA : Expr.LeavesBounded (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (hCA : CtxOkP mp.base2 ψ 4 Δa (divModCertApplied
      (Expr.substConstAll c value' proof)
      (hyps.map (Expr.substConst0 c value'))))
    (ρ4 : Nat → V) (hsat : Sat2 V Δa ρ4) :
    dmEvalV V (fun n => interp2 V ρ4 (dmLeaf mp.base2 c A ψ n))
        (ρ4 3) (ρ4 2) lhs
      = dmEvalV V (fun n => interp2 V ρ4 (dmLeaf mp.base2 c A ψ n))
        (ρ4 3) (ρ4 2) rhs := by
  -- the walk's inputs, at the fixed `Nat` set
  have hmove : ∀ ρ : Nat → V,
      interp2 V ρ (mp.base2.acval Setlec.natName ψ)
        = interp2 V ρ4 (mp.base2.acval Setlec.natName ψ) :=
    fun ρ => acval_interp2_closedC mp.base2 _ ψ ρ ρ4
  have hread : ∀ n ∈ Setlec.natZeroName ::
      (dmBinNames c ++ dmUnNames c), ∀ d' : Nat,
      denoteP mp.base2.acval env ψ d'
        (Expr.substConst0 c value' (.const n []))
        = some (acvalWith mp.base2.acval c A n ψ) :=
    fun n hn d' => fr.read (mem_dmHeadNames hn) d'
  have hbin : ∀ n ∈ dmBinNames c, ∀ ρ : Nat → V,
      DmBinV (interp2 V ρ4 (mp.base2.acval Setlec.natName ψ))
        (interp2 V ρ4 (mp.base2.acval Setlec.natName ψ))
        (interp2 V ρ (acvalWith mp.base2.acval c A n ψ)) := by
    intro n hn ρ
    have h := fr.binHead n hn ρ
    rwa [hmove ρ] at h
  have hun : ∀ n ∈ dmUnNames c, ∀ ρ : Nat → V,
      DmUnV (interp2 V ρ4 (mp.base2.acval Setlec.natName ψ))
        (interp2 V ρ4 (mp.base2.acval Setlec.natName ψ))
        (interp2 V ρ (acvalWith mp.base2.acval c A n ψ)) := by
    intro n hn ρ
    have h := fr.unHead n hn ρ
    rwa [hmove ρ] at h
  have hzero : ∀ ρ : Nat → V,
      interp2 V ρ (acvalWith mp.base2.acval c A Setlec.natZeroName ψ)
        ∈ˢ interp2 V ρ4 (mp.base2.acval Setlec.natName ψ) := by
    intro ρ
    have h := fr.zeroMem ρ
    rwa [hmove ρ] at h
  -- the two sides, walked at depth 4
  obtain ⟨lhsa, hdl, hfl⟩ :=
    dmNatFragP (d := 4) hread fr.leafOk hbin hun hzero lhs hlhs
  obtain ⟨rhsa, hdr, hfr⟩ :=
    dmNatFragP (d := 4) hread fr.leafOk hbin hun hzero rhs hrhs
  -- the slots, at every satisfying valuation
  have hslots : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      ρ 3 ∈ˢ interp2 V ρ4 (mp.base2.acval Setlec.natName ψ) ∧
        ρ 2 ∈ˢ interp2 V ρ4 (mp.base2.acval Setlec.natName ψ) :=
    fun ρ hρ => dmSat_slots hlen h3 h2 hρ ρ4
  -- the statement's reading
  have hnatRead : denoteP mp.base2.acval env ψ 4
      (Expr.substConst0 c value' (.const Setlec.natName []))
      = some (mp.base2.acval Setlec.natName ψ) := by
    rw [fr.read (by simp [dmHeadNames]) 4, fr.natLeaf]
  have hstmt := denoteP_eqSpine (acval := mp.base2.acval) (c := c)
    (value' := value') fr.eqStored hnatRead hdl hdr
  -- the statement's grading
  have hokE : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ ((.app (.app (.app (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.zero.succ])) (mp.base2.acval Setlec.natName ψ)) lhsa)
        rhsa : AVExpr)) := by
    intro ρ hρ
    obtain ⟨hx, hy⟩ := hslots ρ hρ
    obtain ⟨hokl, hml, -⟩ := hfl ρ hx hy
    obtain ⟨hokr, hmr, -⟩ := hfr ρ hx hy
    exact ((heqlaw fr.eqStored _).2 ρ _ lhsa rhsa
      ⟨mp.base2.acval_ok2 _ _ ρ, mp.acval_validV _ _ ρ⟩ hokl hokr
      (by rw [eqSubstP_uN, hmove ρ]; exact fr.natU ρ4)
      (by rw [hmove ρ]; exact hml)
      (by rw [hmove ρ]; exact hmr)).1
  -- the statement's syntactic frame
  obtain ⟨hlL, hbL, hwL⟩ := dmNatFrag_syntax lhs hlhs
  obtain ⟨hlR, hbR, hwR⟩ := dmNatFrag_syntax rhs hrhs
  have hlE : dmLeavesOk (Expr.app (.app (.app
      (.const eqName [.succ .zero]) (.const Setlec.natName [])) lhs)
      rhs) = true := by
    simp only [dmLeavesOk, Expr.fvarLeaves, List.nil_append,
      List.all_append, Bool.and_eq_true]
    exact ⟨hlL, hlR⟩
  have hWE : Expr.WScoped 4 (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const Setlec.natName [])) lhs) rhs)) :=
    wscoped_substConst0 fr.valueNoFvar _
      (dmApp_wscoped (dmApp_wscoped (dmApp_wscoped
        (Expr.WScoped.of_not_hasFvar
          (e := .const eqName [.succ .zero]) rfl)
        (Expr.WScoped.of_not_hasFvar
          (e := .const Setlec.natName []) rfl))
        (hwL 4 (by omega))) (hwR 4 (by omega)))
  have hBE : (Expr.substConst0 c value' (.app (.app (.app
      (.const eqName [.succ .zero]) (.const Setlec.natName [])) lhs)
      rhs)).looseBVarsBounded 0 = true :=
    looseBVarsBounded_substConst0 fr.valueBounded _
      (by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨⟨⟨trivial, trivial⟩, hbL⟩, hbR⟩)
  have hLE : Expr.LeavesBounded (Expr.substConst0 c value'
      (.app (.app (.app (.const eqName [.succ .zero])
        (.const Setlec.natName [])) lhs) rhs)) :=
    dmLeavesOk_leavesBounded
      (dmLeavesOk_substConst0 fr.valueNoFvar hlE)
  have hCE := dmCtxOkP_natLeaves fr hlen h3 h2 hlE
  -- the certificate: the statement is inhabited
  obtain ⟨w, hw⟩ := certValueP mp ψ hacc hreads hinfC hdeC hfacts
    hWA hBA hLA hCA hWE hBE hLE hCE hstmt hokE ρ4 hsat
  -- …hence the two sides are equal
  obtain ⟨hx4, hy4⟩ := hslots ρ4 hsat
  obtain ⟨-, hml4, hel⟩ := hfl ρ4 hx4 hy4
  obtain ⟨-, hmr4, her⟩ := hfr ρ4 hx4 hy4
  rw [show interp2 V ρ4 ((.app (.app (.app (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams
          [Level.zero.succ])) (mp.base2.acval Setlec.natName ψ)) lhsa)
        rhsa : AVExpr))
      = eqv (interp2 V ρ4 lhsa) (interp2 V ρ4 rhsa) from by
    rw [interp2_app, interp2_app, interp2_app]
    exact (heqlaw fr.eqStored _).1 ρ4 _ _ _
      (by rw [eqSubstP_uN]; exact fr.natU ρ4) hml4 hmr4] at hw
  have hlr := eq_of_mem_eqv hw
  show dmEvalV V
      (fun n => interp2 V ρ4 (acvalWith mp.base2.acval c A n ψ))
      (ρ4 (4 - 1 - 0)) (ρ4 (4 - 1 - 1)) lhs
    = dmEvalV V
      (fun n => interp2 V ρ4 (acvalWith mp.base2.acval c A n ψ))
      (ρ4 (4 - 1 - 0)) (ρ4 (4 - 1 - 1)) rhs
  rw [← hel, ← her]
  exact hlr

end Setlec.SetR.Interp2
