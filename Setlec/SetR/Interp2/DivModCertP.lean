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
  | .fvar i _ ty =>
      (i == 0 || i == 1) && ty == Expr.const Setlec.natName []
  | _ => false

/-- **The graded walk.**  A `Nat`-valued statement fragment reads, its
reading is graded, its value is in the frame's `Nat`, and that value is
the `dmEvalV` chain `DivModClausesV` is written in. -/
theorem dmNatFragP {m : EnvS2Core V env} {ψ : Name → Nat}
    {c : Name} {A : (Name → Nat) → AVExpr} {value' : Expr}
    {bins uns : List Name} {d : Nat} {ρ : Nat → V} {natS : V}
    (hread : ∀ n ∈ Setlec.natZeroName :: (bins ++ uns), ∀ d' : Nat,
      denoteP m.acval env ψ d' (Expr.substConst0 c value' (.const n []))
        = some (acvalWith m.acval c A n ψ))
    (hleafOk : ∀ n : Name, AnnotOkP V ρ (acvalWith m.acval c A n ψ))
    (hbin : ∀ n ∈ bins,
      DmBinV natS natS (interp2 V ρ (acvalWith m.acval c A n ψ)))
    (hun : ∀ n ∈ uns,
      DmUnV natS natS (interp2 V ρ (acvalWith m.acval c A n ψ)))
    (hzero : interp2 V ρ
      (acvalWith m.acval c A Setlec.natZeroName ψ) ∈ˢ natS)
    (hx : ρ (d - 1 - 0) ∈ˢ natS) (hy : ρ (d - 1 - 1) ∈ˢ natS) :
    ∀ e : Expr, dmNatFrag bins uns e = true →
      ∃ ea, denoteP m.acval env ψ d
          (Expr.substConst0 c value' e) = some ea ∧
        AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ natS ∧
        interp2 V ρ ea = dmEvalV V
          (fun n => interp2 V ρ (acvalWith m.acval c A n ψ))
          (ρ (d - 1 - 0)) (ρ (d - 1 - 1)) e
  | .app (.app (.const n us) a) b, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hn, rfl⟩, ha⟩, hb⟩ := h
    have hnm : n ∈ bins := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hoka, hma, hea⟩ := dmNatFragP hread hleafOk hbin
      hun hzero hx hy a ha
    obtain ⟨ba, hdb, hokb, hmb, heb⟩ := dmNatFragP hread hleafOk hbin
      hun hzero hx hy b hb
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (.app (acvalWith m.acval c A n ψ) aa) ba, ?_, ?_, ?_, ?_⟩
    · show denoteP m.acval env ψ d
        (.app (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) (Expr.substConst0 c value' b))
        = _
      rw [denoteP_app, denoteP_app, hdn, hda, hdb]
      rfl
    · exact ⟨DmBinV.ok2 (hbin n hnm) hma hmb (hleafOk n).1 hoka.1
        hokb.1 rfl rfl rfl,
        by rw [AnnotValidV_app, AnnotValidV_app]
           exact ⟨⟨(hleafOk n).2, hoka.2⟩, hokb.2⟩⟩
    · rw [interp2_app, interp2_app]
      exact DmBinV.app (hbin n hnm) hma hmb
    · rw [interp2_app, interp2_app, hea, heb]
      rfl
  | .app (.const n us) a, h => by
    simp only [dmNatFrag, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨hn, rfl⟩, ha⟩ := h
    have hnm : n ∈ uns := List.contains_iff_mem.mp hn
    obtain ⟨aa, hda, hoka, hma, hea⟩ := dmNatFragP hread hleafOk hbin
      hun hzero hx hy a ha
    have hdn := hread n (by simp [List.mem_append, hnm]) d
    refine ⟨.app (acvalWith m.acval c A n ψ) aa, ?_, ?_, ?_, ?_⟩
    · show denoteP m.acval env ψ d
        (.app (Expr.substConst0 c value' (.const n []))
          (Expr.substConst0 c value' a)) = _
      rw [denoteP_app, hdn, hda]
      rfl
    · exact ⟨DmUnV.ok1 (hun n hnm) hma (hleafOk n).1 hoka.1 rfl rfl,
        by rw [AnnotValidV_app]; exact ⟨(hleafOk n).2, hoka.2⟩⟩
    · rw [interp2_app]
      exact DmUnV.app (hun n hnm) hma
    · rw [interp2_app, hea]
      rfl
  | .const n us, h => by
    simp only [dmNatFrag, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, hread _ (by simp) d, hleafOk _, hzero, rfl⟩
  | .fvar i nm ty, h => by
    simp only [dmNatFrag, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    rcases hi with rfl | rfl
    · refine ⟨.bvar (d - 1 - 0), ?_, ⟨by simp, by simp⟩, ?_, ?_⟩
      · show denoteP m.acval env ψ d
          (.fvar 0 nm (.const Setlec.natName [])) = _
        rw [denoteP_fvar]
      · rw [interp2_bvar]; exact hx
      · rw [interp2_bvar]; rfl
    · refine ⟨.bvar (d - 1 - 1), ?_, ⟨by simp, by simp⟩, ?_, ?_⟩
      · show denoteP m.acval env ψ d
          (.fvar 1 nm (.const Setlec.natName [])) = _
        rw [denoteP_fvar]
      · rw [interp2_bvar]; exact hy
      · rw [interp2_bvar]; rfl
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

end Setlec.SetR.Interp2
