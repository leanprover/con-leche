module

public import ConLeche.Model.Inductives.NestedCtorRead
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedRestoreOpen
import ConLeche.Model.Inductives.NestedTransfer
public section

/-!
# The restored constructor's `BlockOpened` (task #315, M6 s9′)

The syntactic half of the reading law: the restored constructor's
opened form satisfies the nested arm's opened-form guard
(`BlockOpened`, `ConLeche/Model/Inductives/BlockRep.lean`) at the
BLOCK's targets — a member target reads as the auxiliary's (the two
differ only at the nested positions), a pin target reads as the pin's
container at the restored components.

The input is `ReadCtx.restoredOpened`'s per-field verdict
(`RestoredField`): at an auxiliary-free position the restored domain
IS the auxiliary one; at a finitary nested position it is the pin
re-opened at the parameter openers applied to the auxiliary index
arguments; at a reflexive nested position the auxiliary telescope over
that.  Every clause of `BlockOpened` is then either the auxiliary
clause transported along the first arm, or the pin's head/length facts
(`rk_restoredPin_getAppFn`, `rk_restoredPin_getAppArgs_length`) with
the auxiliary index arguments' facts.

The `mentionsFvar` conjuncts speak about the RESTORED later fields, so
they are re-derived from each later field's own `RestoredField` arm
(`ReadCtx.boLaterFree`): the pin is closed (`pinsClosed`), the
parameter openers are well-scoped below `nP`, and the index arguments
are the auxiliary's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Syntactic helpers -/

/-- A spine misses a variable when its head and every argument do. -/
theorem bo_mentionsFvar_mkAppN_of_false {q : Nat} :
    ∀ (as : List Expr) (f : Expr), f.mentionsFvar q = false →
      (∀ a ∈ as, a.mentionsFvar q = false) → (Expr.mkAppN f as).mentionsFvar q = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, has =>
    bo_mentionsFvar_mkAppN_of_false as (.app f a)
      (by rw [Expr.mentionsFvar_app, hf, has a List.mem_cons_self]; rfl)
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

/-! ## The reading law's context -/

section Assembly

variable {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}

local notation "ENV₁" => (ConLeche.consMutualFormers (fms.take p.k) env)
local notation "SCR" => (ConLeche.consMutualFormers fms env)
local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

variable {st : ElimState} {envAux : Env} {stored : List AuxStored} {fmsA ctorsA₀ : List ConstantVal}
  {mp₁' : EnvModelM V μ (ConLeche.consMutualFormers (fms.take p.k) env)}
  (C : ReadCtx (V := V) (μ := μ) (env := env) (F := F) (mp := mp) (p := p) (b := b) (fms := fms)
    (f₀ := f₀) (ctorsA := ctorsA) (sortss := sortss) (kinds := kinds) (mp₁ := mp₁) (ppsF := ppsF)
    (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF)
    (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF) (ctorsR := ctorsR)
    (pinsS := pinsS) st envAux stored fmsA ctorsA₀ mp₁')
include C

/-! ### The restored fields, positionally -/

/-- **A restored field variable is the auxiliary's twin**: at every
position the restored opening carries `.fvar (nP + i)` whose
annotation stands to the auxiliary domain in `RestoredField`. -/
theorem ReadCtx.boFieldAt {mm j : Nat} {cA : ConstantVal × Nat} {xFvsRc : List Expr}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hlenX : xFvsRc.length = cA.2)
    (hfields : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
      ∃ ty', xFvsRc[i]? = some (.fvar (b.nP + i) ty') ∧
        RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x ty')
    {i : Nat} {y : Expr} (hy : xFvsRc[i]? = some y) :
    ∃ x : Expr, (xFvsF (b.ownOffset mm + j))[i]? = some x ∧ i < cA.2 ∧
      RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x
        y.fvarTypeD := by
  have hil : i < cA.2 := by
    rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hy).1
  have hxl : i < (xFvsF (b.ownOffset mm + j)).length := by
    rw [(C.h.CD _ _ hJ).xLen]; exact hil
  obtain ⟨x, hx⟩ : ∃ x, (xFvsF (b.ownOffset mm + j))[i]? = some x :=
    ⟨_, List.getElem?_eq_getElem hxl⟩
  obtain ⟨ty', hxR, hRF⟩ := hfields i x hx
  refine ⟨x, hx, hil, ?_⟩
  have hyy : y = Expr.fvar (b.nP + i) ty' := Option.some.inj (hy.symm.trans hxR)
  rw [hyy]
  exact hRF

/-- The parameter openers miss every field variable: they are the
variables `0 … nP-1` and their annotations are well-scoped there. -/
theorem ReadCtx.boParamFree {mm j : Nat} {cA : ConstantVal × Nat}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hPws : ∀ (k : Nat) (x : Expr), (fvsPF (b.ownOffset mm + j))[k]? = some x →
      Expr.WScoped k x.fvarTypeD)
    {q : Nat} (hq : b.nP ≤ q) :
    ∀ v ∈ fvsPF (b.ownOffset mm + j), v.mentionsFvar q = false := by
  intro v hv
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hv
  have hkl : k < (fvsPF (b.ownOffset mm + j)).length := (List.getElem?_eq_some_iff.mp hk).1
  rw [(C.h.CD _ _ hJ).pLen] at hkl
  obtain ⟨ty, rfl⟩ := (C.h.CD _ _ hJ).pIdx k v hk
  have hty : ty.mentionsFvar q = false :=
    ConLeche.rk_mentionsFvar_false_of_WScoped (hPws k _ hk) (by omega)
  simp only [Expr.mentionsFvar_fvar, hty, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
  omega

/-- The restored pin at a nested position misses every field variable
(the pin is closed, the openers are the parameters'). -/
theorem ReadCtx.boPinFree {mm j : Nat} {cA : ConstantVal × Nat}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hPws : ∀ (k : Nat) (x : Expr), (fvsPF (b.ownOffset mm + j))[k]? = some x →
      Expr.WScoped k x.fvarTypeD)
    {qn : NestedPin} (hqn : qn ∈ st.pins) {q : Nat} (hq : b.nP ≤ q) :
    (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
        (Expr.abstractRange qn.pin 0 p.nP 0)).mentionsFvar q = false :=
  ConLeche.rk_restoredPin_mentionsFvar_false (ConLeche.rk_pinsClosed_of C.hclosed qn hqn).1
    (C.boParamFree hJ hPws hq)

/-! ### The later restored fields miss the field variable -/

/-- **A restored later field misses the earlier field's variable**:
whatever arm its own `RestoredField` takes, the auxiliary clause
(`hlater`) supplies the index arguments and the telescope, and the pin
contributes nothing (`boPinFree`). -/
theorem ReadCtx.boLaterFree {mm j : Nat} {cA : ConstantVal × Nat} {xFvsRc : List Expr}
    (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hlenX : xFvsRc.length = cA.2)
    (hPws : ∀ (k : Nat) (x : Expr), (fvsPF (b.ownOffset mm + j))[k]? = some x →
      Expr.WScoped k x.fvarTypeD)
    (hfields : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
      ∃ ty', xFvsRc[i]? = some (.fvar (b.nP + i) ty') ∧
        RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x ty')
    {i : Nat}
    (hlater : ∀ y ∈ (xFvsF (b.ownOffset mm + j)).drop (i + 1),
      y.fvarTypeD.mentionsFvar (b.nP + i) = false) :
    ∀ y ∈ xFvsRc.drop (i + 1), y.fvarTypeD.mentionsFvar (b.nP + i) = false := by
  intro y hy
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hy
  rw [List.getElem?_drop] at hn
  obtain ⟨x, hx, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hn
  have hmem : x ∈ (xFvsF (b.ownOffset mm + j)).drop (i + 1) := by
    refine List.mem_of_getElem? (i := n) ?_
    rw [List.getElem?_drop]; exact hx
  have haux := hlater x hmem
  unfold RestoredField at hRF
  rcases hRF with ⟨-, hty⟩ | ⟨q, qn, hq, -, -, hxeq, hty⟩ |
      ⟨q, qn, tbs, is₀, afvs, is, hq, -, -, -, hstripA, -, hstripR⟩
  · rw [hty]; exact haux
  · have hargs := (ConLeche.mentionsFvar_mkAppN_false
      (fvsPF (b.ownOffset mm + j) ++ x.fvarTypeD.getAppArgs.drop b.nP)
      (.const qn.aux (b.lps.map .param)) (by rw [← hxeq]; exact haux)).2
    rw [hty]
    exact bo_mentionsFvar_mkAppN_of_false _ _
      (C.boPinFree hJ hPws (List.mem_of_getElem? hq) (Nat.le_add_right _ _))
      (fun a ha => hargs a (List.mem_append_right _ ha))
  · have hxty : x.fvarTypeD
        = ConLeche.mkPisB tbs (Expr.mkAppN (.const qn.aux (b.lps.map .param))
          (fvsPF (b.ownOffset mm + j) ++ is₀)) := ConLeche.stripPis_mkPisB _ hstripA
    rw [hxty] at haux
    obtain ⟨hbs, hbody⟩ := ConLeche.rk_mentionsFvar_mkPisB_false_inv tbs _ haux
    have hargs := (ConLeche.mentionsFvar_mkAppN_false _ _ hbody).2
    rw [ConLeche.stripPis_mkPisB _ hstripR]
    refine ConLeche.rk_mentionsFvar_mkPisB_false tbs _ hbs ?_
    exact bo_mentionsFvar_mkAppN_of_false _ _
      (C.boPinFree hJ hPws (List.mem_of_getElem? hq) (Nat.le_add_right _ _))
      (fun a ha => hargs a (List.mem_append_right _ ha))

/-! ### The restored constructor's opened form -/

/-- **THE RESTORED CONSTRUCTOR'S OPENED FORM**: the restored
constructor's opening satisfies the nested arm's opened-form guard
(`BlockOpened`) at the block's targets — the auxiliary clauses at a
member target, the pin's head and argument count at a nested one.

`_hmm` (`mm < p.k`) is carried for the caller's symmetry with the
other per-constructor laws; the proof never needs it (every target
fact comes from the field's own kind). -/
theorem ReadCtx.blockOpened_of {mm j : Nat} {cA : ConstantVal × Nat} {xFvsRc : List Expr}
    (_hmm : mm < p.k) (hJ : ctorsA[b.ownOffset mm + j]? = some cA)
    (hlenX : xFvsRc.length = cA.2)
    (hPws : ∀ (k : Nat) (x : Expr), (fvsPF (b.ownOffset mm + j))[k]? = some x →
      Expr.WScoped k x.fvarTypeD)
    (hfields : ∀ (i : Nat) (x : Expr), (xFvsF (b.ownOffset mm + j))[i]? = some x →
      ∃ ty', xFvsRc[i]? = some (.fvar (b.nP + i) ty') ∧
        RestoredField p st b (mutKsOf kinds (b.ownOffset mm + j)) (fvsPF (b.ownOffset mm + j)) i x ty') :
    BlockOpened env (fun i => (D).memberName ((D).tgts mm j i))
      (fun i => (D).nIdxAt ((D).tgts mm j i)) (fun i => (D).nestOf mm j i) (D).pinAt b.lps b.nP cA.2
      (kindsOf (mutKsOf kinds (b.ownOffset mm + j))) (fvsPF (b.ownOffset mm + j)) xFvsRc
      (xrestF (b.ownOffset mm + j)) := by
  have hCD := C.h.CD (b.ownOffset mm + j) cA hJ
  have hO := hCD.opened
  have hlenP : (fvsPF (b.ownOffset mm + j)).length = b.nP := hCD.pLen
  have hidxP := C.fvsPIdx hJ
  have htgtLt : ∀ i, tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < fms.length :=
    (C.h.ksJ _ _ hJ).2.2
  -- a member target: the block model's tables are the auxiliary's
  have hTof : ∀ i, tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k →
      (D).memberName ((D).tgts mm j i)
        = mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) := by
    intro i hi
    show ((fms.take p.k).map (·.cvTa.name)).getD
      (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) .anonymous = _
    rw [C.hName _ hi, C.memberName (htgtLt i)]
  have hNof : ∀ i, tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k →
      (D).nIdxAt ((D).tgts mm j i)
        = mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) := by
    intro i hi
    show ((fms.take p.k).map (·.nIdx)).getD (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) 0 = _
    rw [C.hNIdx _ hi, (C.h.memT _ _ (fms_get (htgtLt i))).2]
  -- the nested key, read back
  have hnestN : ∀ i, (D).nestOf mm j i = none →
      tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i < p.k := by
    intro i hn
    rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) p.k with h | h
    · exact h
    · rw [(D).nestOf_some (Nat.not_lt.mpr h)] at hn; exact nomatch hn
  have hnestS : ∀ i q, (D).nestOf mm j i = some q →
      tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i = p.k + q := by
    intro i q hn
    rcases Nat.lt_or_ge (tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) p.k with h | h
    · rw [(D).nestOf_none h] at hn; exact nomatch hn
    · rw [(D).nestOf_some (Nat.not_lt.mpr h)] at hn
      have h2 : tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i - p.k = q := Option.some.inj hn
      omega
  -- a pin target: the copy's index count is the pin's
  have hpinIdx : ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
      mutualNIdxOf b.members3 (p.k + q) = (pinsS.getD q default).nIdx := by
    intro q qn hq
    have hql : q < pinsS.length := by
      rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨hlt, -⟩ := C.copyName hq
    rw [(C.h.memT _ _ (fms_get hlt)).2, C.PF.pinNIdx q hql]
  refine ⟨hO.residRes, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- an ordinary field
    intro i x hx hk
    rw [kindsOf_getD'] at hk
    obtain ⟨x₀, hx₀, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hx
    unfold RestoredField at hRF
    rcases hRF with ⟨-, hty⟩ | ⟨-, -, -, -, hk', -, -⟩ |
        ⟨-, -, -, -, -, -, -, -, hk', -, -, -, -⟩
    · rw [hty]; exact hO.ord i x₀ hx₀ hk
    · rw [hk] at hk'; exact nomatch hk'
    · rw [hk] at hk'; exact nomatch hk'
  · -- a recursive field at a member target
    intro i x hx hn hk
    rw [kindsOf_getD'] at hk
    have hlt := hnestN i hn
    obtain ⟨x₀, hx₀, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hx
    unfold RestoredField at hRF
    have hty : x.fvarTypeD = x₀.fvarTypeD := by
      rcases hRF with ⟨-, hty⟩ | ⟨q, -, -, htg, -, -, -⟩ |
          ⟨q, -, -, -, -, -, -, htg, -, -, -, -, -⟩
      · exact hty
      · omega
      · omega
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hO.recF i x₀ hx₀ hk
    have g1 : x.fvarTypeD.getAppFn
        = Expr.const ((D).memberName ((D).tgts mm j i)) (b.lps.map .param) := by
      rw [hty, h1, hTof i hlt]
    have g3 : x.fvarTypeD.getAppArgs.length = b.nP + (D).nIdxAt ((D).tgts mm j i) := by
      rw [hty, h3, hNof i hlt]
    exact ⟨g1, by rw [hty]; exact h2, g3, by rw [hty]; exact h4,
      C.boLaterFree hJ hlenX hPws hfields h5, h6⟩
  · -- a reflexive field at a member target
    intro i x hx hn hk
    rw [kindsOf_getD'] at hk
    have hlt := hnestN i hn
    obtain ⟨x₀, hx₀, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hx
    unfold RestoredField at hRF
    have hty : x.fvarTypeD = x₀.fvarTypeD := by
      rcases hRF with ⟨-, hty⟩ | ⟨q, -, -, htg, -, -, -⟩ |
          ⟨q, -, -, -, -, -, -, htg, -, -, -, -, -⟩
      · exact hty
      · omega
      · omega
    obtain ⟨afvs, body, hopA, hne, hares, hfn, htake, hlen, hres, h5, h6⟩ := hO.reflF i x₀ hx₀ hk
    refine ⟨afvs, body, by rw [hty]; exact hopA, hne, hares, ?_, htake, ?_, hres,
      C.boLaterFree hJ hlenX hPws hfields h5, h6⟩
    · rw [hfn, hTof i hlt]
    · rw [hlen, hNof i hlt]
  · -- a recursive field at a pin target
    intro i x q hx hn hk
    rw [kindsOf_getD'] at hk
    have htg := hnestS i q hn
    obtain ⟨x₀, hx₀, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hx
    unfold RestoredField at hRF
    rcases hRF with ⟨hA, -⟩ | ⟨q', qn, hq, htg', -, hxeq, hty⟩ |
        ⟨-, -, -, -, -, -, -, -, hk', -, -, -, -⟩
    · exfalso
      rcases hA with h | h
      · rw [hk] at h; exact nomatch h
      · omega
    · have hqq : q' = q := by omega
      subst hqq
      have hql : q' < pinsS.length := by
        rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq).1
      obtain ⟨hJn, hpin⟩ := C.PF.pinRec q' qn hq
      have hDs := C.PF.pinDs q' hql (fun _ => 0)
      have hbnd : (Expr.mkAppN (.const qn.container (pinsS.getD q' default).lvls)
          (pinsS.getD q' default).DsE).looseBVarsBounded 0 = true := nt_pin_bounded hDs
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q' hql
      have hnp : (pinsS.getD q' default).nPJ = dJ.nP := by rw [hqe]; exact G.pinNP i' hi'
      have hdl : ((pinsS.getD q' default).Ds (fun _ => 0)).length = dJ.nP := by
        rw [hqe]; exact G.pinDsLen i' hi' (fun _ => 0)
      have hDsLen : (pinsS.getD q' default).DsE.length = (pinsS.getD q' default).nPJ := by
        rw [hDs.length, hdl, hnp]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hO.recF i x₀ hx₀ hk
      have hPargs : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs.length
            = (pinsS.getD q' default).nPJ := by
        rw [hpin, ← C.hnP, ← hDsLen]
        exact ConLeche.rk_restoredPin_getAppArgs_length hlenP hidxP hbnd
      have hisLen : (x₀.fvarTypeD.getAppArgs.drop b.nP).length = (pinsS.getD q' default).nIdx := by
        rw [List.length_drop, h3, htg', hpinIdx q' qn hq]
        omega
      have g1 : x.fvarTypeD.getAppFn
          = Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls := by
        rw [hty, Expr.getAppFn_mkAppN, hpin, hJn, ← C.hnP]
        exact ConLeche.rk_restoredPin_getAppFn hlenP hidxP hbnd
      have g2 : x.fvarTypeD.getAppArgs.length
          = (pinsS.getD q' default).nPJ + (pinsS.getD q' default).nIdx := by
        rw [hty, Expr.getAppArgs_mkAppN, List.length_append, hPargs, hisLen]
      have g3 : ∀ e ∈ x.fvarTypeD.getAppArgs.drop (pinsS.getD q' default).nPJ,
          e.constsResolve env = true := by
        rw [hty, Expr.getAppArgs_mkAppN, List.drop_left' hPargs]
        exact h4
      exact ⟨g1, g2, g3, C.boLaterFree hJ hlenX hPws hfields h5, h6⟩
    · rw [hk] at hk'; exact nomatch hk'
  · -- a reflexive field at a pin target
    intro i x q hx hn hk
    rw [kindsOf_getD'] at hk
    have htg := hnestS i q hn
    obtain ⟨x₀, hx₀, -, hRF⟩ := C.boFieldAt hJ hlenX hfields hx
    unfold RestoredField at hRF
    rcases hRF with ⟨hA, -⟩ | ⟨-, -, -, -, hk', -, -⟩ |
        ⟨q', qn, tbs, is₀, afvs, is, hq, htg', -, hopA, hstripA, hiseq, hstripR⟩
    · exfalso
      rcases hA with h | h
      · rw [hk] at h; exact nomatch h
      · omega
    · rw [hk] at hk'; exact nomatch hk'
    · have hqq : q' = q := by omega
      subst hqq
      have hql : q' < pinsS.length := by
        rw [C.PF.pinsLen]; exact (List.getElem?_eq_some_iff.mp hq).1
      obtain ⟨hJn, hpin⟩ := C.PF.pinRec q' qn hq
      have hDs := C.PF.pinDs q' hql (fun _ => 0)
      have hbnd : (Expr.mkAppN (.const qn.container (pinsS.getD q' default).lvls)
          (pinsS.getD q' default).DsE).looseBVarsBounded 0 = true := nt_pin_bounded hDs
      obtain ⟨q₀, kJ, i', dJ, hqe, hi', G⟩ := C.PF.groups dsR xFvsR q' hql
      have hnp : (pinsS.getD q' default).nPJ = dJ.nP := by rw [hqe]; exact G.pinNP i' hi'
      have hdl : ((pinsS.getD q' default).Ds (fun _ => 0)).length = dJ.nP := by
        rw [hqe]; exact G.pinDsLen i' hi' (fun _ => 0)
      have hDsLen : (pinsS.getD q' default).DsE.length = (pinsS.getD q' default).nPJ := by
        rw [hDs.length, hdl, hnp]
      have hPargs : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)).getAppArgs.length
            = (pinsS.getD q' default).nPJ := by
        rw [hpin, ← C.hnP, ← hDsLen]
        exact ConLeche.rk_restoredPin_getAppArgs_length hlenP hidxP hbnd
      have hheadP : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)).getAppFn
            = Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls := by
        rw [hpin, hJn, ← C.hnP]
        exact ConLeche.rk_restoredPin_getAppFn hlenP hidxP hbnd
      -- the auxiliary opening, identified with the telescope's
      obtain ⟨afvs₂, body₂, hopA₂, hne, hares, -, -, hlen, hres, h5, h6⟩ := hO.reflF i x₀ hx₀ hk
      obtain ⟨hfe₂, hbe₂⟩ := Prod.mk.inj (Option.some.inj (hopA₂.symm.trans hopA))
      subst hfe₂
      subst hbe₂
      have hargsB : (Expr.mkAppN (.const qn.aux (b.lps.map (Level.param)))
          (fvsPF (b.ownOffset mm + j) ++ is)).getAppArgs
            = fvsPF (b.ownOffset mm + j) ++ is := by
        rw [Expr.getAppArgs_mkAppN,
          show (Expr.const qn.aux (b.lps.map (Level.param))).getAppArgs = [] from rfl,
          List.nil_append]
      rw [hargsB, List.length_append, hlenP, htg', hpinIdx q' qn hq] at hlen
      rw [hargsB, List.drop_left' hlenP] at hres
      have hisLen : is.length = (pinsS.getD q' default).nIdx := by omega
      -- the restored telescope, opened
      have hxtyA : x₀.fvarTypeD = ConLeche.mkPisB tbs
          (Expr.mkAppN (.const qn.aux (b.lps.map (Level.param)))
            (fvsPF (b.ownOffset mm + j) ++ is₀)) := ConLeche.stripPis_mkPisB _ hstripA
      have hxtyR : x.fvarTypeD = ConLeche.mkPisB tbs
          (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is₀) := ConLeche.stripPis_mkPisB _ hstripR
      have htbsL : tbs.length = (x₀.fvarTypeD.piBinders).1.length :=
        Expr.stripPis_length _ hstripA
      have hheadB : (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)) is₀).getAppFn
            = Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls := by
        rw [Expr.getAppFn_mkAppN]; exact hheadP
      have hpb : (x.fvarTypeD.piBinders).1.length = tbs.length := by
        rw [hxtyR]
        exact ConLeche.rk_piBinders_mkPisB_length tbs _ hheadB
      obtain ⟨fvs, -, -, hlaw⟩ := ConLeche.openPisAtFvars_mkPisB tbs.length tbs rfl (b.nP + i)
      have hlawA := hlaw (Expr.mkAppN (.const qn.aux (b.lps.map (Level.param)))
        (fvsPF (b.ownOffset mm + j) ++ is₀))
      rw [← hxtyA, htbsL, hopA] at hlawA
      obtain ⟨hfe, -⟩ := Prod.mk.inj (Option.some.inj hlawA)
      subst hfe
      have hlawR := hlaw (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
        (Expr.abstractRange qn.pin 0 p.nP 0)) is₀)
      rw [← hxtyR] at hlawR
      have hP'b : (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
          (Expr.abstractRange qn.pin 0 p.nP 0)).looseBVarsBounded 0 = true :=
        nt_looseBVarsBounded_of_denoteMeta _ _
          (C.pinRead (dsR := dsR) (xFvsR := xFvsR) hq hlenP hidxP (fun _ => 0) i)
      have hbodyR : Expr.instSeq afvs₂ (tbs.length - 1)
          (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is₀)
          = Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is := by
        rw [ConLeche.rk_instSeq_mkAppN, ConLeche.rk_instSeq_eq_self_of_bounded _ _ hP'b,
          htbsL, ← hiseq]
      have g0 : openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (b.nP + i)
          = some (afvs₂, Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is) := by
        rw [hpb, ← hbodyR]; exact hlawR
      have g1 : (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is).getAppFn
          = Expr.const (pinsS.getD q' default).J (pinsS.getD q' default).lvls := by
        rw [Expr.getAppFn_mkAppN]; exact hheadP
      have g2 : (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is).getAppArgs.length
          = (pinsS.getD q' default).nPJ + (pinsS.getD q' default).nIdx := by
        rw [Expr.getAppArgs_mkAppN, List.length_append, hPargs, hisLen]
      have g3 : ∀ e ∈ (Expr.mkAppN (Expr.instSeq (fvsPF (b.ownOffset mm + j)) (b.nP - 1)
            (Expr.abstractRange qn.pin 0 p.nP 0)) is).getAppArgs.drop
              (pinsS.getD q' default).nPJ, e.constsResolve env = true := by
        rw [Expr.getAppArgs_mkAppN, List.drop_left' hPargs]; exact hres
      exact ⟨afvs₂, _, g0, hne, hares, g1, g2, g3,
        C.boLaterFree hJ hlenX hPws hfields h5, h6⟩
  · -- the kinds
    intro i hi
    rw [kindsOf_getD']
    exact hO.kinds i hi

end Assembly

end ConLeche.Model
