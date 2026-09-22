module

import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Semantics.Tower.BlockRecKitI
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Capstone
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.FixStageFormer
import ConLeche.Semantics.Tower.FixSquashI

public section

/-!
# G1 — `ResidueOk` from the rule stage's TYPING certificates (task #315, M5)

`checkBlockRule` (`Kernel/Inductives/BlockInstall.lean`) closes with
two runs at the CONSTRUCTORS' environment `envT`, at the depth
`d = rP + nF + nR` of the opened frame

```
p⃗ (the rP stretch)   f⃗ (the constructor's fields)   ih⃗ (the openers)
```

namely

```lean
let tyB ← opsT.inferType envT depth bodyO
unless ← opsT.isDefEq envT depth tyB concl do throw …
```

with `concl` the recursor's OWN conclusion instantiated at the rule's
prefix, the constructor's index expressions and the major `C_J p⃗ f⃗`.
`ResidueOk` (`Semantics/Tower/BlockRecI.lean`) is what the three
regimes consume of those two runs:

```lean
def ResidueOk (V) (Rb : AnnotTerm) (ihvals : List V) (ρ' : Nat → V) (B : V) : Prop :=
  WellDenoted V (consList ihvals ρ') Rb ∧ interp V (consList ihvals ρ') Rb ∈ˢ B
```

This file is the hop between the two, and it has exactly three parts.

* **The certified hop** (`residueOk_of_certs`): `InferClaim` at the
  residue plus `DefEqClaim` between the inferred type and the
  conclusion, both at the frame's context `Δa`, give membership at
  every `Δa`-satisfying valuation.  This is `sidesMem`
  (`Model/IndFire.lean`) with one side instead of two, packaged as
  `ResidueOk`; the k = 0 precedent is `checkConstantVal_reads`
  (`BlockRecRead.lean`), and **what is new is only that the context is
  not nil** — everything else is the same three lemmas.
* **The frame's valuation** (`sat_blockFrame`): the context is
  `ihdoms.reverse ++ (pdoms ++ fdoms).reverse` and `Sat` at it is two
  applications of `sat_of_spineFit` — the regimes' own
  `SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs)` for the prefix and
  the fields, and one `SpineFit` for the `ih` openers.  The second is
  where the regimes pay: the opener's value must lie in the opener's
  DOMAIN (WF: `graph_mem_B` at the kit's graph; IND: `pt` in the
  truth value).
* **The frame's context** (`ctxOk_blockFrame`): the frame is opened by
  THREE `openPisAtFvars` calls at the consecutive offsets `0`, `rP`
  and `rP + nF`, so the openers' concatenation is an
  `∃ ty, x = .fvar i ty` list and `ctxOk_of_openers`
  (`Model/IndFrame.lean`) applies unchanged.

**Where the two runs come from.**  `checkBlockRule_facts`
(`Verify/Inductives/BlockWF.lean`, lane V2) peels the stage's bind
chain but stops at SCOPING — fvar-freedom, level closure, resolution
and `looseBVarsBounded` of the returned right-hand side — and V2's
report says so in as many words ("the stage facts stop at scoping …
it says nothing about what the stage CHECKED").  §6 below is the SAME
peel with the typing witnesses kept (`checkBlockRule_typing`), so G1
is a fact about the CHECK and not about a pair of hypothetical runs.
That theorem belongs beside `checkBlockRule_facts`; it is here only
because this lane owns one file.

What stays a premise is the SEAM to the other halves of M5: `hdoms`,
saying that opener `i`'s stored type reads to the context entry at
that slot (O-2's type readings and G2's per-binder `checkDefEqList`),
`hokΔ`, the context's own grading, and the `ih` openers' `SpineFit`,
which is the regime's to pay.

**The grade, checked and not assumed** (the brief's question): the
stage runs `opsT.inferType`, which at `μ = .verified` is
`inferTypeCore .verified`, and `Rules.inferTypeCore_bridge`
(`Verify/Rules/Bridge.lean`) sends that to `Infer env .full` — never
`.io`, which only `inferTypeCoreIO` reaches. So the residue's typing
IS at the grade G3's argument inversion
(`infer_mkAppN_inv_full`, `BlockRecRegimes.lean`) needs, and the two
halves of G1/G3 compose without a grade side condition.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The certified hop — `InferClaim` + `DefEqClaim` at a context -/

/-- **The residue's typing, converted at a context** — `sidesMem`
(`Model/IndFire.lean`) with ONE side.  The residue's reading inhabits
the conclusion's reading at every valuation satisfying the frame's
context, and is graded there.

`hctxT`, the inferred type's own context correspondence, is DERIVED
(`CtxOk.of_subset` along `inferTypeCore_fvarLeaves`): an inferred
type's leaves are the subject's, so nothing new has to be built for
it. -/
theorem residueMem_of_certs {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F d : Nat}
    {res ty concl : Expr} {Δa : List AnnotTerm} {Rb Ca : AnnotTerm}
    (hinf : ConLeche.inferTypeCore μ envT F d res = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F d ty concl = .ok true)
    (hwsR : Expr.WScoped d res) (hbR : res.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded res)
    (hwsC : Expr.WScoped d concl) (hbC : concl.looseBVarsBounded 0 = true)
    (hLC : Expr.LeavesBounded concl)
    (hctxR : CtxOk mp.base2 ψ d Δa res)
    (hctxC : CtxOk mp.base2 ψ d Δa concl)
    (hRb : denoteMeta mp.base2.acval envT ψ d res = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ d concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ca) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Rb) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ Rb ∈ˢ interp V ρ Ca := by
  obtain ⟨-, -, ihd, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  -- the inferred type's syntax, and its context correspondence
  have hleafT : ∀ l ∈ ty.fvarLeaves, l ∈ res.fvarLeaves :=
    ConLeche.inferTypeCore_fvarLeaves mp.base2.wf F hinf hwsR
  have hwsT : Expr.WScoped d ty :=
    ConLeche.inferTypeCore_WScoped mp.base2.wf F hinf hwsR
  have hbT : ty.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeCore_looseBVars mp.base2.wf F hinf hwsR hbR hLR
  have hLT : Expr.LeavesBounded ty := fun l hl => hLR l (hleafT l hl)
  have hctxT : CtxOk mp.base2 ψ d Δa ty := CtxOk.of_subset hctxR hleafT
  obtain ⟨ta, hta⟩ :=
    inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ) hinf hwsR hbR hLR hctxR hRb
  obtain ⟨hokR, hokT, hmem⟩ := ihi hinf hwsR hbR hLR hctxR hRb hta
  refine ⟨hokR, fun ρ hρ => ?_⟩
  have heq := ihd hdeq hwsT hbT hLT hwsC hbC hLC hctxT hctxC hta hCa hokT hokC ρ hρ
  exact heq ▸ hmem ρ hρ

/-- **G1, at one valuation**: `ResidueOk` in the shape
`hres_of_residueOk` and `famCand_hCand`'s `hst` consume — the residue
reads, is graded, and lands in the conclusion's reading, at the frame
`ρ'` extended by the `ih` openers' VALUES. -/
theorem residueOk_of_certs {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F d : Nat}
    {res ty concl : Expr} {Δa : List AnnotTerm} {Rb Ca : AnnotTerm}
    {ihvals : List V} {ρ' : Nat → V}
    (hinf : ConLeche.inferTypeCore μ envT F d res = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F d ty concl = .ok true)
    (hwsR : Expr.WScoped d res) (hbR : res.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded res)
    (hwsC : Expr.WScoped d concl) (hbC : concl.looseBVarsBounded 0 = true)
    (hLC : Expr.LeavesBounded concl)
    (hctxR : CtxOk mp.base2 ψ d Δa res)
    (hctxC : CtxOk mp.base2 ψ d Δa concl)
    (hRb : denoteMeta mp.base2.acval envT ψ d res = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ d concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ca)
    (hsat : Sat V Δa (consList ihvals ρ')) :
    ResidueOk V Rb ihvals ρ' (interp V (consList ihvals ρ') Ca) := by
  obtain ⟨hok, hmem⟩ :=
    residueMem_of_certs hμ mp hinf hdeq hwsR hbR hLR hwsC hbC hLC hctxR hctxC hRb hCa hokC
  exact ⟨(hok _ hsat).1, hmem _ hsat⟩

/-! ## 2. The frame's valuation — `Sat` at `ih⃗ ⊕ f⃗ ⊕ p⃗` -/

/-- **The opened frame's context is satisfied by the frame's own
values.**  The frame is three telescopes deep and `Sat` at it is two
`sat_of_spineFit`s: the regimes hand over
`SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs)` verbatim (it is
`blockRecPre_kit`'s and `blockRecPre_ind`'s own hypothesis at
`ρ₀ := chainFrame K cand ρ`), and the `ih` openers' fit is the one
thing a REGIME has to pay for: the opener's value must lie in the
opener's DOMAIN — in WF that is the kit's graph (`graph_mem_B`), in
IND the truth value (`pt`).

The context's orientation is `Sat`'s own: innermost first, so the
`ih` block comes first and each telescope is reversed. -/
theorem sat_blockFrame {ρ₀ : Nat → V} {pdoms fdoms ihdoms : List AnnotTerm}
    {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse)
      (consList ihvals (consList (xs ++ fs) ρ₀)) :=
  sat_of_spineFit (by simpa using sat_of_spineFit (Sat_nil V ρ₀) hsp) hih

/-- The frame's context has the frame's own length — the `Δa.length = d`
half of `CtxOk`, read off the two telescopes. -/
theorem sat_blockFrame_length {pdoms fdoms ihdoms : List AnnotTerm}
    {rP nF nR : Nat} (hp : pdoms.length = rP) (hf : fdoms.length = nF)
    (hi : ihdoms.length = nR) :
    (ihdoms.reverse ++ (pdoms ++ fdoms).reverse).length = rP + nF + nR := by
  simp only [List.length_append, List.length_reverse, hp, hf, hi]
  omega

/-! ## 3. The frame's context — three openings at consecutive offsets -/

/-- **Opener lists at consecutive offsets concatenate**: entry `j` of
`fvs₁ ++ fvs₂` is the free variable `i + j`.  Stated over the INDEX
FACT rather than over `openPisAtFvars` itself so that it chains — the
rule frame is THREE openings deep (`openPisAtFvars rP recTy 0`,
`openPisAtFvars nF crest rP`, `openPisAtFvars nR ihTele (rP + nF)`)
and the middle list is not itself an opening's result.

It is all `ctxOk_of_openers`'s `hshape` asks of the frame. -/
theorem openers_append_index {i n₁ : Nat} {fvs₁ fvs₂ : List Expr}
    (h₁ : ∀ (j : Nat) (x : Expr), fvs₁[j]? = some x → ∃ ty, x = Expr.fvar (i + j) ty)
    (hlen₁ : fvs₁.length = n₁)
    (h₂ : ∀ (j : Nat) (x : Expr), fvs₂[j]? = some x → ∃ ty, x = Expr.fvar (i + n₁ + j) ty) :
    ∀ (j : Nat) (x : Expr), (fvs₁ ++ fvs₂)[j]? = some x → ∃ ty, x = Expr.fvar (i + j) ty := by
  intro j x hx
  rcases Nat.lt_or_ge j fvs₁.length with hj | hj
  · rw [List.getElem?_append_left hj] at hx
    exact h₁ j x hx
  · rw [List.getElem?_append_right hj] at hx
    obtain ⟨ty, hty⟩ := h₂ (j - fvs₁.length) x hx
    rw [hlen₁] at hj
    exact ⟨ty, by rw [hty, hlen₁]; congr 1; omega⟩

/-- An opening's own index fact, at its offset — `openPisAtFvars_index`
with the arguments in the shape `openers_append_index` chains at. -/
theorem openers_index {n i : Nat} {e : Expr} {fvs : List Expr} {b : Expr}
    (h : openPisAtFvars n e i = some (fvs, b)) :
    ∀ (j : Nat) (x : Expr), fvs[j]? = some x → ∃ ty, x = Expr.fvar (i + j) ty :=
  openPisAtFvars_index n e i h

/-- **The opener list's own bound**: an opener sits at its own index,
so an index read off the list is below the list's length. -/
theorem openers_lt {fvs : List Expr} {e : Expr}
    (hshape : ∀ (j : Nat) (x : Expr), fvs[j]? = some x → ∃ ty, x = Expr.fvar j ty) :
    ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs → l.1 < fvs.length := by
  intro l _ hmem
  obtain ⟨p, hp⟩ := List.getElem?_of_mem hmem
  obtain ⟨ty, hty⟩ := hshape p _ hp
  have hpl : p < fvs.length := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    omega
  obtain ⟨h1, -⟩ : l.1 = p ∧ l.2 = ty := by
    injection hty with a b
    exact ⟨a, b⟩
  omega

/-! ## 4. `CtxOk` at the rule frame -/

/-- **`CtxOk` at the rule stage's opened frame.**  The frame is
`p⃗ (the rP stretch) f⃗ ih⃗`, opened by three `openPisAtFvars` calls at
the offsets `0`, `rP` and `rP + nF`; any term whose free variables are
among those openers — the residue `bodyO` and the conclusion `concl`
both are — correlates with the context `Δa` at the frame's full depth.

`hdoms` is the SEAM to O-2 and G2: it says that opener `i`'s STORED
type reads to the context's entry at that slot.  For the prefix and
the field openers those entries are the recursor type's and the
constructor telescope's binder domains (`rds`, `pdoms`/`fdoms`); for
the `ih` openers they are the generated `blockIhPis` domains.  The
per-binder `checkDefEqList` of G2 is what makes the rule's own
λ-domains agree with them. -/
theorem ctxOk_blockFrame {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {rP nF nR : Nat} {recTy crest ihTele : Expr}
    {fvsPref fvsF fvsIh : List Expr} {o₁ o₂ o₃ : Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    (hw₁ : Expr.WScoped 0 recTy) (hw₂ : Expr.WScoped rP crest)
    (hw₃ : Expr.WScoped (rP + nF) ihTele)
    {Δa : List AnnotTerm} (hlen : Δa.length = rP + nF + nR)
    (hdoms : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x)
        = some (Δa.getD (rP + nF + nR - 1 - i) default))
    (hokΔ : ∀ i, i < rP + nF + nR → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
        (Δa.getD (rP + nF + nR - 1 - i) default))
    {e : Expr}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh) :
    CtxOk m φ (rP + nF + nR) Δa e := by
  have hl₁ : fvsPref.length = rP := openPisAtFvars_length rP h₁
  have hl₂ : fvsF.length = nF := openPisAtFvars_length nF h₂
  have hl₃ : fvsIh.length = nR := openPisAtFvars_length nR h₃
  have hlenF : (fvsPref ++ fvsF ++ fvsIh).length = rP + nF + nR := by
    simp only [List.length_append, hl₁, hl₂, hl₃]
  -- the shape, by chaining the three openings
  have hs₁₂ : ∀ (j : Nat) (x : Expr), (fvsPref ++ fvsF)[j]? = some x →
      ∃ ty, x = Expr.fvar (0 + j) ty :=
    openers_append_index (n₁ := rP) (openers_index h₁) hl₁
      (by simpa using openers_index h₂)
  have hshape : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      ∃ ty, x = Expr.fvar i ty := by
    have := openers_append_index (i := 0) (n₁ := rP + nF) hs₁₂
      (by simp [hl₁, hl₂]) (by simpa using openers_index h₃)
    simpa using this
  -- the openers' scoping, at the frame's full depth
  have hws : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, Expr.WScoped (rP + nF + nR) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · rcases List.mem_append.mp hx' with hx'' | hx''
      · exact ((openPisAtFvars_WScoped rP recTy 0 h₁ hw₁).1 x hx'').mono (by omega)
      · exact ((openPisAtFvars_WScoped nF crest rP h₂ hw₂).1 x hx'').mono (by omega)
    · exact ((openPisAtFvars_WScoped nR ihTele (rP + nF) h₃ hw₃).1 x hx').mono (by omega)
  refine ctxOk_of_openers m.acval_closed (fvs := fvsPref ++ fvsF ++ fvsIh)
    (Aa := fun i => Δa.getD (rP + nF + nR - 1 - i) default) hlen hshape hws hdoms
    hleaf ?_ ?_ hokΔ
  · intro l hl
    have := openers_lt (e := e) hshape l hl (hleaf l hl)
    omega
  · intro i hi
    rw [List.getD, List.getElem?_eq_getElem (by omega)]
    rfl

/-- A term whose free variables are among the openers has bounded leaf
annotations as soon as the OPENERS do — `Expr.LeavesBounded`, which
`InferClaim` asks of every subject, read off the frame once. -/
theorem leavesBounded_of_openers {fvs : List Expr} {e : Expr}
    (hlbF : ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    Expr.LeavesBounded e := fun l hl => hlbF _ (hleaf l hl)

/-! ## 5. G1, assembled at the rule frame -/

/-- **G1 at the rule frame** — the lane's deliverable.  From

* the stage's two TYPING runs at the constructors' environment
  (`inferTypeCore` on the opened residue, `isDefEqCore` against the
  recursor's conclusion at the rule's prefix, the constructor's index
  expressions and the major) — see the module docstring on why these
  are premises and not `checkBlockRule_facts` projections;
* the frame's three openings and the seam `hdoms`/`hokΔ` to O-2/G2;
* the regimes' own `SpineFit` for the prefix and the fields, and the
  `ih` openers' fit, which is what a regime pays for (WF:
  `graph_mem_B`; IND: `pt`),

`ResidueOk` follows in the shape `hres_of_residueOk` and
`famCand_hCand`'s `hst` consume.

The residue's and the conclusion's `WScoped` are DERIVED from the
frame (`CtxOk.wScoped`), and their `LeavesBounded` from the openers'
own annotations (`leavesBounded_of_openers`); what is irreducibly
per-term is `looseBVarsBounded 0`, which the stage checks on the rule's
input right-hand side and `annotateCore_looseBVars` carries across the
annotation. -/
theorem residueOk_blockFrame {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F rP nF nR : Nat}
    {recTy crest ihTele : Expr} {fvsPref fvsF fvsIh : List Expr} {o₁ o₂ o₃ : Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    (hw₁ : Expr.WScoped 0 recTy) (hw₂ : Expr.WScoped rP crest)
    (hw₃ : Expr.WScoped (rP + nF) ihTele)
    (hlbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    {pdoms fdoms ihdoms : List AnnotTerm}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hdoms : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default))
    (hokΔ : ∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default))
    {bodyO ty concl : Expr} {Rb Ca : AnnotTerm}
    (hinf : ConLeche.inferTypeCore μ envT F (rP + nF + nR) bodyO = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F (rP + nF + nR) ty concl = .ok true)
    (hbR : bodyO.looseBVarsBounded 0 = true) (hbC : concl.looseBVarsBounded 0 = true)
    (hleafR : ∀ l ∈ bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hleafC : ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hRb : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) bodyO = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
      WellDenotedV V ρ Ca)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals) :
    ResidueOk V Rb ihvals (consList (xs ++ fs) ρ₀)
      (interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Ca) := by
  have hlen := sat_blockFrame_length hp hf hidx
  have hctxR := ctxOk_blockFrame (V := V) h₁ h₂ h₃ hw₁ hw₂ hw₃ hlen hdoms hokΔ hleafR
  have hctxC := ctxOk_blockFrame (V := V) h₁ h₂ h₃ hw₁ hw₂ hw₃ hlen hdoms hokΔ hleafC
  exact residueOk_of_certs hμ mp hinf hdeq hctxR.wScoped hbR
    (leavesBounded_of_openers hlbF hleafR) hctxC.wScoped hbC
    (leavesBounded_of_openers hlbF hleafC) hctxR hctxC hRb hCa hokC
    (sat_blockFrame hsp hih)

/-- **Regime IND's `hres`, from the stage's runs** — the consumer
`hres_of_residueOk` (`Model/Inductives/BlockRecRegimes.lean`) applied
to `residueOk_blockFrame`.  `hT` is the conclusion's reading being a
TRUTH VALUE, which at `ℓ = 0` is O-2's fact about the recursor's stored
conclusion and not this lane's. -/
theorem hres_of_blockFrame {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F rP nF nR : Nat}
    {recTy crest ihTele : Expr} {fvsPref fvsF fvsIh : List Expr} {o₁ o₂ o₃ : Expr}
    (h₁ : openPisAtFvars rP recTy 0 = some (fvsPref, o₁))
    (h₂ : openPisAtFvars nF crest rP = some (fvsF, o₂))
    (h₃ : openPisAtFvars nR ihTele (rP + nF) = some (fvsIh, o₃))
    (hw₁ : Expr.WScoped 0 recTy) (hw₂ : Expr.WScoped rP crest)
    (hw₃ : Expr.WScoped (rP + nF) ihTele)
    (hlbF : ∀ x ∈ fvsPref ++ fvsF ++ fvsIh, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    {pdoms fdoms ihdoms : List AnnotTerm}
    (hp : pdoms.length = rP) (hf : fdoms.length = nF) (hidx : ihdoms.length = nR)
    (hdoms : ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF ++ fvsIh)[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (rP + nF + nR - 1 - i) default))
    (hokΔ : ∀ i, i < rP + nF + nR →
      ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
        WellDenotedV V (fun j => ρ (j + (rP + nF + nR - 1 - i) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD (rP + nF + nR - 1 - i) default))
    {bodyO ty concl : Expr} {Rb Ca : AnnotTerm}
    (hinf : ConLeche.inferTypeCore μ envT F (rP + nF + nR) bodyO = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F (rP + nF + nR) ty concl = .ok true)
    (hbR : bodyO.looseBVarsBounded 0 = true) (hbC : concl.looseBVarsBounded 0 = true)
    (hleafR : ∀ l ∈ bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hleafC : ∀ l ∈ concl.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF ++ fvsIh)
    (hRb : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) bodyO = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ (rP + nF + nR) concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) ρ →
      WellDenotedV V ρ Ca)
    {ρ₀ : Nat → V} {xs fs ihvals : List V}
    (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hih : SpineFit (consList (xs ++ fs) ρ₀) ihdoms ihvals)
    (hT : interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Ca ∈ˢ (univZero : V)) :
    ∃ T : V, T ∈ˢ (univZero : V) ∧
      interp V (consList ihvals (consList (xs ++ fs) ρ₀)) Rb ∈ˢ T :=
  ⟨_, hT, (residueOk_blockFrame hμ mp h₁ h₂ h₃ hw₁ hw₂ hw₃ hlbF hp hf hidx hdoms hokΔ
    hinf hdeq hbR hbC hleafR hleafC hRb hCa hokC hsp hih).2⟩

/-! ## 6. The stage's own runs, named

`checkBlockRule_facts` (`Verify/Inductives/BlockWF.lean`) peels the
same bind chain and DISCARDS every witness but the four scoping facts
`EnvWF` needs.  This is that peel with the typing witnesses KEPT — the
two runs `residueOk_blockFrame` consumes, the three openings that
build the frame, and the conclusion the residue is compared against.
It belongs beside `checkBlockRule_facts` in the Verify tier
(V2's open item 3); it is here because this lane owns one file. -/

section Inversion

open ConLeche (checkBlockRule BlockShape ConstantVal BlockFieldKind Level BlockRuleFrame)

local macro "close_throw " h:term : tactic =>
  `(tactic| first
      | exact nomatch $h
      | exact absurd $h (by
          simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          exact fun hh => nomatch hh)
      | exact absurd $h
          (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- **Stage (c)'s TYPING certificates, named.**  A successful
`checkBlockRule` ran, at the CONSTRUCTORS' environment `envT` and at
the depth of the frame it opened,

* `inferTypeCore` on the opened residue `bodyO`, and
* `isDefEqCore` between its result and the recursor's own conclusion
  instantiated at the rule's prefix, the constructor's index
  expressions and the major `C_J p⃗ f⃗`,

and the frame is the three openings at the offsets `0`, `rP` and
`rP + nF`.  Feeding these to `residueOk_blockFrame` is what makes G1 a
fact about the CHECK rather than about a pair of hypothetical runs. -/
theorem checkBlockRule_typing {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind}
    {rhs out : Expr} {F : Nat}
    (h : checkBlockRule (ConLeche.fueledOps μ F) envR (ConLeche.fueledOps μ F) envT p
      recNames rlvls recTys mIs rPs recTgts ri cvR cA ks rhs = .ok out) :
    ∃ (recTy crest ihTele : Expr) (fvsPref fvsF fvsIh : List Expr)
      (o₁ cbody bodyO ty concl : Expr),
      recTys[ri]? = some recTy ∧
      openPisAtFvars (p.rulePrefixAt ri) recTy 0 = some (fvsPref, o₁) ∧
      openPisAtFvars cA.2 crest (p.rulePrefixAt ri) = some (fvsF, cbody) ∧
      openPisAtFvars
          (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length
          (ihTele.instantiateList (fvsPref ++ fvsF).reverse)
          (p.rulePrefixAt ri + cA.2) = some (fvsIh, bodyO) ∧
      ConLeche.inferTypeCore μ envT F
          (p.rulePrefixAt ri + cA.2 +
            (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
          bodyO = .ok ty ∧
      Expr.instPisAtLift
          (fvsPref ++ cbody.getAppArgs.drop p.nP ++
            [Expr.mkAppN (.const cA.1.name (p.lps.map .param)) (fvsPref.take p.nP ++ fvsF)])
          recTy = some concl ∧
      ConLeche.isDefEqCore μ envT F
          (p.rulePrefixAt ri + cA.2 +
            (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
          ty concl = .ok true := by
  unfold checkBlockRule at h
  obtain ⟨recTy, hrecTy, h⟩ := exceptBind_ok h
  by_cases hbv : Expr.looseBVarsBounded 0 rhs = true
  case neg => rw [if_neg hbv] at h; close_throw h
  rw [if_pos hbv] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  obtain ⟨rhsA, _, h⟩ := exceptBind_ok h
  by_cases hlp : Expr.allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : Expr.constsResolve envR rhsA = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  -- the rule's own typing at the rule-less recursor environment
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨x1, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x1
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h; obtain ⟨fvsPref, o₁⟩ := x2
  obtain ⟨x3, _, h⟩ := exceptBind_ok h; obtain ⟨_, crest⟩ := x3
  obtain ⟨x4, hx4, h⟩ := exceptBind_ok h; obtain ⟨fvsF, cbody⟩ := x4
  obtain ⟨x5, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x5
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨ihTele, _, h⟩ := exceptBind_ok h
  obtain ⟨x9, hx9, h⟩ := exceptBind_ok h; obtain ⟨fvsIh, bodyO⟩ := x9
  obtain ⟨ty, hty, h⟩ := exceptBind_ok h
  obtain ⟨concl, hconcl, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  subst hd
  exact ⟨recTy, crest, ihTele, fvsPref, fvsF, fvsIh, o₁, cbody, bodyO, ty, concl,
    ConLeche.unwrapOr_ok hrecTy, ConLeche.unwrapOr_ok hx2, ConLeche.unwrapOr_ok hx4,
    ConLeche.unwrapOr_ok hx9, hty, ConLeche.unwrapOr_ok hconcl, hb⟩

end Inversion

/-! ## 4. THE TWO-FRAME BRIDGE — the rule's frame against the block's
(task #315, M5M-rule)

The IND arm's `ih` leaf (`blockIndIhLeaf_pred`, `BlockRecPreRun.lean`)
is proved from the BLOCK's side: the constructor's walk at the field's
position, whose index expressions and telescope are the readings at
the FIELD's own frame

```
  a⃗ (the parameters)   f⃗.take i (the earlier fields)   b⃗ (the telescope)
```

while the rule body's guarded call is read at the RULE's frame

```
  x⃗ (the recursor's prefix: parameters, motive(s), minors)   f⃗ (ALL
  the fields)   b⃗ (the telescope)
```

and the two frames agree nowhere past `b⃗`: `consList` puts the LAST
value at index 0, so the rule frame's index `0` is `f⃗`'s last field
and the block frame's is field `i - 1`.  The bridge is therefore not a
congruence but the evaluation of the rule lane's own MOVE, `ihIdxAtM`
(`Semantics/Tower/IhSpell.lean`): the rule spells the field's
expression lifted past the `nF - i` later fields (at the telescope's
cutoff) and past the prefix's `o = rP - nP` extra binders (at the
fields' cutoff), and each lift cancels against exactly the block the
rule frame carries and the block frame does not.

`interp_ihIdxAtM` (`Semantics/Tower/FixSquashI.lean`) is the same
statement for the NATIVE route's frame, where the prefix is spelled
`ms ++ [M]` — the minors over the motive — above the parameter frame.
The block route's prefix is ONE list `x⃗` with `x⃗.take nP = a⃗`, so the
lemma is restated here at that shape rather than instantiated: `o` is
then `x⃗.drop nP`'s length and never has to be split.

Three forms cross: a single index expression (`interp_ihIdxAtM_rule`),
the field's telescope as a FIT (`spineFit_ihTeleAtR_rule`, the same
cancellation carried down the telescope, where the cutoff grows with
the spine already consumed) and the applied field
(`interp_fieldApp_rule`, a bvar that lands on `f⃗`'s `i`-th entry, over
the telescope's own variables). -/

section TwoFrame

open ConLeche.Semantics

variable {ρ : Nat → V}

omit [SetTheory V] in
/-- The rule's frame, regrouped: the telescope over ALL the fields
over the prefix. -/
theorem consList_ruleFrame (bs xs fs : List V) (ρ : Nat → V) :
    consList bs (consList (xs ++ fs) ρ) = consList (fs ++ bs) (consList xs ρ) := by
  rw [consList_append, consList_append]

omit [SetTheory V] in
/-- **Dropping a frame's tail**: the values past `k` are exactly the
`shiftE` a lift at cutoff `0` performs. -/
theorem shiftE_drop_consList {n : Nat} (L : List V) (k : Nat)
    (hk : (L.drop k).length = n) (Z : Nat → V) :
    shiftE n 0 (consList L Z) = consList (L.take k) Z := by
  have h : consList L Z = consList (L.drop k) (consList (L.take k) Z) := by
    rw [← consList_append, List.take_append_drop]
  rw [h, ← hk, shiftE_consList]

/-- **One index expression across the two frames.**  `ihIdxAtM`'s
outer lift (`o`, at the fields' cutoff) cancels the prefix's extra
binders `x⃗.drop nP`; its inner lift (`nF - i`, at the telescope's
cutoff) cancels the later fields `f⃗.drop i`. -/
theorem interp_ihIdxAtM_rule {nF o i m : Nat} {xs fs bs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) (hbl : bs.length = m) (E : AnnotTerm) :
    interp V (consList bs (consList (xs ++ fs) ρ)) (ihIdxAtM nF o i 0 m E)
      = interp V (consList bs (consList (fs.take i) (consList as ρ))) E := by
  have hdrop : (xs.drop as.length).length = o := by
    rw [List.length_drop, hxl]; omega
  have hfd : (fs.drop i).length = nF - i := by rw [List.length_drop, hfl]
  have e1 : shiftE o (nF + m) (consList bs (consList (xs ++ fs) ρ))
      = consList (fs ++ bs) (consList as ρ) := by
    rw [consList_ruleFrame,
      show nF + m = (fs ++ bs).length from by rw [List.length_append, hfl, hbl],
      shiftE_consList_len, shiftE_drop_consList xs as.length hdrop ρ, htake]
  have e2 : shiftE (nF - i) m (consList (fs ++ bs) (consList as ρ))
      = consList bs (consList (fs.take i) (consList as ρ)) := by
    rw [consList_append, ← hbl, shiftE_consList_len,
      shiftE_drop_consList fs i hfd (consList as ρ)]
  unfold ihIdxAtM
  simp only [Nat.add_zero]
  rw [interp_liftN, e1, interp_liftN, e2]

/-- **The field's telescope across the two frames, as a FIT** — the
same cancellation carried down the telescope: entry `k` is moved at
the cutoff `k`, which is the length of the spine the walk has already
consumed. -/
theorem spineFit_ihTeleAtGo_rule {nF o i : Nat} {xs fs as : List V}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (ws bs : List V),
      SpineFit (consList ws (consList (xs ++ fs) ρ))
          ((ihTeleAtGo nF o i 0 ws.length tl).map (·.2.2)) bs
        ↔ SpineFit (consList ws (consList (fs.take i) (consList as ρ))) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | dd :: tl, ws, b :: bs => by
    have ih := spineFit_ihTeleAtGo_rule (i := i) hxl htake hfl tl (ws ++ [b]) bs
    rw [List.length_append, List.length_singleton, ← consList_snoc' b ws,
      ← consList_snoc' b ws] at ih
    show (b ∈ˢ interp V (consList ws (consList (xs ++ fs) ρ))
        (ihIdxAtM nF o i 0 ws.length dd.2.2) ∧ _) ↔ (b ∈ˢ _ ∧ _)
    rw [interp_ihIdxAtM_rule (i := i) hxl htake hfl rfl dd.2.2]
    exact and_congr Iff.rfl ih

/-- The binder NUMERALS do not reach the fit: `rebit` leaves every
domain alone. -/
theorem map_dom_ihTeleAtGo_rebit (nF o i l b : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      (ihTeleAtGo nF o i l k (rebit b tl)).map (·.2.2)
        = (ihTeleAtGo nF o i l k tl).map (·.2.2)
  | _, [] => rfl
  | k, dd :: tl => by
    show ihIdxAtM nF o i l k dd.2.2 :: (ihTeleAtGo nF o i l (k + 1) (rebit b tl)).map (·.2.2)
      = ihIdxAtM nF o i l k dd.2.2 :: (ihTeleAtGo nF o i l (k + 1) tl).map (·.2.2)
    rw [map_dom_ihTeleAtGo_rebit nF o i l b (k + 1) tl]

/-- **`hbsB`**: a spine fitting the rule's MOVED telescope at the
rule's frame fits the block's own telescope at the field's frame. -/
theorem spineFit_ihTeleAtR_rule {nF o i b : Nat} {xs fs as bs : List V}
    {tl : List (Nat × Nat × AnnotTerm)}
    (hxl : xs.length = as.length + o) (htake : xs.take as.length = as)
    (hfl : fs.length = nF)
    (h : SpineFit (consList (xs ++ fs) ρ)
      ((ihTeleAtR nF o i 0 (rebit b tl)).map (·.2.2)) bs) :
    SpineFit (consList (fs.take i) (consList as ρ)) (tl.map (·.2.2)) bs := by
  have hq := spineFit_ihTeleAtGo_rule (ρ := ρ) (i := i) hxl htake hfl tl [] bs
  rw [List.length_nil] at hq
  simp only [consList_nil] at hq
  refine hq.mp ?_
  rw [ihTeleAtR, map_dom_ihTeleAtGo_rebit] at h
  exact h

/-- **`hmkB`**: the rule's applied field — the `i`-th field's variable
at the telescope's own variables — IS the block's fold of the
telescope spine onto field `i`. -/
theorem interp_fieldApp_rule {nF i m : Nat} {xs fs bs : List V}
    (hfl : fs.length = nF) (hi : i < nF) (hbl : bs.length = m) :
    interp V (consList bs (consList (xs ++ fs) ρ))
        (AnnotTerm.mkAppN (.bvar (nF - 1 - i + m)) (teleVarsAV m))
      = bs.foldl SetTheory.app (fs.getD i pt) := by
  rw [interp_mkAppN, foldl_app_map, map_teleVarsAV_interp' hbl]
  congr 1
  show consList bs (consList (xs ++ fs) ρ) (nF - 1 - i + m) = fs.getD i pt
  rw [← hbl, consList_apply_add,
    consList_getD_of_lt (xs ++ fs) ρ (nF - 1 - i)
      (by rw [List.length_append, hfl]; omega),
    List.length_append, hfl,
    show xs.length + nF - 1 - (nF - 1 - i) = xs.length + i from by omega,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

end TwoFrame

/-! ## 5. THE RECURSOR TYPE'S BINDER SHAPE — `BlockRecSplitAt` and its
CONVERSE (task #315, M5M-rule)

`BlockRecSplitAt` (`BlockRecPreRun.lean`) is what the three regimes
read OFF a fitting spine of `rec_c`'s binder data: the prefix, the
eliminated member's index values and the major, with the parameters'
fit and the member's own index fit.  The IND arm's `ih` leaf needs the
OPPOSITE direction as well — the callee's spine ASSEMBLED, from an
index spine fitting the member's telescope and a major in the member's
former (`hjoin`, `blockIndIhLeaf_pred`) — and neither direction had a
producer.

Both are the same fact about the STORED type, and this section states
it once.  `BlockRecTyShape` says: `rec_c`'s binder data is `rP c`
binders, then the eliminated member's index telescope, then one more;
its first `nP` binders CARRY the block's parameter telescope (as an
implication between fits, not as a syntactic equality — the recursor
stream stores its own copy of the parameter binders, and only their
READINGS are owed); the index
stretch FITS exactly as the member's own telescope does at the
parameter frame (TWO clauses, one per direction — the two directions
are the two consumers, and they have two DIFFERENT provenances, which
is why they are no longer one `↔`); and the last binder reads as the
member's former applied to the parameters and to the index values.

Nothing here is about the recursion or about a rule: every clause is a
reading of the recursor's own type, which is where the recursor-type
lane delivers it.

**The index clause is bounded by the prefix's own FIT** (session 25,
and the correction of session 24's justification).  It was stated at
EVERY prefix spine of the right length, on the ground that its content
is "a lifting identity — the index domains are the member's lifted
past the prefix's `rP - nP` extra binders".  That ground is false:
`checkBlockRecTys` stores the stream's recursor type AS IS and never
compares its index binders with the member's telescope — not
syntactically, and not by an `isDefEq` of its own.  The only tie is
the MAJOR's domain `T_m p⃗ ı⃗` being TYPE-CORRECT, i.e. the per-argument
`isDefEq`s inside `checkConstantVal`'s inference, and a `DefEqClaim`
concludes at the frames satisfying the opened context and at no
others.  At a prefix spine that fits nothing, a defeq-but-differently-
spelled index binder (`(fun β => β) α` for `α`, which the checker
accepts) reads to an application off its own domain and the `↔` fails.
So the clause takes the prefix fit its two consumers both already
have — and it is split in two, because only ONE of the directions is
payable.

* **forward** (a fit of the recursor's index domains is a fit of the
  member's telescope) is `spineFit_of_major_grading` below: the
  MAJOR's domain is `T_m p⃗ ı⃗` on the nose, so its reading is a spine
  against the member's FORMER, and a spine graded against a λ-tower
  fits the tower's own domains.  The recursor's index binders are not
  looked at at all — which is exactly why this direction works.
* **backward** (a fit of the member's telescope is a fit of the
  recursor's index domains) has NO producer, and none is reachable
  with today's machinery.  The only run fact about those domains is
  the per-argument `isDefEq` inside `checkConstantVal`'s inference of
  the major's domain, and reading it off needs an inversion of
  `inferTypeCore` through a Π-tower and an application spine, which
  does not exist.  Its consumer is `hjoin`/`hfitC'` — the IND arm's
  leaf, which instantiates the induction MOTIVE (`blockIndP`) at a
  spine it has to assemble.  The cheaper repair is on the motive's
  side: state `blockIndP` at the SPLIT data (the prefix's fit, the
  member's index fit, the major's membership) instead of at a
  recursor-spine fit, and the assembly disappears — its consumer
  `blockIndPt` already converts a spine fit into the split data by
  the FORWARD direction.

The MAJOR clause keeps its all-frames quantification, and that is not
an oversight: it is genuinely syntactic.  `checkBlockRecTys` pins the
major's domain to `.const T_m lvls` applied to the prefix and index
BINDERS, so its reading is `mkAppN (acval T_m ψ) (bvars)` and `interp`
folds it into `app`s at every frame, with the bvars landing on the
spine by position. -/

section TyShape

open ConLeche.Semantics

/-! ### List kit -/

theorem list_eq_singleton {α : Type u} {l : List α} (h : l.length = 1) : ∃ z, l = [z] := by
  match l with
  | [] => exact absurd h (by simp)
  | [z] => exact ⟨z, rfl⟩
  | _ :: _ :: _ => exact absurd h (by simp)

theorem list_drop_last {α : Type u} [Inhabited α] {l : List α} {n : Nat}
    (h : l.length = n + 1) : l = l.take n ++ [l.getD n default] := by
  obtain ⟨z, hz⟩ := list_eq_singleton (l := l.drop n) (by rw [List.length_drop, h]; omega)
  have hgz : l.getD n default = z := by
    rw [List.getD_eq_getElem?_getD,
      show l[n]? = (l.drop n)[0]? from by simp [List.getElem?_drop], hz]
    rfl
  rw [hgz, ← hz, List.take_append_drop]

/-! ### Fit kit -/

/-- A fitting spine's prefix fits the domains' prefix. -/
theorem spineFit_take_le :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V} (i : Nat),
      SpineFit ρ Fs as → SpineFit ρ (Fs.take i) (as.take i)
  | [], _, [], i, _ => by rw [List.take_nil, List.take_nil]; trivial
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | _ :: _, _, _ :: _, 0, _ => trivial
  | _ :: _, _, _ :: _, _ + 1, h => ⟨h.1, spineFit_take_le _ h.2⟩

/-- A singleton chain's fit is one membership. -/
theorem spineFit_one {D : AnnotTerm} {ρ : Nat → V} {a : V}
    (h : a ∈ˢ interp V ρ D) : SpineFit ρ [D] [a] := ⟨h, trivial⟩

/-- **A fit of `rp + nI + 1` binders, decomposed** — the prefix, the
index stretch and the ONE last value, each at its own frame. -/
theorem spineFit_split_three {Ds : List AnnotTerm} {ρ : Nat → V} {ys : List V}
    {rp nI : Nat} (hlen : Ds.length = rp + nI + 1) (hfit : SpineFit ρ Ds ys) :
    ∃ (xs is : List V) (mj : V), ys = xs ++ (is ++ [mj]) ∧
      xs.length = rp ∧ is.length = nI ∧
      SpineFit ρ (Ds.take rp) xs ∧
      SpineFit (consList xs ρ) ((Ds.drop rp).take nI) is ∧
      mj ∈ˢ interp V (consList is (consList xs ρ)) ((Ds.drop rp).getD nI default) := by
  have hdrop : (Ds.drop rp).length = nI + 1 := by rw [List.length_drop, hlen]; omega
  have hD : Ds = Ds.take rp
      ++ ((Ds.drop rp).take nI ++ [(Ds.drop rp).getD nI default]) := by
    rw [← list_drop_last hdrop, List.take_append_drop]
  rw [hD] at hfit
  obtain ⟨xs, rest, hyeq, h1, h2⟩ := spineFit_append_inv hfit
  obtain ⟨is, mjs, hreq, h3, h4⟩ := spineFit_append_inv h2
  have hxl : xs.length = rp := by
    rw [h1.length_eq, List.length_take]; omega
  have hisl : is.length = nI := by
    rw [h3.length_eq, List.length_take]; omega
  obtain ⟨mj, rfl⟩ := list_eq_singleton (l := mjs) (by rw [h4.length_eq, List.length_singleton])
  exact ⟨xs, is, mj, by rw [hyeq, hreq], hxl, hisl, h1, h3, h4.1⟩

/-! ### The shape -/

/-- **The recursor type's binder shape** (see the section
docstring). -/
@[expose] def BlockRecTyShape (V : Type w) [SetTheory V] {env : Env} (mo : EnvModel V env)
    (d : BlockData V) (ψ : Name → Nat) (K : Nat) (rP mem : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (ρ : Nat → V) : Prop :=
  ∀ c, c < K →
    d.nP ≤ rP c ∧
    ((rds c).map (·.2.2)).length = rP c + (d.IdsM (mem c) ψ).length + 1 ∧
    (∀ xs : List V, SpineFit ρ (((rds c).map (·.2.2)).take d.nP) xs →
      SpineFit ρ (d.params ψ) xs) ∧
    (∀ xs is : List V, xs.length = rP c →
      SpineFit ρ (((rds c).map (·.2.2)).take (rP c)) xs →
      SpineFit (consList xs ρ)
          ((((rds c).map (·.2.2)).drop (rP c)).take (d.IdsM (mem c) ψ).length) is →
      SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) is) ∧
    (∀ xs is : List V, xs.length = rP c →
      SpineFit ρ (((rds c).map (·.2.2)).take (rP c)) xs →
      SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) is →
      SpineFit (consList xs ρ)
          ((((rds c).map (·.2.2)).drop (rP c)).take (d.IdsM (mem c) ψ).length) is) ∧
    (∀ xs is : List V, xs.length = rP c → is.length = (d.IdsM (mem c) ψ).length →
      interp V (consList is (consList xs ρ))
          ((((rds c).map (·.2.2)).drop (rP c)).getD (d.IdsM (mem c) ψ).length default)
        = (xs.take d.nP ++ is).foldl SetTheory.app
            (interp V ρ (mo.acval (d.memberName (mem c)) ψ)))

/-! ### The index clause's PAYABLE half

The shape's index clause is an `↔` and its two directions have two
different provenances.  This is the FORWARD one, and it is the whole
semantic content of the clause: a spine graded against the member's
FORMER — which is a λ-tower over the member's parameter and index
telescope — fits that telescope, because every application node's
product carries the abstraction's own domain
(`spineFit_of_wellDenoted_lams`, `lamR_mem_piR_dom`).  The major's
domain is `T_m p⃗ ı⃗` on the nose (`checkBlockRecTys` pins it
syntactically), so its READING is that spine and the grading is the
recursor type's own (`piTeleAV_graded` at the major's position).

Nothing here looks at the recursor's index BINDERS: their domains are
the stream's own copies and the checker never compares them with the
member's telescope.  What carries the fit is the major, and that is
why the clause is bounded by the prefix's fit — off a fitting prefix
the grading is not available either. -/

/-- **The major's prefix arguments read to the parameters.**  The
argument spine is `paramBvarsAt nP (rP + nIdx)` — the block's
parameter binders seen from the major's own depth — and the frame
below the major is the prefix followed by the index values, so the
`k`-th one lands on `xs`'s `k`-th entry. -/
theorem map_paramBvarsAt_major {nP rP nIdx : Nat} {xs is : List V} {ρ : Nat → V}
    (hxs : xs.length = rP) (his : is.length = nIdx) (hnP : nP ≤ rP) :
    (paramBvarsAt nP (rP + nIdx)).map (interp V (consList (xs ++ is) ρ)) = xs.take nP := by
  have htkl : (xs.take nP).length = nP := by rw [List.length_take, hxs]; omega
  have hfr : consList (xs ++ is) ρ
      = consList (xs.drop nP ++ is) (consList (xs.take nP) ρ) := by
    rw [← consList_append, ← List.append_assoc, List.take_append_drop]
  rw [show rP + nIdx = nP + ((rP - nP) + nIdx) from by omega]
  rw [map_paramBvarsAt_interp (ρp := consList (xs.take nP) ρ) (fun j => by
    rw [hfr, show (rP - nP) + nIdx = (xs.drop nP ++ is).length from by
      rw [List.length_append, List.length_drop, hxs, his]]
    exact consList_apply_add _ _ j)]
  rw [← frameIdx_eq_reverse_map]
  have hfx := frameIdx_consList' (xs.take nP) ρ
  rw [htkl] at hfx
  exact hfx

/-- **The major's index arguments read to the index values.** -/
theorem map_teleVarsAV_major {nIdx : Nat} {xs is : List V} {ρ : Nat → V}
    (his : is.length = nIdx) :
    (teleVarsAV nIdx).map (interp V (consList (xs ++ is) ρ)) = is := by
  rw [consList_append, ← his]
  exact map_teleVarsAV_interp is (consList xs ρ)

/-- **The MAJOR clause, from the major's READING** — the shape's last
conjunct, which is the reading folded into applications.  It needs no
fit and no frame hypothesis: `checkBlockRecTys` pins the major's
domain to the member's constant applied to the prefix and the index
binders, and `interp` folds a spine at every frame. -/
theorem interp_of_major_reading {env : Env} {mo : EnvModel V env} {nm : Name}
    {ψ : Name → Nat} {ρ : Nat → V} {nP rP nIdx : Nat} {xs is : List V}
    (hxs : xs.length = rP) (his : is.length = nIdx) (hnP : nP ≤ rP)
    (hcl : ∀ ρ₁ ρ₂ : Nat → V,
      interp V ρ₁ (mo.acval nm ψ) = interp V ρ₂ (mo.acval nm ψ)) :
    interp V (consList (xs ++ is) ρ)
        (AnnotTerm.mkAppN (mo.acval nm ψ) (paramBvarsAt nP (rP + nIdx) ++ teleVarsAV nIdx))
      = (xs.take nP ++ is).foldl SetTheory.app (interp V ρ (mo.acval nm ψ)) := by
  rw [interp_mkAppN, ← List.foldl_map (g := fun r a => SetTheory.app r a),
    List.map_append, map_paramBvarsAt_major hxs his hnP, map_teleVarsAV_major his,
    hcl (consList (xs ++ is) ρ) ρ]

/-- **The eliminated member's index fit, from the MAJOR's grading.**

`Params ++ Ids` is the member's own opened telescope (its first `nP`
entries the block's parameters, the rest its indices); `pps` is the
telescope the former's λ-tower binds.  The conclusion splits at `nP`
because that is where the two consumers read it. -/
theorem spineFit_of_major_grading {u : Nat} (hu : u ≠ 0)
    {env : Env} {mo : EnvModel V env} {nm : Name} {ψ : Name → Nat} {ρ : Nat → V}
    {pps : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    {Params Ids : List AnnotTerm} {nP rP nIdx : Nat} {xs is : List V}
    (hxs : xs.length = rP) (his : is.length = nIdx) (hnP : nP ≤ rP)
    (hPlen : Params.length = nP) (hppsLen : nP + nIdx ≤ pps.length)
    (hsplitD : (pps.take (nP + nIdx)).map (·.2.2) = Params ++ Ids)
    (hlam : interp V (consList (xs ++ is) ρ) (mo.acval nm ψ)
      = interp V ρ (mkLamsC u pps B))
    (hwd : WellDenoted V (consList (xs ++ is) ρ)
      (AnnotTerm.mkAppN (mo.acval nm ψ)
        (paramBvarsAt nP (rP + nIdx) ++ teleVarsAV nIdx))) :
    SpineFit ρ Params (xs.take nP) ∧
      SpineFit (consList (xs.take nP) ρ) Ids is := by
  have htkl : (xs.take nP).length = nP := by rw [List.length_take, hxs]; omega
  have hargs : (paramBvarsAt nP (rP + nIdx) ++ teleVarsAV nIdx).map
      (interp V (consList (xs ++ is) ρ)) = xs.take nP ++ is := by
    rw [List.map_append, map_paramBvarsAt_major hxs his hnP, map_teleVarsAV_major his]
  have halen : (paramBvarsAt nP (rP + nIdx) ++ teleVarsAV nIdx).length = nP + nIdx := by
    simp [paramBvarsAt, teleVarsAV]
  have hfit := spineFit_of_wellDenoted_lams (V := V) hu (by rw [halen]; exact hppsLen) hwd hlam
  rw [halen, hsplitD, hargs] at hfit
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
  have hl1 : as₁.length = nP := by rw [h1.length_eq, hPlen]
  obtain ⟨he1, he2⟩ := List.append_inj heq (by rw [htkl, hl1])
  subst he1
  subst he2
  exact ⟨h1, h2⟩

/-- **`BlockRecSplitAt`, from the type's shape** — the FORWARD
direction: a fitting spine decomposes, its prefix's parameters fit the
block's telescope, its index values fit the member's, and its major
lies in the member's former. -/
theorem blockRecSplitAt_of_shape {env : Env} {mo : EnvModel V env} {d : BlockData V}
    {ψ : Name → Nat} {K : Nat} {rP mem : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (h : BlockRecTyShape V mo d ψ K rP mem rds ρ) :
    ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      SpineFit ρ (d.params ψ) ((prefOf (rP c) ys).take d.nP) ∧
      SpineFit (consList ((prefOf (rP c) ys).take d.nP) ρ) (d.IdsM (mem c) ψ)
        (idxOf (rP c) ys) ∧
      majOf ys ∈ˢ ((prefOf (rP c) ys).take d.nP ++ idxOf (rP c) ys).foldl SetTheory.app
        (interp V ρ (mo.acval (d.memberName (mem c)) ψ)) := by
  intro c hc ys hfit
  obtain ⟨hnP, hlenD, hpar, hidsF, -, hmajR⟩ := h c hc
  obtain ⟨xs, is, mj, rfl, hxl, hisl, h1, h3, h4⟩ := spineFit_split_three hlenD hfit
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split]
  refine ⟨hxl, rfl, ?_, hidsF xs is hxl h1 h3, ?_⟩
  · have hp := spineFit_take_le (Fs := ((rds c).map (·.2.2)).take (rP c)) d.nP h1
    rw [List.take_take, Nat.min_eq_left hnP] at hp
    exact hpar _ hp
  · rw [hmajR xs is hxl hisl] at h4
    exact h4

/-- **`hjoin` — `BlockRecSplitAt`'s CONVERSE**: an index spine fitting
the member's own telescope and a major in the member's former assemble
into a fit of the recursor type's binders PAST the rule prefix.  This
is what the `ih` opener's peel is evaluated against
(`blockIndIhLeaf_of`'s `hfitC'`). -/
theorem blockRecJoin_of_shape {env : Env} {mo : EnvModel V env} {d : BlockData V}
    {ψ : Name → Nat} {K : Nat} {rP mem : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (h : BlockRecTyShape V mo d ψ K rP mem rds ρ) {c : Nat} (hc : c < K)
    {xs is : List V} {maj : V} (hxl : xs.length = rP c)
    (hpref : SpineFit ρ (((rds c).map (·.2.2)).take (rP c)) xs)
    (hidx : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (mem c) ψ) is)
    (hmaj : maj ∈ˢ (xs.take d.nP ++ is).foldl SetTheory.app
      (interp V ρ (mo.acval (d.memberName (mem c)) ψ))) :
    SpineFit (consList xs ρ) (((rds c).map (·.2.2)).drop (rP c)) (is ++ [maj]) := by
  obtain ⟨hnP, hlenD, hpar, -, hidsB, hmajR⟩ := h c hc
  have hisl : is.length = (d.IdsM (mem c) ψ).length := hidx.length_eq
  have hdrop : (((rds c).map (·.2.2)).drop (rP c)).length
      = (d.IdsM (mem c) ψ).length + 1 := by rw [List.length_drop, hlenD]; omega
  rw [list_drop_last hdrop]
  refine SpineFit.append (hidsB xs is hxl hpref hidx) (spineFit_one ?_)
  rw [hmajR xs is hxl hisl]
  exact hmaj

end TyShape

end ConLeche.Model
