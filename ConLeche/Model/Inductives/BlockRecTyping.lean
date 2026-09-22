module

import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Semantics.Tower.BlockRecI
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Capstone
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.StructTele
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.StructWF

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

end ConLeche.Model
