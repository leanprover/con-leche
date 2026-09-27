module

public import ConLeche.Model.Inductives.TargetNestCall
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Inductives.TargetFlat
public import ConLeche.Model.Inductives.ContWalk

public section

/-!
# A strict nested call lands (PRIMREC / NESTKN-NL, piece (ii), the node half)

The node case of the node lemma reads a pair's class's fields at the STAGE of its node
(`lfpTuple_induction` at the node's key frame) and must show that each strict call lands
in the stage (own leaf), in the valuation's member / family values, or in a used child's
carrier.  The call was typed at the RELOCATED crest (`callRK`: `relocRK H I hs crest`,
the home layout's crest at the instance, holes relocated above the rule's fields).  This
module states the field side once, over the crest's READING (route (B) of the DESIGN
record "PRIMREC / NESTKN-NL"):

* `piDoms_mem` — a field spine fitting a crest's Π-tower domains lies, field by field, in
  the crest's domains opened at the rule's field variables (`piDomsWith_read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

section Doms

variable {env : Env} {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}

/-- **A field spine fitting a crest's tower lies in its opened domains**: the crest `e`
read at `E` as a Π-tower over `ds`, opened at the field variables `xs` (below `E`) whose
values at `τ` are the fields `fs`; a spine `fs` fitting `ds` at `τ` has field `i` in the
reading of the `i`-th opened domain at `τ`. -/
theorem piDoms_mem
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) {E : Nat} {xs : List Expr} {e : Expr}
    {ds : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm} {doms : List Expr}
    (hxs : ∀ x ∈ xs, ∃ j ty, x = .fvar j ty ∧ j < E ∧ Expr.WScoped j ty)
    (hfb : Expr.fvarsBelow E e) (hdoms : ConLeche.targetPiDomsWith xs e = some doms)
    (hrd : denoteMeta acval env φ E e = some (mkPisAV ds B))
    {τ : Nat → V} {fs : List V} (hfsl : fs.length = xs.length)
    (hvals : ∀ l, l < xs.length →
      interp V τ ((denoteMeta acval env φ E (xs.getD l default)).getD default) = fs.getD l pt)
    (hfit : SpineFit τ (ds.map (·.2.2)) fs) :
    ∀ i, i < xs.length → ∀ A, denoteMeta acval env φ E (doms.getD i default) = some A →
      fs.getD i pt ∈ˢ interp V τ A := by
  intro i hi A hA
  have hdl : ds.length = xs.length := by
    have := hfit.length_eq; simp at this; omega
  obtain ⟨A', hA', hAi⟩ := piDomsWith_read (V := V) (env := env) (φ := φ) hacl hainst E xs e ds B
    doms hxs (by omega) hfb hdoms hrd i hi
  obtain rfl : A' = A := Option.some.inj (hA'.symm.trans hA)
  rw [hAi τ]
  have hvs : (xs.take i).map (fun x => interp V τ ((denoteMeta acval env φ E x).getD default))
      = fs.take i := by
    apply List.ext_getElem (by simp; omega)
    intro l h1 h2
    simp only [List.length_map, List.length_take] at h1
    simp only [List.getElem_map, List.getElem_take]
    have hl : l < xs.length := by omega
    have := hvals l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    exact this
  rw [hvs]
  have hm := FixKI.spineFit_getD_mem' hfit (l := i) (by simp; omega)
  have hgm : (ds.map (·.2.2)).getD i default = (ds.getD i default).2.2 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ds.length by omega)]
  rw [hgm] at hm
  exact hm

/-- **A relocated crest's field lands in its opened domain** (`callRK`'s `fldH`): the home
crest read at the instance's levels as a Π-tower over `ds0`, relocated (`relocRK`) and
opened at the rule's field variables; a field spine fitting `ds0` at the HOME valuation
(`substE` of the instance map at `τ`) has each field in its opened relocated domain at
`τ`. -/
theorem relocField_mem (mT : EnvModel V env)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mT.acval n ψ).inst y k = mT.acval n ψ)
    {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {hs : List Expr} {E : Nat} {φ : Name → Nat}
    (hdl : I.ds.length = H.ctx.nP) {x : Nat → AnnotTerm}
    (hx : ∀ i, i < H.ctx.nP + hs.length → Expr.WScoped E (relocSubst H I hs i) ∧
      (relocSubst H I hs i).looseBVarsBounded 0 = true ∧
      denoteMeta mT.acval env φ E (relocSubst H I hs i) = some (x i))
    {crest : Expr} (hcfb : crest.fvarsBelow (H.ctx.nP + hs.length))
    {ds0 : List (Nat × Nat × AnnotTerm)} {X : AnnotTerm}
    (hread : denoteMeta mT.acval env (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + hs.length) crest
      = some (mkPisAV ds0 X))
    (hfb : Expr.fvarsBelow E (ConLeche.relocRK H I hs crest))
    {xs : List Expr} (hxs : ∀ x ∈ xs, ∃ j ty, x = .fvar j ty ∧ j < E ∧ Expr.WScoped j ty)
    {doms : List Expr} (hdoms : ConLeche.targetPiDomsWith xs (ConLeche.relocRK H I hs crest) = some doms)
    {τ : Nat → V} {fs : List V} (hfsl : fs.length = xs.length)
    (hvals : ∀ l, l < xs.length →
      interp V τ ((denoteMeta mT.acval env φ E (xs.getD l default)).getD default) = fs.getD l pt)
    (hfit : SpineFit (substE V (substTau (H.ctx.nP + hs.length) E x) 0 τ) (ds0.map (·.2.2)) fs) :
    ∀ i, i < xs.length → ∀ A, denoteMeta mT.acval env φ E (doms.getD i default) = some A →
      fs.getD i pt ∈ˢ interp V τ A := by
  have hrd := denoteMeta_relocRK mT hdl hx hcfb
  rw [hread, Option.map_some, AnnotTerm.substAV_mkPisAV] at hrd
  refine piDoms_mem mT.acval_closed hainst hxs hfb hdoms hrd hfsl hvals ?_
  rw [spineFit_substTele]
  exact hfit

end Doms

section Stage

variable {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {D : LfpDatum V}

open Classical in
set_option maxHeartbeats 1600000 in
/-- **A container crest's tower, at the stage** (`stage_fieldMem`'s first half, the crest
given by its reading): the group's constructor `(c, j)` at the key `ds` with the WHOLE
recorded block abstracted to its holes reads as the recorded tower substituted
(`crest_readT`), and a field spine fitting the recorded fields at a stage `Y` fits the
substituted tower at the valuation giving each hole its stage value. -/
theorem crest_stageFit (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup)
    (hkN : D.names.length = D.k) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat}
    {ds : List Expr} (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {ψ : Name → Nat} {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env ψ hi ds dsa)
    {grp : List (Name × Expr)} (hgT : GrpTy env D us grp) (hgn : grp.map (·.1) = D.names)
    {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal} {nF : Nat}
    (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF)) :
    ∃ crest ab X, ConLeche.instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
        (ConLeche.grpSub us hi grp)) = some crest ∧ ab.length = nF ∧
      denoteMeta mp.base2.acval env ψ (hi + grp.length) crest
        = some (mkPisAV (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
            (grpX mp.base2 ψ D us hi grp ds (hi + grp.length))) 0 ab) X) ∧
      ∀ {ρp Y : Nat → V}, Sat V (D.params (Level.substFn ψ lps us)).reverse ρp →
        InTupleSpace (D.w (Level.substFn ψ lps us)) D.N (D.idx (Level.substFn ψ lps us) ρp) Y →
        ∀ {ρ : Nat → V}, keyFrame dsa hi ρ = ρp → ∀ {fs : List V},
        SpineFit (D.frame (Level.substFn ψ lps us) ρp Y) (D.fields (Level.substFn ψ lps us) c j)
          fs →
        SpineFit (consList (grpVals D (Level.substFn ψ lps us) grp ρp Y) ρ)
          ((AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
            (grpX mp.base2 ψ D us hi grp ds (hi + grp.length))) 0 ab).map (·.2.2)) fs := by
  obtain ⟨-, crest, ab, hcr, ⟨Tys, hlT, hTys, hEq⟩, hlab, hread⟩ :=
    crest_readT mp hD hnN hkN hlps hnd hul hds hdsa hgT hc hj hfc
  refine ⟨crest, ab, _, hcr, hlab, hread, ?_⟩
  intro ρp Y hsat hY ρ hρp fs hfit
  have hin : ∀ mm, mm < D.k → decide (InGrp D grp mm) = true := by
    intro mm hmm
    refine decide_eq_true ⟨hmm, ?_⟩
    rw [hgn, List.contains_iff_mem]
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hsub : substE V (substTau (ds.length + D.k) (hi + grp.length)
      (grpX mp.base2 ψ D us hi grp ds (hi + grp.length))) 0
      (consList (grpVals D (Level.substFn ψ lps us) grp ρp Y) ρ)
      = D.frame (Level.substFn ψ lps us) ρp Y := by
    rw [substE_grpT mp hnN hkN hlps hnd hul hds hdsa hgT ρp Y ρ, hρp]
    unfold LfpDatum.frame
    congr 1
    refine List.map_congr_left fun mm hmm => ?_
    rw [if_pos (hin mm (List.mem_range.mp hmm))]
  have hsat' := frameVals_sat mp hD hsat hlT hTys (fun _ => true) Y hY ρ
  simp only [if_true] at hsat'
  rw [spineFit_substTele, hsub]
  exact (hEq.spineFit_iff hsat' fs).mpr hfit

end Stage

end ConLeche.Model
