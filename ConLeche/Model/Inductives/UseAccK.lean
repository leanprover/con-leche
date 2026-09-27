module

public import ConLeche.Model.Inductives.HoleRelAK
public import ConLeche.Model.Inductives.UseRelK
public import ConLeche.Model.Inductives.PosDerivMonoK
public import ConLeche.Model.Inductives.ContAcc
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.ContN2

public section

/-!
# A use of a key-named node is accessible (PRIMREC / NESTKN-M4)

The accessibility twin of `UseRelK.lean`/`UseMonoK.lean`.  At a use of a node
(its frame fact `FrameAccJK` the IH) at a user relation `R` (a `HoleRelAK` at
the user's layout), the node's frame fact is instantiated along the SAME image
relation as for monotonicity (`useRel`: members and parameters the user's,
family `j` its binding's value), and the node's supports are carried back to
the user by BOUND COMPOSITION (PROOFPLAN §3.4):

* `ValAcc`/`ValRich`: a value accessible (every element of it applied to a
  spine of the family's index count has a support) and rich at a spine
  length — what a MET family's binding gives (the bind judgment);
* `ItemSupp`/`itemSupp_use`: every admissible item of the node's base held at
  the image has a support at the user — a member item by the same item, a
  family item by its binding's support;
* `supports_compose`: a support of the node's items composes with the items'
  supports into a support at the user, indexed by `sigmaPairs` of the node's
  bound and a FINITE union of the bindings' bounds (no indexed union, no
  universe closure beyond the level's);
* `holeRelAK_use`: the image relation is a hole relation at the node's base
  (richness through the bindings);
* `rich_of_keyOcc` (PROOFPLAN R4): a key occurrence's value never holds `pt`
  at a POSITIVE level (`LfpClause.injNePt`, which needs a parameter) — so a
  family bound to a key occurrence is vacuously rich.  FALSE at `w = 0`;
  accessibility is only ever read at `w ≠ 0` (`blockAcc_of_run`'s one caller,
  `BlockDatum.lean`, splits on `d.w ψ = 0`);
* `valAcc_key`: a used key's value is accessible, from its carrier's
  accessibility at the key frames;
* `accConclK_of_carrier`: a container instance at the user is accessible, from
  its carrier's accessibility (the leaf);
* `useAccK`: a use's carrier accessible at the user's key frames.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Values, accessible and rich at a spine length -/

/-- **A value accessible at a spine length** along `R`: every element of the
value applied to a spine of `n` arguments has a support (bound `A`, items
admissible by `Q`) carrying it to every related frame. -/
@[expose] def ValAcc (Q : Nat → Nat → Prop) (R : FrameRel V) (A : (Nat → V) → V) (a : AnnotTerm)
    (n : Nat) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ vs : List V, vs.length = n → ∀ y, y ∈ˢ vs.foldl app (interp V ρ a) →
    ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧ (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → y ∈ˢ vs.foldl app (interp V ρ' a)

/-- **A value rich at a spine length** along `R` (`RichOn` at one value). -/
@[expose] def ValRich (Q : Nat → Nat → Prop) (R : FrameRel V) (a : AnnotTerm) (n : Nat) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ vs : List V, vs.length = n → (pt : V) ∈ˢ vs.foldl app (interp V ρ a) →
    ∃ ρ'', R ρ ρ'' ∧ HoldsLe Q ρ ρ'' ∧ ∃ z, z ∈ˢ vs.foldl app (interp V ρ'' a) ∧ z ≠ pt

/-- **Every admissible item of the image has a support at the user**: an
item admissible by `Qc` held at `f ρ` has a support (bound `U`, items
admissible by `Q`) carrying it to `f ρ'` for every related `ρ'`. -/
@[expose] def ItemSupp (Q Qc : Nat → Nat → Prop) (R : FrameRel V) (f : (Nat → V) → Nat → V)
    (U : (Nat → V) → V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ o, Adm Qc o → Holds (f ρ) o →
    ∃ (B : V) (g : V → Occ V), B ⊆ˢ U ρ ∧ (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → Holds (f ρ') o

/-- The items' supports carry the admissible items along `HoldsLe`. -/
theorem ItemSupp.holdsLe {Q Qc : Nat → Nat → Prop} {R : FrameRel V} {f : (Nat → V) → Nat → V}
    {U : (Nat → V) → V} (hU : ItemSupp Q Qc R f U) {ρ ρ'' : Nat → V} (hR : R ρ ρ'')
    (hle : HoldsLe Q ρ ρ'') : HoldsLe Qc (f ρ) (f ρ'') := by
  intro o ho hH
  obtain ⟨B, g, -, hg, hs⟩ := hU ρ ρ'' hR o ho hH
  exact hs ρ'' hR fun b hb => hle _ (hg b hb).1 (hg b hb).2

/-- **BOUND COMPOSITION**: a support of the image's items (bound `Ac` at the
image) composes with the items' supports (bound `U`) into a support at the
user, indexed by the pairs of `sigmaPairs (Ac (f ρ)) (fun _ => U ρ)`. -/
theorem supports_compose {Q Qc : Nat → Nat → Prop} {R : FrameRel V} {f : (Nat → V) → Nat → V}
    {U Ac : (Nat → V) → V} (hU : ItemSupp Q Qc R f U) {Pre Post : (Nat → V) → V → Prop}
    (hc : ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, Pre (f ρ) x →
      ∃ (B : V) (g : V → Occ V), B ⊆ˢ Ac (f ρ) ∧
        (∀ b, b ∈ˢ B → Adm Qc (g b) ∧ Holds (f ρ) (g b)) ∧
        ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds (f ρ') (g b)) → Post (f ρ') x) :
    ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, Pre (f ρ) x →
      ∃ (B : V) (g : V → Occ V), B ⊆ˢ sigmaPairs (Ac (f ρ)) (fun _ => U ρ) ∧
        (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
        ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → Post (f ρ') x := by
  classical
  intro ρ ρ₀ hR x hx
  obtain ⟨B, g, hB, hg, hs⟩ := hc ρ ρ₀ hR x hx
  obtain ⟨Bf, gf, hsk⟩ := skolem_occ (S := B)
    (Q := fun b B' g' => B' ⊆ˢ U ρ ∧ (∀ b', b' ∈ˢ B' → Adm Q (g' b') ∧ Holds ρ (g' b')) ∧
      ∀ ρ', R ρ ρ' → (∀ b', b' ∈ˢ B' → Holds ρ' (g' b')) → Holds (f ρ') (g b))
    fun b hb => hU ρ ρ₀ hR (g b) (hg b hb).1 (hg b hb).2
  refine ⟨sigmaPairs B Bf, fun p => gf (sfst p) (ssnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨b, hB b hb, b', (hsk b hb).1 b' hb', rfl⟩
  · intro p hp
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_sigmaPairs.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    exact (hsk b hb).2.1 b' hb'
  · intro ρ' hR' hheld
    refine hs ρ' hR' fun b hb => (hsk b hb).2.2 ρ' hR' fun b' hb' => ?_
    have := hheld (kpair b b') (mem_sigmaPairs.mpr ⟨b, hb, b', hb', rfl⟩)
    simpa only [sfst_kpair, ssnd_kpair] using this

/-! ## The image relation at the node's base -/

section Use

variable {m : EnvModel V env}

/-- The bound of the bindings' supports: a finite union, and one extra index
for an item carried one-to-one. -/
@[expose] noncomputable def useU (nF : Nat) (Aj : Nat → (Nat → V) → V) (ρ : Nat → V) : V :=
  binUnion unitSet (LfpDatum.finUnion (fun j => Aj j ρ) nF)

theorem useU_mem {w nF : Nat} (hw : w ≠ 0) {Aj : Nat → (Nat → V) → V}
    (hAj : ∀ j ρ, Aj j ρ ∈ˢ (univ w : V)) (ρ : Nat → V) : useU nF Aj ρ ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).binUnion_mem (empty_mem_univ w) (unitSet_mem_univ w)
    (LfpDatum.finUnion_mem hw fun j _ => hAj j ρ)

/-- **The node's base items have supports at the user** (see the module
docstring): a member item is the user's member item, a (met) family item its
binding's support. -/
theorem itemSupp_use {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (hR : HoleRelAK m φ ctx L met d Δa R) (hd : L.hi ≤ d)
    {L' : LayoutK} {metc : List Nat} {xs : List AnnotTerm} (hxl : xs.length = L'.nF)
    {Aj : Nat → (Nat → V) → V}
    (hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < L'.nF → L'.fams[j]? = some (key, nI) →
      j ∈ metc → ∀ hj : j < xs.length, ValAcc (HoleQK ctx L met d) R (Aj j) xs[j] nI) :
    ItemSupp (HoleQK ctx L met d) (HoleQK ctx (layoutBaseK ctx L') metc (ctx.hiAt 0 + L'.nF)) R
      (useVal xs (d - ctx.hiAt 0)) (useU L'.nF Aj) := by
  have h0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  rintro ρ ρ₀ hr ⟨i, vs, y⟩ ho hH
  unfold Adm at ho
  simp only at ho
  rcases ho with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, key, hj, hk, hm, hlt, rfl⟩ | ⟨g, gn, hg, -⟩
  · -- a member: the same item at the user
    have hlt' : ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
    have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.nP + t)
        = (ctx.hiAt 0 - 1 - (ctx.nP + t)) + xs.length := by omega
    have e2 : ctx.hiAt 0 - 1 - (ctx.nP + t) + (d - ctx.hiAt 0) = d - 1 - (ctx.nP + t) := by omega
    refine ⟨unitSet, fun _ => (d - 1 - (ctx.nP + t), vs, y),
      fun b hb => mem_binUnion.mpr (Or.inl hb), fun _ _ => ⟨?_, ?_⟩, fun ρ' _ h' => ?_⟩
    · exact Or.inl ⟨t, ht, by omega, rfl, hn⟩
    · unfold Holds at hH ⊢
      simp only at hH ⊢
      rw [e, useVal_base, e2] at hH
      exact hH
    · have := h' pt pt_mem_unitSet
      unfold Holds at this ⊢
      simp only at this ⊢
      rw [e, useVal_base, e2]
      exact this
  · -- a met family: its binding's support
    simp only [layoutBaseK_nF, layoutBaseK_fams] at hj hk
    have hjx : j < xs.length := by omega
    have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.hiAt 0 + j) = xs.length - 1 - j := by omega
    unfold Holds at hH
    simp only at hH
    rw [e, useVal_fam ρ hjx] at hH
    obtain ⟨B, g, hB, hg, hs⟩ := hmet j key vs.length hj hk hm hjx ρ ρ₀ hr vs rfl y hH
    refine ⟨B, g, fun b hb => mem_binUnion.mpr (Or.inr (LfpDatum.subset_finUnion hj b (hB b hb))),
      hg, fun ρ' hr' h' => ?_⟩
    unfold Holds
    simp only
    rw [e, useVal_fam ρ' hjx]
    exact hs ρ' hr' h'
  · simp at hg

/-- **The image of a user's accessibility hole relation is one at the node's
base** (`holeRelK_use`'s twin): given the bindings fit the families' types
and every MET family's binding is accessible and rich at its index count. -/
theorem holeRelAK_use {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (hR : HoleRelAK m φ ctx L met d Δa R)
    (hd : L.hi ≤ d) {L' : LayoutK} {metc : List Nat} {xs tya : List AnnotTerm}
    (hxl : xs.length = L'.nF)
    (hsat : ∀ ρ, Sat V Δa ρ →
      SpineFit (dropV (d - ctx.hiAt 0) ρ) tya (xs.map (interp V ρ)))
    {Aj : Nat → (Nat → V) → V}
    (hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < L'.nF → L'.fams[j]? = some (key, nI) →
      j ∈ metc → ∀ hj : j < xs.length,
        ValAcc (HoleQK ctx L met d) R (Aj j) xs[j] nI ∧ ValRich (HoleQK ctx L met d) R xs[j] nI)
    (hdsw : ∀ x ∈ L'.dsF, Expr.WScoped (ctx.hiAt 0 + L'.nF) x) :
    HoleRelAK m φ ctx (layoutBaseK ctx L') metc (ctx.hiAt 0 + L'.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) (useRel R xs (d - ctx.hiAt 0)) := by
  have h0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  have hU := itemSupp_use hR hd hxl (Aj := Aj) (metc := metc)
    fun j key nI hj hk hm hjx => (hmet j key nI hj hk hm hjx).1
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- dom
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨sat_of_spineFit (Sat_drop h1 _) (hsat ρ h1), sat_of_spineFit (Sat_drop h2 _) (hsat ρ' h2)⟩
  · -- agree: off the holes the image is the user's valuation, off the user's holes
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    simp only [layoutBaseK_hi] at hi
    by_cases hin : i < xs.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, by omega⟩
      simp only [NestCtx.hiAt] at hxl ⊢; omega
    obtain ⟨q, rfl⟩ : ∃ q, i = q + xs.length := ⟨i - xs.length, by omega⟩
    rw [useVal_base, useVal_base]
    refine hR.agree ρ ρ' hr (q + (d - ctx.hiAt 0)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, by omega⟩
    omega
  · -- no own group at the base
    intro g n hg; simp at hg
  · simpa using hdsw
  · -- symmetric
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  · -- rich: a member by the user's richness, a met family by its binding's
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    rcases hQ with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, key, hj, hk, hm, hlt, rfl⟩ | ⟨g, gn, hg, -⟩
    · have hlt' : ctx.nP + t < ctx.hiAt 0 := by simp only [NestCtx.hiAt]; omega
      have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.nP + t)
          = (ctx.hiAt 0 - 1 - (ctx.nP + t)) + xs.length := by omega
      have e2 : ctx.hiAt 0 - 1 - (ctx.nP + t) + (d - ctx.hiAt 0) = d - 1 - (ctx.nP + t) := by
        omega
      rw [e, useVal_base, e2] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ :=
        hR.rich ρ ρ₀ hr _ vs (Or.inl ⟨t, ht, by omega, rfl, hn⟩) hpt
      refine ⟨useVal xs (d - ctx.hiAt 0) ρ'', ⟨ρ, ρ'', hr'', rfl, rfl⟩, hU.holdsLe hr'' hle'', z,
        ?_, hzp⟩
      rw [e, useVal_base, e2]
      exact hz
    · simp only [layoutBaseK_nF, layoutBaseK_fams] at hj hk
      have hjx : j < xs.length := by omega
      have e : ctx.hiAt 0 + L'.nF - 1 - (ctx.hiAt 0 + j) = xs.length - 1 - j := by omega
      rw [e, useVal_fam ρ hjx] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ :=
        (hmet j key vs.length hj hk hm hjx).2 ρ ρ₀ hr vs rfl hpt
      refine ⟨useVal xs (d - ctx.hiAt 0) ρ'', ⟨ρ, ρ'', hr'', rfl, rfl⟩, hU.holdsLe hr'' hle'', z,
        ?_, hzp⟩
      rw [e, useVal_fam ρ'' hjx]
      exact hz
    · simp at hg
  · -- left-reflexive
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

end Use

/-! ## A key's value -/

/-- **A key's value, applied**: the container's former applied to the key's
parameters is the λ-tower over the member's indices at the key frame
(`former_app_eq`, `grp_holeVal_apply`). -/
theorem keyVal_foldl {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {d : Nat}
    {ps : List Expr} {ba : AnnotTerm}
    (hba : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps) = some ba)
    (hlenP : ps.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hpsw : ∀ x ∈ ps, Expr.WScoped d x) {psa : List AnnotTerm}
    (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {Δa : List AnnotTerm} (hgr : Graded V Δa ba) :
    ∀ σ, Sat V Δa σ → ∀ as : List V, as.foldl app (interp V σ ba)
      = as.foldl app (holeFam (keyFrame psa d σ) (D.ids mm (Level.substFn φ cv.levelParams us))
          fun bs => app (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d σ) mm)
            (tupW (D.u mm (Level.substFn φ cv.levelParams us)) bs)) := by
  intro σ hσ as
  have hgrσ := hgr σ hσ
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP ⊢
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hba
  obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hf hfa
  have hv : vs = psa := DenoteMetaSpine.unique hsp hpsa
  subst vs
  change denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps)
    = some (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa) at hba
  change WellDenotedV V σ (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa) at hgrσ
  change as.foldl app (interp V σ (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa)) = _
  have hdrop : ∀ σ : Nat → V, dropV (d - d) σ = σ := by
    intro σ; funext i; simp [dropV]
  have hs : Sat V (D.params ψ).reverse (keyFrame psa d σ) := by
    have := keyParamsFit mp hD hmm hf (Nat.le_refl d) (is := []) (by simpa using hba)
      (by rw [hψ]; exact hlenP) hpsw hpsa σ hgrσ
    rwa [hdrop, hψ] at this
  have hpl : psa.length = (D.params ψ).length := by
    rw [← DenoteMetaSpine.length_eq hpsa, hlenP]
  rw [interp_mkAppN_foldl, ← List.foldl_append, hψ]
  have hfi : psa.map (interp V σ) = frameIdx (D.params ψ).length (keyFrame psa d σ) := by
    unfold keyFrame
    rw [← hpl, ← List.length_map (f := interp V σ), frameIdx_consList']
  rw [hfi, former_app_eq mp hD hmm hs σ as, ← hfi]
  rw [← hψ] at hs ⊢
  exact grp_holeVal_apply mp hD hpsa (by rw [hψ]; exact hlenP.symm) hmm hs _ as

/-- **A key occurrence's value never holds `pt` at a POSITIVE level**
(PROOFPLAN R4): at its index count the value is its carrier's fibre (or `∅`
off the index domain), and a fibre of a parameterised block at `w ≠ 0` holds
constructor values only, never `pt` (`LfpClause.injNePt`).  So a family bound
to a key occurrence is vacuously rich.  This is FALSE at `w = 0`: a `Prop`
block's elements are `pt`; the closure witness reads accessibility only at
`w ≠ 0`. -/
theorem rich_of_keyOcc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {d : Nat}
    {ps : List Expr} {ba : AnnotTerm}
    (hba : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps) = some ba)
    (hlenP : ps.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hpsw : ∀ x ∈ ps, Expr.WScoped d x) {psa : List AnnotTerm}
    (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {Δa : List AnnotTerm} (hgr : Graded V Δa ba)
    (hw : D.w (Level.substFn φ cv.levelParams us) ≠ 0) (hne : ps ≠ []) :
    ∀ σ, Sat V Δa σ → ∀ vs : List V,
      vs.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length →
      ¬ (pt : V) ∈ˢ vs.foldl app (interp V σ ba) := by
  intro σ hσ vs hvl hpt
  obtain ⟨hL, -, -, -⟩ := mp.lfp_ok D hD
  rw [keyVal_foldl mp hD hmm hf hba hlenP hpsw hpsa hgr σ hσ] at hpt
  have hp0 : (D.params (Level.substFn φ cv.levelParams us)).length ≠ 0 := by
    rw [← hlenP]; exact fun h => hne (List.eq_nil_of_length_eq_zero h)
  have hs : Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse (keyFrame psa d σ) := by
    have hdrop : dropV (d - d) σ = σ := by funext i; simp [dropV]
    have := keyParamsFit mp hD hmm hf (Nat.le_refl d) (is := []) (by simpa using hba) hlenP hpsw
      hpsa σ (hgr σ hσ)
    rwa [hdrop] at this
  rcases holeFam_foldl_full (ρ := keyFrame psa d σ)
      (fun bs => app (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d σ) mm)
        (tupW (D.u mm (Level.substFn φ cv.levelParams us)) bs)) hvl with ⟨hfit, he⟩ | he
  · rw [he] at hpt
    obtain ⟨j, fs, -, hj⟩ := hL.carrier_case hs (Nat.lt_of_lt_of_le hmm hL.kN) (tupW_mem hfit) hpt
    exact hL.injNePt _ hw hp0 mm j fs hj.symm
  · rw [he] at hpt
    exact not_mem_empty _ hpt

/-- **A used key's value is accessible** at its index count, from its
carrier's accessibility at the key frames (the index telescope reading alike
at related frames, N2). -/
theorem valAcc_key {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {d : Nat}
    {ps : List Expr} {ba : AnnotTerm}
    (hba : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps) = some ba)
    (hlenP : ps.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hpsw : ∀ x ∈ ps, Expr.WScoped d x) {psa : List AnnotTerm}
    (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {Δa : List AnnotTerm} {R : FrameRel V} (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (hgr : Graded V Δa ba)
    (hte : ∀ ρ ρ', R ρ ρ' → TeleEq (keyFrame psa d ρ) (keyFrame psa d ρ')
      (D.ids mm (Level.substFn φ cv.levelParams us)))
    {Q : Nat → Nat → Prop} {G : Nat → Prop} (hG : G mm)
    {A : (Nat → V) → V}
    (hacc : ∀ c, G c → ∀ ρ ρ₀, R ρ ρ₀ →
      ∀ i, i ∈ˢ D.idx (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ) c →
      ∀ x, x ∈ˢ app (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ) c) i →
        ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧
          (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
          ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) →
            x ∈ˢ app (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ') c) i) :
    ValAcc Q R A ba (D.ids mm (Level.substFn φ cv.levelParams us)).length := by
  intro ρ ρ₀ hr vs hvl y hy
  obtain ⟨h1, -⟩ := hdom ρ ρ₀ hr
  rw [keyVal_foldl mp hD hmm hf hba hlenP hpsw hpsa hgr ρ h1] at hy
  rcases holeFam_foldl_full (ρ := keyFrame psa d ρ)
      (fun bs => app (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ) mm)
        (tupW (D.u mm (Level.substFn φ cv.levelParams us)) bs)) hvl with ⟨hfit, he⟩ | he
  · rw [he] at hy
    obtain ⟨B, g, hB, hg, hs⟩ := hacc mm hG ρ ρ₀ hr _ (tupW_mem hfit) y hy
    refine ⟨B, g, hB, hg, fun ρ' hr' hh => ?_⟩
    have hy' := hs ρ' hr' hh
    obtain ⟨-, h2⟩ := hdom ρ ρ' hr'
    rw [keyVal_foldl mp hD hmm hf hba hlenP hpsw hpsa hgr ρ' h2, ← (hte ρ ρ' hr').holeFam,
      holeFam_app _ hfit]
    exact hy'
  · rw [he] at hy
    exact absurd hy (not_mem_empty _)

/-! ## The container instance at the user -/

/-- **A container instance is accessible at the user** (the leaf,
`accConcl_of_frameAccOut` at the user's own depth): its carrier accessible at
the key frames, its indices hole-free, the instance in the type regime (a
parameterised block at a positive level has no truth-valued fibre; without
parameters the key frame is the tail, which the relation keeps). -/
theorem accConclK_of_carrier {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level}
    {d : Nat} {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ d
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped d x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ d ds dsa)
    {w : Nat} {ctx : NestCtx} {L : LayoutK} {met : List Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (hR : HoleRelAK mp.base2 φ ctx L met d Δa R) (hgr : Graded V Δa wa)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ d is isa → ∀ v ∈ isa, ConstOn R v)
    (hw : w ≠ 0) (hwD : D.w (Level.substFn φ cv.levelParams us) = w) {G : Nat → Prop}
    (hacc : FrameAccOutG w ctx.nP d (HoleQK ctx L met d) R D (Level.substFn φ cv.levelParams us)
      dsa G) (hG : G mm) :
    AccConclG w ctx.nP L.hi (HoleQK ctx L met) d (Expr.mkAppN (.const (D.member mm) us) (ds ++ is))
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) R wa := by
  obtain ⟨hL, -, -, -⟩ := mp.lfp_ok D hD
  obtain ⟨-, isa, hisa, hk⟩ := keyLeaf mp hD hmm hf (Nat.le_refl d) hwa hlenP hlenI hdsw hdsa
  have hdrop : ∀ σ : Nat → V, dropV (d - d) σ = σ := by
    intro σ; funext i; simp [dropV]
  simp only [hdrop] at hk
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP hlenI hwD hacc hk
  have hmap : ∀ ρ ρ', R ρ ρ' → isa.map (interp V ρ) = isa.map (interp V ρ') := fun ρ ρ' hr =>
    List.map_congr_left fun v hv => hisC isa hisa v hv ρ ρ' hr
  obtain ⟨A, hA, hinv, hacc⟩ := hacc
  refine ⟨?_, ⟨A, ?_, fun ρ _ _ => hA _, ?_⟩, outMent_self _ _⟩
  · -- the type regime
    intro htv ρ ρ' hr
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    obtain ⟨hs1, hf1, he1⟩ := hk ρ (hgr ρ h1)
    obtain ⟨hs2, hf2, he2⟩ := hk ρ' (hgr ρ' h2)
    by_cases hp0 : (D.params ψ).length = 0
    · -- no parameters: the key frame is the tail, which the relation keeps
      have hds0 : dsa = [] := List.eq_nil_of_length_eq_zero (by
        rw [← DenoteMetaSpine.length_eq hdsa, hlenP, hp0])
      subst hds0
      have hkf : keyFrame [] d ρ = keyFrame [] d ρ' := by
        funext j
        show ρ (j + d) = ρ' (j + d)
        exact hR.agree ρ ρ' hr _ fun hh => by simp only [holeP] at hh; omega
      rw [he1, he2, hkf, hmap ρ ρ' hr]
    · -- a parameterised container at a positive level: a truth-valued fibre is empty
      have hwψ : D.w ψ ≠ 0 := hwD ▸ hw
      have hemp : ∀ σ, Sat V (D.params ψ).reverse (keyFrame dsa d σ) →
          SpineFit (keyFrame dsa d σ) (D.ids mm ψ) (isa.map (interp V σ)) →
          interp V σ wa ∈ˢ (univZero : V) →
          interp V σ wa = app (D.carrier ψ (keyFrame dsa d σ) mm)
            (tupW (D.u mm ψ) (isa.map (interp V σ))) → interp V σ wa = empty := by
        intro σ hs hfit hz he
        refine ext fun y => ⟨fun hy => ?_, fun hy => absurd hy (not_mem_empty y)⟩
        exfalso
        have hpt := eq_pt_of_mem_univZero hz hy
        rw [he] at hy
        obtain ⟨j, fs, -, rfl⟩ := hL.carrier_case hs (Nat.lt_of_lt_of_le hmm hL.kN)
          (tupW_mem hfit) hy
        exact hL.injNePt ψ hwψ hp0 mm j fs hpt
      rw [hemp ρ hs1 hf1 (htv ρ ρ' hr).1 he1, hemp ρ' hs2 hf2 (htv ρ ρ' hr).2 he2]
  · -- accessibility
    intro ρ ρ₀ hr x _ hx
    obtain ⟨h1, -⟩ := hR.dom ρ ρ₀ hr
    obtain ⟨-, hf1, he1⟩ := hk ρ (hgr ρ h1)
    rw [he1] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := hacc mm hG ρ ρ₀ hr _ (tupW_mem hf1) x hx
    refine ⟨B, g, hB, hg, fun ρ' hr' hheld => ?_⟩
    obtain ⟨-, h2⟩ := hR.dom ρ ρ' hr'
    obtain ⟨-, -, he2⟩ := hk ρ' (hgr ρ' h2)
    rw [he2, ← hmap ρ ρ' hr']
    exact hs ρ' hr' hheld
  · -- the bound reads parameter positions only
    intro ρ ρ' hag
    refine hinv _ _ fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    exact hag _ (Or.inr ⟨hp1, hp2⟩)

/-! ## A node's frame fact, and a use -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (w : Nat)
  (ctx : NestCtx)

/-- **A node's frame fact for accessibility** (`FrameAccJ` at a layout, the
twin of `FrameMonoK`): at every recorded block holding the node's head,
along every accessibility hole relation at the node's BASE whose pairs
satisfy the container's parameter telescope at the key frames of `DsF`, the
group is well formed, the level parameters distinct, the block at the level,
and the group's carriers accessible in the base (`FrameAccOutG`, the base's
items: members and MET families). -/
@[expose] def FrameAccJK (kn : NestKey) (lo : LayoutOutK) (met : List Nat) : Prop :=
  ContOk mp φ w ctx → ctx.names.contains kn.cname = false → kn.cname ≠ ConLeche.quotName →
  ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
    D.member mm = ((grpOfK lo).headD default).1 →
  ∀ {lps : List Name},
    (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps) →
    lo.L.lvls.length = lps.length →
    (∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true) →
    ∀ {dsa : List AnnotTerm},
      DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa →
    (D.params (Level.substFn φ lps lo.L.lvls)).length = lo.L.dsF.length →
    ((∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨ lps.Nodup) →
    ∀ {Δh : List AnnotTerm} {R₀ : FrameRel V},
    HoleRelAK mp.base2 φ ctx (layoutBaseK ctx lo.L) met (ctx.hiAt 0 + lo.L.nF) Δh R₀ →
    LaySiteK mp.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF) Δh →
    Δh.length = ctx.hiAt 0 + lo.L.nF →
    (∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF) Δh x) →
    (∀ x ∈ lo.L.dsF, Expr.LeavesBounded x) →
    (∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ) ∧
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ')) →
    lps.Nodup ∧ GrpOk ctx D (ctx.hiAt 0 + lo.L.nF) lo.L.lvls lo.L.dsF (grpOfK lo) ∧
    D.w (Level.substFn φ lps lo.L.lvls) = w ∧
    FrameAccOutG w ctx.nP (ctx.hiAt 0 + lo.L.nF)
      (HoleQK ctx (layoutBaseK ctx lo.L) met (ctx.hiAt 0 + lo.L.nF)) R₀ D
      (Level.substFn φ lps lo.L.lvls) dsa (InGrp D (grpOfK lo))

end Motive

set_option maxHeartbeats 800000 in
/-- **A use of a node is accessible** (see the module docstring): the used
container's carrier is accessible at the user's key frames, with a bound of
the level reading only the user's parameter positions — the node's frame
fact along the image relation, its supports composed with the MET bindings'
(`supports_compose`). -/
theorem useAccK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx} {F w : Nat}
    (hw : w ≠ 0) (hok : ContOk mp φ w ctx) {kn : NestKey} {lo : LayoutOutK} {metc : List Nat}
    (hspec : ConLeche.LayoutSpecK (fueledOps .verified F) env ctx kn lo)
    (hhd : ctx.names.contains kn.cname = false ∧ kn.cname ≠ ConLeche.quotName)
    (ihn : FrameAccJK mp φ w ctx kn lo metc)
    {L : LayoutK} {met : List Nat} {d : Nat} {Δa : List AnnotTerm} {R : FrameRel V}
    (hR : HoleRelAK mp.base2 φ ctx L met d Δa R) (hd : L.hi ≤ d) (hΔ : Δa.length = d)
    {n : Name} (hgrp : n ∈ lo.ginfo.map (·.1)) {ps is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const n lo.L.lvls) (ps ++ is))
      = some wa)
    (hgr : Graded V Δa wa) (hpsw : ∀ x ∈ ps, Expr.WScoped d x)
    (hnPc : ∃ Lc, ConLeche.nestContainer ctx n = some (ps.length, Lc))
    (hlenD : lo.L.dsF.length = ps.length)
    {psa : List AnnotTerm} (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {xs tya : List AnnotTerm} (hxl : xs.length = lo.L.nF) (htyl : tya.length = lo.L.nF)
    (hsat : ∀ ρ, Sat V Δa ρ → SpineFit (dropV (d - ctx.hiAt 0) ρ) tya (xs.map (interp V ρ)))
    {Aj : Nat → (Nat → V) → V} (hAj : ∀ j ρ, Aj j ρ ∈ˢ (univ w : V))
    (hAjinv : ∀ j, InvOn (ParamPos d ctx.nP) (Aj j))
    (hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < lo.L.nF → lo.L.fams[j]? = some (key, nI) →
      j ∈ metc → ∀ hj : j < xs.length,
        ValAcc (HoleQK ctx L met d) R (Aj j) xs[j] nI ∧ ValRich (HoleQK ctx L met d) R xs[j] nI)
    (hdsw : ∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ lo.L.dsF, Expr.LeavesBounded x)
    (hlayc : LaySiteK mp.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0))) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa)
    (hCds : ∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) x)
    (hpos : ∀ ρ, Sat V Δa ρ →
      dsa.map (interp V (useVal xs (d - ctx.hiAt 0) ρ)) = psa.map (interp V ρ)) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n ∧ ∃ cv caps,
      env.find? n = some (.indInfo cv caps) ∧ cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams lo.L.lvls)).length = ps.length ∧
      D.w (Level.substFn φ cv.levelParams lo.L.lvls) = w ∧
      FrameAccOutG w ctx.nP d (HoleQK ctx L met d) R D (Level.substFn φ cv.levelParams lo.L.lvls)
        psa (fun c => c = mm) := by
  have hcov := hok.1
  obtain ⟨⟨nPc, Lc, hqC, -⟩, -, hgrpL, hlvl, hgnames, -, -, -, -, -, -⟩ := hspec
  have h0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  have h0d : ctx.hiAt 0 ≤ d := Nat.le_trans h0 hd
  -- the node's canonical group lies in the key's recorded block
  obtain ⟨cvk, capsk, hfk⟩ : ∃ cv caps, env.find? kn.cname = some (.indInfo cv caps) := by
    have hmemh := ConLeche.groupOfK_head_mem (ctx := ctx) kn.cname
    obtain ⟨cv₀, caps₀, hf₀c⟩ := nestContainer_find hqC
    rcases ConLeche.mem_groupOfK hmemh with h | h
    · rw [h] at hf₀c; rw [← hcov.find]; exact ⟨cv₀, caps₀, hf₀c⟩
    · unfold ConLeche.nestBlockOf at h
      rw [hcov.find] at h
      split at h
      · rename_i cv caps hf; exact ⟨cv, caps, hf⟩
      · simp at h
  obtain ⟨D, hD, mmC, hmmC, hnC⟩ := hcov.cover kn.cname cvk capsk hfk hhd.1 hhd.2
  have hgin := groupOfK_in mp hcov hhd.1 hhd.2 hfk hD hmmC
    (by rw [hnC]; exact ConLeche.self_mem_groupOfK kn.cname)
  have hnG : n ∈ ConLeche.groupOfK ctx kn.cname := by
    rw [← hgrpL, ← hgnames]; exact hgrp
  obtain ⟨mm₀, hmm₀, hn₀⟩ := hgin _ (ConLeche.groupOfK_head_mem (ctx := ctx) kn.cname)
  obtain ⟨mm, hmm, hn⟩ := hgin n hnG
  obtain ⟨cv₀, caps₀, hf₀⟩ := (mp.lfp_ok D hD).2.1.1 mm₀ hmm₀
  obtain ⟨cv, caps, hfc⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  rw [hn] at hfc
  -- the block's level parameters
  obtain ⟨lps, hlps, hlenP₀, hcvl₀, hnL⟩ := contBlock_facts mp hcov hD hmm₀ hf₀
    (by rw [hn₀]; exact hqC)
  have hcvl : cv.levelParams = lps := by
    obtain ⟨cv', caps', hf', h'⟩ := hlps mm hmm
    rw [hn, hfc] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact h'
  obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hfc hfa
  change lo.L.lvls.length = cv.levelParams.length at hul
  rw [hcvl] at hul
  -- the parameter counts
  obtain ⟨Ln, hqn⟩ := hnPc
  obtain ⟨-, -, hlenPn, -, -⟩ := contBlock_facts mp hcov hD hmm (by rw [hn]; exact hfc)
    (by rw [hn]; exact hqn)
  have hlenPs : ∀ ψ, (D.params ψ).length = ps.length := hlenPn
  -- the node's frame fact along the image of the user's relation
  have hR₀ := holeRelAK_use hR hd (L' := lo.L) (metc := metc) hxl hsat (Aj := Aj) hmet
    (fun x hx => (hdsw x hx).1)
  have hΔc : (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)).length = ctx.hiAt 0 + lo.L.nF := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hΔ, htyl]; omega
  have hhead : D.member mm₀ = ((grpOfK lo).headD default).1 := by
    have hnames : (grpOfK lo).map (·.1) = ConLeche.groupOfK ctx kn.cname := by
      rw [grpOfK_names, hgnames, hgrpL]
    rw [hn₀, ← hnames]
    cases h : grpOfK lo with
    | nil => rw [h] at hnames; exact absurd hnames.symm (ConLeche.groupOfK_ne_nil kn.cname)
    | cons p ps' => simp
  have hkf : ∀ ρ, Sat V Δa ρ →
      keyFrame dsa (ctx.hiAt 0 + lo.L.nF) (useVal xs (d - ctx.hiAt 0) ρ) = keyFrame psa d ρ := by
    intro ρ hρ
    have := keyFrame_useVal (xs := xs) h0d ρ (hpos ρ hρ)
    rwa [hxl] at this
  have hdrop : ∀ ρ : Nat → V, dropV (d - d) ρ = ρ := by
    intro ρ; funext i; simp [dropV]
  have hwa' : denoteMeta mp.base2.acval env φ d
      (Expr.mkAppN (.const (D.member mm) lo.L.lvls) (ps ++ is)) = some wa := by rw [hn]; exact hwa
  have hfit : ∀ σ σ', useRel R xs (d - ctx.hiAt 0) σ σ' →
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ) ∧
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    rw [hkf ρ h1, hkf ρ' h2]
    have k1 := keyParamsFit mp hD hmm (by rw [hn]; exact hfc) (Nat.le_refl d) hwa'
      (by rw [hcvl, hlenPs]) hpsw hpsa ρ (hgr ρ h1)
    have k2 := keyParamsFit mp hD hmm (by rw [hn]; exact hfc) (Nat.le_refl d) hwa'
      (by rw [hcvl, hlenPs]) hpsw hpsa ρ' (hgr ρ' h2)
    rw [hdrop, hcvl] at k1 k2
    exact ⟨k1, k2⟩
  obtain ⟨hndl, -, hwD, Ac, hAc, hAcinv, hacc⟩ := ihn hok hhd.1 hhd.2 hD hmm₀ hhead hlps hul hdsw
    hdsa (by rw [hlenPs, hlenD]) (hnL.imp (fun ⟨L', hL', hne⟩ => ⟨_, L', hL', hne⟩) id) hR₀ hlayc
    hΔc hCds hLds hfit
  have hG : InGrp D (grpOfK lo) mm := ⟨hmm, by
    rw [List.contains_iff_mem, grpOfK_names, hn]; exact hgrp⟩
  -- the node's items, supported at the user
  have hU := itemSupp_use hR hd hxl (Aj := Aj) (metc := metc)
    fun j key nI hj hk hm hjx => (hmet j key nI hj hk hm hjx).1
  refine ⟨D, hD, mm, hmm, hn, cv, caps, hfc, by rw [hcvl]; exact hndl, hlenPs _, by rw [hcvl]; exact hwD,
    fun ρ => sigmaPairs (Ac (useVal xs (d - ctx.hiAt 0) ρ)) (fun _ => useU lo.L.nF Aj ρ),
    fun ρ => (univ_isTGUniverse hw).sigmaPairs_mem (hAc _) fun _ _ => useU_mem hw hAj ρ,
    fun ρ ρ' hag => ?_, ?_⟩
  · -- the bound reads the user's parameter positions only
    have hAeq : Ac (useVal xs (d - ctx.hiAt 0) ρ) = Ac (useVal xs (d - ctx.hiAt 0) ρ') := by
      refine hAcinv _ _ fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := hp
      have hpx : xs.length ≤ p := by simp only [NestCtx.hiAt] at hp2; omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + xs.length := ⟨p - xs.length, by omega⟩
      rw [useVal_base, useVal_base]
      have hq : q < ctx.hiAt 0 := by omega
      have hq2 : ctx.hiAt 0 - 1 - q < ctx.nP := by omega
      exact hag _ ⟨by omega, by omega⟩
    have hUeq : useU lo.L.nF Aj ρ = useU lo.L.nF Aj ρ' := by
      unfold useU
      congr 2
      funext j
      exact hAjinv j ρ ρ' hag
    show sigmaPairs _ _ = sigmaPairs _ _
    rw [hAeq, hUeq]
  · -- the composed supports
    rintro c rfl ρ ρ₀ hr i hiI x hx
    have hcomp := supports_compose hU (Ac := Ac)
      (Pre := fun σ y => i ∈ˢ D.idx (Level.substFn φ lps lo.L.lvls)
          (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ) c ∧
        y ∈ˢ app (D.carrier (Level.substFn φ lps lo.L.lvls)
          (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ) c) i)
      (Post := fun σ y => y ∈ˢ app (D.carrier (Level.substFn φ lps lo.L.lvls)
          (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ) c) i)
      (fun ρ ρ₀ hr y ⟨hi, hy⟩ => by
        obtain ⟨B, g, hB, hg, hs⟩ := hacc c hG _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i hi y hy
        exact ⟨B, g, hB, hg, fun ρ' hr' hh => hs _ ⟨ρ, ρ', hr', rfl, rfl⟩ hh⟩)
    obtain ⟨h1, -⟩ := hR.dom ρ ρ₀ hr
    rw [hcvl] at hiI hx ⊢
    rw [← hkf ρ h1] at hiI hx
    obtain ⟨B, g, hB, hg, hs⟩ := hcomp ρ ρ₀ hr x ⟨hiI, hx⟩
    refine ⟨B, g, hB, hg, fun ρ' hr' hh => ?_⟩
    obtain ⟨-, h2⟩ := hR.dom ρ ρ' hr'
    rw [← hkf ρ' h2]
    exact hs ρ' hr' hh

end ConLeche.Model
