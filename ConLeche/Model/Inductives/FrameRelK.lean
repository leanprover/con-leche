module

public import ConLeche.Model.Inductives.HoleRelK
public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.SumKit

public section

/-!
# The frame relation at a key-named layout (PRIMREC / NESTKN-M2)

A node of the key-named positivity check walks its crests at its layout
`L`: the flexible families (its BASE, depth `hc = hiAt0 + L.nF`) and above
them its own group's holes.  `frameRelK_holeRelK`: the frame relation
(`frameRel`, `ContWalk.lean`) built over a hole relation at the base is a
hole relation at the whole layout — the families inherited from the base,
the own holes growing at `DsF` exactly as today's frame holes
(`frameRel_grow`).  With `frameIterGen` this is the node's frame fact
(`PosDerivMonoK.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal NestCtx NestKey LayoutK)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **The frame relation is a hole relation at the layout** (see the module
docstring). -/
theorem frameRelK_holeRelK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hc : Nat}
    {ds : List Expr} (hds : ∀ x ∈ ds, Expr.WScoped hc x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mp.base2.acval env φ hc ds dsa)
    (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
    {grp : List (Name × Expr)} (hg : GrpWf ctx D hc us ds grp)
    {L : LayoutK} {met : List Nat} (hLgrp : L.grp = grp.map (·.1)) (hLds : L.dsF = ds)
    (hhc : hc = ctx.hiAt 0 + L.nF) (hLhi : L.hi = hc + grp.length)
    {Δh : List AnnotTerm} {R₀ : FrameRel V}
    (hR₀ : HoleRelK mp.base2 φ ctx (layoutBaseK ctx L) met hc Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hc ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hc ρ')) :
    HoleRelK mp.base2 φ ctx L met (hc + grp.length) ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRel R₀ D (Level.substFn φ lps us) grp dsa hc) := by
  have hagree : R₀.AgreesOff (holeP hc ctx.nP hc) := by
    have := hR₀.agree; rwa [layoutBaseK_hi, ← hhc] at this
  have hvS : ∀ ρ ρ', (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) (keyFrame dsa hc ρ'))).length
        = grp.length := fun _ _ => by simp [grpVals]
  have hvL : ∀ ρ', (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hc ρ'))).length = grp.length :=
    fun _ => by simp [grpVals]
  have hle0 : ctx.hiAt 0 ≤ hc := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the layout's shape
    rw [hLhi, hLgrp, List.length_map, hhc]
  · -- dom
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact frameRel_sat mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hR₀.dom hagree ρ ρ' hr
  · -- agree
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    by_cases hig : i < grp.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [NestCtx.hiAt] at hle0 ⊢ <;> omega
    obtain ⟨j, rfl⟩ : ∃ j, i = j + grp.length := ⟨i - grp.length, by omega⟩
    have e1 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) (keyFrame dsa hc ρ'))) ρ j
    have e2 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hc ρ'))) ρ' j
    rw [hvS] at e1; rw [hvL] at e2
    rw [e1, e2]
    refine hagree ρ ρ' hr j fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, by omega, ?_⟩
    rw [hLhi]; omega
  · -- member
    rintro t ht _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.nP + t < hc := by simp only [NestCtx.hiAt] at hle0 ⊢; omega
    have e1 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) (keyFrame dsa hc ρ'))) ρ
      (hc - 1 - (ctx.nP + t))
    have e2 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hc ρ'))) ρ' (hc - 1 - (ctx.nP + t))
    rw [hvS] at e1; rw [hvL] at e2
    rw [show hc + grp.length - 1 - (ctx.nP + t) = hc - 1 - (ctx.nP + t) + grp.length by omega,
      e1, e2]
    exact hR₀.member t ht ρ ρ' hr as has
  · -- the flexible families, inherited from the base
    rintro j key nI hj hk hmet _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ as has
    have hlt : ctx.hiAt 0 + j < hc := by omega
    have e1 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) (keyFrame dsa hc ρ'))) ρ
      (hc - 1 - (ctx.hiAt 0 + j))
    have e2 := consList_apply_add (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hc ρ'))) ρ' (hc - 1 - (ctx.hiAt 0 + j))
    rw [hvS] at e1; rw [hvL] at e2
    rw [show hc + grp.length - 1 - (ctx.hiAt 0 + j) = hc - 1 - (ctx.hiAt 0 + j) + grp.length by
      omega, e1, e2]
    exact hR₀.fam j key nI hj hk hmet ρ ρ' hr as has
  · -- the own holes: the group's, growing at `DsF`
    rintro g n hgn dsa' hsp ni - _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ is his
    have hgl : g < grp.length := by
      have := (List.getElem?_eq_some_iff.mp hgn).1
      rw [hLgrp, List.length_map] at this; exact this
    rw [hLds] at hsp
    obtain ⟨dsa₀, hsp₀, rfl⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ)
      (Nat.le_add_right hc grp.length) (fun x hx => (hds x hx).1) hsp
    obtain rfl := DenoteMetaSpine.unique hdsa hsp₀
    rw [show hc + grp.length - hc = grp.length by omega]
    have hmS : ∀ σ xs, xs.length = grp.length →
        (dsa.map (AnnotTerm.liftN grp.length · 0)).map (interp V (consList xs σ))
          = dsa.map (interp V σ) := by
      intro σ xs hx
      rw [List.map_map]
      refine List.map_congr_left fun a _ => ?_
      show interp V (consList xs σ) (a.liftN grp.length 0) = _
      rw [← hx, interp_liftN_consList]
    rw [hmS ρ _ (hvS ρ ρ'), hmS ρ' _ (hvL ρ')]
    have hpos : hc + grp.length - 1 - (ctx.hiAt 0 + L.nF + g) = grp.length - 1 - g := by omega
    rw [hpos, consList_getElem_pos (hvS ρ ρ') hgl, consList_getElem_pos (hvL ρ') hgl]
    exact frameRel_grow mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hagree hfit ρ ρ' hr
      g hgl is
  · -- the parameters stay scoped
    intro x hx
    rw [hLhi]
    rw [hLds] at hx
    exact Expr.WScoped.mono (Nat.le_add_right hc grp.length) (hds x hx).1

end ConLeche.Model
