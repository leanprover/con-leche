module

public import ConLeche.Model.Inductives.AccGen
public import ConLeche.Model.Inductives.HoleRelK
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Inductives.SumKit

public section

/-!
# The accessibility hole relation at a key-named layout (PRIMREC / NESTKN-M4)

`HoleRelAK` is `HoleRelA` (`NestPosAcc.lean`) at a LAYOUT of the key-named
positivity check (variant E) instead of a path of frames, the accessibility
twin of `HoleRelK`.  The admissible items (`HoleQK`) at depth `d`:

* a member hole at its full arity (as today);
* a flexible family at its index count — only where the node MET it
  (PROOFPLAN R1: an unmet family is unconstrained);
* an own hole at its member's full arity (`nestArity`, today's frame clause).

Related frames satisfy the context, agree off the holes, and the relation is
symmetric, left-reflexive and rich at the admissible items; the own holes are
blind in the layout's `DsF` (`FrameBlind`, today's frame clause).

`frameRelAK_holeRelAK`: the frame relation for accessibility (`frameRelA`)
over a relation at the node's BASE is a relation at the node's layout.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey NestHole LayoutK)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The admissible items -/

/-- **The admissible items at a layout** (see the module docstring). -/
@[expose] def HoleQK (ctx : NestCtx) (L : LayoutK) (met : List Nat) (d : Nat) :
    Nat → Nat → Prop :=
  fun i n =>
    (∃ t, t < ctx.names.length ∧ ctx.nP + t < d ∧ i = d - 1 - (ctx.nP + t) ∧
      n = ctx.nP + ctx.nIdxs.getD t 0) ∨
    (∃ (j : Nat) (key : NestKey), j < L.nF ∧ L.fams[j]? = some (key, n) ∧ j ∈ met ∧
      ctx.hiAt 0 + j < d ∧ i = d - 1 - (ctx.hiAt 0 + j)) ∨
    (∃ (g : Nat) (gn : Name), L.grp[g]? = some gn ∧ ctx.hiAt 0 + L.nF + g < d ∧
      i = d - 1 - (ctx.hiAt 0 + L.nF + g) ∧ n = ConLeche.nestArity ctx gn)

/-- One binder down, the admissible items are the same holes. -/
theorem shiftQ_holeQK {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    (hd : ctx.hiAt 0 + L.nF + L.grp.length ≤ d) (i n : Nat) :
    shiftQ (HoleQK ctx L met d) i n ↔ HoleQK ctx L met (d + 1) i n := by
  cases i with
  | zero =>
    simp only [shiftQ, false_iff]
    rintro (⟨t, ht, -, hi, -⟩ | ⟨j, key, hj, -, -, -, hi⟩ | ⟨g, gn, hg, -, hi, -⟩)
    · simp only [NestCtx.hiAt] at hd; omega
    · omega
    · have := (List.getElem?_eq_some_iff.mp hg).1; omega
  | succ i =>
    simp only [shiftQ]
    constructor
    · rintro (⟨t, ht, hlt, hi, hn⟩ | ⟨j, key, hj, hk, hm, hlt, hi⟩ | ⟨g, gn, hg, hlt, hi, hn⟩)
      · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
      · exact Or.inr (Or.inl ⟨j, key, hj, hk, hm, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨g, gn, hg, by omega, by omega, hn⟩)
    · rintro (⟨t, ht, hlt, hi, hn⟩ | ⟨j, key, hj, hk, hm, hlt, hi⟩ | ⟨g, gn, hg, hlt, hi, hn⟩)
      · refine Or.inl ⟨t, ht, ?_, by omega, hn⟩
        simp only [NestCtx.hiAt] at hd; omega
      · exact Or.inr (Or.inl ⟨j, key, hj, hk, hm, by omega, by omega⟩)
      · have := (List.getElem?_eq_some_iff.mp hg).1
        exact Or.inr (Or.inr ⟨g, gn, hg, by omega, by omega, hn⟩)

/-- The admissible items `k` positions further down. -/
theorem holeQK_shift {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d k i n : Nat}
    (h : HoleQK ctx L met d i n) : HoleQK ctx L met (d + k) (i + k) n := by
  rcases h with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, key, hj, hk, hm, hlt, rfl⟩ | ⟨g, gn, hg, hlt, rfl, hn⟩
  · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
  · exact Or.inr (Or.inl ⟨j, key, hj, hk, hm, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨g, gn, hg, by omega, by omega, hn⟩)

/-- **At the root layout the admissible items are the member holes**, as on
the empty path. -/
theorem holeQK_root_iff {ctx : NestCtx} {met : List Nat} {d i n : Nat} :
    HoleQK ctx (ConLeche.rootLayoutK ctx) met d i n ↔ HoleQ ctx [] d i n := by
  constructor
  · rintro (h | ⟨j, key, hj, -⟩ | ⟨g, gn, hg, -⟩)
    · exact Or.inl h
    · simp [ConLeche.rootLayoutK] at hj
    · simp [ConLeche.rootLayoutK] at hg
  · rintro (h | ⟨j, hk, hj, -⟩)
    · exact Or.inl h
    · simp at hj

/-- The admissible items at the base are admissible at the layout. -/
theorem holeQK_of_base {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d i n : Nat}
    (h : HoleQK ctx (layoutBaseK ctx L) met d i n) : HoleQK ctx L met d i n := by
  rcases h with h | h | ⟨g, gn, hg, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · simp at hg

/-- **The admissible items at a node's walk**: its own holes (at the top
`|grp|` positions, at their members' full arity) and the base's moved up. -/
theorem holeQK_frame {ctx : NestCtx} {L : LayoutK} {met : List Nat} {i n : Nat}
    (h : HoleQK ctx L met (ctx.hiAt 0 + L.nF + L.grp.length) i n) :
    (∃ g, ∃ hg : g < L.grp.length, i = L.grp.length - 1 - g ∧
        n = ConLeche.nestArity ctx L.grp[g]) ∨
      (L.grp.length ≤ i ∧ HoleQK ctx (layoutBaseK ctx L) met (ctx.hiAt 0 + L.nF)
        (i - L.grp.length) n) := by
  rcases h with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, key, hj, hk, hm, hlt, rfl⟩ | ⟨g, gn, hg, hlt, rfl, hn⟩
  · refine Or.inr ⟨by simp only [NestCtx.hiAt]; omega, Or.inl ⟨t, ht, ?_, ?_, hn⟩⟩
    · simp only [NestCtx.hiAt]; omega
    · simp only [NestCtx.hiAt]; omega
  · refine Or.inr ⟨by omega, Or.inr (Or.inl ⟨j, key, by simpa using hj, by simpa using hk, hm,
      by omega, by omega⟩)⟩
  · have hgl := (List.getElem?_eq_some_iff.mp hg)
    refine Or.inl ⟨g, hgl.1, by omega, ?_⟩
    rw [hn, hgl.2]

/-- **The admissible items at a node's walk, at its frame group** (`holeQK_frame`
read through the frame's group `grp`, whose names are the layout's). -/
theorem holeQK_split {ctx : NestCtx} {L : LayoutK} {met : List Nat} {grp : List (Name × Expr)}
    (hLgrp : L.grp = grp.map (·.1)) {hc : Nat} (hhc : hc = ctx.hiAt 0 + L.nF) :
    ∀ i n, HoleQK ctx L met (hc + grp.length) i n →
      (∃ j, ∃ _ : j < grp.length, i = grp.length - 1 - j ∧
        n = ConLeche.nestArity ctx grp[j].1) ∨
      (grp.length ≤ i ∧ HoleQK ctx (layoutBaseK ctx L) met hc (i - grp.length) n) := by
  have hgl : L.grp.length = grp.length := by rw [hLgrp, List.length_map]
  intro i n hq
  rw [show hc + grp.length = ctx.hiAt 0 + L.nF + L.grp.length by rw [hgl]; omega] at hq
  rcases holeQK_frame hq with ⟨g, hg', hi, hn⟩ | ⟨hle, hq'⟩
  · have hgg : g < grp.length := by rw [← hgl]; exact hg'
    refine Or.inl ⟨g, hgg, by rw [hi, hgl], ?_⟩
    rw [hn]
    congr 1
    simp [hLgrp]
  · rw [hgl, ← hhc] at hq'
    rw [hgl] at hle
    exact Or.inr ⟨hle, hq'⟩

/-! ## The relation -/

/-- **The accessibility hole relation at a layout** (see the module
docstring). -/
structure HoleRelAK (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (L : LayoutK)
    (met : List Nat) (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  /-- the layout's shape: families, then the own group -/
  hiEq : L.hi = ctx.hiAt 0 + L.nF + L.grp.length
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP L.hi)
  /-- the own holes are blind in the layout's parameters -/
  own : ∀ (g : Nat) (n : Name), L.grp[g]? = some n → ∀ dsa,
    DenoteMetaSpine m.acval env φ d L.dsF dsa →
    FrameBlind R (d - 1 - (ctx.hiAt 0 + L.nF + g)) dsa
  /-- the layout's parameters are scoped below its holes -/
  dsScoped : ∀ x ∈ L.dsF, Expr.WScoped L.hi x
  symm : R.Symm
  rich : RichOn (HoleQK ctx L met d) R
  /-- left-reflexive: a hole's richness enlarges the tuple at the SAME
  enclosing frame -/
  lrefl : ∀ ρ ρ₀, R ρ ρ₀ → R ρ ρ

/-- **Under a binder** whose domain carries its values to every larger
related frame: the relation one level deeper (`HoleRelA.underBoth`). -/
theorem HoleRelAK.underBoth {ctx : NestCtx} {L : LayoutK} {met : List Nat} {d : Nat}
    {Δa : List AnnotTerm} {R : FrameRel V} (h : HoleRelAK m φ ctx L met d Δa R) (hd : L.hi ≤ d)
    (ta : AnnotTerm)
    (htr : ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe (HoleQK ctx L met d) ρ ρ'' →
      ∀ x, x ∈ˢ interp V ρ ta → x ∈ˢ interp V ρ₀ ta → x ∈ˢ interp V ρ'' ta) :
    HoleRelAK m φ ctx L met (d + 1) (ta :: Δa) (R.underBoth ta) where
  hiEq := h.hiEq
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 hx'⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.underBoth ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  own := by
    intro g n hg dsa' hsp
    have hglt : g < L.grp.length := (List.getElem?_eq_some_iff.mp hg).1
    have hlt : ctx.hiAt 0 + L.nF + g < d := by have := h.hiEq; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + L.nF + g) = d - 1 - (ctx.hiAt 0 + L.nF + g) + 1 by omega]
    exact FrameBlind.underBoth (h.own g n hg dsa hdsa) ta
  dsScoped := h.dsScoped
  symm := h.symm.underBoth ta
  rich := RichOn.congrQ (shiftQ_holeQK (by have := h.hiEq; omega)) (h.rich.underBoth htr)
  lrefl := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, -⟩
    exact ⟨x, ρ, ρ, rfl, rfl, h.lrefl ρ ρ' hR, hx, hx⟩

/-- **The root layout's relation is the frameless one** (a member
constructor's walk). -/
theorem holeRelAK_root {ctx : NestCtx} {met : List Nat} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRelA m φ ctx [] d Δa R) :
    HoleRelAK m φ ctx (ConLeche.rootLayoutK ctx) met d Δa R where
  hiEq := by simp [ConLeche.rootLayoutK]
  dom := h.dom
  agree := by simpa [ConLeche.rootLayoutK] using h.agree
  own := by intro g n hg; simp [ConLeche.rootLayoutK] at hg
  dsScoped := by intro x hx; simp [ConLeche.rootLayoutK] at hx
  symm := h.symm
  rich := RichOn.congrQ (fun _ _ => holeQK_root_iff.symm) h.rich
  lrefl := h.lrefl

/-! ## The frame relation at a layout -/

set_option maxHeartbeats 1600000 in
/-- **The frame relation for accessibility is a hole relation at the
layout** (`frameRelA_holeRelA` at a layout): the flexible families and the
members inherited from the base, the own holes the group's (blind in `DsF`
by N2, rich by enlarging the tuple at one fibre). -/
theorem frameRelAK_holeRelAK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
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
    (hR₀ : HoleRelAK mp.base2 φ ctx (layoutBaseK ctx L) met hc Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hc ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hc ρ'))
    (hw' : D.w (Level.substFn φ lps us) ≠ 0) :
    HoleRelAK mp.base2 φ ctx L met (hc + grp.length) ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hc) := by
  have harity := grp_arity mp hD hnN hkN hfind hg (Level.substFn φ lps us)
  have hvl : ∀ ρp Y, (grpVals D (Level.substFn φ lps us) grp ρp Y).length = grp.length :=
    fun _ _ => grpVals_length _ _ _ _ _
  have hgl : L.grp.length = grp.length := by rw [hLgrp, List.length_map]
  have hagree0 : R₀.AgreesOff (holeP hc ctx.nP hc) := by
    have := hR₀.agree; rwa [layoutBaseK_hi, ← hhc] at this
  -- the tail below the key's depth agrees along the relation
  have htail : ∀ ρ ρ', R₀ ρ ρ' → ∀ j, ρ (j + hc) = ρ' (j + hc) :=
    fun ρ ρ' hr j => hagree0 ρ ρ' hr _ fun hp => by have := hp.1; omega
  -- a position of the frame: a group hole, or the enclosing frame's
  have hposE : ∀ (ρ ρp Y : Nat → V) (i : Nat), grp.length ≤ i →
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ i = ρ (i - grp.length) := by
    intro ρ ρp Y i hi
    have := consList_apply_add (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ (i - grp.length)
    rw [hvl, show i - grp.length + grp.length = i by omega] at this
    exact this
  -- a group hole's position
  have hposG : ∀ (ρ ρp Y : Nat → V) (j : Nat) (hj : j < grp.length),
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ (grp.length - 1 - j)
        = D.holeVal (Level.substFn φ lps us) ρp Y (D.names.idxOf (grp[j]).1) := by
    intro ρ ρp Y j hj
    rw [consList_getElem_pos (hvl ρp Y) hj]
    simp [grpVals]
  -- the members' arities at the group
  have hmm_of : ∀ (j : Nat) (hj : j < grp.length), ∃ mm, mm < D.k ∧
      D.names.idxOf (grp[j]).1 = mm ∧
      ConLeche.nestArity ctx (grp[j]).1 = (D.pars mm (Level.substFn φ lps us)).length
        + (D.ids mm (Level.substFn φ lps us)).length := by
    intro j hj
    have hpi : grp[j] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
    exact ⟨mm, hmm, hidx, by rw [harity _ hpi, hidx]⟩
  -- the admissible items at the frame
  have hsplit := holeQK_split (met := met) hLgrp hhc
  refine
    { hiEq := ?_, dom := ?_, agree := ?_, own := ?_, dsScoped := ?_, symm := ?_, rich := ?_,
      lrefl := ?_ }
  · -- the layout's shape
    rw [hLhi, hLgrp, List.length_map, hhc]
  · -- the context
    exact frameRelA_dom mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hR₀.dom
  · -- agreement off the holes
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, -, -, rfl, rfl⟩ i hi
    by_cases hig : i < grp.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [NestCtx.hiAt] at hhc hLhi ⊢ <;> omega
    rw [hposE _ _ _ _ (by omega), hposE _ _ _ _ (by omega)]
    refine hagree0 ρ ρ' hr _ fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, by omega, ?_⟩
    rw [hLhi]; omega
  · -- the own holes are blind in the layout's parameters
    rintro g n hgn dsa' hsp _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩ is
    have hj : g < grp.length := by
      have := (List.getElem?_eq_some_iff.mp hgn).1
      rw [hgl] at this; exact this
    rw [hLds] at hsp
    obtain ⟨dsa₀, hsp₀, rfl⟩ :=
      DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) (Nat.le_add_right hc grp.length)
        (fun x hx => (hds x hx).1) hsp
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
    rw [hmS ρ _ (hvl _ _), hmS ρ' _ (hvl _ _)]
    have hposi : hc + grp.length - 1 - (ctx.hiAt 0 + L.nF + g) = grp.length - 1 - g := by omega
    rw [hposi, hposG _ _ _ _ hj]
    obtain ⟨mm, hmm, hidx, -⟩ := hmm_of _ hj
    rw [hidx]
    obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
    obtain ⟨mm', -, -, hidx', -, -, -, -, -, hte⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (List.getElem_mem hj)
    rw [hidx] at hidx'
    subst hidx'
    calc (dsa.map (interp V ρ) ++ is).foldl app
          (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hc ρ') Y' mm)
        = (dsa.map (interp V ρ) ++ is).foldl app
          (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hc ρ) Y' mm) := by
          rw [holeVal_keyFrame_eq (parsLen_dsa mp hD hdsa hlenP hmm)
            (fun j => (htail ρ ρ' hr j).symm) rfl (Y' := Y')]
      _ = _ := grp_holeVal_apply mp hD hdsa hlenP hmm hs Y' is
      _ = _ := by rw [(hte ρ ρ' (hagree0 ρ ρ' hr)).holeFam]
      _ = _ := (grp_holeVal_apply mp hD hdsa hlenP hmm hs' Y' is).symm
  · -- the parameters are scoped
    intro x hx
    rw [hLhi]
    rw [hLds] at hx
    exact Expr.WScoped.mono (Nat.le_add_right hc grp.length) (hds x hx).1
  · -- symmetric
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    exact ⟨ρ', ρ, Y', Y, hR₀.symm ρ ρ' hr, hY', hY, rfl, rfl⟩
  · -- rich
    rintro _ _ ⟨ρ, ρ₀, Y, Y₀, hr, hY, hY₀, rfl, rfl⟩ i vs hQ hpt
    rcases hsplit i vs.length hQ with ⟨j, hj, rfl, hn⟩ | ⟨hle, hQ'⟩
    · -- an own hole: enlarge the tuple at the same enclosing frame
      obtain ⟨mm, hmm, hidx, har⟩ := hmm_of _ hj
      rw [hposG _ _ _ _ hj, hidx] at hpt
      have hlenv : vs.length = (D.pars mm (Level.substFn φ lps us)).length
          + (D.ids mm (Level.substFn φ lps us)).length := by rw [hn, har]
      rcases grp_hole_full mp hD hdsa hlenP hmm ρ Y hlenv with ⟨hfv, he⟩ | he
      · rw [he] at hpt
        have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
        have htt : tupW (D.u mm (Level.substFn φ lps us))
            (vs.drop (D.pars mm (Level.substFn φ lps us)).length)
            ∈ˢ D.idx (Level.substFn φ lps us) (keyFrame dsa hc ρ) mm := by
          refine Classical.byContradiction fun hni => ?_
          rw [app_off_dom_of_mem_piSet (hY mm hmmN) hni] at hpt
          exact not_mem_empty _ hpt
        obtain ⟨Y'', hY'', hle'', hz⟩ := tuple_enlarge (t := mm)
          (tt := tupW (D.u mm (Level.substFn φ lps us))
            (vs.drop (D.pars mm (Level.substFn φ lps us)).length)) hw' hY
        refine ⟨consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) Y'') ρ,
          ⟨ρ, ρ, Y, Y'', hR₀.lrefl ρ ρ₀ hr, hY, hY'', rfl, rfl⟩, ?_, empty, ?_,
          pt_ne_empty.symm⟩
        · rintro ⟨i', vs', y⟩ ho hH
          unfold Adm at ho
          rcases hsplit i' vs'.length ho with ⟨j', hj', rfl, hn'⟩ | ⟨hle', -⟩
          · obtain ⟨mm', hmm', hidx', har'⟩ := hmm_of _ hj'
            unfold Holds at hH ⊢
            simp only at hH ⊢
            rw [hposG _ _ _ _ hj', hidx'] at hH ⊢
            rw [holeVal_keyFrame (parsLen_dsa mp hD hdsa hlenP hmm')] at hH ⊢
            exact foldlApp_mono_holeFam (by rw [List.length_append, hn', har'])
              (fun bs => hle'' mm' _) y hH
          · unfold Holds at hH ⊢
            simp only at hH ⊢
            rw [hposE _ _ _ _ hle'] at hH ⊢
            exact hH
        · show empty ∈ˢ vs.foldl app (consList (grpVals D (Level.substFn φ lps us) grp
            (keyFrame dsa hc ρ) Y'') ρ (grp.length - 1 - j))
          rw [hposG _ _ _ _ hj, hidx]
          rw [holeVal_keyFrame (parsLen_dsa mp hD hdsa hlenP hmm), holeFam_app _ hfv]
          exact hz hmmN htt
      · rw [he] at hpt
        exact absurd hpt (not_mem_empty _)
    · -- an enclosing hole: the enclosing relation's richness
      rw [hposE _ _ _ _ hle] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR₀.rich ρ ρ₀ hr (i - grp.length) vs hQ' hpt
      let Y'' : Nat → V := mixT (InGrp D grp)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hc ρ'')) Y
      have hY'' : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa hc ρ'')) Y'' := by
        intro c hc'
        show mixT (InGrp D grp) _ Y c ∈ˢ _
        unfold mixT
        split
        · rename_i hG
          rw [← grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG
            (hagree0 ρ ρ'' hr'')]
          exact hY c hc'
        · exact lfpTuple_mem _ _ _ _ c hc'
      have hgv : grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ'') Y''
          = grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ) Y :=
        grpVals_eq mp hD hdsa hlenP (fun j => (htail ρ ρ'' hr'' j).symm)
          (fun p hp => by
            show mixT (InGrp D grp) _ Y _ = _
            unfold mixT
            rw [if_pos (grp_inGrp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp)])
          (fun p hp => grp_idx_lt mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp)
      refine ⟨consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hc ρ'') Y'') ρ'',
        ⟨ρ, ρ'', Y, Y'', hr'', hY, hY'', rfl, rfl⟩, ?_, z, ?_, hzp⟩
      · rintro ⟨i', vs', y⟩ ho hH
        unfold Adm at ho
        unfold Holds at hH ⊢
        simp only at hH ⊢
        rcases hsplit i' vs'.length ho with ⟨j', hj', rfl, -⟩ | ⟨hle', hQo⟩
        · rw [hgv, hposG _ _ _ _ hj']
          rw [hposG _ _ _ _ hj'] at hH
          exact hH
        · rw [hposE _ _ _ _ hle'] at hH ⊢
          exact hle'' (i' - grp.length, vs', y) hQo hH
      · show z ∈ˢ vs.foldl app (consList _ ρ'' i)
        rw [hposE _ _ _ _ hle]
        exact hz
  · -- left-reflexive
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, -, rfl, rfl⟩
    exact ⟨ρ, ρ, Y, Y, hR₀.lrefl ρ ρ' hr, hY, hY, rfl, rfl⟩

end ConLeche.Model
