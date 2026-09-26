module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Model.Inductives.TargetNodeList

public section

/-!
# Toward the node presentation's DYNAMIC part (lane NESTIND, session 20)

`TgtNodeDyn` (`TargetNodeList.lean`) asks, at every node of the list, the
kit's `trans`: a spine fitting at an ADMISSIBLE frame of the node, at a
hole tuple below the node's true carrier, fits at the true frame and
carrier.  At a derived node (a container instantiation) this is the
frame's monotonicity in its key's parameters — `FrameMono`, the
positivity derivation's conclusion at the frame — along a hole relation
from the admissible valuation of the node's frame stack to the TRUE one.
This module supplies the two generic pieces:

* `trans_of_frameConcl` — `trans` from `FrameMono`'s conclusion (at the
  group tuple `grpTuple`) when the group is the container's WHOLE
  recorded block and the block has no instance components (`LfpCover.wid`):
  the clause's `fitsMono` along `Y ≤ carrier`, then the fit's dependence
  on the members only (`LfpDatum.hfits_congr_members`);
* `frameRelS_holeRel` — the frame relation generalised (the twin of
  `frameRel_holeRel`, `ContWalk.lean`, kept local): the SMALLER side's new
  holes hold ANY tuple below the larger side's carrier on the group (a
  node's separated tuple, the kit's `S`), the LARGER side's new holes any
  values that contain the carrier's hole values at the key's parameters
  and full arity (the group's CONSTANTS at the true valuation, by the
  clause's `leaf`).  This is where `HoleRel.frame` must be stated at FULL
  arity only (lane NESTIND, session 20): a partial application of a hole
  value is a graph, and a graph over a smaller family is not contained in
  one over a larger family.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps grpNews)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `trans` from the frame's conclusion -/

section Trans

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V} {ψ : Name → Nat}

/-- **`trans` at a derived node from `FrameMono`'s conclusion**: the frame's
group covers every member (`hall`) and the operator is as wide as its
members (`hwid`); the admissible frame `ρs` reads the true frame `ρt`'s
index sets.  A spine fitting at `ρs` and a tuple `Y` below the true
carrier fits at `ρs` and the true carrier (`fitsMono`), hence at `ρs` and
the group tuple (they agree on the members), hence — the frame's
conclusion — at the true frame and carrier. -/
theorem trans_of_frameConcl (hcl : LfpClause acval D) (hwid : D.N = D.k)
    {grp : List (Name × Expr)} (hall : ∀ c, c < D.k → InGrp D grp c) {ρs ρt : Nat → V}
    (hconcl : ∀ g, InGrp D grp g → ∀ t j fs,
      D.HFits ψ ρs (grpTuple D ψ grp ρs ρt) t g j fs → D.HFits ψ ρt (D.carrier ψ ρt) t g j fs)
    (hsat : Sat V (D.params ψ).reverse ρs) (hidx : ∀ c, c < D.N → D.idx ψ ρs c = D.idx ψ ρt c)
    {Y : Nat → V}
    (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ ρt) Y)
    (hle : TupleLe D.N (D.idx ψ ρt) Y (D.carrier ψ ρt)) {t : V} {c j : Nat} {fs : List V}
    (hc : c < D.N) (hf : D.HFits ψ ρs Y t c j fs) : D.HFits ψ ρt (D.carrier ψ ρt) t c j fs := by
  have hC : InTupleSpace (D.w ψ) D.N (D.idx ψ ρs) (D.carrier ψ ρt) := fun m hm => by
    rw [hidx m hm]; exact lfpTuple_mem _ _ _ _ m hm
  have hY' : InTupleSpace (D.w ψ) D.N (D.idx ψ ρs) Y := fun m hm => by
    rw [hidx m hm]; exact hY m hm
  have hle' : TupleLe D.N (D.idx ψ ρs) Y (D.carrier ψ ρt) := fun m hm => by
    rw [hidx m hm]; exact hle m hm
  have h1 := hcl.fitsMono ψ ρs hsat Y _ hY' hC hle' c hc t j fs hf
  have hck : c < D.k := hwid ▸ hc
  refine hconcl c (hall c hck) t j fs ((LfpDatum.hfits_congr_members fun m hm => ?_).mp h1)
  unfold grpTuple
  rw [if_pos (hall m hm)]

end Trans

/-! ## The frame relation at a separated tuple -/

/-- **The frame relation at a separated tuple**: the enclosing relation at
the key's depth, the smaller side extended by the group's hole values at
a tuple `Y` chosen by `A`, the larger side by the values `vL`. -/
@[expose] def frameRelS (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (dsa : List AnnotTerm) (hi : Nat)
    (A : (Nat → V) → (Nat → V) → (Nat → V) → Prop) (vL : (Nat → V) → List V) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ' Y, R₀ ρ ρ' ∧ A ρ ρ' Y ∧
    σ = consList (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ ∧ σ' = consList (vL ρ') ρ'

/-- A tuple of the space below another on the group fits under it at every
spine of the group member's hole leaf. -/
theorem app_tupW_sub {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} {Y X : Nat → V} {mm : Nat}
    (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y) (hmm : mm < D.N)
    (hle : ∀ t, t ∈ˢ D.idx ψ ρp mm → app (Y mm) t ⊆ˢ app (X mm) t) (bs : List V) :
    app (Y mm) (tupW (D.u mm ψ) bs) ⊆ˢ app (X mm) (tupW (D.u mm ψ) bs) := by
  by_cases ht : tupW (D.u mm ψ) bs ∈ˢ D.idx ψ ρp mm
  · exact hle _ ht
  · rw [app_off_dom_of_mem_piSet (hY mm hmm) ht]
    intro x hx
    exact absurd hx (not_mem_empty x)

/-- A hole relation is inherited by a sub-relation. -/
theorem HoleRel.restrict {env : Env} {m : EnvModel V env} {φ : Name → Nat} {ctx : NestCtx}
    {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm} {R₀ R : FrameRel V}
    (h : HoleRel m φ ctx prog d Δa R₀) (hsub : ∀ a b, R a b → R₀ a b) :
    HoleRel m φ ctx prog d Δa R where
  dom := fun a b hr => h.dom a b (hsub a b hr)
  agree := fun a b hr => h.agree a b (hsub a b hr)
  member := fun t ht a b hr => h.member t ht a b (hsub a b hr)
  frame := fun i hk hki dsa hsp ni har a b hr => h.frame i hk hki dsa hsp ni har a b (hsub a b hr)
  dsScoped := h.dsScoped

/-- **A hole relation, pair by pair**: every related pair lies in some hole
relation (the frames' scoping is the relation's own). -/
theorem HoleRel.of_pointwise {env : Env} {m : EnvModel V env} {φ : Name → Nat} {ctx : NestCtx}
    {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm} {R : FrameRel V}
    (h : ∀ a b, R a b → ∃ R', HoleRel m φ ctx prog d Δa R' ∧ R' a b)
    (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x) :
    HoleRel m φ ctx prog d Δa R where
  dom := fun a b hr => by obtain ⟨R', h', hr'⟩ := h a b hr; exact h'.dom a b hr'
  agree := fun a b hr => by obtain ⟨R', h', hr'⟩ := h a b hr; exact h'.agree a b hr'
  member := fun t ht a b hr => by obtain ⟨R', h', hr'⟩ := h a b hr; exact h'.member t ht a b hr'
  frame := fun i hk hki dsa hsp ni har a b hr => by
    obtain ⟨R', h', hr'⟩ := h a b hr; exact h'.frame i hk hki dsa hsp ni har a b hr'
  dsScoped := hsc

section Frame

variable {env : Env} {φ : Name → Nat} {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
  {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

/-- **The frame relation at a separated tuple is a hole relation** of the
frame's walk: the smaller side's tuple `Y` lies in its key frame's space
and below the larger side's carrier on the group (`hA`), the larger side's
values inhabit the holes' entries (`hvLdom`) and contain the carrier's
hole values at the key's parameters and full arity (`hvL`). -/
theorem frameRelS_holeRel {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List AnnotTerm} {R₀ : FrameRel V} (hR₀ : HoleRel mp.base2 φ ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {A : (Nat → V) → (Nat → V) → (Nat → V) → Prop} {vL : (Nat → V) → List V}
    (hA : ∀ ρ ρ' Y, R₀ ρ ρ' → A ρ ρ' Y →
      InTupleSpace (D.w (Level.substFn φ lps us)) D.N
        (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y ∧
      ∀ c, InGrp D grp c → ∀ t, t ∈ˢ D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ) c →
        app (Y c) t ⊆ˢ app (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') c) t)
    (hvLlen : ∀ ρ', (vL ρ').length = grp.length)
    (hvLdom : ∀ ρ ρ', R₀ ρ ρ' → SpineFit ρ' (grpTys mp.base2 φ grp) (vL ρ'))
    (hvL : ∀ ρ ρ', R₀ ρ ρ' → ∀ (p : Nat) (hp : p < grp.length) (is : List V),
      is.length + ds.length = ConLeche.nestArity ctx (grp[p]'hp).1 →
      (dsa.map (interp V ρ') ++ is).foldl app
          (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ')
            (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) (D.names.idxOf (grp[p]'hp).1))
        ⊆ˢ (dsa.map (interp V ρ') ++ is).foldl app ((vL ρ')[p]'(by rw [hvLlen]; exact hp))) :
    HoleRel mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRelS R₀ D (Level.substFn φ lps us) grp dsa hi A vL) := by
  subst hhi
  refine HoleRel.of_pointwise (fun σ σ' hr => ?_) ?_
  · obtain ⟨ρ, ρ', Y, hr, hAY, rfl, rfl⟩ := hr
    obtain ⟨hYs, hYle⟩ := hA ρ ρ' Y hr hAY
    -- the enclosing relation at the one pair
    have hR₁ := hR₀.restrict (R := fun a b => a = ρ ∧ b = ρ') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact hr
    have hlenN : (grpNews us ds (ctx.hiAt prog.length) grp).length = grp.length := by
      simp [grpNews]
    have hext := HoleRel.extend hR₁ (grpNews us ds (ctx.hiAt prog.length) grp)
      (fun x hx a ha => by
        simp only [grpNews, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        exact (hds a ha).1)
      (grpTys mp.base2 φ grp).reverse
      (fun ρ₁ _ => grpVals D (Level.substFn φ lps us) grp
        (keyFrame dsa (ctx.hiAt prog.length) ρ₁) Y)
      (fun _ ρ₁' => vL ρ₁')
      (fun _ _ => by simp [grpVals, grpNews]) (fun _ ρ₁' => by rw [hvLlen]; simp [grpNews])
      ?_ ?_
    · rw [hlenN] at hext
      exact ⟨_, hext, ρ, ρ', ⟨rfl, rfl⟩, rfl, rfl⟩
    · -- the holes' values inhabit their entries
      rintro a b ⟨ha, hb⟩
      rw [ha, hb]
      obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
      refine ⟨?_, ?_⟩
      · exact sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
          _ Y hYs ρ)
      · exact sat_of_spineFit h2 (hvLdom ρ ρ' hr)
    · -- the new holes grow at their keys' parameters, at full arity
      rintro a b ⟨ha, hb⟩ p hk hkp dsa' hsp' hp is har
      rw [ha, hb]
      have hp' : p < grp.length := by simpa [grpNews] using hp
      simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hp', Option.map_some,
        Option.some.injEq] at hkp
      subst hkp
      obtain rfl := DenoteMetaSpine.unique hdsa hsp'
      have hpi : grp[p] ∈ grp := List.getElem_mem _
      obtain ⟨mm, hmm, hpm, hidx, -, -, -, -, -, hte⟩ :=
        grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
      obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
      have hG : InGrp D grp mm := ⟨hmm, by
        rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hpi, hpm⟩⟩
      have hmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfpClause_of_mem hD).kN
      -- the index count: the kernel's arity is the member's telescope
      have harity := grp_arity mp hD hnN hkN hfind hg (Level.substFn φ lps us) _ hpi
      rw [hidx] at harity
      have hpl := parsLen_dsa mp hD hdsa hlenP hmm
      have hisl : is.length = (D.ids mm (Level.substFn φ lps us)).length := by
        have := DenoteMetaSpine.length_eq hdsa
        simp only at har
        omega
      refine Subset.trans ?_ (hvL ρ ρ' hr p hp' is (by simpa using har))
      simp only [grpVals, List.getElem_map, hidx]
      rw [grp_holeVal_apply mp hD hdsa hlenP hmm hs,
        grp_holeVal_apply mp hD hdsa hlenP hmm hs',
        (hte ρ ρ' (hR₀.agree ρ ρ' hr)).holeFam]
      exact foldlApp_mono_holeFam hisl fun bs =>
        app_tupW_sub hYs hmN (hYle mm hG) bs
  · -- the frames' parameter terms are scoped (the extension's own, at the
    -- empty relation)
    have h0 := HoleRel.extend (hR₀.restrict (R := fun _ _ => False) fun _ _ h => h.elim)
      (grpNews us ds (ctx.hiAt prog.length) grp)
      (fun x hx a ha => by
        simp only [grpNews, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        exact (hds a ha).1)
      (grpTys mp.base2 φ grp).reverse
      (fun _ _ => List.replicate (grpNews us ds (ctx.hiAt prog.length) grp).length empty)
      (fun _ _ => List.replicate (grpNews us ds (ctx.hiAt prog.length) grp).length empty)
      (fun _ _ => List.length_replicate) (fun _ _ => List.length_replicate)
      (fun _ _ h => h.elim) (fun _ _ h => h.elim)
    exact h0.dsScoped

end Frame
end ConLeche.Model

/-! ## The member holes at a derived node's admissible valuation

A derived node's frame stack holds the block's member holes below its
frames.  At the TRUE valuation they hold the member CONSTANTS (their
readings, `nodeTrueVal`), which a hole relation compares at every
full-arity argument list (`HoleRel.member`); at the block's own
parameters a constant reads the carrier (the clause's `leaf`), elsewhere
another instance's.  The admissible member hole is therefore PATCHED
(design (i) of session 19): the separated tuple `Y₀`'s family at the
block's own parameters `P`, the constant's value elsewhere — contained in
the constant at every full-arity argument list once `Y₀` is below the
carrier at `P`. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

open Classical in
/-- **The patched member hole**: over member `m`'s own parameters and
indices (read from `ρ`, below the parameter frame), `Y₀`'s component at
the block's parameters `P`, the value `cv` (the member constant's)
applied elsewhere. -/
@[expose] noncomputable def memberPatch (D : LfpDatum V) (ψ : Name → Nat) (ρ : Nat → V)
    (P : List V) (Y₀ : Nat → V) (cv : V) (m : Nat) : V :=
  holeFam ρ (D.pars m ψ ++ D.ids m ψ) fun as =>
    if as.take (D.pars m ψ).length = P then
      app (Y₀ m) (tupW (D.u m ψ) (as.drop (D.pars m ψ).length))
    else as.foldl app cv

/-- A spine fitting a member's own parameter telescope fits the block's. -/
theorem spineFit_params_of_pars {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}
    (hcl : LfpClause acval D) {m : Nat} (hm : m < D.k) {ψ : Name → Nat} {ρ : Nat → V}
    {as : List V} (h : SpineFit ρ (D.pars m ψ) as) : SpineFit ρ (D.params ψ) as := by
  have hs := sat_of_spineFit (Sat_nil (V := V) ρ) h
  rw [List.append_nil] at hs
  refine spineFit_of_sat_consList' ?_ (hcl.parsSatInv m hm ψ _ hs)
  rw [SpineFit.length_eq h, hcl.parsLen m hm ψ]

/-- **The patched member hole is below the member constant** at every
full-arity argument list, once `Y₀` is below the carrier at the block's
parameters `P` (the clause's `leaf` there; elsewhere they agree; off the
member's telescope the patch is empty). -/
theorem memberPatch_sub {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}
    (hcl : LfpClause acval D) {m : Nat} (hm : m < D.k) {ψ : Name → Nat} {ρ : Nat → V}
    {P : List V} (hP : SpineFit ρ (D.params ψ) P) {Y₀ : Nat → V}
    (hY : ∀ bs, app (Y₀ m) (tupW (D.u m ψ) bs)
      ⊆ˢ app (D.carrier ψ (consList P ρ) m) (tupW (D.u m ψ) bs))
    (as : List V) (hlen : as.length = (D.pars m ψ).length + (D.ids m ψ).length) :
    as.foldl app (memberPatch D ψ ρ P Y₀ (interp V ρ (acval (D.member m) ψ)) m)
      ⊆ˢ as.foldl app (interp V ρ (acval (D.member m) ψ)) := by
  classical
  unfold memberPatch
  rcases holeFam_foldl_full (ρ := ρ) (Fs := D.pars m ψ ++ D.ids m ψ) (vs := as)
      (fun as => if as.take (D.pars m ψ).length = P then
        app (Y₀ m) (tupW (D.u m ψ) (as.drop (D.pars m ψ).length))
      else as.foldl app (interp V ρ (acval (D.member m) ψ)))
      (by rw [List.length_append]; exact hlen) with ⟨hfit, heq⟩ | he
  · rw [heq]
    split
    · rename_i hP'
      obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_split hfit
      have hl1 : as₁.length = (D.pars m ψ).length := SpineFit.length_eq h1
      rw [List.take_left' hl1] at hP'
      subst hP'
      rw [List.drop_left' hl1, hcl.leaf m hm ψ ρ as₁ as₂ hP h2]
      exact hY as₂
    · exact Subset.refl _
  · rw [he]
    intro x hx
    exact absurd hx (not_mem_empty x)

/-- The clause's `leaf`, the constant's value read at any valuation. -/
theorem interp_acval_closed_leaf {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}
    (hcl : LfpClause acval D) {mm : Nat} (hm : mm < D.k) {ψ : Name → Nat} {ρ : Nat → V}
    {as is : List V} (h1 : SpineFit ρ (D.params ψ) as) (h2 : SpineFit (consList as ρ) (D.ids mm ψ) is)
    (σ : Nat → V) (hclosed : interp V σ (acval (D.member mm) ψ) = interp V ρ (acval (D.member mm) ψ)) :
    (as ++ is).foldl app (interp V σ (acval (D.member mm) ψ))
      = app (D.carrier ψ (consList as ρ) mm) (tupW (D.u mm ψ) is) := by
  rw [hclosed]; exact hcl.leaf mm hm ψ ρ as is h1 h2

/-- **A frame hole's TRUE value**: at a key frame satisfying the block's
parameters, the carrier's hole value applied to the key's parameters and
a full index spine is contained in the member CONSTANT's value applied to
the same (the clause's `leaf`) — the premise `hvL` of `frameRelS_holeRel`
at the true valuation, whose frame holes hold the group's constants. -/
theorem keyHole_sub_const {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}
    (hcl : LfpClause acval D) {mm : Nat} (hm : mm < D.k) {ψ : Name → Nat}
    {dsa : List AnnotTerm} {hi : Nat} {ρ : Nat → V}
    (hl : (D.pars mm ψ).length = dsa.length) (σ : Nat → V)
    (hclosed : ∀ σ σ' : Nat → V, interp V σ (acval (D.member mm) ψ)
      = interp V σ' (acval (D.member mm) ψ)) (is : List V)
    (his : is.length = (D.ids mm ψ).length) :
    (dsa.map (interp V ρ) ++ is).foldl app
        (D.holeVal ψ (keyFrame dsa hi ρ) (D.carrier ψ (keyFrame dsa hi ρ)) mm)
      ⊆ˢ (dsa.map (interp V ρ) ++ is).foldl app (interp V σ (acval (D.member mm) ψ)) := by
  rw [holeVal_keyFrame hl]
  rcases holeFam_foldl_full (ρ := fun j => ρ (j + hi)) (Fs := D.pars mm ψ ++ D.ids mm ψ)
      (vs := dsa.map (interp V ρ) ++ is)
      (fun vs => app (D.carrier ψ (keyFrame dsa hi ρ) mm) (tupW (D.u mm ψ)
        (vs.drop (D.pars mm ψ).length)))
      (by simp [his, hl]) with ⟨hfit, heq⟩ | he
  · rw [heq]
    obtain ⟨as₁, as₂, hsplit, h1, h2⟩ := spineFit_append_split hfit
    have hl1 : as₁.length = (D.pars mm ψ).length := SpineFit.length_eq h1
    have hlm : (dsa.map (interp V ρ)).length = as₁.length := by simp [hl1, hl]
    obtain ⟨rfl, rfl⟩ := List.append_inj hsplit hlm
    rw [show (D.pars mm ψ).length = (dsa.map (interp V ρ)).length by simp [hl],
      List.drop_left, interp_acval_closed_leaf hcl hm (spineFit_params_of_pars hcl hm h1) h2 σ
        (hclosed σ _)]
    unfold keyFrame
    exact Subset.refl _
  · rw [he]
    intro x hx
    exact absurd hx (not_mem_empty x)

end ConLeche.Model
