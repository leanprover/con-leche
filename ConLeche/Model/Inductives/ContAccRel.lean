module

public import ConLeche.Model.Inductives.ContWalk
public import ConLeche.Model.Inductives.NestPosAcc
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The container frame's accessibility relation (lane ACCMODEL, session 3)

The twin of `frameRel`/`frameRel_holeRel` (`ContWalk.lean`) for the
accessibility route: a container frame's walk runs along `frameRelA` — the
enclosing relation `R₀` at the key's depth, extended by the reached group's
hole values at ANY tuple of the container's space (comparable frames, no
order) — and `frameRelA` is an accessibility hole relation (`HoleRelA`) of
the frame's walk (`frameRelA_holeRelA`).

The one new fact is that a group member's hole value reads its key frame
only through the frame's TAIL (`holeVal_keyFrame`: the λ-tower binds the
parameters itself), so the frame's holes are blind in their keys'
parameters (with N2's `TeleEq` for the index telescope), and a hole value
does not move when the enclosing frame changes off the holes.  Richness: a
new hole is enlarged at the SAME enclosing frame (`lrefl`, the tuple
enlarged at one fibre as in `LfpDatum.accRel_rich`); an enclosing hole by
the enclosing relation's own richness, the tuple kept on the group.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## A hole value reads only its key frame's tail -/

/-- **A group member's hole value at a key frame** is the λ-tower over the
member's parameters and indices read from the key frame's TAIL: the
parameters are bound by the tower itself. -/
theorem holeVal_keyFrame {D : LfpDatum V} {ψ : Name → Nat} {dsa : List AnnotTerm} {hi : Nat}
    {c : Nat} (hl : (D.pars c ψ).length = dsa.length) (ρ Y : Nat → V) :
    D.holeVal ψ (keyFrame dsa hi ρ) Y c
      = holeFam (fun j => ρ (j + hi)) (D.pars c ψ ++ D.ids c ψ)
          (fun vs => app (Y c) (tupW (D.u c ψ) (vs.drop (D.pars c ψ).length))) := by
  unfold LfpDatum.holeVal keyFrame
  have hl' : (D.pars c ψ).length = (dsa.map (interp V ρ)).length := by rw [List.length_map, hl]
  rw [hl', shiftE_consList, ← hl']

/-- Two frames agreeing below the key's depth have the same group hole
values. -/
theorem holeVal_keyFrame_eq {D : LfpDatum V} {ψ : Name → Nat} {dsa : List AnnotTerm} {hi : Nat}
    {c : Nat} (hl : (D.pars c ψ).length = dsa.length) {ρ ρ' Y Y' : Nat → V}
    (ht : ∀ j, ρ (j + hi) = ρ' (j + hi)) (hY : Y c = Y' c) :
    D.holeVal ψ (keyFrame dsa hi ρ) Y c = D.holeVal ψ (keyFrame dsa hi ρ') Y' c := by
  rw [holeVal_keyFrame hl, holeVal_keyFrame hl, hY]
  congr 1
  funext j
  exact ht j

theorem foldlApp_mono_holeFam {ρ : Nat → V} {Fs : List AnnotTerm} {vs : List V}
    {g g' : List V → V} (hlen : vs.length = Fs.length) (hg : ∀ bs, g bs ⊆ˢ g' bs) :
    vs.foldl app (holeFam ρ Fs g) ⊆ˢ vs.foldl app (holeFam ρ Fs g') := by
  rcases holeFam_foldl_full (ρ := ρ) (Fs := Fs) (vs := vs) g hlen with ⟨hf, he⟩ | he
  · rw [he, holeFam_app g' hf]
    exact hg vs
  · rw [he]
    intro x hx
    exact absurd hx (not_mem_empty x)

/-! ## Enlarging a tuple at one fibre -/

open Classical in
/-- **A tuple enlarged by `∅` at one fibre** stays in the space (at a
positive level) and contains the old one. -/
theorem tuple_enlarge {w' k : Nat} (hw : w' ≠ 0) {Is Y : Nat → V}
    (hY : InTupleSpace w' k Is Y) {t : Nat} {tt : V} :
    ∃ Y'' : Nat → V, InTupleSpace w' k Is Y'' ∧ (∀ m i, app (Y m) i ⊆ˢ app (Y'' m) i) ∧
      (t < k → tt ∈ˢ Is t → (empty : V) ∈ˢ app (Y'' t) tt) := by
  by_cases htk : t < k
  · let Y'' : Nat → V := fun m => if m = t then
      graph (fun i => if i = tt then binUnion (app (Y t) i) (sing empty) else app (Y t) i)
        (Is t) else Y m
    have hU := univ_isTGUniverse (V := V) hw
    refine ⟨Y'', ?_, ?_, ?_⟩
    · intro m hm
      by_cases hmt : m = t
      · subst hmt
        simp only [Y'', if_pos rfl]
        refine graph_mem_famSpace fun i hi => ?_
        split
        · exact hU.binUnion_mem (empty_mem_univ _) (famSpace_app (hY m hm) hi)
            (hU.sing_mem (empty_mem_univ _) (empty_mem_univ _))
        · exact famSpace_app (hY m hm) hi
      · simp only [Y'', if_neg hmt]
        exact hY m hm
    · intro m i y hy
      by_cases hmt : m = t
      · subst hmt
        simp only [Y'', if_pos rfl]
        by_cases hi : i ∈ˢ Is m
        · rw [app_graph hi]
          split
          · exact mem_binUnion.mpr (Or.inl hy)
          · exact hy
        · rw [app_off_dom_of_mem_piSet (hY m htk) hi] at hy
          exact absurd hy (not_mem_empty y)
      · simp only [Y'', if_neg hmt]
        exact hy
    · intro _ htt
      simp only [Y'', if_pos rfl, app_graph htt]
      exact mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))
  · exact ⟨Y, hY, fun _ _ => Subset.refl _, fun h => absurd h htk⟩

/-! ## The admissible items of a frame's walk -/

/-- **The admissible items under a frame**: the new holes (positions below
the group's length, at their members' full arity) and the enclosing ones
moved up. -/
theorem holeQ_frame_iff {ctx : NestCtx} {prog news : List NestHole} {i n : Nat} :
    HoleQ ctx (news.reverse ++ prog) (ctx.hiAt prog.length + news.length) i n ↔
      (∃ (j : Nat) (hk : NestHole), news[j]? = some hk ∧ i = news.length - 1 - j ∧
        n = ConLeche.nestArity ctx hk.key.cname) ∨
      (news.length ≤ i ∧ HoleQ ctx prog (ctx.hiAt prog.length) (i - news.length) n) := by
  constructor
  · rintro (⟨t, ht, hlt, rfl, hn⟩ | ⟨j, hk, hj, hlt, rfl, hn⟩)
    · refine Or.inr ⟨by simp only [NestCtx.hiAt]; omega, Or.inl ⟨t, ht, ?_, ?_, hn⟩⟩
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt]; omega
    · rw [List.reverse_append, List.reverse_reverse] at hj
      by_cases hjp : j < prog.length
      · rw [List.getElem?_append_left (by simpa using hjp)] at hj
        refine Or.inr ⟨by simp only [NestCtx.hiAt] at hlt ⊢; omega, Or.inr ⟨j, hk, hj, ?_, ?_, hn⟩⟩
        · simp only [NestCtx.hiAt]; omega
        · simp only [NestCtx.hiAt]; omega
      · rw [List.getElem?_append_right (by simpa using hjp), List.length_reverse] at hj
        have hjn := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨j - prog.length, hk, hj, ?_, hn⟩
        simp only [NestCtx.hiAt]; omega
  · rintro (⟨j, hk, hj, rfl, hn⟩ | ⟨hle, ⟨t, ht, hlt, hi, hn⟩ | ⟨j, hk, hj, hlt, hi, hn⟩⟩)
    · have hjn := (List.getElem?_eq_some_iff.mp hj).1
      refine Or.inr ⟨prog.length + j, hk, ?_, ?_, ?_, hn⟩
      · rw [List.reverse_append, List.reverse_reverse,
          List.getElem?_append_right (by simp), List.length_reverse]
        simpa using hj
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt]; omega
    · refine Or.inl ⟨t, ht, by omega, ?_, hn⟩
      simp only [NestCtx.hiAt] at hi hlt ⊢; omega
    · have hjp := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_reverse] at hjp
      refine Or.inr ⟨j, hk, ?_, ?_, ?_, hn⟩
      · rw [List.reverse_append, List.reverse_reverse,
          List.getElem?_append_left (by simpa using hjp)]
        exact hj
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt] at hi hlt ⊢; omega

/-! ## The relation -/

/-- **The frame relation for accessibility**: the enclosing relation at the
key's depth, extended by the group's hole values at ANY tuple of the
container's space at each side's key frame. -/
@[expose] def frameRelA (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (dsa : List AnnotTerm) (hi : Nat) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ' Y Y', R₀ ρ ρ' ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ)) Y ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ')) Y' ∧
    σ = consList (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ ∧
    σ' = consList (grpVals D ψ grp (keyFrame dsa hi ρ') Y') ρ'

theorem grpVals_length (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp Y : Nat → V) : (grpVals D ψ grp ρp Y).length = grp.length := by
  simp [grpVals]

theorem grpNews_length (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    (grpNews us ds hi grp).length = grp.length := by
  simp [grpNews]

section Frame

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
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

omit hnN hkN hfind hlps hnd hul hds hg in
/-- The members' own parameter telescopes are as long as the key's. -/
theorem parsLen_dsa {mm : Nat} (hmm : mm < D.k) :
    (D.pars mm (Level.substFn φ lps us)).length = dsa.length := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  rw [h.parsLen mm hmm, hlenP, DenoteMetaSpine.length_eq hdsa]

omit hnN hkN hfind hlps hnd hul hds hg in
/-- The group's hole values do not move with the frame below the key's
depth, nor off the group. -/
theorem grpVals_eq {ρ ρ' Y Y' : Nat → V} (ht : ∀ j, ρ (j + hi) = ρ' (j + hi))
    (hY : ∀ p ∈ grp, Y (D.names.idxOf p.1) = Y' (D.names.idxOf p.1))
    (hmem : ∀ p ∈ grp, D.names.idxOf p.1 < D.k) :
    grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y
      = grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ') Y' := by
  unfold grpVals
  refine List.map_congr_left fun p hp => ?_
  exact holeVal_keyFrame_eq (parsLen_dsa mp hD hdsa hlenP (hmem p hp)) ht (hY p hp)

/-- A group member's index is a member. -/
theorem grp_idx_lt {p : Name × Expr} (hp : p ∈ grp) : D.names.idxOf p.1 < D.k := by
  obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
  rw [hidx]; exact hmm

omit hnN hkN hfind hlps hnd hul hds hg in
/-- **The frame hole's value at full arity** is an occurrence of the tuple
at its member, or `∅`. -/
theorem grp_hole_full {mm : Nat} (hmm : mm < D.k) (ρ Y : Nat → V) {vs : List V}
    (hlen : vs.length = (D.pars mm (Level.substFn φ lps us)).length
      + (D.ids mm (Level.substFn φ lps us)).length) :
    (SpineFit (fun j => ρ (j + hi)) (D.pars mm (Level.substFn φ lps us)
        ++ D.ids mm (Level.substFn φ lps us)) vs ∧
      vs.foldl app (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y mm)
        = app (Y mm) (tupW (D.u mm (Level.substFn φ lps us))
            (vs.drop (D.pars mm (Level.substFn φ lps us)).length))) ∨
      vs.foldl app (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y mm) = empty := by
  rw [holeVal_keyFrame (parsLen_dsa mp hD hdsa hlenP hmm)]
  exact holeFam_foldl_full _ (by rw [List.length_append]; exact hlen)

/-- The group's hole values inhabit their context entries (the members'
former types). -/
theorem grpVals_fit (ρp X : Nat → V)
    (hX : InTupleSpace (D.w (Level.substFn φ lps us)) D.N (D.idx (Level.substFn φ lps us) ρp) X)
    (σ : Nat → V) :
    SpineFit σ (grpTys mp.base2 φ grp) (grpVals D (Level.substFn φ lps us) grp ρp X) := by
  refine spineFit_of_closed σ (by simp [grpVals, grpTys]) fun i hi hi' σ' => ?_
  have hpi : grp[i]'(by simpa [grpVals] using hi) ∈ grp := List.getElem_mem _
  obtain ⟨mm, hmm, -, hidx, cv, caps, hf, -, hp2, -⟩ :=
    grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
  obtain ⟨ta, hta⟩ := mp.type_reads _ (ConLeche.Semantics.Env.find?_mem hf)
    (Level.substFn φ lps us)
  simp only [grpVals, grpTys, List.getElem_map]
  rw [hidx, hp2, denotePInstLevels mp.base2 φ lps us 0 cv.type]
  change denoteMeta mp.base2.acval env _ 0 cv.type = _ at hta
  rw [hta, Option.getD_some]
  exact holeVal_mem_type mp hD hmm hf hta hX σ'

/-- A group member's index is in the group. -/
theorem grp_inGrp {p : Name × Expr} (hp : p ∈ grp) : InGrp D grp (D.names.idxOf p.1) := by
  obtain ⟨mm, hmm, hpm, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
  rw [hidx]
  exact ⟨hmm, by rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpm⟩⟩

/-- **The frame relation is an accessibility hole relation** of the
frame's walk (see the module docstring). -/
theorem frameRelA_holeRelA {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List AnnotTerm} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    (hw' : D.w (Level.substFn φ lps us) ≠ 0)
    (harity : ∀ p ∈ grp, ConLeche.nestArity ctx p.1
      = (D.pars (D.names.idxOf p.1) (Level.substFn φ lps us)).length
        + (D.ids (D.names.idxOf p.1) (Level.substFn φ lps us)).length) :
    HoleRelA mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) := by
  subst hhi
  have hvl : ∀ ρp Y, (grpVals D (Level.substFn φ lps us) grp ρp Y).length = grp.length :=
    fun _ _ => grpVals_length _ _ _ _ _
  have hnl := grpNews_length us ds (ctx.hiAt prog.length) grp
  have hlen' : ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog).length
      = grp.length + prog.length := by
    rw [List.length_append, List.length_reverse, hnl]
  -- the tail below the key's depth agrees along the relation
  have htail : ∀ ρ ρ', R₀ ρ ρ' → ∀ j, ρ (j + ctx.hiAt prog.length) = ρ' (j + ctx.hiAt prog.length) :=
    fun ρ ρ' hr j => hR₀.agree ρ ρ' hr _ fun hp => by have := hp.1; omega
  have hagree : ∀ ρ ρ', R₀ ρ ρ' →
      AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) ρ ρ' :=
    fun ρ ρ' hr => hR₀.agree ρ ρ' hr
  -- a position of the frame: a group hole, or the enclosing frame's
  have hpos : ∀ (ρ : Nat → V) (vs : List V) (i : Nat), grp.length ≤ i →
      consList vs ρ i = ρ (i - grp.length) ∨ vs.length ≠ grp.length := by
    intro ρ vs i hi
    by_cases hl : vs.length = grp.length
    · left
      have := consList_apply_add vs ρ (i - grp.length)
      rw [hl, show i - grp.length + grp.length = i by omega] at this
      exact this
    · exact Or.inr hl
  have hposE : ∀ (ρ ρp Y : Nat → V) (i : Nat), grp.length ≤ i →
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ i = ρ (i - grp.length) := by
    intro ρ ρp Y i hi
    rcases hpos ρ (grpVals D (Level.substFn φ lps us) grp ρp Y) i hi with h | h
    · exact h
    · exact absurd (hvl ρp Y) h
  -- a group hole's position
  have hposG : ∀ (ρ ρp Y : Nat → V) (j : Nat) (hj : j < grp.length),
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ (grp.length - 1 - j)
        = D.holeVal (Level.substFn φ lps us) ρp Y (D.names.idxOf (grp[j]).1) := by
    intro ρ ρp Y j hj
    rw [consList_getElem_pos (hvl ρp Y) hj]
    simp [grpVals]
  -- the new frames are the group's members at the key
  have hnewj : ∀ (j : Nat) (hk : NestHole), (grpNews us ds (ctx.hiAt prog.length) grp)[j]? = some hk →
      ∃ hj : j < grp.length, hk = { key := ⟨(grp[j]).1, us, ds⟩, base := ctx.hiAt prog.length } := by
    intro j hk h
    have hj : j < grp.length := by
      have := (List.getElem?_eq_some_iff.mp h).1; rwa [hnl] at this
    refine ⟨hj, ?_⟩
    simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
      Option.some.injEq] at h
    exact h.symm
  -- the members' arities at the group
  have hmm_of : ∀ (j : Nat) (hj : j < grp.length), ∃ mm, mm < D.k ∧
      D.names.idxOf (grp[j]).1 = mm ∧
      ConLeche.nestArity ctx (grp[j]).1 = (D.pars mm (Level.substFn φ lps us)).length
        + (D.ids mm (Level.substFn φ lps us)).length := by
    intro j hj
    have hpi : grp[j] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
    exact ⟨mm, hmm, hidx, by rw [harity _ hpi, hidx]⟩
  -- the admissible positions
  have hQiff := fun (i n : Nat) => holeQ_frame_iff (ctx := ctx) (prog := prog)
    (news := grpNews us ds (ctx.hiAt prog.length) grp) (i := i) (n := n)
  rw [hnl] at hQiff
  refine
    { dom := ?_, agree := ?_, frame := ?_, dsScoped := ?_, symm := ?_, rich := ?_, lrefl := ?_ }
  · -- the context
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
    exact ⟨sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY ρ),
      sat_of_spineFit h2 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY' ρ')⟩
  · -- agreement off the holes
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, -, -, rfl, rfl⟩ i hi
    rw [hlen'] at hi
    by_cases hig : i < grp.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [NestCtx.hiAt] <;> omega
    rw [hposE _ _ _ _ (by omega), hposE _ _ _ _ (by omega)]
    refine hR₀.agree ρ ρ' hr _ fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, by omega, ?_⟩
    simp only [NestCtx.hiAt] at h3 ⊢; omega
  · -- the frames are blind in their keys' parameters
    rintro i key hk dsa' hsp _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩ is
    rw [List.reverse_append, List.reverse_reverse] at hk
    have hws : ∀ x ∈ key.key.ds, Expr.WScoped (ctx.hiAt prog.length) x := by
      by_cases hi : i < prog.reverse.length
      · rw [List.getElem?_append_left hi] at hk
        exact hR₀.dsScoped i key hk
      · rw [List.getElem?_append_right (by omega)] at hk
        obtain ⟨-, rfl⟩ := hnewj _ key hk
        exact fun x hx => (hds x hx).1
    obtain ⟨dsa₀, hsp₀, rfl⟩ :=
      DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) (Nat.le_add_right _ grp.length) hws hsp
    rw [show ctx.hiAt prog.length + grp.length - ctx.hiAt prog.length = grp.length by omega]
    have hmS : ∀ σ xs, xs.length = grp.length →
        (dsa₀.map (AnnotTerm.liftN grp.length · 0)).map (interp V (consList xs σ))
          = dsa₀.map (interp V σ) := by
      intro σ xs hx
      rw [List.map_map]
      refine List.map_congr_left fun a _ => ?_
      show interp V (consList xs σ) (a.liftN grp.length 0) = _
      rw [← hx, interp_liftN_consList]
    rw [hmS ρ _ (hvl _ _), hmS ρ' _ (hvl _ _)]
    by_cases hi : i < prog.reverse.length
    · -- an enclosing frame
      rw [List.getElem?_append_left hi] at hk
      have hlt : i < prog.length := by simpa using hi
      have := hR₀.frame i key hk dsa₀ hsp₀ ρ ρ' hr is
      rw [hposE _ _ _ _ (by simp only [NestCtx.hiAt]; omega)]
      rw [show ctx.hiAt prog.length + grp.length - 1 - (ctx.hiAt 0 + i) - grp.length
        = ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i) by simp only [NestCtx.hiAt]; omega]
      exact this
    · -- a new frame: a group member's hole value
      rw [List.getElem?_append_right (by omega), List.length_reverse] at hk
      obtain ⟨hj, rfl⟩ := hnewj _ key hk
      obtain rfl := DenoteMetaSpine.unique hdsa hsp₀
      have hposi : ctx.hiAt prog.length + grp.length - 1 - (ctx.hiAt 0 + i)
          = grp.length - 1 - (i - prog.length) := by
        simp only [NestCtx.hiAt, List.length_reverse] at hi ⊢; omega
      rw [hposi, hposG _ _ _ _ hj]
      obtain ⟨mm, hmm, hidx, -⟩ := hmm_of _ hj
      rw [hidx]
      obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
      have hmm' : D.names.idxOf (grp[i - prog.length]).1 = mm := hidx
      obtain ⟨mm', -, -, hidx', -, -, -, -, -, hte⟩ :=
        grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (List.getElem_mem hj)
      rw [hmm'] at hidx'
      subst hidx'
      calc (dsa.map (interp V ρ) ++ is).foldl app
            (D.holeVal (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ') Y' mm)
          = (dsa.map (interp V ρ) ++ is).foldl app
            (D.holeVal (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) Y' mm) := by
            rw [holeVal_keyFrame_eq (parsLen_dsa mp hD hdsa hlenP hmm)
              (fun j => (htail ρ ρ' hr j).symm) rfl (Y' := Y')]
        _ = _ := grp_holeVal_apply mp hD hdsa hlenP hmm hs Y' is
        _ = _ := by rw [(hte ρ ρ' (hagree ρ ρ' hr)).holeFam]
        _ = _ := (grp_holeVal_apply mp hD hdsa hlenP hmm hs' Y' is).symm
  · -- the keys' parameters are scoped
    intro i key hk x hx
    rw [hlen']
    rw [List.reverse_append, List.reverse_reverse] at hk
    refine Expr.WScoped.mono (show ctx.hiAt prog.length ≤ ctx.hiAt (grp.length + prog.length) by
      simp only [NestCtx.hiAt]; omega) ?_
    by_cases hi : i < prog.reverse.length
    · rw [List.getElem?_append_left hi] at hk
      exact hR₀.dsScoped i key hk x hx
    · rw [List.getElem?_append_right (by omega), List.length_reverse] at hk
      have hmem : x ∈ ds := by
        obtain ⟨_, hkey⟩ := hnewj _ key hk
        rw [hkey] at hx
        exact hx
      exact (hds x hmem).1
  · -- symmetric
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    exact ⟨ρ', ρ, Y', Y, hR₀.symm ρ ρ' hr, hY', hY, rfl, rfl⟩
  · -- rich
    rintro _ _ ⟨ρ, ρ₀, Y, Y₀, hr, hY, hY₀, rfl, rfl⟩ i vs hQ hpt
    rcases (hQiff i vs.length).mp hQ with ⟨j, hk, hjk, rfl, hn⟩ | ⟨hle, hQ'⟩
    · -- a new hole: enlarge the tuple at the same enclosing frame
      obtain ⟨hj, rfl⟩ := hnewj _ hk hjk
      obtain ⟨mm, hmm, hidx, har⟩ := hmm_of _ hj
      rw [hposG _ _ _ _ hj, hidx] at hpt
      have hlenv : vs.length = (D.pars mm (Level.substFn φ lps us)).length
          + (D.ids mm (Level.substFn φ lps us)).length := by rw [hn, har]
      rcases grp_hole_full mp hD hdsa hlenP hmm ρ Y hlenv with ⟨hfv, he⟩ | he
      · rw [he] at hpt
        have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
        have htt : tupW (D.u mm (Level.substFn φ lps us))
            (vs.drop (D.pars mm (Level.substFn φ lps us)).length)
            ∈ˢ D.idx (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) mm := by
          refine Classical.byContradiction fun hni => ?_
          rw [app_off_dom_of_mem_piSet (hY mm hmmN) hni] at hpt
          exact not_mem_empty _ hpt
        obtain ⟨Y'', hY'', hle'', hz⟩ := tuple_enlarge (t := mm)
          (tt := tupW (D.u mm (Level.substFn φ lps us))
            (vs.drop (D.pars mm (Level.substFn φ lps us)).length)) hw' hY
        refine ⟨consList (grpVals D (Level.substFn φ lps us) grp
            (keyFrame dsa (ctx.hiAt prog.length) ρ) Y'') ρ,
          ⟨ρ, ρ, Y, Y'', hR₀.lrefl ρ ρ₀ hr, hY, hY'', rfl, rfl⟩, ?_, empty, ?_,
          pt_ne_empty.symm⟩
        · rintro ⟨i', vs', y⟩ ho hH
          unfold Adm at ho
          rcases (hQiff i' vs'.length).mp ho with ⟨j', hk', hjk', rfl, hn'⟩ | ⟨hle', -⟩
          · obtain ⟨hj', rfl⟩ := hnewj _ hk' hjk'
            obtain ⟨mm', hmm', hidx', har'⟩ := hmm_of _ hj'
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
            (keyFrame dsa (ctx.hiAt prog.length) ρ) Y'') ρ (grp.length - 1 - j))
          rw [hposG _ _ _ _ hj, hidx]
          rw [holeVal_keyFrame (parsLen_dsa mp hD hdsa hlenP hmm), holeFam_app _ hfv]
          exact hz hmmN htt
      · rw [he] at hpt
        exact absurd hpt (not_mem_empty _)
    · -- an enclosing hole: the enclosing relation's richness
      rw [hposE _ _ _ _ hle] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR₀.rich ρ ρ₀ hr (i - grp.length) vs hQ' hpt
      let Y'' : Nat → V := mixT (InGrp D grp)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ'')) Y
      have hY'' : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
          (D.idx (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ'')) Y'' := by
        intro c hc
        show mixT (InGrp D grp) _ Y c ∈ˢ _
        unfold mixT
        split
        · rename_i hG
          rw [← grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG (hagree ρ ρ'' hr'')]
          exact hY c hc
        · exact lfpTuple_mem _ _ _ _ c hc
      have hgv : grpVals D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ'') Y''
          = grpVals D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ) Y :=
        grpVals_eq mp hD hdsa hlenP (fun j => (htail ρ ρ'' hr'' j).symm)
          (fun p hp => by
            show mixT (InGrp D grp) _ Y _ = _
            unfold mixT
            rw [if_pos (grp_inGrp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp)])
          (fun p hp => grp_idx_lt mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp)
      refine ⟨consList (grpVals D (Level.substFn φ lps us) grp
          (keyFrame dsa (ctx.hiAt prog.length) ρ'') Y'') ρ'',
        ⟨ρ, ρ'', Y, Y'', hr'', hY, hY'', rfl, rfl⟩, ?_, z, ?_, hzp⟩
      · rintro ⟨i', vs', y⟩ ho hH
        unfold Adm at ho
        unfold Holds at hH ⊢
        simp only at hH ⊢
        rcases (hQiff i' vs'.length).mp ho with ⟨j', hk', hjk', rfl, -⟩ | ⟨hle', hQo⟩
        · obtain ⟨hj', -⟩ := hnewj _ hk' hjk'
          rw [hgv, hposG _ _ _ _ hj']
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

end Frame

/-- **A frame hole's full arity is its member's telescope** (the premise
`harity` of `frameRelA_holeRelA`): the kernel's `nestArity` (the member's
stored type's binder count) is the recorded parameter and index count —
the recorded reading ends in a sort, so the type's syntactic tail is no
variable, and `nestInstType` saw a sort there (`instPis_count_of_read`'s
pieces, lane NESTIND). -/
theorem grp_arity {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {hi : Nat} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp) (ψ : Name → Nat) :
    ∀ p ∈ grp, ConLeche.nestArity ctx p.1
      = (D.pars (D.names.idxOf p.1) ψ).length + (D.ids (D.names.idxOf p.1) ψ).length := by
  intro p hp
  obtain ⟨⟨mm, hmm, hpm⟩, nI, hrun⟩ := hg.2 p hp
  obtain ⟨cvC, caps, hfC, -, -, ty, s, hty, hs, -, -, -⟩ := ConLeche.nestInstType_inv hrun
  obtain ⟨cv, caps', hf, hab⟩ := (mp.lfp_ok D hD).2.2.1 mm hmm
  have hfC' : env.find? (D.member mm) = some (.indInfo cvC caps) := by
    rw [← hfind, ← hpm]; exact hfC
  rw [hf] at hfC'
  obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps' = caps := by simpa using hfC'
  obtain ⟨ab, hread, hmap, -⟩ := hab ψ
  have hok := tailOk_of_read _ cv.type rfl hread
  obtain ⟨-, l2, l3⟩ := tail_instantiateLevelParams cv.levelParams us cv.type
  obtain ⟨-, k2⟩ := tail_instPisWith ds (l3.mpr hok) hty
  have hsty : SortTail ty := by
    unfold SortTail; rw [← piBinders_snd_eq, hs]; trivial
  have hse : SortTail cv.type := l2.mp (k2.mp hsty)
  obtain ⟨ab', u', heq, hlen⟩ := read_of_sortTail _ cv.type rfl hse hread
  obtain ⟨rfl, -⟩ := mkPisAV_sort_eq heq
  have hidx : D.names.idxOf p.1 = mm := by rw [hpm]; exact idxOf_member hnN hkN hmm
  have hnA : ConLeche.nestArity ctx p.1 = cv.type.piBinders.1.length := by
    unfold ConLeche.nestArity; rw [hfC]
  rw [hnA, hidx, ← piCount_eq_length, ← hlen, ← List.length_append, ← hmap, List.length_map]

end ConLeche.Model
