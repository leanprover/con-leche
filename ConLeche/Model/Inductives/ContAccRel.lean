module

public import ConLeche.Model.Inductives.ContWalk
public import ConLeche.Model.Inductives.NestPosAcc
import ConLeche.Model.Env.LfpAcc
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The container frame's accessibility relation

The twin of `frameRel`/`frameRel_holeRel` (`ContWalk.lean`) for the
accessibility route: a container frame's walk runs along `frameRelA` — the
enclosing relation `R₀` at the key's depth, extended by the reached group's
hole values at ANY tuple of the container's space (comparable frames, no
order) — and `frameRelA` is an accessibility hole relation (`HoleRelA`) of
the frame's walk (`frameRelA_holeRelA`).

A frame hole stands for its member's whole application (it takes no
parameters), and a group member's hole value reads its key frame only
through the index telescope, which reads alike at two frames agreeing off
the holes (N2's `TeleEq`), so a hole value does not move when the
enclosing frame changes off the holes.  The holes never
hold the point: a new hole's value at its full arity is a fibre of the
tuple (a strict set, as in `LfpDatum.accRel_ptFree`) or `∅`; an enclosing
hole is the enclosing relation's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The admissible items of a frame's walk -/

/-- **The admissible items under a frame**: the new holes (positions below
the group's length, at their members' full arity) and the enclosing ones
moved up. -/
theorem holeQ_frame_iff {ctx : NestCtx} {prog news : List NestHole} {i n : Nat} :
    HoleQ ctx (news.reverse ++ prog) (ctx.hiAt prog.length + news.length) i n ↔
      (∃ (j : Nat) (hk : NestHole), news[j]? = some hk ∧ i = news.length - 1 - j ∧
        n + hk.key.ds.length = ConLeche.nestArity ctx hk.key.cname) ∨
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
    (grp : List (Name × Expr)) (dsa : List Term) (hi : Nat) : FrameRel V :=
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

variable (mp : EnvModelM V env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

omit hnN hkN hfind hlps hnd hul hds hg in
/-- The members' own parameter telescopes are as long as the key's. -/
theorem parsLen_dsa {mm : Nat} (hmm : mm < D.k) :
    (D.pars mm (Level.substFn φ lps us)).length = dsa.length := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  rw [h.parsLen mm hmm, hlenP, DenoteSpine.length_eq hdsa]

omit hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
/-- **The frame hole's value at full arity** is an occurrence of the tuple
at its member, or `∅`, or the point. -/
theorem grp_hole_full {mm : Nat} (ρp Y : Nat → V) {vs : List V}
    (hlen : vs.length = (D.ids mm (Level.substFn φ lps us)).length) :
    (SpineFit ρp (D.ids mm (Level.substFn φ lps us)) vs ∧
      vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm)
        = app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) vs)) ∨
      (¬ SpineFit ρp (D.ids mm (Level.substFn φ lps us)) vs ∧
        (vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm) = empty ∨
          vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm) = pt)) := by
  unfold LfpDatum.holeVal
  rcases holeFam_foldl_full (ρ := ρp) (Fs := D.ids mm (Level.substFn φ lps us)) (vs := vs)
      (fun vs => app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) vs)) hlen with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- A group member's index is in the group. -/
theorem grp_inGrp {p : Name × Expr} (hp : p ∈ grp) : InGrp D grp (D.names.idxOf p.1) := by
  obtain ⟨mm, hmm, hpm, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
  rw [hidx]
  exact ⟨hmm, by rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpm⟩⟩

/-- **The frame relation is an accessibility hole relation** of the
frame's walk (see the module docstring). -/
theorem frameRelA_holeRelA {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hwD : D.w (Level.substFn φ lps us) = w)
    (harity : ∀ p ∈ grp, ConLeche.nestArity ctx p.1
      = (D.pars (D.names.idxOf p.1) (Level.substFn φ lps us)).length
        + (D.ids (D.names.idxOf p.1) (Level.substFn φ lps us)).length) :
    HoleRelA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ hi grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) := by
  subst hhi
  have hvl : ∀ ρp Y, (grpVals D (Level.substFn φ lps us) grp ρp Y).length = grp.length :=
    fun _ _ => grpVals_length _ _ _ _ _
  have hnl := grpNews_length us ds (ctx.hiAt prog.length) grp
  have hlen' : ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog).length
      = grp.length + prog.length := by
    rw [List.length_append, List.length_reverse, hnl]
  have hagree : ∀ ρ ρ', R₀ ρ ρ' →
      AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) ρ ρ' :=
    fun ρ ρ' hr => hR₀.agree ρ ρ' hr
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
  -- the members' index arities at the group
  have hmm_of : ∀ (j : Nat) (hj : j < grp.length), ∃ mm, mm < D.k ∧
      D.names.idxOf (grp[j]).1 = mm ∧
      ConLeche.nestArity ctx (grp[j]).1 = ds.length + (D.ids mm (Level.substFn φ lps us)).length := by
    intro j hj
    have hpi : grp[j] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
    refine ⟨mm, hmm, hidx, ?_⟩
    rw [harity _ hpi, hidx, parsLen_dsa mp hD hdsa hlenP hmm, ← DenoteSpine.length_eq hdsa]
  -- the admissible positions
  have hQiff := fun (i n : Nat) => holeQ_frame_iff (ctx := ctx) (prog := prog)
    (news := grpNews us ds (ctx.hiAt prog.length) grp) (i := i) (n := n)
  rw [hnl] at hQiff
  refine
    { dom := ?_, agree := ?_, dsScoped := ?_, symm := ?_, ptFree := ?_, lrefl := ?_ }
  · -- the context
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
    exact ⟨sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY),
      sat_of_spineFit h2 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _ hY')⟩
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
  · -- point-free: a new hole's value at its full arity is a fibre of the
    -- tuple (a strict set) or `∅`; an enclosing hole is the enclosing
    -- relation's
    intro hw
    have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD]; exact hw
    rintro _ _ ⟨ρ, ρ₀, Y, Y₀, hr, hY, hY₀, rfl, rfl⟩ i vs hQ hpt
    rcases (hQiff i vs.length).mp hQ with ⟨j, hk, hjk, rfl, hn⟩ | ⟨hle, hQ'⟩
    · obtain ⟨hj, rfl⟩ := hnewj _ hk hjk
      obtain ⟨mm, hmm, hidx, har⟩ := hmm_of _ hj
      rw [hposG _ _ _ _ hj, hidx] at hpt
      have hlenv : vs.length = (D.ids mm (Level.substFn φ lps us)).length := by
        simp only at hn; omega
      rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ)
          (keyFrame dsa (ctx.hiAt prog.length) ρ) Y hlenv with ⟨hfv, he⟩ | he
      · rw [he] at hpt
        have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
        exact ((mem_strictU_pos hw').mp (famSpace_app (hY mm hmmN) (tupW_mem hfv))).2.2 hpt
      · rcases he.2 with he | he
        · rw [he] at hpt
          exact not_mem_empty _ hpt
        · rw [he] at hpt
          exact not_mem_self _ hpt
    · rw [hposE _ _ _ _ hle] at hpt
      exact hR₀.ptFree hw ρ ρ₀ hr (i - grp.length) vs hQ' hpt
  · -- left-reflexive
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, -, rfl, rfl⟩
    exact ⟨ρ, ρ, Y, Y, hR₀.lrefl ρ ρ' hr, hY, hY, rfl, rfl⟩

end Frame

/-- **A frame hole's full arity is its member's telescope** (the premise
`harity` of `frameRelA_holeRelA`): the kernel's `nestArity` (the member's
stored type's binder count) is the recorded parameter and index count —
the recorded reading ends in a sort, so the type's syntactic tail is no
variable, and `nestInstType` saw a sort there (`instPis_count_of_read`'s
pieces). -/
theorem grp_arity (mp : EnvModelM V env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {hi : Nat} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp) (ψ : Name → Nat) :
    ∀ p ∈ grp, ConLeche.nestArity ctx p.1
      = (D.pars (D.names.idxOf p.1) ψ).length + (D.ids (D.names.idxOf p.1) ψ).length := by
  intro p hp
  obtain ⟨⟨mm, hmm, hpm⟩, nI, hrun⟩ := hg.2.2 p hp
  obtain ⟨cvC, caps, hfC, -, -, ty, s, hty, hs, -, -, -⟩ := ConLeche.nestInstType_inv hrun
  obtain ⟨cv, caps', hf, hab⟩ := (mp.lfp_ok D hD).2.2.1 mm hmm
  have hfC' : env.find? (D.member mm) = some (.indInfo cvC caps) := by
    rw [← hfind, ← hpm]; exact hfC
  rw [hf] at hfC'
  obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps' = caps := by simpa using hfC'
  obtain ⟨ab, hread, hmap⟩ := hab ψ
  have hok := tailOk_of_read _ cv.type rfl hread
  obtain ⟨-, l2, l3⟩ := tail_instantiateLevelParams cv.levelParams us cv.type
  obtain ⟨-, k2⟩ := tail_instPisWith ds (l3.mpr hok) hty
  have hsty : SortTail ty := by
    unfold SortTail; rw [← piBinders_snd_eq, hs]; trivial
  have hse : SortTail cv.type := l2.mp (k2.mp hsty)
  obtain ⟨ab', u', heq, hlen⟩ := read_of_sortTail _ cv.type rfl hse hread
  obtain ⟨hab', -⟩ := mkPisAV_sort_eq heq
  have hll : ab.length = ab'.length := by simpa using congrArg List.length hab'
  have hidx : D.names.idxOf p.1 = mm := by rw [hpm]; exact idxOf_member hnN hkN hmm
  have hnA : ConLeche.nestArity ctx p.1 = cv.type.piBinders.1.length := by
    unfold ConLeche.nestArity; rw [hfC]
  rw [hnA, hidx, ← piCount_eq_length, ← hlen, ← hll, ← List.length_append, ← hmap]

end ConLeche.Model
