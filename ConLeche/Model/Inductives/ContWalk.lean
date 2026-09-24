module

public import ConLeche.Model.Inductives.ContCtor
public import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# A container frame's walk (lane CONTSEM, steps 3–4)

`nestCtors` inverted constructor by constructor (`nestCtors_sem`), the
state invariant threaded, and the frame lemma (`frame_sem`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

theorem nodup_of_nameNodup : ∀ {ns : List Name}, ConLeche.Name.nodup ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nameNodup h.2⟩
    have := h.1
    simp [hm] at this

/-- What a successful frame walk leaves of one constructor: its level
parameters distinct, and its instantiated, abstracted type read, walked
positively along the frame relation, its result the hole applied with
hole-free indices. -/
@[expose] def CtorWalked (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (hi : Nat)
    (us : List Level) (ds : List Expr) (nPc : Nat) (sub : Name → List Level → Option Expr)
    (R : FrameRel V) (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca cur,
    instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
      = some crest ∧
    denoteMeta m.acval env φ hi crest = some ca ∧ ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop nPc).all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiPosThen (ResultAt m φ ctx.nP hi (hi + x.2) cur) x.2 R ca

/-- **A frame's constructors, walked** (see the module docstring): the
state invariant is kept, and when no restart is pending every
constructor was walked positively. -/
theorem nestCtors_sem {ctx : NestCtx} {F : Nat} {I : NestState → Prop}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    (hrec : NestPosSem m φ ctx (fun _ => True) I rec)
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr} {nPc : Nat}
    {sub : Name → List Level → Option Expr} (hhi : ctx.hiAt prog.length = hi)
    {Δ : List AnnotTerm} {R : FrameRel V} (hR : HoleRel m φ ctx prog hi Δ R)
    (hprem : ∀ (x : ConstantVal × Nat) (crest : Expr),
      instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      (∃ ty, ConLeche.inferTypeCore .verified env F hi crest = .ok ty) →
      ∃ ca, Frame hi crest ∧ CtxOkP m φ hi Δ crest ∧
        denoteMeta m.acval env φ hi crest = some ca ∧ Graded V Δ ca) :
    ∀ (ctors : List (ConstantVal × Nat)) (st st' : NestState),
      ConLeche.nestCtors ctx (fueledOps .verified F) env rec prog hi us ds nPc sub ctors st
        = .ok st' → I st →
      I st' ∧ (st'.restart = none → ∀ x ∈ ctors, CtorWalked m φ ctx hi us ds nPc sub R x) := by
  intro ctors
  induction ctors with
  | nil =>
    intro st st' h hI
    simp only [ConLeche.nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, fun _ x hx => nomatch hx⟩
  | cons x cs ih =>
    intro st st' h hI
    obtain ⟨cv, nF⟩ := x
    simp only [ConLeche.nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    have hnd' : cv.levelParams.Nodup := nodup_of_nameNodup hnd
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    rename_i sv hsv
    obtain ⟨ca, hfr, hC, hca, hgr⟩ := hprem (cv, nF) crest hcrest' ⟨ty, hty⟩
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    obtain ⟨hI₁, hpos⟩ := nestFields_sem (P := fun _ => True) hrec nF 0 crest st ks nds cur st₁
      (hi + nF) hr (fun _ _ => trivial) (by omega) (by rw [hhi]; omega) hfr hI hC hca hgr
      (by simpa using hR)
    dsimp only at h
    by_cases hrs : st₁.restart.isSome = true
    · rw [if_pos hrs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨hI₁, fun hc => ?_⟩
      rw [hc] at hrs; exact nomatch hrs
    rw [if_neg hrs] at h
    have hc₁ : st₁.restart = none := by simpa using hrs
    split at h
    · rename_i hok
      obtain ⟨hI', hrest⟩ := ih st₁ st' h hI₁
      refine ⟨hI', fun hc x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.and_eq_true] at hok
        refine ⟨hnd', crest, ca, cur, hcrest', hca, hok.1, hok.2, ?_⟩
        have := hpos hc₁
        rwa [hhi] at this
      · exact hrest hc x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The frame's group, its holes and its relation -/

/-- A λ-tower applied along a fitting prefix is the tower over the rest. -/
theorem holeFam_append_apply :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V} (Gs : List AnnotTerm) (g : List V → V)
      (is : List V), SpineFit ρ Fs as →
      (as ++ is).foldl app (holeFam ρ (Fs ++ Gs) g)
        = is.foldl app (holeFam (consList as ρ) Gs fun bs => g (as ++ bs))
  | [], _, [], _, _, _, _ => rfl
  | [], _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, [], _, _, _, h => h.elim
  | F :: Fs, ρ, a :: as, Gs, g, is, h => by
    show (as ++ is).foldl app (app (lamR 1 (interp V ρ F) _) a) = _
    rw [app_lamR_pos (by decide) h.1, consList_cons]
    exact holeFam_append_apply (Fs := Fs) Gs (fun as => g (a :: as)) is h.2

/-- A spine of values each inhabiting its closed domain fits. -/
theorem spineFit_of_closed :
    ∀ {Ds : List AnnotTerm} {as : List V} (ρ : Nat → V), as.length = Ds.length →
      (∀ i (hi : i < as.length) (hi' : i < Ds.length) (σ : Nat → V),
        as[i] ∈ˢ interp V σ Ds[i]) → SpineFit ρ Ds as
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | D :: Ds, a :: as, ρ, h, hm =>
    ⟨hm 0 (by simp) (by simp) ρ, spineFit_of_closed _ (by simpa using h)
      fun i hi hi' σ => hm (i + 1) (by simpa using hi) (by simpa using hi') σ⟩

/-- **The frame's group is well formed**: nonempty, its names distinct,
each a member of the container's block `D`, each at the frame's key
through `nestInstType` (its hole's type the member's former at the key's
levels). -/
@[expose] def GrpOk (ctx : NestCtx) (D : LfpDatum V) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  grp ≠ [] ∧ (grp.map (·.1)).Nodup ∧ ∀ p ∈ grp, (∃ mm, mm < D.k ∧ p.1 = D.member mm) ∧
    ∃ nI, ConLeche.nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2)

/-- Member `mm` of `D` is in the frame's group. -/
@[expose] def InGrp (D : LfpDatum V) (grp : List (Name × Expr)) (mm : Nat) : Prop :=
  mm < D.k ∧ (grp.map (·.1)).contains (D.member mm) = true

/-- The frame's hole values at a key frame `ρp` and a tuple `Y`. -/
@[expose] noncomputable def grpVals (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp Y : Nat → V) : List V :=
  grp.map fun p => D.holeVal ψ ρp Y (D.names.idxOf p.1)

/-- The frame's new walk entries (one per group member, at the key). -/
@[expose] def grpNews (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    List NestHole :=
  grp.map fun p => { key := ⟨p.1, us, ds⟩, base := hi }

/-- The frame's holes' context entries (their former types, read). -/
@[expose] noncomputable def grpTys (m : EnvModel V env) (φ : Name → Nat) (grp : List (Name × Expr)) :
    List AnnotTerm :=
  grp.map fun p => (denoteMeta m.acval env φ 0 p.2).getD .prf

open Classical in
/-- The smaller side's tuple: the larger carrier on the group, the
smaller one elsewhere (`carrier_le_on_group'`'s bound). -/
@[expose] noncomputable def grpTuple (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp ρp' : Nat → V) : Nat → V :=
  fun c => if InGrp D grp c then D.carrier ψ ρp' c else D.carrier ψ ρp c

/-- **The frame relation**: the enclosing relation at the key's depth,
extended by the group's hole values — at the smaller side of the
smaller key frame and `grpTuple`, at the larger side of the larger key
frame and its carrier. -/
@[expose] def frameRel (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (dsa : List AnnotTerm) (hi : Nat) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ', R₀ ρ ρ' ∧
    σ = consList (grpVals D ψ grp (keyFrame dsa hi ρ)
      (grpTuple D ψ grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))) ρ ∧
    σ' = consList (grpVals D ψ grp (keyFrame dsa hi ρ') (D.carrier ψ (keyFrame dsa hi ρ'))) ρ'

omit [SetTheory V] in
theorem idxOf_member {D : LfpDatum V} (hnd : D.names.Nodup) (hkN : D.names.length = D.k)
    {mm : Nat} (hmm : mm < D.k) : D.names.idxOf (D.member mm) = mm := by
  have hmem : D.member mm = D.names[mm]'(by omega) := by
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hmem]
  exact hnd.idxOf_getElem mm (by omega)

/-- **A group member's facts** (N2 at the key, via `n2_link`). -/
theorem grpMember {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
    (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
    {grp : List (Name × Expr)} (hg : GrpOk ctx D hi us ds grp) {p : Name × Expr} (hp : p ∈ grp) :
    ∃ mm, mm < D.k ∧ p.1 = D.member mm ∧ D.names.idxOf p.1 = mm ∧ ∃ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      p.2 = cv.type.instantiateLevelParams lps us ∧
      ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
        TeleEq (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') (D.ids mm (Level.substFn φ lps us)) := by
  obtain ⟨-, -, hall⟩ := hg
  obtain ⟨⟨mm, hmm, hpm⟩, nI, hrun⟩ := hall p hp
  obtain ⟨cv, caps, hf, hcl⟩ := hlps mm hmm
  rw [hpm] at hrun
  subst hcl
  obtain ⟨hcty, -, hte⟩ := n2_link mp hD hmm hfind hrun hf hnd hul hlenP hds hdsa
  exact ⟨mm, hmm, hpm, by rw [hpm]; exact idxOf_member hnN hkN hmm, cv, caps, hf, rfl, hcty, hte⟩

/-- The frame's member substitution (`nestFrame`'s `sub`): the group's
members at the key's levels to their holes. -/
@[expose] def grpSub (us : List Level) (hi : Nat) (grp : List (Name × Expr)) :
    Name → List Level → Option Expr :=
  fun c us' => if us' == us then
    (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)).lookup c else none

theorem lookup_getElem :
    ∀ {L : List (Name × Expr)}, (L.map (·.1)).Nodup → ∀ (i : Nat) (hi : i < L.length),
      L.lookup L[i].1 = some L[i].2
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | p :: L, hnd, 0, _ => by simp [List.lookup]
  | p :: L, hnd, i + 1, hi => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hne : (L[i]'(by simpa using hi)).1 ≠ p.1 := by
      intro he
      exact hnd.1 (by rw [← he]; exact List.mem_map_of_mem (List.getElem_mem _))
    have hbeq : ((L[i]'(by simpa using hi)).1 == p.1) = false := by simpa using hne
    simp only [List.getElem_cons_succ, List.lookup, hbeq]
    exact lookup_getElem hnd.2 i _

theorem lookup_none {L : List (Name × Expr)} {k : Name} (hk : k ∉ L.map (·.1)) :
    L.lookup k = none := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hne : k ≠ p.1 := fun h => hk (by simp [h])
    have hbeq : (k == p.1) = false := by simpa using hne
    simp only [List.lookup, hbeq]
    exact ih fun h => hk (List.mem_cons_of_mem _ h)

theorem mapIdx_hole_keys {hi : Nat} (grp : List (Name × Expr)) :
    (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)).map (·.1) = grp.map (·.1) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

/-- The substitution at a member of the group is its hole. -/
theorem grpSub_mem {us : List Level} {hi : Nat} {grp : List (Name × Expr)}
    (hnd : (grp.map (·.1)).Nodup) {i : Nat} (hi' : i < grp.length) :
    grpSub us hi grp grp[i].1 us = some (.fvar (hi + i) grp[i].2) := by
  unfold grpSub
  rw [if_pos (by simp)]
  have hnd' : ((grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)).map (·.1)).Nodup := by
    rw [mapIdx_hole_keys]; exact hnd
  have := lookup_getElem hnd' i (by simpa using hi')
  simpa using this

/-- Off the group the substitution is nothing. -/
theorem grpSub_none {us us' : List Level} {hi : Nat} {grp : List (Name × Expr)} {c : Name}
    (hc : c ∉ grp.map (·.1)) : grpSub us hi grp c us' = none := by
  unfold grpSub
  split
  · exact lookup_none (by rw [mapIdx_hole_keys]; exact hc)
  · rfl

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
  {grp : List (Name × Expr)} (hg : GrpOk ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

/-- A group member's index sets agree at the two key frames. -/
theorem grp_idx_eq {c : Nat} (hc : InGrp D grp c) {ρ ρ' : Nat → V}
    (hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ') :
    D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ) c
      = D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ') c := by
  obtain ⟨hck, hcg⟩ := hc
  obtain ⟨p, hp, hpc⟩ : ∃ p ∈ grp, p.1 = D.member c := by
    simpa using hcg
  obtain ⟨mm, hmm, hpm, -, -, -, -, -, -, hte⟩ :=
    grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
  have hmc : mm = c := by
    have h1 := idxOf_member hnN hkN hmm
    rw [← hpm, hpc, idxOf_member hnN hkN hck] at h1
    exact h1.symm
  subst hmc
  exact (hte ρ ρ' hag).idxSet

/-- The group's tuple lies in the smaller key frame's tuple space. -/
theorem grpTuple_mem {ρ ρ' : Nat → V} (hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ') :
    InTupleSpace (D.w (Level.substFn φ lps us)) D.N (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ))
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ')) := by
  intro c hc
  unfold grpTuple
  by_cases hG : InGrp D grp c
  · rw [if_pos hG, grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG hag]
    exact lfpTuple_mem _ _ _ _ c hc
  · rw [if_neg hG]
    exact lfpTuple_mem _ _ _ _ c hc

omit hnN hkN hfind hlps hnd hul hds hg in
/-- A hole value of the group, applied to the key's parameters and then
to anything, is the λ-tower over the member's indices at the key frame. -/
theorem grp_holeVal_apply {mm : Nat} (hmm : mm < D.k) {ρ : Nat → V}
    (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ)) (Y : Nat → V)
    (is : List V) :
    (dsa.map (interp V ρ) ++ is).foldl app (D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y mm)
      = is.foldl app (holeFam (keyFrame dsa hi ρ) (D.ids mm (Level.substFn φ lps us))
          fun bs => app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) bs)) := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  generalize hψ : Level.substFn φ lps us = ψ at hs hlenP ⊢
  have hpl := h.parsLen mm hmm ψ
  have hsP := h.parsSat mm hmm ψ _ hs
  have hla : (dsa.map (interp V ρ)).length = (D.pars mm ψ).length := by
    rw [List.length_map, hpl, hlenP, DenoteMetaSpine.length_eq hdsa]
  have hsp := spineFit_of_sat_consList' hla hsP
  unfold LfpDatum.holeVal
  unfold keyFrame
  rw [← hla, shiftE_consList, holeFam_append_apply _ _ is hsp]
  congr 2
  funext bs
  simp [hla]

/-- **The frame relation is a hole relation** of the frame's walk: the
enclosing relation at the key's depth extended by the group's holes
(their context entries the members' former types, their values
inhabiting them; the new holes grow at the key's parameters because
their indices read the same at the two key frames, N2). -/
theorem frameRel_holeRel {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List AnnotTerm} {R₀ : FrameRel V} (hR₀ : HoleRel mp.base2 φ ctx prog hi Δh R₀)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ')) :
    HoleRel mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ grp).reverse ++ Δh)
      (frameRel R₀ D (Level.substFn φ lps us) grp dsa hi) := by
  subst hhi
  have hlenN : (grpNews us ds (ctx.hiAt prog.length) grp).length = grp.length := by
    simp [grpNews]
  have hext := HoleRel.extend hR₀ (grpNews us ds (ctx.hiAt prog.length) grp)
    (fun x hx a ha => by
      simp only [grpNews, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact (hds a ha).1)
    (grpTys mp.base2 φ grp).reverse
    (fun ρ ρ' => grpVals D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ)
        (keyFrame dsa (ctx.hiAt prog.length) ρ')))
    (fun ρ ρ' => grpVals D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ')))
    (fun _ _ => by simp [grpVals, grpNews]) (fun _ _ => by simp [grpVals, grpNews])
    ?_ ?_
  · rw [hlenN] at hext
    exact hext
  · -- the holes' values inhabit their entries
    have key : ∀ (ρp X : Nat → V), InTupleSpace (D.w (Level.substFn φ lps us)) D.N
        (D.idx (Level.substFn φ lps us) ρp) X → ∀ σ : Nat → V,
        SpineFit σ (grpTys mp.base2 φ grp) (grpVals D (Level.substFn φ lps us) grp ρp X) := by
      intro ρp X hX σ
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
    intro ρ ρ' hr
    obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
    refine ⟨?_, ?_⟩
    · exact sat_of_spineFit h1 (key _ _ (grpTuple_mem mp hD hnN hkN hfind hlps hnd hul hds hdsa
        hlenP hg (hR₀.agree ρ ρ' hr)) ρ)
    · exact sat_of_spineFit h2 (key _ _ (lfpTuple_mem _ _ _ _) ρ')
  · -- the new holes grow at their keys' parameters
    intro ρ ρ' hr p hk hkp dsa' hsp' hp is
    have hp' : p < grp.length := by simpa [grpNews] using hp
    simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hp', Option.map_some,
      Option.some.injEq] at hkp
    subst hkp
    obtain rfl := DenoteMetaSpine.unique hdsa hsp'
    have hpi : grp[p] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, hpm, hidx, -, -, -, -, -, hte⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
    have hG : InGrp D grp mm := ⟨hmm, by
      rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hpi, hpm⟩⟩
    obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
    simp only [grpVals, List.getElem_map, hidx]
    rw [grp_holeVal_apply mp hD hdsa hlenP hmm hs,
      grp_holeVal_apply mp hD hdsa hlenP hmm hs',
      (hte ρ ρ' (hR₀.agree ρ ρ' hr)).holeFam]
    have hY : grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ)
        (keyFrame dsa (ctx.hiAt prog.length) ρ') mm
        = D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ') mm := by
      unfold grpTuple; rw [if_pos hG]
    rw [hY]
    exact Subset.refl _

end Frame

end ConLeche.Model
