module

import ConLeche.Model.Inductives.ContCtor
public import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.PosDerivInv

public section

/-!
# A container frame's walk (lane CONTSEM, steps 3–4)

The frame's semantic kit: its group, holes and relation, the
constructors' readings, and `frameIter` — the reached group's carriers
grow along the frame relation, from the frame's derivation
(`PosDerivMono.lean` supplies the walked constructors by induction on
`PosD`; its accessibility twin is `frameIterAcc`, `ContAccFrame.lean`).
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

/-- **The frame's group is well formed, possibly empty** (lane NESTIND,
O12): its names distinct, each a member of the container's block `D`,
each at the frame's key through `nestInstType`.  The EMPTY group is the
group-free reading of an instantiated container constructor (every
member stays a constant), which the recursor's rule data read at an
outside major. -/
@[expose] def GrpWf (ctx : NestCtx) (D : LfpDatum V) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  (grp.map (·.1)).Nodup ∧ ∀ p ∈ grp, (∃ mm, mm < D.k ∧ p.1 = D.member mm) ∧
    ∃ nI, ConLeche.nestInstType (m := CheckM) ctx hi ⟨p.1, us, ds⟩ = .ok (nI, p.2)

/-- **The frame's group is well formed**: nonempty, its names distinct,
each a member of the container's block `D`, each at the frame's key
through `nestInstType` (its hole's type the member's former at the key's
levels). -/
@[expose] def GrpOk (ctx : NestCtx) (D : LfpDatum V) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  grp ≠ [] ∧ GrpWf ctx D hi us ds grp

/-- Member `mm` of `D` is in the frame's group. -/
@[expose] def InGrp (D : LfpDatum V) (grp : List (Name × Expr)) (mm : Nat) : Prop :=
  mm < D.k ∧ (grp.map (·.1)).contains (D.member mm) = true

/-- The frame's hole values at a key frame `ρp` and a tuple `Y`. -/
@[expose] noncomputable def grpVals (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp Y : Nat → V) : List V :=
  grp.map fun p => D.holeVal ψ ρp Y (D.names.idxOf p.1)

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
    {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp) {p : Name × Expr} (hp : p ∈ grp) :
    ∃ mm, mm < D.k ∧ p.1 = D.member mm ∧ D.names.idxOf p.1 = mm ∧ ∃ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      p.2 = cv.type.instantiateLevelParams lps us ∧
      ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
        TeleEq (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') (D.ids mm (Level.substFn φ lps us)) := by
  obtain ⟨-, hall⟩ := hg
  obtain ⟨⟨mm, hmm, hpm⟩, nI, hrun⟩ := hall p hp
  obtain ⟨cv, caps, hf, hcl⟩ := hlps mm hmm
  rw [hpm] at hrun
  subst hcl
  obtain ⟨hcty, -, hte⟩ := n2_link mp hD hmm hfind hrun hf hnd hul hlenP hds hdsa
  exact ⟨mm, hmm, hpm, by rw [hpm]; exact idxOf_member hnN hkN hmm, cv, caps, hf, rfl, hcty, hte⟩

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

/-- The substituted variables of a frame's constructor type: the key's
parameters, then each member's hole (in the group) or constant. -/
@[expose] def grpS (D : LfpDatum V) (us : List Level) (hi : Nat) (grp : List (Name × Expr))
    (ds : List Expr) : Nat → Expr :=
  fun q => if q < ds.length then ds.getD q default else
    (grpSub us hi grp (D.member (q - ds.length)) us).getD (.const (D.member (q - ds.length)) us)

/-- Their readings at the frame's depth. -/
@[expose] noncomputable def grpX (m : EnvModel V env) (φ : Name → Nat) (D : LfpDatum V)
    (us : List Level) (hi : Nat) (grp : List (Name × Expr)) (ds : List Expr) (d : Nat) :
    Nat → AnnotTerm :=
  fun q => (denoteMeta m.acval env φ d (grpS D us hi grp ds q)).getD .prf

/-- The substitution's values are the group's holes. -/
theorem grpSub_some {us us' : List Level} {hi : Nat} {grp : List (Name × Expr)} {c : Name}
    {r : Expr} (h : grpSub us hi grp c us' = some r) :
    ∃ i, ∃ hi' : i < grp.length, r = .fvar (hi + i) grp[i].2 := by
  unfold grpSub at h
  split at h
  · obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp h
    have hmem : (c, r) ∈ (grp.mapIdx fun i (c, ty) => (c, Expr.fvar (hi + i) ty)) := by
      rw [hl]; simp
    obtain ⟨i, hi', he⟩ := List.getElem_of_mem hmem
    have hi'' : i < grp.length := by simpa using hi'
    refine ⟨i, hi'', ?_⟩
    rw [List.getElem_mapIdx] at he
    exact (congrArg Prod.snd he).symm
  · exact nomatch h

/-- **The group's hole types, without the walk** (lane NESTIND, session
15): the names distinct, each a member of `D`, each hole typed by the
member's former at the key's levels.  `GrpWf` gives it (`grpWf_ty`);
the recursor stage's (D) typing states it directly (its group is the
container's recorded block, its hole types the formers at the major's
levels), with no `nestInstType` run. -/
@[expose] def GrpTy (env : Env) (D : LfpDatum V) (us : List Level) (grp : List (Name × Expr)) :
    Prop :=
  (grp.map (·.1)).Nodup ∧ ∀ p ∈ grp, ∃ mm, mm < D.k ∧ p.1 = D.member mm ∧ ∃ cv caps,
    env.find? (D.member mm) = some (.indInfo cv caps) ∧
    p.2 = cv.type.instantiateLevelParams cv.levelParams us

section FrameT

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  {grp : List (Name × Expr)} (hgT : GrpTy env D us grp)

include hD hnN hkN hlps hnd hul hds hdsa hgT

omit hD hnd hul hds hdsa in
/-- A group member's hole type is closed and reads the same at every depth. -/
theorem grp_typeT {p : Name × Expr} (hp : p ∈ grp) :
    p.2.hasFvar = false ∧ p.2.looseBVarsBounded 0 = true ∧
    ∃ mm cv caps, mm < D.k ∧ p.1 = D.member mm ∧ D.names.idxOf p.1 = mm ∧
      env.find? (D.member mm) = some (.indInfo cv caps) ∧
      ∃ ta, denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cv.type = some ta ∧
        ∀ d, denoteMeta mp.base2.acval env φ d p.2 = some ta := by
  obtain ⟨mm, hmm, hpm, cv, caps, hf, hp2⟩ := hgT.2 p hp
  have hidx : D.names.idxOf p.1 = mm := by rw [hpm]; exact idxOf_member hnN hkN hmm
  obtain ⟨cv', caps', hf', hlp⟩ := hlps mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  rw [hlp] at hp2
  have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  have hcl : p.2.hasFvar = false := by
    rw [hp2, Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbb : p.2.looseBVarsBounded 0 = true := by
    rw [hp2, Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
  obtain ⟨ta, hta⟩ := mp.type_reads _ (ConLeche.Semantics.Env.find?_mem hf) (Level.substFn φ lps us)
  change denoteMeta mp.base2.acval env _ 0 cv.type = _ at hta
  refine ⟨hcl, hbb, mm, cv, caps, hmm, hpm, hidx, hf, ta, hta, fun d => ?_⟩
  have h0 : denoteMeta mp.base2.acval env φ 0 p.2 = some ta := by
    rw [hp2, denotePInstLevels]; exact hta
  exact denoteMeta_depth_of_closed mp.base2.acval_closed hcl
    (fun k => denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hcl hbb h0 1 k) h0 d

omit hD hnd in
/-- The frame's substituted variables are scoped, bvar-closed and read. -/
theorem grpS_readT (q : Nat) (hq : q < ds.length + D.k) :
    Expr.WScoped (hi + grp.length) (grpS D us hi grp ds q) ∧
    (grpS D us hi grp ds q).looseBVarsBounded 0 = true ∧
    denoteMeta mp.base2.acval env φ (hi + grp.length) (grpS D us hi grp ds q)
      = some (grpX mp.base2 φ D us hi grp ds (hi + grp.length) q) := by
  suffices h : Expr.WScoped (hi + grp.length) (grpS D us hi grp ds q) ∧
      (grpS D us hi grp ds q).looseBVarsBounded 0 = true ∧
      ∃ v, denoteMeta mp.base2.acval env φ (hi + grp.length) (grpS D us hi grp ds q) = some v by
    obtain ⟨h1, h2, v, hv⟩ := h
    refine ⟨h1, h2, ?_⟩
    unfold grpX; rw [hv]; rfl
  unfold grpS
  by_cases hqd : q < ds.length
  · rw [if_pos hqd]
    have hmem : ds.getD q default ∈ ds := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqd]; exact List.getElem_mem _
    obtain ⟨hw, hb⟩ := hds _ hmem
    refine ⟨Expr.WScoped.mono (by omega) hw, hb, ?_⟩
    rw [denoteMeta_lift mp.base2.acval_closed hw _ (by omega),
      DenoteMetaSpine.getD hdsa default q hqd]
    exact ⟨_, rfl⟩
  · rw [if_neg hqd]
    have hmm : q - ds.length < D.k := by omega
    by_cases hG : D.member (q - ds.length) ∈ grp.map (·.1)
    · obtain ⟨i, hi', hgi⟩ : ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member (q - ds.length) := by
        obtain ⟨i, hi', h⟩ := List.getElem_of_mem hG
        exact ⟨i, by simpa using hi', by simpa using h⟩
      rw [← hgi, grpSub_mem hgT.1 hi', Option.getD_some]
      obtain ⟨hcl, -, -⟩ := grp_typeT mp (φ := φ) hnN hkN hlps hgT
        (List.getElem_mem hi')
      refine ⟨by simp only [Expr.WScoped]; exact ⟨by omega, Expr.WScoped.of_not_hasFvar hcl⟩,
        by simp [Expr.looseBVarsBounded], ?_⟩
      rw [denoteMeta_fvar]; exact ⟨_, rfl⟩
    · rw [grpSub_none hG, Option.getD_none]
      obtain ⟨cv, caps, hf, hlp⟩ := hlps _ hmm
      refine ⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded], ?_⟩
      rw [denoteMeta_const hf (by rw [hul, ← hlp]; rfl)]
      exact ⟨_, rfl⟩

omit hD in
open Classical in
/-- **The substituted valuation of a frame walk valuation**: the member
slots hold the group's hole values (the group) or the formers (the rest),
the parameters the key frame. -/
theorem substE_grpT (ρp Y ρ : Nat → V) :
    substE V (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0
        (consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ)
      = consList ((List.range D.k).map fun mm =>
          if decide (InGrp D grp mm) = true then D.holeVal (Level.substFn φ lps us) ρp Y mm
          else interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
        (keyFrame dsa hi ρ) := by
  have hvl : (grpVals D (Level.substFn φ lps us) grp ρp Y).length = grp.length := by
    simp [grpVals]
  rw [substE_substTau]
  congr 1
  · -- the member slots
    refine List.map_congr_left fun mm hmm => ?_
    have hmm' : mm < D.k := List.mem_range.mp hmm
    have hr := (grpS_readT mp hnN hkN hlps hul hds hdsa hgT (ds.length + mm)
      (by omega)).2.2
    unfold grpS at hr
    rw [if_neg (by omega), show ds.length + mm - ds.length = mm by omega] at hr
    by_cases hG : InGrp D grp mm
    · rw [if_pos (by simpa using hG)]
      obtain ⟨i, hi', hgi⟩ : ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member mm := by
        obtain ⟨i, hi', h⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hG.2)
        exact ⟨i, by simpa using hi', by simpa using h⟩
      rw [← hgi, grpSub_mem hgT.1 hi', Option.getD_some, denoteMeta_fvar] at hr
      rw [← Option.some.inj hr, interp_bvar,
        show hi + grp.length - 1 - (hi + i) = grp.length - 1 - i by omega,
        consList_getElem_pos hvl hi']
      simp only [grpVals, List.getElem_map]
      rw [hgi, idxOf_member hnN hkN hmm']
    · rw [if_neg (by simpa using hG)]
      have hG' : D.member mm ∉ grp.map (·.1) := fun h =>
        hG ⟨hmm', List.contains_iff_mem.mpr h⟩
      rw [grpSub_none hG', Option.getD_none] at hr
      obtain ⟨cv, caps, hf, hlp⟩ := hlps _ hmm'
      rw [denoteMeta_const hf (by rw [hul, ← hlp]; rfl)] at hr
      rw [← Option.some.inj hr]
      subst hlp
      exact acval_interp_closedC mp.base2 _ _ _ _
  · -- the parameter frame
    funext q
    unfold keyFrame
    rw [show consList (List.map (interp V ρ) dsa) (fun j => ρ (j + hi)) q = _ from
      consList_map_apply _ _ q, List.length_map, ← DenoteMetaSpine.length_eq hdsa]
    by_cases hq : q < ds.length
    · rw [if_pos hq, if_pos hq]
      have hr := (grpS_readT mp hnN hkN hlps hul hds hdsa hgT (ds.length - 1 - q)
        (by omega)).2.2
      unfold grpS at hr
      rw [if_pos (by omega)] at hr
      have hmem : ds.getD (ds.length - 1 - q) default ∈ ds := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      rw [denoteMeta_lift mp.base2.acval_closed (hds _ hmem).1 _ (by omega),
        DenoteMetaSpine.getD hdsa default _ (by omega)] at hr
      rw [← Option.some.inj hr, show hi + grp.length - hi = (grpVals D (Level.substFn φ lps us) grp
        ρp Y).length by rw [hvl]; omega, interp_liftN_consList]
      have hlt : ds.length - 1 - q < dsa.length := by
        rw [← DenoteMetaSpine.length_eq hdsa]; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt, Option.getD_some, Option.map_some, Option.getD_some]
    · rw [if_neg hq, if_neg hq]
      rw [show q - ds.length + (hi + grp.length)
        = (q - ds.length + hi) + (grpVals D (Level.substFn φ lps us) grp ρp Y).length by
          rw [hvl]; omega, consList_apply_add]

/-- **A frame constructor's type, read** (the container substitution
law at the frame, `frameCrest_read`, over the recorded reading M2): the
group's constructor `(c, j)`, instantiated at the key and with the group
abstracted to its holes, reads at the frame's depth as the recorded
Π-tower substituted by the frame's variables. -/
theorem crest_readT {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
        (grpSub us hi grp)) = some crest ∧
      (∃ Tys : List AnnotTerm, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cvm.type
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denoteMeta mp.base2.acval env φ (hi + grp.length) crest
        = some (mkPisAV (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab)
            (AnnotTerm.substAV (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D us hi grp ds (hi + grp.length)))
              (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
                ((List.range ds.length).map (fun i => AnnotTerm.bvar (ds.length + D.k + nF - 1 - i))
                  ++ D.resIdx (Level.substFn φ lps us) c j)) ab.length)) := by
  obtain ⟨-, -, -, -, hrd⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', hf', hcl, hlpsC, hocc, -, A, hA, hread⟩ := hrd c hc j hj
  rw [hfc] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cv = cv' ∧ ds.length = nPc' ∧ nF = nF' := by
    simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf'
    exact ⟨hf'.1, hf'.2.1, hf'.2.2⟩
  have hlp : cv.levelParams = lps := by
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC c hc
    obtain ⟨cvm', capsm', hfm', hlm'⟩ := hlps c hc
    rw [hfm] at hfm'
    obtain ⟨rfl, rfl⟩ : cvm = cvm' ∧ capsm = capsm' := by simpa using hfm'
    rw [← hlm, hlm']
  refine ⟨hlp, ?_⟩
  obtain ⟨-, -, ab, Tys, hab, hlab, hlT, hTys, hEqF⟩ := hread (Level.substFn φ lps us)
  have hk : D.names.length = D.k := hkN
  have hAw : Expr.WScoped (ds.length + D.names.length) A := by
    have := ConLeche.memberCrest_wscoped (ctx := canonCtx D.names cv.levelParams ds.length)
      (holes := canonHoles ds.length D.k)
      (fun x hx => by
        obtain ⟨mm, hmm, rfl⟩ := mem_canonHoles hx
        refine ⟨?_, _, _, rfl⟩
        simp only [Expr.WScoped, ConLeche.NestCtx.hiAt, canonCtx]
        exact ⟨by omega, trivial⟩)
      (fun x hx => by
        obtain ⟨i, hi'⟩ := List.getElem?_of_mem hx
        have hlt : i < ds.length := by
          have := (List.getElem?_eq_some_iff.mp hi').1
          simpa [canonCtx, canonParams] using this
        change (canonParams ds.length)[i]? = _ at hi'
        rw [canonParams_getElem? hi']
        simp only [Expr.WScoped, ConLeche.NestCtx.hiAt, canonCtx]
        exact ⟨by omega, trivial⟩) hcl hA
    simpa [ConLeche.NestCtx.hiAt, canonCtx] using this
  obtain ⟨crest, hcr, hcrd⟩ := frameCrest_read mp.base2 (φ := φ)
    (ctx := canonCtx D.names cv.levelParams ds.length) (holes := canonHoles ds.length D.k)
    (us := us) (sub := grpSub us hi grp) (ds := ds) (D' := hi + grp.length)
    (s := grpS D us hi grp ds) (x := grpX mp.base2 φ D us hi grp ds (hi + grp.length))
    (fun mm hmm => ⟨_, canonHoles_getElem? (by simpa [canonCtx, hk] using hmm)⟩)
    (by rw [hlp]; exact hnd) (by rw [hlp]; exact hul) (canonParams_length _)
    (fun mm hmm => by
      show grpS D us hi grp ds (ds.length + mm) = _
      unfold grpS
      rw [if_neg (by omega), show ds.length + mm - ds.length = mm by omega]
      rfl)
    (fun n vs hn => grpSub_none (fun hm => by
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hm
      obtain ⟨mm, hmm, hpm, -⟩ := hgT.2 p hp
      have : D.names.contains (D.member mm) = true := by
        rw [List.contains_iff_mem]
        unfold LfpDatum.member
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _
      change D.names.contains n = false at hn
      rw [← hpn, hpm, this] at hn
      exact nomatch hn))
    (fun i hi' => by
      show grpS D us hi grp ds i = _
      unfold grpS; rw [if_pos (show i < ds.length from hi')])
    (fun i hi' => ⟨.sort .zero, by
      show (canonParams ds.length)[i]? = _
      simp [canonParams, List.getElem?_range (show i < ds.length from hi')]⟩) rfl
    (fun i hi' => grpS_readT mp hnN hkN hlps hul hds hdsa hgT i
      (by simpa [canonCtx, hk] using hi'))
    hcl hAw hocc hA (by
      show denoteMeta _ env (Level.substFn φ cv.levelParams us) (ds.length + D.names.length) A = _
      rw [hk, hlp]; exact hab)
  simp only [canonCtx, hk] at hcrd
  exact ⟨crest, ab, hcr, ⟨Tys, hlT, hTys, hEqF⟩, hlab, hcrd⟩

omit hD hnd hul hdsa in
/-- **A frame constructor's type is framed and its leaves are in the
frame's context**: the key's parameters' leaves (below the key's depth,
where the enclosing context holds them) and the group's holes (typed by
their members' formers, the new entries). -/
theorem crest_frameT {Δh : List AnnotTerm} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {e crest : Expr} (hcl : e.hasFvar = false) (hbb : e.looseBVarsBounded 0 = true)
    (hcr : instPisWith ds (e.replaceConsts (grpSub us hi grp)) = some crest) :
    Frame (hi + grp.length) crest ∧
    CtxOkP mp.base2 φ (hi + grp.length) ((grpTys mp.base2 φ grp).reverse ++ Δh) crest := by
  have hsubv : ∀ c us' r, grpSub us hi grp c us' = some r →
      ∃ i, ∃ hi' : i < grp.length, r = .fvar (hi + i) grp[i].2 := fun _ _ _ h => grpSub_some h
  -- the leaves
  have hleaves : ∀ l ∈ crest.fvarLeaves, (∃ x ∈ ds, l ∈ x.fvarLeaves) ∨
      ∃ i, ∃ hi' : i < grp.length, l = (hi + i, grp[i].2) := by
    intro l hl
    rcases ConLeche.fvarLeaves_instPisWith hcr l hl with hl' | hl'
    · obtain ⟨c, us', r, hr, hlr⟩ := ConLeche.fvarLeaves_replaceConsts_closed e hcl l hl'
      obtain ⟨i, hi', rfl⟩ := hsubv c us' r hr
      obtain ⟨hcl', -⟩ := grp_typeT mp (φ := φ) hnN hkN hlps hgT
        (List.getElem_mem hi')
      simp only [Expr.fvarLeaves, ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl',
        List.mem_singleton] at hlr
      exact Or.inr ⟨i, hi', hlr⟩
    · exact Or.inl hl'
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- scoped
    refine ConLeche.wscoped_instPisWith (fun x hx => Expr.WScoped.mono (by omega) (hds x hx).1)
      (ConLeche.WScoped.replaceConsts_closed (fun c us' r hr => ?_) e hcl) hcr
    obtain ⟨i, hi', rfl⟩ := hsubv c us' r hr
    obtain ⟨hcl', -⟩ := grp_typeT mp (φ := φ) hnN hkN hlps hgT
      (List.getElem_mem hi')
    simp only [Expr.WScoped]
    exact ⟨by omega, Expr.WScoped.of_not_hasFvar hcl'⟩
  · -- bvar-closed
    refine ConLeche.looseBVarsBounded_instPisWith (fun x hx => (hds x hx).2)
      (ConLeche.looseBVarsBounded_replaceConsts (fun c us' r hr => ?_) e 0 hbb) hcr
    obtain ⟨i, hi', rfl⟩ := hsubv c us' r hr
    simp [Expr.looseBVarsBounded]
  · -- leaves bounded
    intro l hl
    rcases hleaves l hl with ⟨x, hx, hlx⟩ | ⟨i, hi', rfl⟩
    · exact hLds x hx l hlx
    · exact (grp_typeT mp (φ := φ) hnN hkN hlps hgT (List.getElem_mem hi')).2.1
  · -- the context discipline
    refine CtxOkP.extend (by simp [grpTys]) hΔ fun l hl => ?_
    rcases hleaves l hl with ⟨x, hx, hlx⟩ | ⟨i, hi', rfl⟩
    · exact Or.inl ((hCds x hx).2 l hlx)
    · obtain ⟨hcl', -, mm, cv, caps, hmm, -, -, hf, ta, hta, hread⟩ :=
        grp_typeT mp (φ := φ) hnN hkN hlps hgT (List.getElem_mem hi')
      have htys : (grpTys mp.base2 φ grp)[i]? = some ta := by
        simp only [grpTys, List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some,
          hread 0, Option.getD_some]
      refine Or.inr ⟨i, hi', rfl, Expr.WScoped.of_not_hasFvar hcl', ta, hread _, ?_,
        fun σ _ => mp.type_wellDenotedV _ (ConLeche.Semantics.Env.find?_mem hf) _ ta hta σ⟩
      rw [List.getElem?_reverse (by simp [grpTys]; omega)]
      simp only [grpTys, List.length_map]
      rw [show grp.length - 1 - (grp.length - 1 - i) = i by omega]
      exact htys

end FrameT

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
    intro ρ ρ' hr p hk hkp dsa' hsp' hp is _
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

/-- `GrpWf` gives the group's hole types. -/
theorem grpWf_ty : GrpTy env D us grp :=
  ⟨hg.1, fun p hp => by
    obtain ⟨mm, hmm, hpm, -, cv, caps, hf, hlp, hp2, -⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
    exact ⟨mm, hmm, hpm, cv, caps, hf, by rw [hlp]; exact hp2⟩⟩

/-- A group member's hole type is closed and reads the same at every depth. -/
theorem grp_type {p : Name × Expr} (hp : p ∈ grp) :
    p.2.hasFvar = false ∧ p.2.looseBVarsBounded 0 = true ∧
    ∃ mm cv caps, mm < D.k ∧ p.1 = D.member mm ∧ D.names.idxOf p.1 = mm ∧
      env.find? (D.member mm) = some (.indInfo cv caps) ∧
      ∃ ta, denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cv.type = some ta ∧
        ∀ d, denoteMeta mp.base2.acval env φ d p.2 = some ta :=
  grp_typeT mp hnN hkN hlps
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) hp

/-- The frame's substituted variables are scoped, bvar-closed and read. -/
theorem grpS_read (q : Nat) (hq : q < ds.length + D.k) :
    Expr.WScoped (hi + grp.length) (grpS D us hi grp ds q) ∧
    (grpS D us hi grp ds q).looseBVarsBounded 0 = true ∧
    denoteMeta mp.base2.acval env φ (hi + grp.length) (grpS D us hi grp ds q)
      = some (grpX mp.base2 φ D us hi grp ds (hi + grp.length) q) :=
  grpS_readT mp hnN hkN hlps hul hds hdsa
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) q hq

open Classical in
/-- **The substituted valuation of a frame walk valuation**: the member
slots hold the group's hole values (the group) or the formers (the rest),
the parameters the key frame. -/
theorem substE_grp (ρp Y ρ : Nat → V) :
    substE V (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0
        (consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ)
      = consList ((List.range D.k).map fun mm =>
          if decide (InGrp D grp mm) = true then D.holeVal (Level.substFn φ lps us) ρp Y mm
          else interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
        (keyFrame dsa hi ρ) :=
  substE_grpT mp hnN hkN hlps hnd hul hds hdsa
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) ρp Y ρ

/-- **A frame constructor's type, read** (the container substitution
law at the frame, `frameCrest_read`, over the recorded reading M2): the
group's constructor `(c, j)`, instantiated at the key and with the group
abstracted to its holes, reads at the frame's depth as the recorded
Π-tower substituted by the frame's variables. -/
theorem crest_read {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
        (grpSub us hi grp)) = some crest ∧
      (∃ Tys : List AnnotTerm, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cvm.type
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denoteMeta mp.base2.acval env φ (hi + grp.length) crest
        = some (mkPisAV (AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab)
            (AnnotTerm.substAV (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D us hi grp ds (hi + grp.length)))
              (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
                ((List.range ds.length).map (fun i => AnnotTerm.bvar (ds.length + D.k + nF - 1 - i))
                  ++ D.resIdx (Level.substFn φ lps us) c j)) ab.length)) :=
  crest_readT mp hD hnN hkN hlps hnd hul hds hdsa
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) hc hj hfc

/-- **A frame constructor's type is framed and its leaves are in the
frame's context**: the key's parameters' leaves (below the key's depth,
where the enclosing context holds them) and the group's holes (typed by
their members' formers, the new entries). -/
theorem crest_frame {Δh : List AnnotTerm} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    {e crest : Expr} (hcl : e.hasFvar = false) (hbb : e.looseBVarsBounded 0 = true)
    (hcr : instPisWith ds (e.replaceConsts (grpSub us hi grp)) = some crest) :
    Frame (hi + grp.length) crest ∧
    CtxOkP mp.base2 φ (hi + grp.length) ((grpTys mp.base2 φ grp).reverse ++ Δh) crest :=
  crest_frameT mp hnN hkN hlps hds
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) hΔ hCds hLds hcl hbb hcr

omit hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
/-- **The frame's hole values satisfy the recorded reading's hole
context** (lane ALPHA1): the parameters at the key frame, then each
member's value in its former type — a group member's hole value
(`holeVal_mem_type`), another member's own leaf (`mem_type`). -/
theorem frameVals_sat {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env ψ 0 cvm.type = some (Tys.getD mm default))
    (P : Nat → Bool) (X : Nat → V) (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) (ρ : Nat → V) :
    Sat V (D.params ψ ++ Tys).reverse (consList ((List.range D.k).map fun mm =>
      if P mm = true then D.holeVal ψ ρp X mm else interp V ρ (mp.base2.acval (D.member mm) ψ))
      ρp) := by
  rw [List.reverse_append]
  refine sat_of_spineFit hs ?_
  have key : ∀ (n : Nat), n ≤ D.k → SpineFit ρp (Tys.take n) ((List.range n).map fun mm =>
      if P mm = true then D.holeVal ψ ρp X mm else interp V ρ (mp.base2.acval (D.member mm) ψ)) := by
    intro n
    induction n with
    | zero => intro _; simp [SpineFit]
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.take_add_one]
      have hTn : Tys[n]? = some (Tys.getD n default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hTn]
      refine (ih (by omega)).append ⟨?_, trivial⟩
      obtain ⟨cvm, caps, hfm, hr⟩ := hTys n (by omega)
      simp only
      split
      · exact holeVal_mem_type mp hD (by omega) hfm hr hX _
      · have hmt := mp.mem_type _ (List.mem_of_find?_eq_some hfm) ψ _ hr
          (consList ((List.range n).map fun mm => if P mm = true then D.holeVal ψ ρp X mm
            else interp V ρ (mp.base2.acval (D.member mm) ψ)) ρp)
        rw [ConLeche.Semantics.Env.find?_name hfm] at hmt
        rw [acval_interp_closedC mp.base2 _ _ ρ (consList ((List.range n).map fun mm =>
          if P mm = true then D.holeVal ψ ρp X mm
          else interp V ρ (mp.base2.acval (D.member mm) ψ)) ρp)]
        exact hmt
  have := key D.k (Nat.le_refl _)
  rwa [List.take_of_length_le (by omega)] at this

open Classical in
/-- **A frame's final walk grows its group's carriers** (NESTPLAN L3,
CONTSEM step 4): the constructors of the reached group, instantiated at
the key and walked along the frame relation, make every member of the
group grow between the two key frames of each related pair — by
`carrier_le_on_group'`, whose walk premise is the per-constructor
transfer at the frame relation.  The state invariant is kept whatever
the outcome. -/
theorem frameIter (hin : RulesInputs V mp.base2 φ) {F : Nat}
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2))
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {Δh : List AnnotTerm}
    {R₀ : FrameRel V} (hR₀ : HoleRel mp.base2 φ ctx prog hi Δh R₀) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ'))
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hwalk : ∀ {Δ : List AnnotTerm} {R : FrameRel V},
      HoleRel mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) Δ R →
      ∀ (Q : ConstantVal × Nat → Prop),
      (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
        instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
          (grpSub us hi grp)) = some crest →
        (∃ ty, ConLeche.inferTypeCore .verified env F (hi + grp.length) crest = .ok ty) →
        ∃ ca, Frame (hi + grp.length) crest ∧ CtxOkP mp.base2 φ (hi + grp.length) Δ crest ∧
          denoteMeta mp.base2.acval env φ (hi + grp.length) crest = some ca ∧ Graded V Δ ca) →
      (∀ x ∈ ctors, Q x) →
      ∀ x ∈ ctors, CtorWalked mp.base2 φ ctx (hi + grp.length) us ds ds.length (grpSub us hi grp)
        R x) :
    (∀ ρ ρ', R₀ ρ ρ' → ∀ c, InGrp D grp c →
      FamLe (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') c)) ∧
      -- the per-constructor HOLE-FIT transfer the carriers' growth is built
      -- from (`ctor_transfer` along the frame relation), exported for lane
      -- NESTIND (lane NESTKERN session 2)
      ∀ ρ ρ', R₀ ρ ρ' → ∀ g, InGrp D grp g → ∀ t j fs,
        D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
          (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))
          t g j fs →
        D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) t g j fs := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  obtain ⟨hctorsIn, hctorsAll⟩ := ConLeche.groupCtors_spec hgc
  -- every walked constructor is one of the group's constructors
  have hQ : ∀ x ∈ ctors, ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2) := by
    intro x hx
    obtain ⟨cn, hcn, nP', L, hL, hnP, hxL⟩ := hctorsIn x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcn
    obtain ⟨⟨c, hc, hpc⟩, -⟩ := hg.2 p hp
    obtain ⟨nP'', L', hL', hlen', hfL⟩ := hcov c hc
    rw [hpc, hL'] at hL
    obtain ⟨rfl, rfl⟩ : nP'' = nP' ∧ L' = L := by simpa using hL
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxL
    have hnP' : nP'' = ds.length := by
      rcases hnP with h' | h'
      · exact h'
      · rw [h'] at hj; exact absurd hj (Nat.not_lt_zero _)
    refine ⟨c, j, ⟨hc, ?_⟩, by rw [← hlen']; exact hj, by rw [← hnP']; exact hfL j hj⟩
    rw [List.contains_iff_mem, List.mem_map]
    exact ⟨p, hp, hpc⟩
  -- the frame relation, and the walk along it
  have hR' := frameRel_holeRel mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hR₀ hfit
  have hw := hwalk hR'
    (fun x => ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2))
    (fun x crest hQx hcr hinf => by
      obtain ⟨c, j, ⟨hc, -⟩, hj, hfc⟩ := hQx
      have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
      have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
      have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0 = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      obtain ⟨hfr, hC⟩ := crest_frame mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hΔ hCds hLds
        hcl hbb hcr
      obtain ⟨-, crest', ab, hcr', -, -, hrd⟩ :=
        crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hc hj hfc
      rw [hcr] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨ty, hty⟩ := hinf
      have hIS : InferSemFull mp.base2 φ (hi + grp.length) crest ty :=
        infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty)
      obtain ⟨-, -, -, -, hgr, -⟩ := hIS hfr hC.toCtxOk hrd
      exact ⟨_, hfr, hC, hrd, hgr⟩)
    hQ
  have hkNN := h.kN
  have htr : ∀ ρ ρ', R₀ ρ ρ' → ∀ g, InGrp D grp g → ∀ t j fs,
      D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
        (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))
        t g j fs →
      D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) t g j fs := by
    intro ρ ρ' hr g hG t j fs hf
    obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
    have hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ' := by
      have := hR₀.agree ρ ρ' hr; rwa [hhi] at this
    have hj : j < D.nctors g := hf.1

    -- the constructor `(g, j)`
    obtain ⟨nP', L, hL, hlenL, hfL⟩ := hcov g hG.1
    have hjL : j < L.length := by rw [hlenL]; exact hj
    obtain ⟨hxmem, hnP'⟩ : L[j] ∈ ctors ∧ nP' = ds.length := by
      obtain ⟨nP'', L'', hL'', hnP'', hall⟩ :=
        hctorsAll (D.member g) (List.contains_iff_mem.mp hG.2)
      rw [hL] at hL''
      obtain ⟨rfl, rfl⟩ : nP' = nP'' ∧ L = L'' := by simpa using hL''
      refine ⟨hall _ (List.getElem_mem hjL), ?_⟩
      rcases hnP'' with h' | h'
      · exact h'
      · rw [h'] at hjL; exact absurd hjL (Nat.not_lt_zero _)
    have hfc := hfL j hjL
    rw [hnP'] at hfc
    obtain ⟨-, crest, ca, cur, hcr, hca, hres, hidx, hpos⟩ := hw _ hxmem
    obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
      crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
    rw [hcr] at hcr'
    obtain rfl := Option.some.inj hcr'
    rw [hca] at hrd
    obtain rfl := Option.some.inj hrd
    -- the substituted result head is the member's hole
    have hhead : ∃ p, ((substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) (D.k - 1 - g)).liftN L[j].2 0
          = .bvar p := by
      have hgk := hG.1
      simp only [substTau, if_pos (show D.k - 1 - g < ds.length + D.k by omega)]
      rw [show ds.length + D.k - 1 - (D.k - 1 - g) = ds.length + g by omega]
      have hr := (grpS_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (ds.length + g)
        (by omega)).2.2
      unfold grpS at hr
      rw [if_neg (by omega), show ds.length + g - ds.length = g by omega] at hr
      obtain ⟨i, hi', hgi⟩ : ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member g := by
        obtain ⟨i, hi', h'⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hG.2)
        exact ⟨i, by simpa using hi', by simpa using h'⟩
      rw [← hgi, grpSub_mem hg.1 hi', Option.getD_some, denoteMeta_fvar] at hr
      rw [← Option.some.inj hr]
      exact ⟨hi + grp.length - 1 - (hi + i) + L[j].2, by simp⟩
    obtain ⟨p, hp⟩ := hhead
    have hS := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (keyFrame dsa hi ρ)
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ')) ρ
    have hLv := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (keyFrame dsa hi ρ')
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) ρ'
    have hagS := holeAgree_instance mp hD hs ρ (fun mm => decide (InGrp D grp mm))
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))
      (vs := (List.range D.k).map fun mm =>
        if decide (InGrp D grp mm) = true then
          D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ')) mm
        else interp V ρ (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
      (by simp) (fun m hm => by simp)
    have hagL := holeAgree_instance mp hD hs' ρ' (fun mm => decide (InGrp D grp mm))
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ'))
      (vs := (List.range D.k).map fun mm =>
        if decide (InGrp D grp mm) = true then
          D.holeVal (Level.substFn φ lps us) (keyFrame dsa hi ρ')
            (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) mm
        else interp V ρ' (mp.base2.acval (D.member mm) (Level.substFn φ lps us)))
      (by simp) (fun m hm => by simp)
    have htS : (fun c => if decide (InGrp D grp c) = true then
          grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') c
        else D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ) c)
        = grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') := by
      funext c
      unfold grpTuple
      by_cases hc : InGrp D grp c <;> simp [hc]
    have htL : (fun c => if decide (InGrp D grp c) = true then
          D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') c
        else D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') c)
        = D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') := by
      funext c
      by_cases hc : InGrp D grp c <;> simp [hc]
    rw [htS, hlenP] at hagS
    rw [htL, hlenP] at hagL
    have hsatS := frameVals_sat mp hD hs hlT hTys (fun mm => decide (InGrp D grp mm))
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))
      (grpTuple_mem mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hag) ρ
    have hsatL := frameVals_sat mp hD hs' hlT hTys (fun mm => decide (InGrp D grp mm))
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ'))
      (fun c hc => lfpTuple_mem _ _ _ _ c hc) ρ'
    exact ctor_transfer hEqF hlen hlenP hp hpos hres hidx
      (h.holeApp _ g (Nat.lt_of_lt_of_le hG.1 hkNN) j hj) ⟨ρ, ρ', hr, rfl, rfl⟩ hS hLv hagS hagL
      hsatS hsatL t fs hf
  refine ⟨fun ρ ρ' hr => ?_, htr⟩
  obtain ⟨hs, hs'⟩ := hfit ρ ρ' hr
  have hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ' := by
    have := hR₀.agree ρ ρ' hr; rwa [hhi] at this
  intro c hc
  exact h.carrier_le_on_group' hs hs' (InGrp D grp)
    (fun g _ hG => grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG hag)
    (fun g _ hG t _ j fs hf => htr ρ ρ' hr g hG t j fs hf) c (Nat.lt_of_lt_of_le hc.1 hkNN) hc

end Frame

/-! ## The level parameters of a recorded block -/

/-- The lps of a recorded block's constructor are its members'. -/
theorem ctor_lps {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal} {nPc nF : Nat}
    (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF)) : cv.levelParams = lps := by
  obtain ⟨-, -, -, -, hrd⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hrd c hc j hj
  rw [hfc] at hf'
  obtain rfl : cv = cv' := by
    simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf'
    exact hf'.1
  obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC c hc
  obtain ⟨cvm', capsm', hfm', hlm'⟩ := hlps c hc
  rw [hfm] at hfm'
  obtain ⟨rfl, rfl⟩ : cvm = cvm' ∧ capsm = capsm' := by simpa using hfm'
  rw [← hlm, hlm']

end ConLeche.Model
