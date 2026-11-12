module

import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Inductives.ContCtor
public import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Env.BlockLfpTup
import ConLeche.Model.Env.BlockLfpMono
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Semantics.Tower.BlockTower
import ConLeche.Verify.Inductives.NestNfScope
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Inductives.TypeStep

public section

/-!
# A container frame's walk

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

open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- What a successful frame walk leaves of one constructor: its level
parameters distinct, and its instantiated, abstracted type (`nestCrest`)
read, walked positively along the frame relation, its result the hole
applied with hole-free indices. -/
@[expose] def CtorWalked (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (hi : Nat)
    (us : List Level) (ds : List Expr) (names : List Name) (holes : List Expr)
    (R : FrameRel V) (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca cur,
    ConLeche.nestCrest names us ds holes (x.1.type.instantiateLevelParams x.1.levelParams us)
      = some crest ∧
    denote m.acval env φ hi crest = some ca ∧ ConLeche.nestResHead cur = true ∧
    cur.getAppArgs.all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiPosThen (ResultAt m φ ctx.nP hi (hi + x.2) cur) x.2 R ca

/-! ## The frame's group, its holes and its relation -/

/-- **A spine of values each inhabiting its entry read below the earlier
ones fits**, when entry `i` is a reading over the base frame lifted past
the `i` earlier values. -/
theorem spineFit_of_lifted :
    ∀ (Ts : List Term) (vs pre : List V) (ρ : Nat → V), Ts.length = vs.length →
      (∀ i (h : i < Ts.length) (h' : i < vs.length), ∃ t,
        Ts[i] = t.liftN (pre.length + i) 0 ∧ vs[i] ∈ˢ interp V ρ t) →
      SpineFit (consList pre ρ) Ts vs
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | T :: Ts, v :: vs, pre, ρ, hl, hm => by
    obtain ⟨t, ht, hv⟩ := hm 0 (by simp) (by simp)
    refine ⟨?_, ?_⟩
    · simp only [List.getElem_cons_zero, Nat.add_zero] at ht hv
      rw [ht, interp_liftN_consList]; exact hv
    · have := spineFit_of_lifted Ts vs (pre ++ [v]) ρ (by simpa using hl) fun i h h' => by
        obtain ⟨t, ht, hv⟩ := hm (i + 1) (by simpa using h) (by simpa using h')
        refine ⟨t, ?_, by simpa using hv⟩
        simp only [List.getElem_cons_succ, List.length_append, List.length_singleton] at ht ⊢
        rw [ht, show pre.length + (i + 1) = pre.length + 1 + i by omega]
      rwa [consList_append, consList_cons, consList_nil] at this

/-- **A graded Π-tower stays graded past a fitting prefix.** -/
theorem wellDenoted_mkPisAV_append (B : Term) :
    ∀ (ab₁ ab₂ : List Term) (ρ : Nat → V) (as : List V),
      SpineFit ρ (ab₁) as → WellDenoted V ρ (mkPisAV (ab₁ ++ ab₂) B) →
      WellDenoted V (consList as ρ) (mkPisAV ab₂ B)
  | [], _, _, [], _, h => h
  | [], _, _, _ :: _, hf, _ => hf.elim
  | _ :: _, _, _, [], hf, _ => hf.elim
  | d :: ab₁, ab₂, ρ, a :: as, hf, h => by
    simp only [List.cons_append, mkPisAV, WellDenoted_pi] at h
    exact wellDenoted_mkPisAV_append B ab₁ ab₂ (cons a ρ) as hf.2 (h.2.2.1 a hf.1)

/-- **The frame's group is well formed**: its names distinct, the
container's WHOLE recorded block (N2-eager: `PosD.frame.hgrp`), each at
the frame's key through `nestInstType` (its hole's type the member's
former instantiated at the key). -/
@[expose] def GrpWf (ctx : NestCtx) (D : LfpDatum V) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  (grp.map (·.1)).Nodup ∧ (∀ c, c ∈ grp.map (·.1) ↔ c ∈ D.names) ∧
    ∀ p ∈ grp, (∃ mm, mm < D.k ∧ p.1 = D.member mm) ∧
      ∃ mm cv caps nI, mm < D.k ∧ p.1 = D.member mm ∧
        ctx.find? p.1 = some (.indInfo cv caps) ∧
        ConLeche.NestInstFacts ctx hi ⟨p.1, us, ds⟩ cv.levelParams (D.formerAt mm cv).type nI p.2

/-- **The frame's group is well formed**, nonempty. -/
@[expose] def GrpOk (ctx : NestCtx) (D : LfpDatum V) (hi : Nat) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  grp ≠ [] ∧ GrpWf ctx D hi us ds grp

/-- Member `mm` of `D` is in the frame's group (every member is:
`inGrp_of_lt`). -/
@[expose] def InGrp (D : LfpDatum V) (grp : List (Name × Expr)) (mm : Nat) : Prop :=
  mm < D.k ∧ (grp.map (·.1)).contains (D.member mm) = true

omit [SetTheory V] in
/-- **Every member is in the frame's group** (the group is the whole
recorded block). -/
theorem inGrp_of_lt {D : LfpDatum V} {grp : List (Name × Expr)}
    (hall : ∀ c, c ∈ grp.map (·.1) ↔ c ∈ D.names) (hkN : D.names.length = D.k) {mm : Nat}
    (hmm : mm < D.k) : InGrp D grp mm := by
  refine ⟨hmm, List.contains_iff_mem.mpr ((hall _).mpr ?_)⟩
  unfold LfpDatum.member
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.getElem_mem _

/-- The frame's hole values at a key frame `ρp` and a tuple `Y`. -/
@[expose] noncomputable def grpVals (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp Y : Nat → V) : List V :=
  grp.map fun p => D.holeVal ψ ρp Y (D.names.idxOf p.1)

/-- The frame's holes' context entries: hole `i`'s type (its former
instantiated at the key, an OPEN term scoped at the key's depth `hi`),
read at its own depth `hi + i`. -/
@[expose] noncomputable def grpTys (m : EnvModel V env) (φ : Name → Nat) (hi : Nat)
    (grp : List (Name × Expr)) : List Term :=
  grp.mapIdx fun i p => (denote m.acval env φ (hi + i) p.2).getD .prf

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
    (grp : List (Name × Expr)) (dsa : List Term) (hi : Nat) : FrameRel V :=
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
theorem grpMember (mp : EnvModelM V env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
    (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
    (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
    (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
    {grp : List (Name × Expr)} (hg : GrpWf ctx D hi us ds grp) {p : Name × Expr} (hp : p ∈ grp) :
    ∃ mm, mm < D.k ∧ p.1 = D.member mm ∧ D.names.idxOf p.1 = mm ∧ ∃ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      ((D.formerAt mm cv).type.stripPis ds.length).isSome = true ∧
      instPisWith ds ((D.formerAt mm cv).type.instantiateLevelParams lps us) = some p.2 ∧
      ∀ ρ ρ' : Nat → V, AgreeOff (holeP hi ctx.nP hi) ρ ρ' →
        TeleEq (keyFrame dsa hi ρ) (keyFrame dsa hi ρ') (D.ids mm (Level.substFn φ lps us)) := by
  obtain ⟨-, -, hall⟩ := hg
  obtain ⟨-, mm, cv, caps, nI, hmm, hpm, hfc, hF⟩ := hall p hp
  rw [hfind, hpm] at hfc
  change env.find? (D.member mm) = _ at hfc
  obtain ⟨cv', caps', hf, hcl⟩ := hlps mm hmm
  rw [hf] at hfc
  obtain ⟨rfl, rfl⟩ : cv' = cv ∧ caps' = caps := by simpa using hfc
  subst hcl
  rw [hpm] at hF
  obtain ⟨hcty, -, hte⟩ := n2_link mp hD hmm hf hF hnd hul hlenP hds hdsa
  exact ⟨mm, hmm, hpm, by rw [hpm]; exact idxOf_member hnN hkN hmm, cv', caps', hf, rfl, hF.strip,
    hcty, hte⟩

/-- The substituted variables of a frame's constructor type: the key's
parameters, then each member's hole. -/
@[expose] def grpS (D : LfpDatum V) (hi : Nat) (grp : List (Name × Expr)) (ds : List Expr) :
    Nat → Expr :=
  fun q => if q < ds.length then ds.getD q default else
    (grpHoles hi grp).getD ((grp.map (·.1)).idxOf (D.member (q - ds.length))) default

/-- Their readings at the frame's depth. -/
@[expose] noncomputable def grpX (m : EnvModel V env) (φ : Name → Nat) (D : LfpDatum V)
    (hi : Nat) (grp : List (Name × Expr)) (ds : List Expr) (d : Nat) : Nat → Term :=
  fun q => (denote m.acval env φ d (grpS D hi grp ds q)).getD .prf

/-- **The group's hole types, without the walk**: the names distinct, the
recorded block's, each hole typed by the member's former instantiated at
the key.  `GrpWf` gives it (`grpWf_ty`); the recursor stage's (D) typing
states it directly, with no `nestInstType` run. -/
@[expose] def GrpTy (env : Env) (D : LfpDatum V) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  (grp.map (·.1)).Nodup ∧ (∀ c, c ∈ grp.map (·.1) ↔ c ∈ D.names) ∧
    ∀ p ∈ grp, ∃ mm, mm < D.k ∧ p.1 = D.member mm ∧ ∃ cv caps,
      env.find? (D.member mm) = some (.indInfo cv caps) ∧
      ((D.formerAt mm cv).type.stripPis ds.length).isSome = true ∧
      instPisWith ds ((D.formerAt mm cv).type.instantiateLevelParams cv.levelParams us) = some p.2

omit [SetTheory V] in
/-- The group's hole of member `mm`. -/
theorem grpHoles_member {D : LfpDatum V} {grp : List (Name × Expr)} {hi : Nat}
    (hall : ∀ c, c ∈ grp.map (·.1) ↔ c ∈ D.names) (hkN : D.names.length = D.k) {mm : Nat}
    (hmm : mm < D.k) :
    ∃ i, ∃ hi' : i < grp.length, grp[i].1 = D.member mm ∧
      (grp.map (·.1)).idxOf (D.member mm) = i ∧
      (grpHoles hi grp).getD i default = .fvar (hi + i) grp[i].2 := by
  have hmem : D.member mm ∈ grp.map (·.1) := List.contains_iff_mem.mp (inGrp_of_lt hall hkN hmm).2
  have hlt : (grp.map (·.1)).idxOf (D.member mm) < grp.length := by
    have := List.idxOf_lt_length_of_mem hmem; simpa using this
  refine ⟨_, hlt, ?_, rfl, ?_⟩
  · have := List.getElem_idxOf (xs := grp.map (·.1)) (x := D.member mm)
      (by rw [List.length_map]; exact hlt)
    rw [List.getElem_map] at this
    exact this
  · simp [grpHoles, List.getD_eq_getElem?_getD, hlt]

section FrameT

variable (mp : EnvModelM V env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hgT : GrpTy env D us ds grp)

include hD hnN hkN hlps hnd hul hds hdsa hlenP hgT

omit hnN hkN in
/-- **A group member's hole type**: scoped at the key's depth, its leaves
the key's parameters', read there as the member's index telescope
substituted at the parameters' readings. -/
theorem grp_typeT {p : Name × Expr} (hp : p ∈ grp) :
    Expr.WScoped hi p.2 ∧ p.2.looseBVarsBounded 0 = true ∧
    (∀ l ∈ p.2.fvarLeaves, ∃ x ∈ ds, l ∈ x.fvarLeaves) ∧
    ∃ mm cv caps, mm < D.k ∧ p.1 = D.member mm ∧
      env.find? (D.member mm) = some (.indInfo cv caps) ∧ ∃ abF : List Term,
        denote mp.base2.acval env (Level.substFn φ lps us) 0 (D.formerAt mm cv).type
          = some (mkPisAV abF (.sort (D.w (Level.substFn φ lps us)))) ∧
        abF = D.pars mm (Level.substFn φ lps us) ++ D.ids mm (Level.substFn φ lps us) ∧
        (abF.drop ds.length) = D.ids mm (Level.substFn φ lps us) ∧
        denote mp.base2.acval env φ hi p.2
          = some (mkPisAV (Term.substTele (substTau ds.length hi fun i => dsa.getD i default) 0
              (abF.drop ds.length)) (.sort (D.w (Level.substFn φ lps us)))) := by
  obtain ⟨mm, hmm, hpm, cv, caps, hf, hstrip, hp2⟩ := hgT.2.2 p hp
  obtain ⟨cv', caps', hf', hlp⟩ := hlps mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  subst hlp
  obtain ⟨hwf₁, hwf₂, -⟩ := mp.formerAt_wf hD hmm hf
  have hcl : ((D.formerAt mm cv).type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hwf₁
  have hbb : ((D.formerAt mm cv).type.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0
      = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf₂
  refine ⟨ConLeche.wscoped_instPisWith (fun x hx => (hds x hx).1)
      (Expr.WScoped.of_not_hasFvar hcl) hp2,
    ConLeche.looseBVarsBounded_instPisWith (fun x hx => (hds x hx).2) hbb hp2,
    fun l hl => ?_, ?_⟩
  · rcases ConLeche.fvarLeaves_instPisWith hp2 l hl with hl' | hl'
    · rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl] at hl'; exact nomatch hl'
    · exact hl'
  · obtain ⟨abF, h1, h2, h4, h5⟩ :=
      instFormer_readB mp hD hmm hf hnd hul hlenP hds hdsa hstrip hp2
    exact ⟨mm, cv, caps, hmm, hpm, hf, abF, h1, h2, h4, h5⟩

omit hnN hkN in
/-- **A group member's hole type reads graded** wherever the key's
parameters fit and read graded. -/
theorem grp_typeT_wd {p : Name × Expr} (hp : p ∈ grp) {ta : Term}
    (hta : denote mp.base2.acval env φ hi p.2 = some ta) (ρ : Nat → V)
    (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ))
    (hw : ∀ a ∈ dsa, WellDenoted V ρ a) : WellDenoted V ρ ta := by
  obtain ⟨-, -, -, mm, cv, caps, hmm, -, hf, abF, hread, hmap, -, hrd⟩ :=
    grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT hp
  rw [hta] at hrd
  obtain rfl := Option.some.inj hrd
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  generalize hψ : Level.substFn φ lps us = ψ at hs hlenP hread hmap
  have hdl : dsa.length = ds.length := (DenoteSpine.length_eq hdsa).symm
  have hpl : (D.pars mm ψ).length = ds.length := (h.parsLen mm hmm ψ).trans hlenP
  -- the substituted tower is the tail tower at the key frame
  have hτ : ∀ j, WellDenoted V (shiftE 0 0 ρ)
      (substTau ds.length hi (fun i => dsa.getD i default) j) := by
    intro j
    rw [shiftE_zero_zero]
    unfold substTau
    split
    · rename_i hj
      exact hw _ (by
        show dsa.getD (ds.length - 1 - j) default ∈ dsa
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _)
    · simp
  have heq : mkPisAV (Term.substTele (substTau ds.length hi fun i => dsa.getD i default) 0
        (abF.drop ds.length)) (.sort (D.w ψ))
      = Term.substAV (substTau ds.length hi fun i => dsa.getD i default)
          (mkPisAV (abF.drop ds.length) (.sort (D.w ψ))) 0 := by
    rw [Term.substAV_mkPisAV]; rfl
  rw [heq]
  refine (WellDenoted_substAV _ _ 0 ρ fun j => hτ j).mpr ?_
  rw [← keyFrame_eq_substE hdl]
  · -- the member's closed type, graded at every frame, past the parameters
    have hwd := (mp.formerAt_wellDenotedTy hD hmm hf hread (fun j => ρ (j + hi))).1
    have hsP := h.parsSat mm hmm ψ _ hs
    have hfit : SpineFit (fun j => ρ (j + hi)) ((abF.take ds.length))
        (dsa.map (interp V ρ)) := by
      have hm1 : (abF.take ds.length) = D.pars mm ψ := by
        rw [hmap, ← hpl, List.take_left' rfl]
      rw [hm1]
      exact spineFit_of_sat_consList (by rw [List.length_map, hdl, hpl]) hsP
    rw [← List.take_append_drop ds.length abF] at hwd
    exact wellDenoted_mkPisAV_append _ _ _ _ _ hfit hwd

omit hnN in
/-- The frame's substituted variables are scoped, bvar-closed and read. -/
theorem grpS_readT (q : Nat) (hq : q < ds.length + D.k) :
    Expr.WScoped (hi + grp.length) (grpS D hi grp ds q) ∧
    (grpS D hi grp ds q).looseBVarsBounded 0 = true ∧
    denote mp.base2.acval env φ (hi + grp.length) (grpS D hi grp ds q)
      = some (grpX mp.base2 φ D hi grp ds (hi + grp.length) q) := by
  suffices h : Expr.WScoped (hi + grp.length) (grpS D hi grp ds q) ∧
      (grpS D hi grp ds q).looseBVarsBounded 0 = true ∧
      ∃ v, denote mp.base2.acval env φ (hi + grp.length) (grpS D hi grp ds q) = some v by
    obtain ⟨h1, h2, v, hv⟩ := h
    refine ⟨h1, h2, ?_⟩
    unfold grpX; rw [hv]; rfl
  unfold grpS
  by_cases hqd : q < ds.length
  · rw [ite_eq_left hqd]
    have hmem : ds.getD q default ∈ ds := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqd]; exact List.getElem_mem _
    obtain ⟨hw, hb⟩ := hds _ hmem
    refine ⟨Expr.WScoped.mono (by omega) hw, hb, ?_⟩
    rw [denote_lift mp.base2.acval_closed hw _ (by omega),
      DenoteSpine.getD hdsa default q hqd]
    exact ⟨_, rfl⟩
  · rw [ite_eq_right hqd]
    obtain ⟨i, hi', -, hidx, hget⟩ := grpHoles_member (hi := hi) hgT.2.1 hkN
      (show q - ds.length < D.k by omega)
    rw [hidx, hget]
    obtain ⟨hw, -⟩ := grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT (List.getElem_mem hi')
    refine ⟨by simp only [Expr.WScoped]; exact ⟨by omega, Expr.WScoped.mono (by omega) hw⟩,
      by simp [Expr.looseBVarsBounded], ?_⟩
    rw [denote_fvar]; exact ⟨_, rfl⟩

/-- **The substituted valuation of a frame walk valuation IS the recorded
block's hole frame** at the key frame and the tuple the group's hole
values are read at. -/
theorem substE_grpT (Y ρ : Nat → V) :
    substE V (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0
        (consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y) ρ)
      = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y := by
  have hvl : (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y).length
      = grp.length := by simp [grpVals]
  rw [substE_substTau]
  unfold LfpDatum.frame
  congr 1
  · -- the member slots
    refine List.map_congr_left fun mm hmm => ?_
    have hmm' : mm < D.k := List.mem_range.mp hmm
    have hr := (grpS_readT mp hD hkN hlps hnd hul hds hdsa hlenP hgT (ds.length + mm)
      (by omega)).2.2
    unfold grpS at hr
    rw [ite_eq_right (by omega), show ds.length + mm - ds.length = mm by omega] at hr
    obtain ⟨i, hi', hgi, hidx, hget⟩ := grpHoles_member (hi := hi) hgT.2.1 hkN hmm'
    rw [hidx, hget, denote_fvar] at hr
    rw [← Option.some.inj hr, interp_bvar,
      show hi + grp.length - 1 - (hi + i) = grp.length - 1 - i by omega,
      consList_getElem_pos hvl hi']
    simp only [grpVals, List.getElem_map]
    rw [hgi, idxOf_member hnN hkN hmm']
  · -- the parameter frame
    generalize hvs : grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y = vs at hvl ⊢
    funext q
    unfold keyFrame
    rw [show consList (List.map (interp V ρ) dsa) (fun j => ρ (j + hi)) q = _ from
      consList_map_apply _ _ q, List.length_map, ← DenoteSpine.length_eq hdsa]
    by_cases hq : q < ds.length
    · rw [ite_eq_left hq, ite_eq_left hq]
      have hr := (grpS_readT mp hD hkN hlps hnd hul hds hdsa hlenP hgT (ds.length - 1 - q)
        (by omega)).2.2
      unfold grpS at hr
      rw [ite_eq_left (by omega)] at hr
      have hmem : ds.getD (ds.length - 1 - q) default ∈ ds := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      rw [denote_lift mp.base2.acval_closed (hds _ hmem).1 _ (by omega),
        DenoteSpine.getD hdsa default _ (by omega)] at hr
      rw [← Option.some.inj hr, show hi + grp.length - hi = vs.length by rw [hvl]; omega,
        interp_liftN_consList]
      have hlt : ds.length - 1 - q < dsa.length := by
        rw [← DenoteSpine.length_eq hdsa]; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt, Option.getD_some, Option.map_some, Option.getD_some]
    · rw [ite_eq_right hq, ite_eq_right hq]
      rw [show q - ds.length + (hi + grp.length) = (q - ds.length + hi) + vs.length by
        rw [hvl]; omega, consList_apply_add]

omit hnN in
/-- **A frame constructor's type, read** (the container substitution
law at the frame, `frameCrest_read`, over the recorded reading M2): the
group's constructor `(c, j)`, instantiated at the key and with the whole
applications of the group's members abstracted to their holes, reads at
the frame's depth as the recorded Π-tower substituted by the frame's
variables. -/
theorem crest_readT {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} {iT : Name} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF iT)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp)
        (cv.type.instantiateLevelParams cv.levelParams us) = some crest ∧
      (∃ Tys : List Term, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          instPisWith (canonParams ds.length) (D.formerAt mm cvm).type = some ty ∧
          denote mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab)
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denote mp.base2.acval env φ (hi + grp.length) crest
        = some (mkPisAV (Term.substTele (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0 ab)
            (Term.substAV (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D hi grp ds (hi + grp.length)))
              (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
                (D.resIdx (Level.substFn φ lps us) c j)) ab.length)) := by
  obtain ⟨-, -, -, ⟨-, hrd⟩, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', iT', hf', hcl, hlpsC, -, A, hA, hocc, hread⟩ := hrd c hc j hj
  rw [hfc] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cv = cv' ∧ ds.length = nPc' ∧ nF = nF' := by
    simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf'
    exact ⟨hf'.1, hf'.2.1, hf'.2.2.1⟩
  have hlp : cv.levelParams = lps := by
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC c hc
    obtain ⟨cvm', capsm', hfm', hlm'⟩ := hlps c hc
    rw [hfm] at hfm'
    obtain ⟨rfl, rfl⟩ : cvm = cvm' ∧ capsm = capsm' := by simpa using hfm'
    rw [← hlm, hlm']
  refine ⟨hlp, ?_⟩
  obtain ⟨-, -, ab, Tys, hab, hlab, hlT, hTys, hEqF⟩ := hread (Level.substFn φ lps us)
  have hk : D.names.length = D.k := hkN
  obtain ⟨crest, hcr, hcrd⟩ := frameCrest_read mp.base2 (φ := φ) (names := D.names)
    (gnames := grp.map (·.1)) (lps := cv.levelParams) (n := ds.length) (us := us) (ds := ds)
    (holes := grpHoles hi grp) (D' := hi + grp.length)
    (s := grpS D hi grp ds) (x := grpX mp.base2 φ D hi grp ds (hi + grp.length))
    (by rw [hlp]; exact hnd) (by rw [hlp]; exact hul) rfl hgT.2.1
    (fun i hi' => by
      show grpS D hi grp ds i = _
      unfold grpS; rw [ite_eq_left hi'])
    (fun mm hmm => by
      show grpS D hi grp ds (ds.length + mm) = _
      unfold grpS
      rw [ite_eq_right (by omega), show ds.length + mm - ds.length = mm by omega]
      rfl)
    (by simp [grpHoles])
    (fun i hi' => grpS_readT mp hD hkN hlps hnd hul hds hdsa hlenP hgT i (by omega))
    hcl hocc hA (by rw [hk, hlp]; exact hab)
  rw [hk] at hcrd
  exact ⟨crest, ab, hcr, ⟨Tys, hlT, hTys, hEqF⟩, hlab, hcrd⟩

omit hnN hkN in
/-- **A frame constructor's type is framed and its leaves are in the
frame's context**: the key's parameters' leaves (below the key's depth,
where the enclosing context holds them) and the group's holes (typed by
their members' formers at the key, the new entries). -/
theorem crest_frameT {Δh : List Term} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkey : ∀ ρ, Sat V Δh ρ →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      ∀ a ∈ dsa, WellDenoted V ρ a)
    {e crest : Expr} (hcl : e.hasFvar = false) (hbb : e.looseBVarsBounded 0 = true)
    (hcr : ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp) e = some crest) :
    Frame (hi + grp.length) crest ∧
    CtxOkP mp.base2 φ (hi + grp.length) ((grpTys mp.base2 φ hi grp).reverse ++ Δh) crest := by
  have hhl : (grp.map (·.1)).length ≤ (grpHoles hi grp).length := by simp [grpHoles]
  -- the leaves
  have hleaves : ∀ l ∈ crest.fvarLeaves, (∃ x ∈ ds, l ∈ x.fvarLeaves) ∨
      ∃ i, ∃ hi' : i < grp.length, l = (hi + i, grp[i].2) := by
    intro l hl
    obtain ⟨a, ha, hla⟩ := ConLeche.fvarLeaves_nestCrest hcl hhl hcr l hl
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl ⟨a, ha, hla⟩
    · obtain ⟨i, hi', rfl⟩ := ConLeche.grpHoles_hole ha
      simp only [Expr.fvarLeaves, List.mem_cons] at hla
      rcases hla with rfl | hla
      · exact Or.inr ⟨i, hi', rfl⟩
      · exact Or.inl ((grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT
          (List.getElem_mem hi')).2.2.1 l hla)
  have hsc : ConLeche.ScB (hi + grp.length) crest := by
    refine ConLeche.ScB.of_nestCrest ⟨Expr.WScoped.of_not_hasFvar hcl, hbb⟩ hhl
      (fun x hx => ?_) hcr
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨Expr.WScoped.mono (by omega) (hds x hx).1, (hds x hx).2⟩
    · obtain ⟨i, hi', rfl⟩ := ConLeche.grpHoles_hole hx
      obtain ⟨hw, hb, -⟩ := grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT
        (List.getElem_mem hi')
      exact ConLeche.ScB.fvar (by omega) ⟨Expr.WScoped.mono (by omega) hw, hb⟩
  refine ⟨⟨hsc.1, hsc.2, ?_⟩, ?_⟩
  · -- leaves bounded
    intro l hl
    rcases hleaves l hl with ⟨x, hx, hlx⟩ | ⟨i, hi', rfl⟩
    · exact hLds x hx l hlx
    · exact (grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT (List.getElem_mem hi')).2.1
  · -- the context discipline
    refine CtxOkP.extend (by simp [grpTys]) hΔ fun l hl => ?_
    rcases hleaves l hl with ⟨x, hx, hlx⟩ | ⟨i, hi', rfl⟩
    · exact Or.inl ((hCds x hx).2 l hlx)
    · obtain ⟨hw, -, -, mm, cv, caps, -, -, -, abF, -, -, -, hta⟩ :=
        grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT (List.getElem_mem hi')
      have hread : denote mp.base2.acval env φ (hi + i) grp[i].2
          = some ((mkPisAV (Term.substTele (substTau ds.length hi fun i => dsa.getD i default)
              0 (abF.drop ds.length)) (.sort (D.w (Level.substFn φ lps us)))).liftN i 0) := by
        rw [denote_lift mp.base2.acval_closed hw _ (by omega), hta, Option.map_some,
          show hi + i - hi = i by omega]
      refine Or.inr ⟨i, hi', rfl, Expr.WScoped.mono (by omega) hw, _, hread, ?_, fun σ hσ => ?_⟩
      · rw [List.getElem?_reverse (by simp [grpTys]; omega)]
        simp only [grpTys, List.length_mapIdx]
        rw [show grp.length - 1 - (grp.length - 1 - i) = i by omega, List.getElem?_mapIdx,
          List.getElem?_eq_getElem hi', Option.map_some, hread, Option.getD_some]
      · -- graded: the prefix context below the hole
        have hs' : Sat V Δh (fun j => σ (j + i)) := by
          have h1 := Sat_drop hσ i
          rwa [List.drop_drop, List.drop_left' (by simp [grpTys]; omega)] at h1
        refine ⟨?_, by rw [interp_liftN]; exact IsTy_mkPisAV_sort _ _ _⟩
        rw [WellDenoted_liftN, show shiftE i 0 σ = fun j => σ (j + i) by funext j; simp [shiftE]]
        obtain ⟨hk1, hk2⟩ := hkey _ hs'
        exact grp_typeT_wd mp hD hlps hnd hul hds hdsa hlenP hgT (List.getElem_mem hi') hta _
          hk1 hk2

end FrameT

/-- **The hole frame's hole values satisfy the recorded reading's hole
context**: the parameters at the key frame, then each member's hole value
in its canonical hole type (`canonHoleTy_read`, `LfpDatum.holeVal_mem`). -/
theorem frameVals_sat (mp : EnvModelM V env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    {nPc : Nat} (hnP : (D.params ψ).length = nPc) {Tys : List Term} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      instPisWith (canonParams nPc) (D.formerAt mm cvm).type = some ty ∧
      denote mp.base2.acval env ψ (nPc + mm) ty = some (Tys.getD mm default))
    (X : Nat → V) (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) :
    Sat V (D.params ψ ++ Tys).reverse (D.frame ψ ρp X) := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  rw [List.reverse_append]
  unfold LfpDatum.frame
  refine sat_of_spineFit hs ?_
  have := spineFit_of_lifted Tys ((List.range D.k).map (D.holeVal ψ ρp X)) [] ρp (by simp [hlT])
    fun i hi hi' => by
      have hik : i < D.k := by rw [← hlT]; exact hi
      obtain ⟨cvm, caps, ty, hfm, hty, hrd⟩ := hTys i hik
      obtain ⟨abF, -, -, hmap, hw, hrd0⟩ :=
        canonHoleTy_read mp hD hik hfm ((h.parsLen i hik ψ).trans hnP) hty
      refine ⟨mkPisAV (abF.drop nPc) (.sort (D.w ψ)), ?_, ?_⟩
      · rw [denote_lift mp.base2.acval_closed hw _ (by omega), hrd0, Option.map_some] at hrd
        have e := Option.some.inj hrd
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at e
        rw [← e, List.length_nil, Nat.zero_add, show nPc + i - nPc = i by omega]
      · simp only [List.getElem_map, List.getElem_range]
        exact LfpDatum.holeVal_mem h.kN hX.toU hik hmap
  simpa using this

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

omit [SetTheory V] hD hnN hkN hfind hlps hnd hul hds hdsa hlenP in
/-- Every constructor a group's walk visits is one of the group's
members' constructors. -/
theorem grpCtors_found
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2 iT))
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors) :
    ∀ x ∈ ctors, ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2 iT) := by
  obtain ⟨hctorsIn, -⟩ := ConLeche.groupCtors_spec hgc
  intro x hx
  obtain ⟨cn, hcn, nP', L, hL, hnP, hxL⟩ := hctorsIn x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcn
  obtain ⟨⟨c, hc, hpc⟩, -⟩ := hg.2.2 p hp
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

omit [SetTheory V] hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
/-- A group member's constructor is one the group's walk visits. -/
theorem grpCtor_found
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2 iT))
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {g j : Nat} (hG : InGrp D grp g) (hj : j < D.nctors g) :
    ∃ x ∈ ctors, ∃ iT, env.find? (D.ctorName g j) = some (.ctorInfo x.1 ds.length x.2 iT) := by
  obtain ⟨-, hctorsAll⟩ := ConLeche.groupCtors_spec hgc
  obtain ⟨nP', L, hL, hlenL, hfL⟩ := hcov g hG.1
  have hjL : j < L.length := by rw [hlenL]; exact hj
  obtain ⟨nP'', L'', hL'', hnP'', hall⟩ :=
    hctorsAll (D.member g) (List.contains_iff_mem.mp hG.2)
  rw [hL] at hL''
  obtain ⟨rfl, rfl⟩ : nP' = nP'' ∧ L = L'' := by simpa using hL''
  refine ⟨L[j], hall _ (List.getElem_mem hjL), ?_⟩
  rcases hnP'' with h' | h'
  · rw [← h']; exact hfL j hjL
  · rw [h'] at hjL; exact absurd hjL (Nat.not_lt_zero _)

/-- A group member's index sets agree at the two key frames. -/
theorem grp_idx_eq {c : Nat} (hc : InGrp D grp c) {ρ ρ' : Nat → V}
    (hag : AgreeOff (holeP hi ctx.nP hi) ρ ρ') :
    D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ) c
      = D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ') c := by
  obtain ⟨hck, hcg⟩ := hc
  obtain ⟨p, hp, hpc⟩ : ∃ p ∈ grp, p.1 = D.member c := by
    simpa using hcg
  obtain ⟨mm, hmm, hpm, -, -, -, -, -, -, -, hte⟩ :=
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
  · rw [ite_eq_left hG, grp_idx_eq mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG hag]
    exact lfpTuple_mem _ _ _ _ c hc
  · rw [ite_eq_right hG]
    exact lfpTuple_mem _ _ _ _ c hc

/-- `GrpWf` gives the group's hole types. -/
theorem grpWf_ty : GrpTy env D us ds grp :=
  ⟨hg.1, hg.2.1, fun p hp => by
    obtain ⟨mm, hmm, hpm, -, cv, caps, hf, hlp, hstrip, hp2, -⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hp
    exact ⟨mm, hmm, hpm, cv, caps, hf, hstrip, by rw [hlp]; exact hp2⟩⟩

/-- **The group's hole values inhabit their context entries** (the
members' formers instantiated at the key, read at the holes' depths). -/
theorem grpVals_fit (ρ X : Nat → V)
    (hX : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) X) :
    SpineFit ρ (grpTys mp.base2 φ hi grp)
      (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) X) := by
  have hgT := grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have := spineFit_of_lifted (grpTys mp.base2 φ hi grp)
    (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) X) [] ρ
    (by simp [grpTys, grpVals]) fun i hi' hi'' => by
      have hi3 : i < grp.length := by simpa [grpTys] using hi'
      obtain ⟨hw, -, -, mm, cv, caps, hmm, hpm, hf, abF, -, -, hmap, hta⟩ :=
        grp_typeT mp hD hlps hnd hul hds hdsa hlenP hgT (List.getElem_mem hi3)
      refine ⟨mkPisAV (Term.substTele (substTau ds.length hi
        fun i => dsa.getD i default) 0 (abF.drop ds.length))
          (.sort (D.w (Level.substFn φ lps us))), ?_, ?_⟩
      · simp only [grpTys, List.getElem_mapIdx, List.length_nil, Nat.zero_add]
        rw [denote_lift mp.base2.acval_closed hw _ (by omega), hta, Option.map_some,
          Option.getD_some, show hi + i - hi = i by omega]
      · simp only [grpVals, List.getElem_map]
        rw [hpm, idxOf_member hnN hkN hmm]
        have heq : mkPisAV (Term.substTele (substTau ds.length hi
            fun i => dsa.getD i default) 0 (abF.drop ds.length))
              (.sort (D.w (Level.substFn φ lps us)))
            = Term.substAV (substTau ds.length hi fun i => dsa.getD i default)
                (mkPisAV (abF.drop ds.length) (.sort (D.w (Level.substFn φ lps us)))) 0 := by
          rw [Term.substAV_mkPisAV]; rfl
        rw [heq, interp_substAV, ← keyFrame_eq_substE (DenoteSpine.length_eq hdsa).symm]
        exact LfpDatum.holeVal_mem h.kN hX.toU hmm hmap
  simpa using this

/-- **The frame relation is a hole relation** of the frame's walk: the
enclosing relation at the key's depth extended by the group's holes
(their context entries the members' formers instantiated at the key,
their values inhabiting them; the new holes grow because their values
are the SAME at the two sides — the index sets read alike at the two key
frames, N2, and the smaller side's tuple is the larger carrier on the
group). -/
theorem frameRel_holeRel {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRel mp.base2 φ ctx prog hi Δh R₀) :
    HoleRel mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ hi grp).reverse ++ Δh)
      (frameRel R₀ D (Level.substFn φ lps us) grp dsa hi) := by
  subst hhi
  have hlenN : (grpNews us ds (ctx.hiAt prog.length) grp).length = grp.length := by
    simp [grpNews]
  have hext := HoleRel.extend hR₀ (grpNews us ds (ctx.hiAt prog.length) grp)
    (fun x hx a ha => by
      simp only [grpNews, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      exact (hds a ha).1)
    (grpTys mp.base2 φ (ctx.hiAt prog.length) grp).reverse
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
    intro ρ ρ' hr
    obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
    exact ⟨sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _
        (grpTuple_mem mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (hR₀.agree ρ ρ' hr))),
      sat_of_spineFit h2 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg _ _
        (lfpTuple_mem _ _ _ _))⟩
  · -- the new holes grow: their values are the same at both sides
    intro ρ ρ' hr p hk hkp hp is _
    have hp' : p < grp.length := by simpa [grpNews] using hp
    have hpi : grp[p] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, hpm, hidx, -, -, -, -, -, -, hte⟩ :=
      grpMember mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hpi
    have hG : InGrp D grp mm := ⟨hmm, by
      rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hpi, hpm⟩⟩
    simp only [grpVals, List.getElem_map, hidx]
    have hY : grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa (ctx.hiAt prog.length) ρ)
        (keyFrame dsa (ctx.hiAt prog.length) ρ') mm
        = D.carrier (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ') mm := by
      unfold grpTuple; rw [ite_eq_left hG]
    unfold LfpDatum.holeVal
    rw [hY, (hte ρ ρ' (hR₀.agree ρ ρ' hr)).holeFam]
    exact Subset.refl _

/-- The frame's substituted variables are scoped, bvar-closed and read. -/
theorem grpS_read (q : Nat) (hq : q < ds.length + D.k) :
    Expr.WScoped (hi + grp.length) (grpS D hi grp ds q) ∧
    (grpS D hi grp ds q).looseBVarsBounded 0 = true ∧
    denote mp.base2.acval env φ (hi + grp.length) (grpS D hi grp ds q)
      = some (grpX mp.base2 φ D hi grp ds (hi + grp.length) q) :=
  grpS_readT mp hD hkN hlps hnd hul hds hdsa hlenP
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) q hq

/-- **The substituted valuation of a frame walk valuation IS the recorded
block's hole frame** at the key frame. -/
theorem substE_grp (Y ρ : Nat → V) :
    substE V (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0
        (consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y) ρ)
      = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y :=
  substE_grpT mp hD hnN hkN hlps hnd hul hds hdsa hlenP
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) Y ρ

/-- **A frame constructor's type, read** (`crest_readT` at a walked
group). -/
theorem crest_read {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} {iT : Name} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF iT)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp)
        (cv.type.instantiateLevelParams cv.levelParams us) = some crest ∧
      (∃ Tys : List Term, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          instPisWith (canonParams ds.length) (D.formerAt mm cvm).type = some ty ∧
          denote mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab)
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denote mp.base2.acval env φ (hi + grp.length) crest
        = some (mkPisAV (Term.substTele (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D hi grp ds (hi + grp.length))) 0 ab)
            (Term.substAV (substTau (ds.length + D.k) (hi + grp.length)
              (grpX mp.base2 φ D hi grp ds (hi + grp.length)))
              (Term.mkAppN (.bvar (nF + (D.k - 1 - c)))
                (D.resIdx (Level.substFn φ lps us) c j)) ab.length)) :=
  crest_readT mp hD hkN hlps hnd hul hds hdsa hlenP
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) hc hj hfc

/-- **A frame constructor's type is framed and its leaves are in the
frame's context** (`crest_frameT` at a walked group). -/
theorem crest_frame {Δh : List Term} (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkey : ∀ ρ, Sat V Δh ρ →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      ∀ a ∈ dsa, WellDenoted V ρ a)
    {e crest : Expr} (hcl : e.hasFvar = false) (hbb : e.looseBVarsBounded 0 = true)
    (hcr : ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp) e = some crest) :
    Frame (hi + grp.length) crest ∧
    CtxOkP mp.base2 φ (hi + grp.length) ((grpTys mp.base2 φ hi grp).reverse ++ Δh) crest :=
  crest_frameT mp hD hlps hnd hul hds hdsa hlenP
    (grpWf_ty mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg) hΔ hCds hLds hkey hcl hbb hcr

/-- **A frame's final walk grows its group's carriers**: the constructors
of the group, instantiated at the key and walked along the frame
relation, make every member of the group grow between the two key
frames of each related pair — by `carrier_le_on_group'`, whose walk
premise is the per-constructor transfer at the frame relation. -/
theorem frameIter (hin : RulesInputs V mp.base2 φ) {F : Nat}
    (hcov : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
      L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
        ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2 iT))
    {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi) {Δh : List Term}
    {R₀ : FrameRel V} (hR₀ : HoleRel mp.base2 φ ctx prog hi Δh R₀) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkey : ∀ ρ, Sat V Δh ρ →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      ∀ a ∈ dsa, WellDenoted V ρ a)
    {ctors : List (ConstantVal × Nat)}
    (hgc : ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hwalk : ∀ {Δ : List Term} {R : FrameRel V},
      HoleRel mp.base2 φ ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length) Δ R →
      ∀ (Q : ConstantVal × Nat → Prop),
      (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
        ConLeche.nestCrest (grp.map (·.1)) us ds (grpHoles hi grp)
          (x.1.type.instantiateLevelParams x.1.levelParams us) = some crest →
        (∃ ty u, ConLeche.inferTypeCore .verified false env F (hi + grp.length) crest = .ok ty ∧
          ConLeche.ensureSortCore .verified false env F (hi + grp.length) ty = .ok u) →
        ∃ ca, Frame (hi + grp.length) crest ∧ CtxOkP mp.base2 φ (hi + grp.length) Δ crest ∧
          denote mp.base2.acval env φ (hi + grp.length) crest = some ca ∧ GradedTy V Δ ca) →
      (∀ x ∈ ctors, Q x) →
      ∀ x ∈ ctors, CtorWalked mp.base2 φ ctx (hi + grp.length) us ds (grp.map (·.1))
        (grpHoles hi grp) R x) :
    (∀ ρ ρ', R₀ ρ ρ' → ∀ c, InGrp D grp c →
      FamLe (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ) c)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ') c)) ∧
      -- the per-constructor HOLE-FIT transfer the carriers' growth is built
      -- from (`ctor_transfer` along the frame relation), exported
      ∀ ρ ρ', R₀ ρ ρ' → ∀ g, InGrp D grp g → ∀ t j fs,
        D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
          (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ'))
          t g j fs →
        D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ')
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) t g j fs := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hQ := grpCtors_found hg hcov hgc
  have hfit : ∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ') := fun ρ ρ' hr =>
    ⟨(hkey ρ (hR₀.dom ρ ρ' hr).1).1, (hkey ρ' (hR₀.dom ρ ρ' hr).2).1⟩
  -- the frame relation, and the walk along it
  have hR' := frameRel_holeRel mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hhi hR₀
  have hw := hwalk hR'
    (fun x => ∃ c j, InGrp D grp c ∧ j < D.nctors c ∧
      ∃ iT, env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2 iT))
    (fun x crest hQx hcr hinf => by
      obtain ⟨c, j, ⟨hc, -⟩, hj, _, hfc⟩ := hQx
      have hwf := mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfc)
      have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
      have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0
          = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
      obtain ⟨hfr, hC⟩ := crest_frame mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hΔ hCds
        hLds hkey hcl hbb hcr
      obtain ⟨-, crest', ab, hcr', -, -, hrd⟩ :=
        crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hc hj hfc
      rw [hcr] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨ty, u, hty, hsort⟩ := hinf
      exact ⟨_, hfr, hC, hrd, gradedTy_of_sort hin hty hsort hfr hC.toCtxOk hrd⟩)
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
    obtain ⟨x, hxmem, _, hfc⟩ := grpCtor_found hcov hgc hG hj
    obtain ⟨-, crest, ca, cur, hcr, hca, hres, hidx, hpos⟩ := hw _ hxmem
    obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
      crest_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hG.1 hj hfc
    rw [hcr] at hcr'
    obtain rfl := Option.some.inj hcr'
    rw [hca] at hrd
    obtain rfl := Option.some.inj hrd
    -- the substituted result head is the member's hole
    have hhead : ∃ p, ((substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D hi grp ds (hi + grp.length))) (D.k - 1 - g)).liftN x.2 0
          = .bvar p := by
      have hgk := hG.1
      simp only [substTau, ite_eq_left (show D.k - 1 - g < ds.length + D.k by omega)]
      rw [show ds.length + D.k - 1 - (D.k - 1 - g) = ds.length + g by omega]
      have hr := (grpS_read mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg (ds.length + g)
        (by omega)).2.2
      unfold grpS at hr
      rw [ite_eq_right (by omega), show ds.length + g - ds.length = g by omega] at hr
      obtain ⟨i, hi', -, hidx', hget⟩ := grpHoles_member (hi := hi) hg.2.1 hkN hgk
      rw [hidx', hget, denote_fvar] at hr
      rw [← Option.some.inj hr]
      exact ⟨hi + grp.length - 1 - (hi + i) + x.2, by simp⟩
    obtain ⟨p, hp⟩ := hhead
    have hS := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
      (grpTuple D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) (keyFrame dsa hi ρ')) ρ
    have hLv := substE_grp mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) ρ'
    have hsatS := frameVals_sat mp hD hs hlenP hlT hTys _
      (grpTuple_mem mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hag)
    have hsatL := frameVals_sat mp hD hs' hlenP hlT hTys
      (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ')) (lfpTuple_mem _ _ _ _)
    exact ctor_transfer hEqF hlen hp hpos hres hidx ⟨ρ, ρ', hr, rfl, rfl⟩ hS hLv hsatS hsatL t fs hf
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
theorem ctor_lps (mp : EnvModelM V env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal} {nPc nF : Nat} {iT : Name}
    (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF iT)) : cv.levelParams = lps := by
  obtain ⟨-, -, -, ⟨-, hrd⟩, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', iT', hf', -, hlpsC, -⟩ := hrd c hc j hj
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
