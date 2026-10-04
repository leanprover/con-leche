module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Inductives.ContCtor
import ConLeche.Model.NatEqs
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Inductives.HoleBack
import ConLeche.Verify.Inductives.ReplaceApps
import ConLeche.Verify.SubstFvars
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Model.Annot.BitLevels
import ConLeche.Verify.Inductives.ClassGenScope

public section

/-!
# An INSTANTIATED container constructor, read

A recursor whose major is an outside container `C us ds` (an auxiliary
recursor of a nested block) has one minor premise per constructor of
`C`'s component, its fields the constructor's type INSTANTIATED at the
major's levels `us` and parameters `ds` — every member of `C`'s block
stays applied, `D.member mm .{us} ds`, read by its leaf.

That type IS the recorded canonical abstraction (`LfpCtorReads`' `A`) at
the levels `us` with the canonical parameters substituted by `ds` and each
canonical hole filled back with its member's whole application
(`Expr.replaceApps_canon_fill`), one parallel substitution
(`Expr.substFvars`, read by `denoteMeta_substFvars`): `instCtor_read`.
The member applications, read, ARE the carrier's hole values
(`former_app_eq`), so the substituted valuation is the carrier's hole
frame (`instTau_frame`), and a spine fits the instantiated constructor's
fields exactly when it hole-fits the recorded constructor at the key frame
and the carrier (`instCtor_fit`, `instCtor_decode`).  This is what the
recursor's rule data read at an outside class: the decoding fit of a
container constructor is the clause's own `HFits` at the parameters'
readings.
-/

namespace ConLeche.Expr

theorem replaceFVars_mkAppN (g : Nat → Option Expr) :
    ∀ (as : List Expr) (f : Expr),
      (Expr.mkAppN f as).replaceFVars g = Expr.mkAppN (f.replaceFVars g) (as.map (·.replaceFVars g))
  | [], _ => rfl
  | a :: as, f => replaceFVars_mkAppN g as (.app f a)

/-- **Filling the canonical holes back** with the members' whole
applications at the parameters' images: on a term whose variables are the
canonical parameters, abstracting the members' applications to the
canonical holes and then replacing each hole by its member applied to
`ds` (and each parameter by its image in `ds`) is replacing the
parameters. -/
theorem replaceApps_canon_fill {names : List Name} {us : List Level} {n : Nat}
    {g : Nat → Option Expr} {ds : List Expr} (hdl : ds.length = n)
    (hg : ∀ i, i < n → g i = some (ds.getD i default))
    (hh : ∀ m, m < names.length →
      g (n + m) = some (Expr.mkAppN (.const (names.getD m .anonymous) us) ds)) :
    ∀ t : Expr, t.fvarsBelow n →
      (t.replaceApps (ConLeche.nestCanonSub names us n) 0 n).replaceFVars g
        = t.replaceFVars g := by
  have hhit : ∀ (e h : Expr), e.appHole? (ConLeche.nestCanonSub names us n) 0 n = some h →
      h.replaceFVars g = e.replaceFVars g := by
    intro e h hh'
    unfold appHole? at hh'
    cases hp : e.phApp? 0 n with
    | none => rw [hp] at hh'; exact nomatch hh'
    | some p =>
      rw [hp, Option.bind_some] at hh'
      obtain ⟨m, hm, hmc, hv, rfl⟩ := ConLeche.nestCanonSub_some hh'
      obtain ⟨c, v⟩ := p
      simp only at hmc hv
      subst hv
      obtain ⟨args, rfl, hlen, hvar⟩ := phApp?_spine n hp
      have hc : names.getD m .anonymous = c := by
        rw [List.getD_eq_getElem?_getD, hmc, Option.getD_some]
      rw [replaceFVars_mkAppN]
      simp only [replaceFVars, hh m hm, Option.getD_some, hc]
      congr 1
      apply List.ext_getElem (by simp [hlen, hdl])
      intro q h1 h2
      rw [List.getElem_map]
      have h1' : q < args.length := by omega
      obtain ⟨ty, hx⟩ := hvar q (args[q]'h1') (List.getElem?_eq_getElem _)
      rw [hx]
      simp only [replaceFVars, Nat.zero_add, hg q (by omega), Option.getD_some]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  intro t
  induction t with
  | const c v =>
    intro _
    rw [replaceApps_const]
    split
    · rename_i h hh; exact hhit _ _ hh
    · rfl
  | app a x iha ihx =>
    intro hb
    simp only [fvarsBelow] at hb
    rw [replaceApps_app]
    split
    · rename_i h hh; exact hhit _ _ hh
    · simp only [replaceFVars, iha hb.1, ihx hb.2]
  | lam t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihb hb.2]
  | forallE t body m iht ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihb hb.2]
  | letE t v body iht ihv ihb =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, iht hb.1, ihv hb.2.1, ihb hb.2.2]
  | proj s' i x ih =>
    intro hb; simp only [fvarsBelow] at hb
    simp only [replaceApps, replaceFVars, ih hb]
  | fvar i ty _ => intro _; simp only [replaceApps]
  | bvar => intro _; rfl
  | sort => intro _; rfl
  | lit => intro _; rfl

end ConLeche.Expr

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal NestCtx)
open ConLeche.SetTheory.Tower (projS)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- The substituted variables of an instantiated constructor type: the
key's parameters, then each member applied to them. -/
@[expose] def instS (D : LfpDatum V) (us : List Level) (ds : List Expr) : Nat → Expr :=
  fun q => if q < ds.length then ds.getD q default else
    Expr.mkAppN (.const (D.member (q - ds.length)) us) ds

/-- **The instantiated constructor's substitution**: the parameters at
their readings, every member its application's reading (the depth-`hi`
readings of `instS`). -/
@[expose] noncomputable def instTau {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (φ : Name → Nat) (D : LfpDatum V) (us : List Level) (hi : Nat) (ds : List Expr) :
    Nat → AnnotTerm :=
  substTau (ds.length + D.k) hi fun q => (denoteMeta mp.base2.acval env φ hi (instS D us ds q)).getD .prf

section Inst

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)

include hD hnN hkN hlps hnd hul hds hdsa hlenP

omit hD hnN hkN hnd hlenP in
/-- The instantiated constructor's substituted variables are scoped,
bvar-closed and read (a member's application to its leaf applied to the
parameters' readings). -/
theorem instS_read (q : Nat) (hq : q < ds.length + D.k) :
    Expr.WScoped hi (instS D us ds q) ∧ (instS D us ds q).looseBVarsBounded 0 = true ∧
    denoteMeta mp.base2.acval env φ hi (instS D us ds q)
      = some (if q < ds.length then dsa.getD q default else
          AnnotTerm.mkAppN (mp.base2.acval (D.member (q - ds.length)) (Level.substFn φ lps us))
            dsa) := by
  unfold instS
  by_cases hqd : q < ds.length
  · rw [ite_eq_left hqd, ite_eq_left hqd]
    have hmem : ds.getD q default ∈ ds := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqd]; exact List.getElem_mem _
    exact ⟨(hds _ hmem).1, (hds _ hmem).2, DenoteMetaSpine.getD hdsa default q hqd⟩
  · rw [ite_eq_right hqd, ite_eq_right hqd]
    obtain ⟨cv, caps, hf, hlp⟩ := hlps (q - ds.length) (by omega)
    have hsc := ConLeche.ScB.mkAppN (d := hi) (f := .const (D.member (q - ds.length)) us)
      (xs := ds) ⟨by simp [Expr.WScoped], rfl⟩ fun x hx => hds x hx
    refine ⟨hsc.1, hsc.2, ?_⟩
    have hc := denoteMeta_const (acval := mp.base2.acval) (φ := φ) (d := hi) hf
      (by rw [hul, ← hlp]; rfl)
    rw [denoteMeta_mkAppN hdsa hc]
    subst hlp
    rfl

omit hnN hkN in
/-- **An instantiated container constructor, read**: constructor `(c, j)`
of `D`'s component `c`, at the levels `us` and the parameters `ds`
(depth `hi`), is a Π-tower that reads at depth `hi` as the recorded one
substituted by `instTau`; its recorded fields agree with the record's
under the parameters and the members' canonical hole types. -/
theorem instCtor_read {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    {nF : Nat} (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF)) :
    cv.levelParams = lps ∧ ∃ crest ab,
      ConLeche.instPisWith ds (cv.type.instantiateLevelParams cv.levelParams us) = some crest ∧
      (∃ Tys : List AnnotTerm, Tys.length = D.k ∧
        (∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
          ConLeche.instPisWith (canonParams ds.length) cvm.type = some ty ∧
          denoteMeta mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
            = some (Tys.getD mm default)) ∧
        FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn φ lps us) c j)) ∧ ab.length = nF ∧
      denoteMeta mp.base2.acval env φ hi crest
        = some (mkPisAV (AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab)
            (AnnotTerm.substAV (instTau mp φ D us hi ds)
              (AnnotTerm.mkAppN (.bvar (nF + (D.k - 1 - c)))
                (D.resIdx (Level.substFn φ lps us) c j)) ab.length)) := by
  obtain ⟨-, -, -, hk, hrd⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', hf', hcl, hlpsC, -, A, hA, hocc, hread⟩ := hrd c hc j hj
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
  subst hlp
  obtain ⟨-, -, ab, Tys, hab, hlab, hlT, hTys, hEqF⟩ := hread (Level.substFn φ cv.levelParams us)
  generalize hn : ds.length = n at hA hab hTys hEqF
  have hdl := hn
  -- the recorded abstraction, unfolded
  unfold ConLeche.nestCanonCrest at hA
  obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.mp hA
  have hlv := map_param_subst (lps := cv.levelParams) (us := us) hnd hul
  have ht0w : Expr.WScoped n t0 :=
    ConLeche.wscoped_instPisWith (fun a ha => by
        simp only [ConLeche.nestPhs, List.mem_map, List.mem_range] at ha
        obtain ⟨i, hi', rfl⟩ := ha
        simp only [Expr.WScoped]
        exact ⟨hi', by simp⟩)
      (Expr.WScoped.of_not_hasFvar hcl) ht0
  have htL : ConLeche.instPisWith (ConLeche.nestPhs n)
      (cv.type.instantiateLevelParams cv.levelParams us)
      = some (t0.instantiateLevelParams cv.levelParams us) := by
    have := Expr.instPisWith_instantiateLevelParams cv.levelParams us (ConLeche.nestPhs n)
      (fun a ha => by
        simp only [ConLeche.nestPhs, List.mem_map] at ha
        obtain ⟨i, -, rfl⟩ := ha
        exact ⟨_, _, rfl⟩) ht0
    rwa [Expr.nestPhs_instantiateLevelParams] at this
  have htb : Expr.fvarsBelow n (t0.instantiateLevelParams cv.levelParams us) :=
    Expr.fvarsBelow_instantiateLevelParams' _ _ ht0w.fvarsBelow
  have hAb : Expr.fvarsBelow (n + D.k)
      ((t0.replaceApps (ConLeche.nestCanonSub D.names (cv.levelParams.map .param) n) 0 n)
        |>.instantiateLevelParams cv.levelParams us) := by
    refine Expr.fvarsBelow_instantiateLevelParams' _ _ (Expr.WScoped.fvarsBelow
      (Expr.WScoped_of_leaves _ fun l hl => ?_))
    obtain ⟨i, hi', rfl⟩ := ConLeche.fvarLeaves_nestCanonCrest hcl
      (by unfold ConLeche.nestCanonCrest; rw [ht0]; rfl) l hl
    exact ⟨by omega, by simp [Expr.WScoped]⟩
  -- the images
  have hsR := instS_read mp (D := D) hlps hul hds hdsa (φ := φ)
  have himg : ∀ i, i < n + D.k → (instS D us ds i).looseBVarsBounded 0 = true :=
    fun i hi' => (hsR i (by omega)).2.1
  -- the instantiated type is the substituted canonical abstraction
  have hsub := Expr.substFvars_instPisWith (D := hi) (s := instS D us ds) himg _ htL
  have hphsD : (ConLeche.nestPhs n).map (Expr.substFvars (n + D.k) hi (instS D us ds)) = ds := by
    apply List.ext_getElem (by simp [ConLeche.nestPhs, hn])
    intro i h1 h2
    simp only [ConLeche.nestPhs, List.getElem_map, List.getElem_range] at h1 ⊢
    rw [Expr.substFvars_fvar_lt (by omega)]
    unfold instS
    rw [ite_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  have hcl' : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hcl
  rw [hphsD, substFvars_of_not_hasFvar hcl'] at hsub
  have hfill : Expr.substFvars (n + D.k) hi (instS D us ds)
        (t0.instantiateLevelParams cv.levelParams us)
      = Expr.substFvars (n + D.k) hi (instS D us ds)
        ((t0.replaceApps (ConLeche.nestCanonSub D.names (cv.levelParams.map .param) n) 0 n)
          |>.instantiateLevelParams cv.levelParams us) := by
    rw [Expr.substFvars_eq_replaceFVars _ (Expr.fvarsBelow_mono (by omega) htb),
      Expr.substFvars_eq_replaceFVars _ hAb,
      ← Expr.replaceApps_canon_instantiateLevelParams hlv t0 hocc]
    refine (Expr.replaceApps_canon_fill (names := D.names) hdl (fun i hi' => ?_)
      (fun m hm => ?_) _ htb).symm
    · unfold instS
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    · unfold instS
      rw [ite_eq_left (by omega), ite_eq_right (by omega), show n + m - ds.length = m by omega]
      rfl
  rw [hfill] at hsub
  refine ⟨_, ab, hsub, ⟨Tys, hlT, hTys, hEqF⟩, hlab, ?_⟩
  have h := denoteMeta_substFvars (φ := φ) mp.base2 (b := n + D.k) (D := hi) (s := instS D us ds)
    (x := fun q => (denoteMeta mp.base2.acval env φ hi (instS D us ds q)).getD .prf)
    (fun i hi' => by
      obtain ⟨h1, h2, h3⟩ := hsR i (by omega)
      exact ⟨h1, h2, by rw [h3]; rfl⟩) _ 0 (by rw [Nat.add_zero]; exact hAb)
  rw [Nat.add_zero, Nat.add_zero, denotePInstLevels mp.base2 φ cv.levelParams us,
    hab, Option.map_some,
    AnnotTerm.substAV_mkPisAV, Nat.zero_add] at h
  unfold instTau
  rw [hn]
  exact h

omit hnN hkN hnd in
/-- **The instantiated constructor's substituted valuation IS the
carrier's hole frame** at the key frame, where the key frame satisfies the
parameter telescope: the members' applications, read, are the carrier's
hole values (`former_app_eq`). -/
theorem instTau_frame (ρ : Nat → V)
    (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ)) :
    substE V (instTau mp φ D us hi ds) 0 ρ
      = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ)
          (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) := by
  have hsR := instS_read mp (D := D) hlps hul hds hdsa (φ := φ)
  have hdl : dsa.length = ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  unfold instTau
  rw [substE_substTau]
  unfold LfpDatum.frame
  congr 1
  · -- the member slots
    refine List.map_congr_left fun mm hmm => ?_
    have hmm' : mm < D.k := List.mem_range.mp hmm
    have hr := (hsR (ds.length + mm) (by omega)).2.2
    rw [ite_eq_right (by omega), show ds.length + mm - ds.length = mm by omega] at hr
    rw [hr, Option.getD_some, interp_mkAppN_foldl]
    have hfi : dsa.map (interp V ρ) = frameIdx (D.params (Level.substFn φ lps us)).length
        (keyFrame dsa hi ρ) := by
      unfold keyFrame
      rw [hlenP, ← hdl, ← List.length_map (f := interp V ρ), frameIdx_consList']
    rw [hfi, former_app_eq mp hD hmm' hs]
  · -- the parameter frame
    funext q
    unfold keyFrame
    rw [show consList (List.map (interp V ρ) dsa) (fun j => ρ (j + hi)) q = _ from
      consList_map_apply _ _ q, List.length_map, hdl]
    by_cases hq : q < ds.length
    · rw [ite_eq_left hq, ite_eq_left hq]
      have hr := (hsR (ds.length - 1 - q) (by omega)).2.2
      rw [ite_eq_left (by omega)] at hr
      rw [hr, Option.getD_some]
      have hlt : ds.length - 1 - q < dsa.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt, Option.getD_some, Option.map_some, Option.getD_some]
    · rw [ite_eq_right hq, ite_eq_right hq]

omit hnN hkN hnd in
/-- **The fields of an instantiated container constructor, at the
carrier**: at a valuation whose key frame satisfies the container's
parameter telescope, a spine fits the instantiated constructor's fields
as read exactly when it fits the recorded fields at the carrier's hole
frame; and the recorded result indices read alike at the two. -/
theorem instCtor_fit {c j : Nat} (_hc : c < D.k) (_hj : j < D.nctors c) {nF : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      ConLeche.instPisWith (canonParams ds.length) cvm.type = some ty ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
        = some (Tys.getD mm default))
    (hEq : FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
      (D.fields (Level.substFn φ lps us) c j)) (hlen : ab.length = nF)
    {ρ : Nat → V} (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ)) :
    (∀ fs : List V,
      SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs ↔
        SpineFit (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))
          (D.fields (Level.substFn φ lps us) c j) fs) ∧
    ∀ fs : List V,
      SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs →
      ∀ e ∈ D.resIdx (Level.substFn φ lps us) c j,
        interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)
          = interp V (consList fs (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ)
              (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))) e := by
  have hS := instTau_frame mp hD hlps hul hds hdsa hlenP ρ hs
  have hsat := frameVals_sat mp hD hs hlenP hlT hTys
    (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)) (lfpTuple_mem _ _ _ _)
  have hfit : ∀ fs : List V,
      SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs ↔
        SpineFit (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ)
            (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ)))
          (D.fields (Level.substFn φ lps us) c j) fs := by
    intro fs
    rw [spineFit_substTele, hS]
    exact hEq.spineFit_iff hsat fs
  refine ⟨hfit, fun fs hsp e he => ?_⟩
  have hfl : fs.length = nF := by
    rw [hsp.length_eq, List.length_map, substTele_length, hlen]
  rw [interp_substAV, ← hfl, ← Nat.zero_add fs.length, substE_consList, hS]

omit hnN hkN hnd in
/-- **The decoding of an instantiated container constructor**: a
spine fitting the instantiated constructor's fields (as read,
`instCtor_read`) at a valuation whose key frame satisfies the
container's parameter telescope has result index values fitting the
component's index telescope (`LfpClause.resIdxFit`), so its index tuple
lies in the index set; the spine hole-fits the recorded constructor at
the carrier at that tuple, and the constructor's leaf applied to the
parameters and the spine is the clause's injection. -/
theorem instCtor_decode {c j : Nat} (hc : c < D.k)
    (hj : j < D.nctors c) {nF : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps ty, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      ConLeche.instPisWith (canonParams ds.length) cvm.type = some ty ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) (ds.length + mm) ty
        = some (Tys.getD mm default))
    (hEq : FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
      (D.fields (Level.substFn φ lps us) c j)) (hlen : ab.length = nF)
    {ρ : Nat → V} (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ))
    {fs : List V}
    (hfit : SpineFit ρ ((AnnotTerm.substTele (instTau mp φ D us hi ds) 0 ab).map (·.2.2)) fs) :
    SpineFit (keyFrame dsa hi ρ) (D.ids c (Level.substFn φ lps us))
        ((D.resIdx (Level.substFn φ lps us) c j).map fun e =>
          interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)) ∧
      D.HFits (Level.substFn φ lps us) (keyFrame dsa hi ρ)
        (D.carrier (Level.substFn φ lps us) (keyFrame dsa hi ρ))
        (tupW (D.u c (Level.substFn φ lps us))
          ((D.resIdx (Level.substFn φ lps us) c j).map fun e =>
            interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)))
        c j fs ∧
      (dsa.map (interp V ρ) ++ fs).foldl app
          (interp V ρ (mp.base2.acval (D.ctorName c j) (Level.substFn φ lps us)))
        = D.inj (Level.substFn φ lps us) c j fs := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  have hcN : c < D.N := Nat.lt_of_lt_of_le hc h.kN
  obtain ⟨hF, hI⟩ := instCtor_fit mp hD hlps hul hds hdsa hlenP hc hj hlT hTys hEq hlen hs
  have hI' := hI fs hfit
  generalize hψ : Level.substFn φ lps us = ψ at hs hlenP hF hI' ⊢
  have hfC := (hF fs).mp hfit
  -- the index values, read at the carrier's frame
  have hmapEq : (D.resIdx ψ c j).map (fun e =>
        interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF))
      = (D.resIdx ψ c j).map (interp V (consList fs
          (D.frame ψ (keyFrame dsa hi ρ) (D.carrier ψ (keyFrame dsa hi ρ))))) :=
    List.map_congr_left fun e he => hI' e he
  have hidx : SpineFit (keyFrame dsa hi ρ) (D.ids c ψ)
      ((D.resIdx ψ c j).map fun e =>
        interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF)) := by
    rw [hmapEq, ← hψ]; rw [← hψ] at hs hfC; exact h.resIdxFit _ _ hs c hcN j hj fs hfC
  have hIk := h.idxOk ψ _ hs c hcN
  have hlenI := hidx.length_eq
  have hHF : D.HFits ψ (keyFrame dsa hi ρ) (D.carrier ψ (keyFrame dsa hi ρ))
      (tupW (D.u c ψ) ((D.resIdx ψ c j).map fun e =>
        interp V (consList fs ρ) (AnnotTerm.substAV (instTau mp φ D us hi ds) e nF))) c j fs := by
    refine ⟨hj, hfC, fun l hl => ?_⟩
    have hlr : l < (D.resIdx ψ c j).length := by
      rw [List.length_map] at hlenI; omega
    refine ⟨(D.resIdx ψ c j)[l], List.getElem?_eq_getElem hlr, ?_⟩
    rw [projS_tupW hIk hidx hl, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hlr, Option.map_some, Option.getD_some,
      hI' _ (List.getElem_mem hlr)]
  refine ⟨hidx, hHF, ?_⟩
  -- the constructor's leaf at the parameters and the spine
  have hdl : (dsa.map (interp V ρ)).length = (D.params ψ).length := by
    rw [List.length_map, ← DenoteMetaSpine.length_eq hdsa, hlenP]
  have hsa : SpineFit (fun j => ρ (j + hi)) (D.params ψ) (dsa.map (interp V ρ)) :=
    spineFit_of_sat_consList hdl hs
  have := h.ctor c hcN j ψ (fun j => ρ (j + hi)) (dsa.map (interp V ρ)) fs _ hsa
    (tupW_mem hidx) hHF
  rw [acval_interp_closed mp.base2 _ _ ρ (fun j => ρ (j + hi))]
  exact this

end Inst

end ConLeche.Model
