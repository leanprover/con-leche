module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.HoleSubst
import ConLeche.Model.IndSubst
public import ConLeche.Kernel.Inductives.RecCheck

public section

/-!
# The (D) typing's field, read at the separated tuple (lane NESTIND, session 15, item 2)

Ruling (D) types every call at an OUTSIDE major a second time with the
family's classes abstracted (`targetClassCallsOk`): the call's field's
type is the container's STORED constructor with its own group replaced
by holes (`replaceConsts`, the positivity walk's frame substitution
`grpSub`), instantiated at the major's ancestor-abstracted parameters and
read at the rule's field variables (`targetPiDomsWith`).  The class
induction (`NestedClassIndOwed`) reads the field VALUE of a decoding —
a hole fit of the container's recorded clause at a frame and a hole
tuple — in that type: this file is the bridge.

* syntax: `targetPiDomsWith` is `instPisAt`'s domain list; the (D)
  substitution is the walk's `grpSub`; the member abstraction commutes
  with the instantiations;
* `instPisAt_fvars_mem`: an `instPisAt` peel at variables reads each
  domain as the Π-tower's entry at the earlier values — a spine fitting
  the tower's telescope lies in the peeled domains;
* `grpCtor_fit`: the constructor so abstracted and instantiated reads as
  the recorded fields at the clause's hole frame (`crest_readT`,
  `substE_grpT`, M2's `FieldsEqOn`) when every member of the container's
  block is in the group — the (D) group is the whole recorded block.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal instPisWith)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Syntax -/

omit [SetTheory V] in
/-- `targetPiDomsWith` is the domain list of `instPisAt`. -/
theorem targetPiDomsWith_eq :
    ∀ (xs : List Expr) (e : Expr),
      ConLeche.targetPiDomsWith xs e = (Expr.instPisAt xs e).map Prod.fst
  | [], _ => rfl
  | _ :: _, .bvar _ | _ :: _, .fvar _ _ | _ :: _, .sort _ | _ :: _, .const _ _
  | _ :: _, .app _ _ | _ :: _, .lam _ _ _ | _ :: _, .letE _ _ _ | _ :: _, .lit _
  | _ :: _, .proj _ _ _ => rfl
  | x :: xs, .forallE d b _ => by
    simp only [ConLeche.targetPiDomsWith, Expr.instPisAt, targetPiDomsWith_eq xs]
    cases Expr.instPisAt xs (b.instantiate1 x) <;> rfl

/-! ## One instantiation as a parallel substitution -/

/-- The substitution of `AnnotTerm.inst x`: `x` at the cut, the rest one
lower. -/
@[expose] def tau1 (x : AnnotTerm) : Nat → AnnotTerm
  | 0 => x
  | j + 1 => .bvar j

omit [SetTheory V] in
theorem inst_eq_substAV (x : AnnotTerm) :
    ∀ (e : AnnotTerm) (k : Nat), e.inst x k = AnnotTerm.substAV (tau1 x) e k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    by_cases h : i < k
    · rw [AnnotTerm.substAV_bvar_lt _ h]; simp [AnnotTerm.inst, h]
    · rw [AnnotTerm.substAV_bvar_ge _ (by omega)]
      by_cases he : i = k
      · subst he; simp [AnnotTerm.inst, tau1]
      · obtain ⟨j, hj⟩ : ∃ j, i - k = j + 1 := ⟨i - k - 1, by omega⟩
        simp only [AnnotTerm.inst, h, he, if_false, hj, tau1, AnnotTerm.liftN]
        rw [if_neg (by omega)]
        congr 1; omega
  | sort u => intro k; rfl
  | const c us => intro k; rfl
  | prf => intro k; rfl
  | app f a ihf iha => intro k; simp only [AnnotTerm.inst, ihf, iha]; rfl
  | lam u A b ihA ihb => intro k; simp only [AnnotTerm.inst, ihA, ihb]; rfl
  | pi u v A B ihA ihB => intro k; simp only [AnnotTerm.inst, ihA, ihB]; rfl
  | eqE a b iha ihb => intro k; simp only [AnnotTerm.inst, iha, ihb]; rfl
  | fst e ihe => intro k; simp only [AnnotTerm.inst, ihe]; rfl
  | snd e ihe => intro k; simp only [AnnotTerm.inst, ihe]; rfl

theorem substE_tau1 (x : AnnotTerm) (ρ : Nat → V) :
    substE V (tau1 x) 0 ρ = cons (interp V ρ x) ρ := by
  funext i
  cases i with
  | zero => simp [substE, tau1, shiftE_zero]
  | succ j => simp [substE, tau1, interp_bvar, shiftE_zero]

/-! ## An `instPisAt` peel at variables -/

set_option maxHeartbeats 1600000 in
/-- **An `instPisAt` peel reads each domain as the tower's entry at the
earlier values**: if `ty` reads as `mkPisAV tele R` and the spine's
elements read to the values `fs` (at the valuation `ρ`), a spine `fs`
fitting the telescope lies in the peeled domains, entry by entry. -/
theorem instPisAt_fvars_mem {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {doms : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (doms, rs) →
      ∀ {Dp : Nat} {tele : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm},
      (∀ x ∈ sp, Expr.WScoped Dp x ∧ x.looseBVarsBounded 0 = true) →
      Expr.WScoped Dp ty →
      denoteMeta acval env φ Dp ty = some (mkPisAV tele R) → sp.length ≤ tele.length →
      ∀ (ρ : Nat → V) (fs : List V), SpineFit ρ (tele.map (·.2.2)) fs →
      (∀ q x, sp[q]? = some x → ∃ a, denoteMeta acval env φ Dp x = some a ∧
        interp V ρ a = fs.getD q pt) →
      ∀ q A, q < sp.length → denoteMeta acval env φ Dp (doms.getD q default) = some A →
        fs.getD q pt ∈ˢ interp V ρ A := by
  intro sp
  induction sp with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q _ hq; exact absurd hq (by simp)
  | cons a sp ih =>
    intro ty doms rs h Dp tele R hsp hw hT hlen ρ fs hfit hvals q A hq hA
    match ty, h, hw, hT with
    | .forallE dom body mb, h, hw, hT =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hdw, hbw⟩ : Expr.WScoped Dp dom ∧ Expr.WScoped Dp body := by
        simpa [Expr.WScoped] using hw
      obtain ⟨ta, ba, hta, hba, hpi⟩ := denoteMeta_forallE_inv hT
      -- the telescope's head
      match tele, fs, hfit, hlen with
      | [], _, _, hlen => exact absurd hlen (by simp)
      | _ :: _, [], hfit, _ => exact hfit.elim
      | t0 :: tele', f0 :: fs', hfit, hlen =>
        simp only [mkPisAV, AnnotTerm.pi.injEq] at hpi
        obtain ⟨-, -, rfl, rfl⟩ := hpi
        obtain ⟨hf0, hfit'⟩ := hfit
        obtain ⟨xa, hxa, hxv⟩ := hvals 0 a rfl
        simp only [List.getD_cons_zero] at hxv
        cases q with
        | zero =>
          simp only [List.getD_cons_zero] at hA ⊢
          rw [hta] at hA
          obtain rfl := Option.some.inj hA
          exact hf0
        | succ q =>
          simp only [List.getD_cons_succ] at hA ⊢
          obtain ⟨hwa, hbwa⟩ := hsp a List.mem_cons_self
          -- the body at the head's value
          have hbody : denoteMeta acval env φ Dp (body.instantiate1 a)
              = some (mkPisAV (AnnotTerm.substTele (tau1 xa) 0 tele')
                  (AnnotTerm.substAV (tau1 xa) R (0 + tele'.length))) := by
            rw [denoteMeta_beta hacl hainst (ty := dom) hbw.fvarsBelow hwa hbwa hxa 0, hba]
            simp only [Option.map_some, inst_eq_substAV, AnnotTerm.substAV_mkPisAV]
          have hfitT : SpineFit ρ ((AnnotTerm.substTele (tau1 xa) 0 tele').map (·.2.2)) fs' := by
            rw [spineFit_substTele, substE_tau1, hxv]; exact hfit'
          exact ih h1 (fun x hx => hsp x (List.mem_cons_of_mem _ hx))
            (Expr.WScoped.instantiate1_gen hwa 0 hbw) hbody
            (by rw [AnnotTerm.substTele_length]; simpa using hlen) ρ fs' hfitT
            (fun q' x hx => by
              obtain ⟨a', ha', hv'⟩ := hvals (q' + 1) x (by simpa using hx)
              exact ⟨a', ha', by simpa using hv'⟩)
            q A (by simpa using hq) hA

/-! ## The group-abstracted constructor at a FULL group -/

section Grp

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List AnnotTerm}
  (hdsa : DenoteMetaSpine mp.base2.acval env φ hi ds dsa)
  {grp : List (Name × Expr)} (hgT : GrpTy env D us grp)
  (hfull : ∀ mm, mm < D.k → InGrp D grp mm)

include hD hnN hkN hlps hnd hul hds hdsa hgT hfull

omit hD in
/-- **A full group's substituted valuation is the clause's hole frame**:
every member slot holds its hole value. -/
theorem substE_grp_full (Y ρ : Nat → V) :
    substE V (substTau (ds.length + D.k) (hi + grp.length)
        (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0
        (consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y) ρ)
      = D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y := by
  rw [substE_grpT mp hnN hkN hlps hnd hul hds hdsa hgT]
  unfold LfpDatum.frame
  congr 1
  refine List.map_congr_left fun mm hmm => ?_
  rw [if_pos (by simpa using hfull mm (List.mem_range.mp hmm))]

/-- **The group-abstracted constructor's fields at a full group, read at
the group's hole values, ARE the clause's fields at its hole frame**
(`instCtor_fit`'s twin at the full group, no hole agreement: every member
is a hole): at a key frame satisfying the parameter telescope and a tuple
`Y` of the tuple space, a spine fits the one exactly when it fits the
other. -/
theorem grpCtor_fit {nF : Nat} {c j : Nat}
    {ab : List (Nat × Nat × AnnotTerm)} {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env (Level.substFn φ lps us) 0 cvm.type
        = some (Tys.getD mm default))
    (hEq : FieldsEqOn V (D.params (Level.substFn φ lps us) ++ Tys).reverse (ab.map (·.2.2))
      (D.fields (Level.substFn φ lps us) c j)) (_hlen : ab.length = nF)
    {ρ : Nat → V} (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ))
    {Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)
    (fs : List V) :
    SpineFit (consList (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y) ρ)
        ((AnnotTerm.substTele (substTau (ds.length + D.k) (hi + grp.length)
          (grpX mp.base2 φ D us hi grp ds (hi + grp.length))) 0 ab).map (·.2.2)) fs ↔
      SpineFit (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y)
        (D.fields (Level.substFn φ lps us) c j) fs := by
  rw [spineFit_substTele, substE_grp_full mp hnN hkN hlps hnd hul hds hdsa hgT hfull]
  have hsat := frameVals_sat mp hD hs hlT hTys (fun _ => true) Y hY ρ
  have hsat' : Sat V (D.params (Level.substFn φ lps us) ++ Tys).reverse
      (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y) := by
    simpa [LfpDatum.frame] using hsat
  exact hEq.spineFit_iff hsat' fs


set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE (item 2)**: a decoding's field, read in the
group-abstracted constructor's field type.  The container's constructor
`(c, j)` with its whole block abstracted to the group's holes (`grpSub`)
and instantiated at the key `ds` is peeled at the field variables
`fvsF` (at `B + q`, below the key's depth `hi`) — the (D) typing's field
types `ftys`.  At a valuation whose key frame satisfies the parameter
telescope, whose group slots hold a tuple `Y`'s hole values and whose
field slots hold `fs`, a spine `fs` hole-fitting the recorded
constructor at `(keyFrame, Y)` lies, field by field, in those types. -/
theorem grpField_mem {c j nF B : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal}
    (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF))
    {crest : Expr}
    (hcr : instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us hi grp)) = some crest)
    {fvsF : List Expr} (hfvl : fvsF.length = nF)
    (hfv : ∀ q x, fvsF[q]? = some x → ∃ ty, x = .fvar (B + q) ty ∧ Expr.WScoped (B + q) ty)
    (hB : B + nF ≤ hi)
    {ftys : List Expr} (hft : ConLeche.targetPiDomsWith fvsF crest = some ftys)
    {ρ : Nat → V} (hs : Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa hi ρ))
    {Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn φ lps us)) D.N
      (D.idx (Level.substFn φ lps us) (keyFrame dsa hi ρ)) Y)
    {fs : List V}
    (hfit : SpineFit (D.frame (Level.substFn φ lps us) (keyFrame dsa hi ρ) Y)
      (D.fields (Level.substFn φ lps us) c j) fs)
    (hfsv : ∀ q, q < nF → ρ (hi - 1 - (B + q)) = fs.getD q pt) :
    ∀ q A, q < nF →
      denoteMeta mp.base2.acval env φ (hi + grp.length) (ftys.getD q default) = some A →
      fs.getD q pt ∈ˢ interp V (consList (grpVals D (Level.substFn φ lps us) grp
        (keyFrame dsa hi ρ) Y) ρ) A := by
  have hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (mp.base2.acval n ψ).liftN 1 k = mp.base2.acval n ψ :=
    fun n ψ k => liftN_eq_self_of_closed (mp.base2.cval_closedL n ψ) k 1
  have hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mp.base2.acval n ψ).inst y k = mp.base2.acval n ψ :=
    fun n ψ y k => AVExprSubst.inst_eq_self_of_closed (mp.base2.acval_closed n ψ) y k
  -- the frame constructor's reading (M2 at the group)
  have hcr' := hcr
  obtain ⟨-, crest', ab, hcr0, ⟨Tys, hlT, hTys, hEq⟩, hlab, hread⟩ :=
    crest_readT mp hD hnN hkN hlps hnd hul hds hdsa hgT hc hj hfc
  rw [hcr0] at hcr'
  have hcc : crest' = crest := Option.some.inj hcr'
  rw [hcc] at hread
  -- the spine fits the substituted telescope at the group's valuation
  have hvl : (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y).length
      = grp.length := by simp [grpVals]
  have hfitT := (grpCtor_fit mp hD hnN hkN hlps hnd hul hds hdsa hgT hfull hlT hTys hEq hlab hs
    hY fs).mpr hfit
  -- the peel at the field variables
  have hft' := hft
  rw [targetPiDomsWith_eq] at hft'
  obtain ⟨⟨doms, rs⟩, hpeel, hdoms⟩ := Option.map_eq_some_iff.mp hft'
  obtain rfl : doms = ftys := hdoms
  have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
  have hclE : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hwcr : Expr.WScoped (hi + grp.length) crest := by
    refine ConLeche.wscoped_instPisWith (fun x hx => Expr.WScoped.mono (by omega) (hds x hx).1)
      (ConLeche.WScoped.replaceConsts_closed (fun c us' r hr => ?_) _ hclE) hcr
    obtain ⟨i, hi', rfl⟩ := grpSub_some hr
    obtain ⟨hcl', -⟩ := grp_typeT mp (φ := φ) hnN hkN hlps hgT (List.getElem_mem hi')
    simp only [Expr.WScoped]
    exact ⟨by omega, Expr.WScoped.of_not_hasFvar hcl'⟩
  intro q A hq hA
  refine instPisAt_fvars_mem hacl hainst fvsF hpeel (Dp := hi + grp.length)
    (fun x hx => ?_) hwcr hread (by rw [AnnotTerm.substTele_length, hlab, hfvl]; exact Nat.le_refl _)
    _ fs hfitT (fun q' x hx => ?_) q A (by rw [hfvl]; exact hq) hA
  · obtain ⟨q', hq'⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl, hty⟩ := hfv q' x hq'
    have hq'l : q' < nF := by rw [← hfvl]; exact (List.getElem?_eq_some_iff.mp hq').1
    exact ⟨by simp only [Expr.WScoped]; exact ⟨by omega, hty⟩, rfl⟩
  · obtain ⟨ty, rfl, -⟩ := hfv q' x hx
    have hq'l : q' < nF := by rw [← hfvl]; exact (List.getElem?_eq_some_iff.mp hx).1
    refine ⟨_, denoteMeta_fvar _ _ _ _, ?_⟩
    rw [interp_bvar, show hi + grp.length - 1 - (B + q')
        = (hi - 1 - (B + q')) + (grpVals D (Level.substFn φ lps us) grp (keyFrame dsa hi ρ) Y).length
        by rw [hvl]; omega, consList_apply_add]
    exact hfsv q' hq'l


end Grp

end ConLeche.Model
