module

public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Inductives.HoleSubst
public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Verify.Cached.TargetRecC

public section

/-!
# The flat homes' cycles (PRIMREC, lane FLATHOME)

A family checked off the walk (`targetFlatRouteOf`) calls around a cycle
only inside ONE flat home: outside classes of one recorded block at one
instantiation, each such call typed at the home's HOLES
(`targetIntraCallOk`).  Their completeness — every element of such a
class has a derivation along the calls inside its layer (`Der`,
`TargetRank.lean`) — is the home's own lfp induction
(`lfpTuple_induction`) at the class's frame: the stage tuple is the
carrier separated by "derivable at every class of the layer this
component is", and a call around the cycle lands in it because the
field fits its constructor's hole reading at the stage (the recorded
M2 reading, `crest_readT`) and the call's typing holds at every value
of the holes (`holeCall_gen`).  No walk, no member tie.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode TargetIh TargetFamily)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 1. A Π-tower's domains at existing variables -/

omit [SetTheory V] in
/-- Instantiation under a Π-tower, entry by entry. -/
theorem inst_mkPisAV_entries (a : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (t : Nat),
      (mkPisAV ds B).inst a t
        = mkPisAV ((List.range ds.length).map fun l =>
            ((ds.getD l default).1, (ds.getD l default).2.1, (ds.getD l default).2.2.inst a (t + l)))
          (B.inst a (t + ds.length))
  | [], B, t => rfl
  | d :: ds, B, t => by
    simp only [mkPisAV, AnnotTerm.inst_pi, List.length_cons]
    rw [inst_mkPisAV_entries a ds B (t + 1), List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [mkPisAV, List.getD_cons_zero, Nat.add_zero]
    congr 2
    · refine List.map_congr_left fun l _ => ?_
      simp only [Function.comp, List.getD_cons_succ]
      rw [show t + 1 + l = t + (l + 1) by omega]
    · rw [show t + 1 + ds.length = t + (ds.length + 1) by omega]

/-- A telescope instantiation's leaves are the telescope's or the
arguments'. -/
theorem instPisWith_fvarLeaves :
    ∀ (as : List Expr) (e r : Expr), ConLeche.instPisWith as e = some r →
      ∀ l ∈ r.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves
  | [], e, r, h, l, hl => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; exact Or.inl hl
  | a :: as, e, r, h, l, hl => by
    cases e with
    | forallE dom body bm =>
      simp only [ConLeche.instPisWith] at h
      rcases instPisWith_fvarLeaves as _ r h l hl with h1 | ⟨x, hx, h1⟩
      · rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 h1 with h2 | h2
        · exact Or.inl (by simp [Expr.fvarLeaves, h2])
        · exact Or.inr ⟨a, List.mem_cons_self, h2⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h1⟩
    | _ => simp [ConLeche.instPisWith] at h

/-- A telescope's domains at given arguments: their leaves are the
telescope's or the arguments'. -/
theorem piDomsWith_fvarLeaves :
    ∀ (xs : List Expr) (e : Expr) (doms : List Expr), ConLeche.targetPiDomsWith xs e = some doms →
      ∀ d ∈ doms, ∀ l ∈ d.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ x ∈ xs, l ∈ x.fvarLeaves
  | [], e, doms, h, d, hd, l, hl => by
    simp only [ConLeche.targetPiDomsWith, Option.some.injEq] at h; subst h; exact nomatch hd
  | x :: xs, e, doms, h, d, hd, l, hl => by
    cases e with
    | forallE dom body bm =>
      simp only [ConLeche.targetPiDomsWith] at h
      cases hr : ConLeche.targetPiDomsWith xs (body.instantiate1 x) with
      | none => rw [hr] at h; exact nomatch h
      | some l' =>
        rw [hr] at h
        simp only [Functor.map, Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Or.inl (by simp [Expr.fvarLeaves, hl])
        · rcases piDomsWith_fvarLeaves xs _ l' hr d hd l hl with h1 | ⟨y, hy, h1⟩
          · rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 h1 with h2 | h2
            · exact Or.inl (by simp [Expr.fvarLeaves, h2])
            · exact Or.inr ⟨x, List.mem_cons_self, h2⟩
          · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h1⟩
    | _ => simp [ConLeche.targetPiDomsWith] at h

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

/-- **A Π-tower's domains, instantiated at existing variables, read**: the
`i`-th domain of `e` with its earlier binders instantiated at the free
variables `xs` (below the depth `E`) reads as the tower's `i`-th domain
at the valuation holding the variables' values. -/
theorem piDomsWith_read
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) (E : Nat) :
    ∀ (xs : List Expr) (e : Expr) (ds : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm)
      (doms : List Expr),
      (∀ x ∈ xs, ∃ j ty, x = .fvar j ty ∧ j < E ∧ Expr.WScoped j ty) → xs.length ≤ ds.length →
      Expr.fvarsBelow E e → ConLeche.targetPiDomsWith xs e = some doms →
      denoteMeta acval env φ E e = some (mkPisAV ds B) →
      ∀ i, i < xs.length → ∃ A,
        denoteMeta acval env φ E (doms.getD i default) = some A ∧
        ∀ τ : Nat → V, interp V τ A
          = interp V (consList ((xs.take i).map fun x =>
              interp V τ ((denoteMeta acval env φ E x).getD default)) τ) (ds.getD i default).2.2
  | [], _, _, _, _, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: xs, e, ds, B, doms, hxs, hlen, hfb, hdoms, hrd, i, hi => by
    obtain ⟨j, ty, rfl, hj, hjty⟩ := hxs _ List.mem_cons_self
    cases ds with
    | nil => exact absurd hlen (by simp)
    | cons d ds =>
    cases e with
    | forallE dom body bm =>
      simp only [denoteMeta] at hrd
      cases hA : denoteMeta acval env φ E dom with
      | none => rw [hA] at hrd; exact nomatch hrd
      | some da =>
      cases hB : denoteMeta acval env φ (E + 1) (body.instantiate1 (.fvar E dom)) with
      | none => rw [hA, hB] at hrd; exact nomatch hrd
      | some ba =>
      rw [hA, hB] at hrd
      simp only [mkPisAV] at hrd
      injection hrd with hrd
      injection hrd with h1 h2 hda hba
      simp only [Expr.fvarsBelow] at hfb
      simp only [ConLeche.targetPiDomsWith] at hdoms
      cases hr : ConLeche.targetPiDomsWith xs (body.instantiate1 (.fvar j ty)) with
      | none => rw [hr] at hdoms; exact nomatch hdoms
      | some l =>
      rw [hr] at hdoms
      simp only [Functor.map, Option.map_some, Option.some.injEq] at hdoms
      subst hdoms
      cases i with
      | zero =>
        refine ⟨da, by simp [hA], fun τ => ?_⟩
        simp [hda]
      | succ i =>
        -- the tail: `body` instantiated at the variable
        have hwv : Expr.WScoped E (.fvar j ty) := by
          simp only [Expr.WScoped]; exact ⟨hj, hjty⟩
        have hbeta := denoteMeta_beta (acval := acval) (env := env) (φ := φ) (d := E)
          (ty := dom) hacl hainst hfb.2 hwv (by simp [Expr.looseBVarsBounded])
          (denoteMeta_fvar _ _ _ _) 0
        rw [hB, hba, Option.map_some, inst_mkPisAV_entries] at hbeta
        have hlen' : xs.length ≤ ((List.range ds.length).map fun l =>
            ((ds.getD l default).1, (ds.getD l default).2.1,
              (ds.getD l default).2.2.inst (.bvar (E - 1 - j)) (0 + l))).length := by
          simp at hlen ⊢; omega
        obtain ⟨A, hA', hAi⟩ := piDomsWith_read hacl hainst E xs _ _ _ l
          (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hlen'
          (ConLeche.Expr.fvarsBelow_instantiate1_gen (show Expr.fvarsBelow E (.fvar j ty) from hj)
            0 hfb.2) hr hbeta i (by simpa using hi)
        refine ⟨A, by simpa using hA', fun τ => ?_⟩
        rw [hAi τ]
        have hil : i < ds.length := by simp at hi hlen; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hil,
          Option.map_some, Option.getD_some]
        rw [interp_inst]
        have hvl : ((xs.take i).map fun x =>
            interp V τ ((denoteMeta acval env φ E x).getD default)).length = i := by
          simp only [List.length_map, List.length_take]; simp at hi; omega
        generalize hvs : ((xs.take i).map fun x =>
            interp V τ ((denoteMeta acval env φ E x).getD default)) = vs at hvl ⊢
        have hsh : shiftE (0 + i) 0 (consList vs τ) = τ := by
          rw [Nat.zero_add, ← hvl]; exact shiftE_consList _ _
        have hie : ∀ v : V, instE (0 + i) v (consList vs τ) = consList vs (cons v τ) := by
          intro v
          rw [Nat.zero_add, ← hvl, show vs.length = vs.length + 0 from rfl, instE_consList_add,
            instE_zero]
        rw [hsh, hie]
        simp only [List.take_succ_cons, List.map_cons, consList_cons, denoteMeta_fvar,
          Option.getD_some, interp_bvar, hvs, List.getElem?_cons_succ]
    | _ => simp [ConLeche.targetPiDomsWith] at hdoms

/-! ## 2. A field at the stage lies in its home-abstracted type

The constructor with the home abstracted to its holes BEFORE its
instantiation (`grpSub`, the kernel's `crestH`) reads, past the holes, as
the recorded M2 tower substituted at the class's parameters and the
holes (`crest_readT`); so at the valuation giving each hole its STAGE
value (the hole value of a sub-tuple `Y` of the tuple space), a field
spine fitting the recorded fields with holes at `Y` fits its domains
(`spineFit_substTele`, `FieldsEqOn`), and each field lies in its domain
instantiated at the rule's field variables (`piDomsWith_read`). -/

section Stage

variable {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env) {D : LfpDatum V}

open Classical in
set_option maxHeartbeats 1600000 in
/-- **A field at the stage lies in its home-abstracted type** (see above). -/
theorem stage_fieldMem (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k)
    {lps : List Name}
    (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat}
    {ds : List Expr} (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true)
    {ψ : Name → Nat} {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env ψ hi ds dsa)
    {grp : List (Name × Expr)} (hgT : GrpTy env D us grp) (hgn : grp.map (·.1) = D.names)
    {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c) {cv : ConstantVal} {nF : Nat}
    (hfc : env.find? (D.ctorName c j) = some (.ctorInfo cv ds.length nF))
    {crestH : Expr}
    (hcr : ConLeche.instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (ConLeche.grpSub us hi grp)) = some crestH)
    {fvsF : List Expr} (hfvl : fvsF.length = nF)
    (hfvs : ∀ x ∈ fvsF, ∃ j' ty, x = .fvar j' ty ∧ j' < hi ∧ Expr.WScoped j' ty)
    {doms : List Expr} (hdoms : ConLeche.targetPiDomsWith fvsF crestH = some doms)
    {ρp Y : Nat → V} (hsat : Sat V (D.params (Level.substFn ψ lps us)).reverse ρp)
    (hY : InTupleSpace (D.w (Level.substFn ψ lps us)) D.N (D.idx (Level.substFn ψ lps us) ρp) Y)
    {ρ : Nat → V} (hρp : keyFrame dsa hi ρ = ρp)
    {fs : List V} (hfsl : fs.length = nF)
    (hvals : ∀ l, l < nF → interp V ρ ((denoteMeta mp.base2.acval env ψ hi
      (fvsF.getD l default)).getD default) = fs.getD l pt)
    (hfit : SpineFit (D.frame (Level.substFn ψ lps us) ρp Y) (D.fields (Level.substFn ψ lps us) c j)
      fs) :
    ∀ i, i < nF → ∀ A, denoteMeta mp.base2.acval env ψ (hi + grp.length) (doms.getD i default)
      = some A →
      fs.getD i pt ∈ˢ interp V (consList (grpVals D (Level.substFn ψ lps us) grp ρp Y) ρ) A := by
  intro i hiF A hA
  obtain ⟨-, crest, ab, hcr', ⟨Tys, hlT, hTys, hEq⟩, hlab, hread⟩ :=
    crest_readT mp hD hnN hkN hlps hnd hul hds hdsa hgT hc hj hfc
  have hce : crest = crestH := Option.some.inj (hcr'.symm.trans hcr)
  rw [hce] at hread
  generalize hσ : substTau (ds.length + D.k) (hi + grp.length)
    (grpX mp.base2 ψ D us hi grp ds (hi + grp.length)) = σ at hread
  generalize hτ : consList (grpVals D (Level.substFn ψ lps us) grp ρp Y) ρ = τ
  -- (1) the substituted valuation is the stage's hole frame
  have hin : ∀ mm, mm < D.k → decide (InGrp D grp mm) = true := by
    intro mm hmm
    refine decide_eq_true ⟨hmm, ?_⟩
    rw [hgn, List.contains_iff_mem]
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hsub : substE V σ 0 τ = D.frame (Level.substFn ψ lps us) ρp Y := by
    rw [← hσ, ← hτ, substE_grpT mp hnN hkN hlps hnd hul hds hdsa hgT ρp Y ρ, hρp]
    unfold LfpDatum.frame
    congr 1
    refine List.map_congr_left fun mm hmm => ?_
    rw [if_pos (hin mm (List.mem_range.mp hmm))]
  -- (2) the fields fit the tower's domains at the stage
  have hsat' := frameVals_sat mp hD hsat hlT hTys (fun _ => true) Y hY ρ
  simp only [if_true] at hsat'
  have hfitT : SpineFit τ ((AnnotTerm.substTele σ 0 ab).map (·.2.2)) fs := by
    rw [spineFit_substTele, hsub]
    exact (hEq.spineFit_iff hsat' fs).mpr hfit
  -- (3) the domain at the rule's field variables
  have hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (mp.base2.acval n ψ).liftN 1 k = mp.base2.acval n ψ := mp.base2.acval_closed
  have hgcl : ∀ q ∈ grp, q.2.hasFvar = false := fun q hq => (grp_typeT (φ := ψ) mp hnN hkN hlps hgT hq).1
  have hwc : Expr.WScoped (hi + grp.length) crestH :=
    ConLeche.wscoped_instPisWith (fun a ha => ((hds a ha).1).mono (by omega))
      (ConLeche.WScoped.replaceConsts_closed (ConLeche.Cached.grpSub_WScoped hgcl) _ (by
        rw [Expr.hasFvar_instantiateLevelParams]
        exact (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)).1)) hcr
  obtain ⟨A', hA', hAi⟩ := piDomsWith_read (V := V) hacl (acval_inst_self mp.base2) (hi + grp.length)
    fvsF crestH _ _ doms
    (fun x hx => by
      obtain ⟨j', ty, rfl, hj', hty⟩ := hfvs x hx
      exact ⟨j', ty, rfl, by omega, hty⟩)
    (by rw [substTele_length, hlab, hfvl]; exact Nat.le_refl _) hwc.fvarsBelow hdoms hread i (by omega)
  obtain rfl : A' = A := Option.some.inj (hA'.symm.trans hA)
  rw [hAi τ]
  -- (4) the variables' values are the fields'
  have hvs : (fvsF.take i).map (fun x => interp V τ ((denoteMeta mp.base2.acval env ψ
      (hi + grp.length) x).getD default)) = fs.take i := by
    apply List.ext_getElem (by simp [hfvl, hfsl])
    intro l h1 h2
    simp only [List.length_map, List.length_take] at h1
    simp only [List.getElem_map, List.getElem_take]
    have hl : l < nF := by omega
    obtain ⟨j', ty, hx, hj', -⟩ := hfvs _ (List.getElem_mem (show l < fvsF.length by omega))
    rw [hx, denoteMeta_fvar, Option.getD_some, interp_bvar]
    have := hvals l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show l < fvsF.length by omega),
      Option.getD_some, hx, denoteMeta_fvar, Option.getD_some, interp_bvar] at this
    rw [← hτ, show hi + grp.length - 1 - j' = (hi - 1 - j')
      + (grpVals D (Level.substFn ψ lps us) grp ρp Y).length by simp [grpVals]; omega,
      consList_apply_add, this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  rw [hvs]
  have hm := FixKI.spineFit_getD_mem' hfitT (l := i) (by simp [substTele_length, hlab]; omega)
  have hlt : i < (AnnotTerm.substTele σ 0 ab).length := by simp [substTele_length, hlab]; omega
  have hgm : ((AnnotTerm.substTele σ 0 ab).map (·.2.2)).getD i default
      = ((AnnotTerm.substTele σ 0 ab).getD i default).2.2 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rw [hgm] at hm
  exact hm

end Stage

end ConLeche.Model
