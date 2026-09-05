import Setlec.SetP.DirectEntryFreeP

/-!
# The projection entry's frames (task #175 W4c, P3 module 7, part 4)

`entryFrames`: at every assignment, the entry type's opened frame
identified with the block's —

* the parameter entries are the constructor's (`recParamIdent` at
  opening length `1`, through the entry stage's parameter pin);
* the subject's entry is the family at the parameters
  (`famSpineRow` + the subject-domain pin);
* the residual is the constructor's `i`-th field domain at the
  parameters and the subject's earlier projections (the residual pin
  and the `instPisAt` peel's reading), read at the subject's
  projection spine — under the `Prop` guard, which at a squash
  instance makes the earlier fields proof fields so that the point
  spine fits them.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

omit [SetTheory V] in
theorem DomsBelow.getD_below {k : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)} (j : Nat), DomsBelow k ds → j < ds.length →
      VExpr.bvarsBelow (k + j) (ds.getD j default).2.2.erase
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d :: ds, 0, h, _ => by simpa using h.1
  | d :: ds, j + 1, h, hj => by
    rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.getD_below j h.2 (by simpa using hj)

/-- **The entry's frames.** -/
theorem entryFrames (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F nP nF i : Nat} {T C : Name} {lps : List Name} {resSort vb : Level}
    {cvTa cvCa : ConstantVal} {caps : IndCaps}
    {ptyA prest resid sdom tfv : Expr} {fvsP tFvs : List Expr}
    {sbs : List (Name × Expr × BinderMeta)} {sbody : Expr}
    {cdomsP : List Expr} {crestP : Expr} {cds : List Expr}
    {nmC : Name} {fdom bodyC : Expr} {mbC : BinderMeta}
    (hopP : openPisAtFvars nP ptyA 0 = some (fvsP, prest))
    (hsb : prest.stripPis 1 = some (sbs, sbody))
    (hsd : (sbs[0]?).map (·.2.1) = some sdom)
    (hsdeq : Setlec.isDefEqCore μ env F nP sdom
      (Expr.mkAppN (.const T (lps.map .param)) fvsP) = .ok true)
    (hopT : openPisAtFvars 1 prest nP = some (tFvs, resid))
    (htfv : tFvs[0]? = some tfv)
    (hci : Expr.instPisAt fvsP cvCa.type = some (cdomsP, crestP))
    (hdoms : Setlec.checkDirectDomsAt (Setlec.fueledOps μ F) env 0 fvsP cdomsP nP = .ok ())
    (hcf : Expr.instPisAt (fvsP ++ (List.range i).map fun j => Expr.proj T j tfv) cvCa.type
      = some (cds, .forallE nmC fdom bodyC mbC))
    (hrdeq : Setlec.isDefEqCore μ env F (nP + 1) resid fdom = .ok true)
    (hfT : env.find? T = some (.indInfo cvTa caps)) (hlpsT : cvTa.levelParams = lps)
    (hfC : env.find? C = some (.ctorInfo cvCa nP nF))
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry ∧ entry.tower = true)
    (hi : i < nF)
    {eds : (Name → Nat) → List (Nat × Nat × AVExpr)} {R : (Name → Nat) → AVExpr}
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)} {sorts : List Level}
    (hED : EntryData mp.base2 ptyA lps nP vb (fvsP ++ tFvs) resid eds R)
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    (hCD : CtorData mp.base2 T cvCa nP nF resSort ds)
    (hleafT : ∀ ψ, mp.base2.acval T ψ
      = directTyAV (resSort.eval ψ) (pps ψ) (((ds ψ).drop nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ → resSort.eval ψ ≠ 0 →
        FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)))
    (hsorts : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp2 V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    ∀ ψ : Name → Nat,
      (∀ i', i' ≤ nP → ∀ ρ : Nat → V,
        Sat2 V ((((eds ψ).map (·.2.2)).reverse).drop (nP + 1 - i')) ρ ↔
        Sat2 V (((((ds ψ).take nP).map (·.2.2)).reverse).drop (nP - i')) ρ) ∧
      (∀ ρ : Nat → V, Sat2 V ((((eds ψ).map (·.2.2)).reverse).drop 1) ρ →
        interp2 V ρ ((((eds ψ).map (·.2.2)).reverse).getD 0 default)
          = towerSet (resSort.eval ψ) (teleOfFields ρ (((ds ψ).drop nP).map (·.2.2)))) ∧
      (∀ used : Nat → Bool,
        (resSort.eval ψ = 0 → ∀ j, j < i → used j = true →
          (sorts.getD j .zero).eval ψ = 0) →
        (∀ j, j < i → used j = false →
          ∃ X : AVExpr, (((ds ψ).drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j)) →
        ∀ ρ : Nat → V, Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ →
          interp2 V ρ (R ψ)
            = interp2 V (consList (projList i (ρ 0)) (fun j => ρ (j + 1)))
                ((((ds ψ).drop nP).map (·.2.2)).getD i default)) := by
  intro ψ
  -- the constants' facts
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (Setlec.SetR.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the opening
  have hopAll : openPisAtFvars (nP + 1) ptyA 0 = some (fvsP ++ tFvs, resid) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopT)
  have hidxE : ∀ (k : Nat) (x : Expr), (fvsP ++ tFvs)[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
    intro k x hx
    obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index _ _ _ hopAll k x hx
    exact ⟨nm, ty, by rw [Nat.zero_add]⟩
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopP
  have hlenE : (fvsP ++ tFvs).length = nP + 1 := openPisAtFvars_length _ hopAll
  have htakeP : (fvsP ++ tFvs).take nP = fvsP := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  -- the subject variable
  obtain ⟨nmT, dom, mbT, rfl, rfl⟩ := stripPis_one_inv hsb
  simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hsd
  subst hsd
  rw [openPisAtFvars_one] at hopT
  simp only [Option.some.injEq, Prod.mk.injEq] at hopT
  obtain ⟨rfl, rfl⟩ := hopT
  simp only [List.getElem?_cons_zero, Option.some.injEq] at htfv
  subst htfv
  have hR := hED.opened ψ
  have hlenΓ : (((eds ψ).map (·.2.2)).reverse).length = nP + 1 := by simp [hED.len ψ]
  -- the claims at the two fuels
  have hc := claimsAtP_of hμ mp ψ F
  -- (1) the parameter frame is the constructor's
  have hpins := Setlec.checkDirectDomsAt_inv hdoms
  obtain ⟨hiffP, -, -, -, -⟩ := recParamIdent (k := 1) hc hR hidxE hlenE (hCD.len ψ)
    (hCD.read ψ) (hCD.okTy ψ) hCf hCb (by rw [htakeP]; exact hci)
    (by rw [htakeP]; exact hpins)
  -- the former's walks
  have hFsOk : ∀ (ψ' : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ').map (·.2.2)).reverse ρ →
      FieldsOkB (resSort.eval ψ') ρ (((ds ψ').drop nP).map (·.2.2)) ∧
      FieldsValid ρ (((ds ψ').drop nP).map (·.2.2)) :=
    fun ψ' ρ h => hokB ψ' ρ ((hiff ψ' ρ).mp h)
  have hwalks := formerWalks hFD hFsOk ψ
  have hsatP : ∀ ρ : Nat → V, Sat2 V ((((eds ψ).map (·.2.2)).reverse).drop 1) ρ →
      Sat2 V (((pps ψ).map (·.2.2)).reverse) ρ := by
    intro ρ hρ
    have h := (hiffP nP (Nat.le_refl _) ρ).mp (by
      rw [show nP + 1 - nP = 1 from by omega]; exact hρ)
    rw [Nat.sub_self, List.drop_zero] at h
    exact (hiff ψ ρ).mpr h
  -- (2) the subject's domain is the family at the parameters
  have hsubj : ∀ ρ : Nat → V, Sat2 V ((((eds ψ).map (·.2.2)).reverse).drop 1) ρ →
      interp2 V ρ ((((eds ψ).map (·.2.2)).reverse).getD 0 default)
        = towerSet (resSort.eval ψ) (teleOfFields ρ (((ds ψ).drop nP).map (·.2.2))) := by
    obtain ⟨hws, hbd, hLB, hCbF, hread, hrow⟩ :=
      famSpineRow (k := 1) hR hidxE hlenE hfT hlpsT (hleafT ψ) (hFD.bits ψ) (hFD.below ψ)
        (hFD.len ψ) (fun ρ => (hwalks ρ).1) (fun ρ => (hwalks ρ).2) hsatP 0 (Nat.zero_le _)
    simp only [Nat.add_zero, Nat.sub_zero, htakeP] at hws hbd hLB hCbF hread hrow
    have hsfv : (fvsP ++ [Expr.fvar nP nmT dom])[nP]? = some (.fvar nP nmT dom) := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.sub_self]; rfl
    obtain ⟨-, hwJ, hbJ, hLJ, hleafJ⟩ := hR.var nP _ hsfv
    simp only [Expr.fvarTypeD] at hwJ hbJ hLJ hleafJ
    have hdJ := hR.doms nP _ hsfv
    simp only [Expr.fvarTypeD] at hdJ
    rw [show nP + 1 - 1 - nP = 0 from by omega] at hdJ
    have hCJ := hR.ctx (i := nP) (by omega) hwJ hleafJ
    rw [show nP + 1 - nP = 1 from by omega] at hCJ
    have hokJ : ∀ ρ : Nat → V, Sat2 V ((((eds ψ).map (·.2.2)).reverse).drop 1) ρ →
        AnnotOkP V ρ ((((eds ψ).map (·.2.2)).reverse).getD 0 default) := by
      intro ρ hρ
      have := hR.okΓ nP (by omega) ρ (by rw [show nP + 1 - nP = 1 from by omega]; exact hρ)
      rwa [show nP + 1 - 1 - nP = 0 from by omega] at this
    have heq := hc.defEqRow hsdeq hwJ hbJ hLJ hws hbd hLB hCJ hCbF hdJ hread hokJ
      (fun ρ hρ => (hrow ρ hρ).1)
    intro ρ hρ
    rw [heq ρ hρ, (hrow ρ hρ).2]
  refine ⟨hiffP, hsubj, ?_⟩
  -- (3) the residual
  intro used hguard hfree
  -- the frame's split
  have hsplitΓ : ((eds ψ).map (·.2.2)).reverse
      = (((eds ψ).map (·.2.2)).reverse).getD 0 default
        :: (((eds ψ).map (·.2.2)).reverse).drop 1 := by
    have := drop_succ_eq_getD_cons (Γ := ((eds ψ).map (·.2.2)).reverse) (n := nP + 1)
      (i := nP) hlenΓ (by omega)
    rw [Nat.sub_self, List.drop_zero, show nP + 1 - 1 - nP = 0 from by omega,
      show nP + 1 - nP = 1 from by omega] at this
    exact this
  -- the frame's facts, at a satisfying valuation
  have hframe : ∀ ρ : Nat → V, Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ →
      ρ 0 ∈ˢ towerSet (resSort.eval ψ)
        (teleOfFields (fun j => ρ (j + 1)) (((ds ψ).drop nP).map (·.2.2))) ∧
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) := by
    intro ρ hρ
    rw [hsplitΓ] at hρ
    obtain ⟨hx, ht⟩ := Sat2_cons_inv hρ
    have hsat := (hiffP nP (Nat.le_refl _) _).mp (by
      rw [show nP + 1 - nP = 1 from by omega]; exact ht)
    rw [Nat.sub_self, List.drop_zero] at hsat
    refine ⟨?_, hsat⟩
    rw [← hsubj _ ht]
    exact hx
  -- the constructor type's reading at the entry's depth
  have hctyRead : denoteP mp.base2.acval env ψ (nP + 1) cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAV mp.base2 T nP nF ψ)) :=
    denoteP_depth_of_closed mp.base2.acval_closed hCf
      (fun k => denoteP_closed mp.base2.acval_erase mp.base2.cval_closed hCf hCb (hCD.read ψ) 1 k)
      (hCD.read ψ) (nP + 1)
  -- the arguments' scoping
  have hfvsPidx : ∀ (k : Nat) (x : Expr), fvsP[k]? = some x →
      ∃ nm ty, x = Expr.fvar k nm ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    exact hidxE k x (by rw [List.getElem?_append_left (by omega)]; exact hx)
  have hvarE : ∀ x ∈ fvsP ++ [Expr.fvar nP nmT dom],
      Expr.WScoped (nP + 1) x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧
      ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP ++ [Expr.fvar nP nmT dom] := by
    intro x hx
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
    have hkl : k < nP + 1 := by
      have := (List.getElem?_eq_some_iff.mp hk).1; omega
    obtain ⟨nm, ty, rfl⟩ := hidxE k _ hk
    obtain ⟨-, hwk, hbk, hLk, hleafk⟩ := hR.var k _ hk
    simp only [Expr.fvarTypeD] at hwk hbk hLk hleafk
    refine ⟨by simp only [Expr.WScoped]; exact ⟨hkl, hwk⟩, rfl, ?_, ?_⟩
    · intro l hl
      simp only [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact hbk
      · exact hLk l hl
    · intro l hl
      simp only [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact hx
      · exact hleafk l hl
  have htfvE : Expr.fvar nP nmT dom ∈ fvsP ++ [Expr.fvar nP nmT dom] := by simp
  have hargs : ∀ a ∈ fvsP ++ (List.range i).map (fun j => Expr.proj T j (.fvar nP nmT dom)),
      Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨h1, h2, -, -⟩ := hvarE a (List.mem_append_left _ ha)
      exact ⟨h1, h2⟩
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      obtain ⟨h1, h2, -, -⟩ := hvarE _ htfvE
      refine ⟨?_, by simp [Expr.looseBVarsBounded]⟩
      simp only [Expr.WScoped] at h1 ⊢
      exact h1
  have hargsLeaves : ∀ a ∈ fvsP ++ (List.range i).map (fun j => Expr.proj T j (.fvar nP nmT dom)),
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP ++ [Expr.fvar nP nmT dom] := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hvarE a (List.mem_append_left _ ha)).2.2.2
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      rw [show (Expr.proj T j (Expr.fvar nP nmT dom)).fvarLeaves
          = (Expr.fvar nP nmT dom).fvarLeaves from by simp [Expr.fvarLeaves]]
      exact (hvarE _ htfvE).2.2.2
  have hargsLB : ∀ a ∈ fvsP ++ (List.range i).map (fun j => Expr.proj T j (.fvar nP nmT dom)),
      Expr.LeavesBounded a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hvarE a (List.mem_append_left _ ha)).2.2.1
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      intro l hl
      rw [show (Expr.proj T j (Expr.fvar nP nmT dom)).fvarLeaves
          = (Expr.fvar nP nmT dom).fvarLeaves from by simp [Expr.fvarLeaves]] at hl
      exact (hvarE _ htfvE).2.2.1 l hl
  have hctyW : Expr.WScoped (nP + 1) cvCa.type := Expr.WScoped.of_not_hasFvar hCf
  have hctyNil : cvCa.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf
  -- `fdom`'s scoping and leaves
  obtain ⟨-, hresW⟩ := instPisAt_WScoped (d := nP + 1) _ _ hcf hctyW (fun a ha => (hargs a ha).1)
  have hfdW : Expr.WScoped (nP + 1) fdom := by
    simp only [Expr.WScoped] at hresW; exact hresW.1
  obtain ⟨-, hresB⟩ := instPisAt_bounded _ hcf hCb (fun a ha => (hargs a ha).2)
  have hfdB : fdom.looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hresB; exact hresB.1
  have hfdLeaves : ∀ l ∈ fdom.fvarLeaves, l ∈ (Expr.forallE nmC fdom bodyC mbC).fvarLeaves := by
    intro l hl
    simp only [Expr.fvarLeaves]
    exact List.mem_append_left _ hl
  have hfdL : Expr.LeavesBounded fdom := by
    intro l hl
    rcases instPisAt_leaves _ hcf l (Or.inr (hfdLeaves l hl)) with h | ⟨a, ha, hla⟩
    · rw [hctyNil] at h; exact absurd h List.not_mem_nil
    · exact hargsLB a ha l hla
  have hfdIn : ∀ l ∈ fdom.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP ++ [Expr.fvar nP nmT dom] := by
    intro l hl
    rcases instPisAt_leaves _ hcf l (Or.inr (hfdLeaves l hl)) with h | ⟨a, ha, hla⟩
    · rw [hctyNil] at h; exact absurd h List.not_mem_nil
    · exact hargsLeaves a ha l hla
  -- `fdom`'s reading: the field domain at the argument readings
  have hspP := denoteSpineP_entryParams (acval := mp.base2.acval) (env := env) (φ := ψ)
    hfvsPidx hlenP
  have hspX := denoteSpineP_entryProjs (acval := mp.base2.acval) (env := env) (φ := ψ)
    (nP := nP) (nmT := nmT) (sdom := dom) hprev
  have hsp := DenoteSpineP.append hspP hspX
  obtain ⟨restA, hrest, hpeel⟩ := denoteP_instPisAt_peel mp.base2.acval_closed
    (acval_inst_self mp.base2) _ hcf hctyW hargs hctyRead hsp
  obtain ⟨fdomA, ba, hfdA, -, rfl⟩ := denoteP_forallE_inv hrest
  -- the peel is the instantiation sequence of the field domain
  have hlenVs : (entryParamBvars nP ++ entryProjAVs i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  have hlenDs := hCD.len ψ
  have hsplitDs : ds ψ = (ds ψ).take (nP + i) ++ (ds ψ).drop (nP + i) :=
    (List.take_append_drop _ _).symm
  have htele : PiTeleP (nP + i) (mkPisAV (ds ψ) (ctorBodyAV mp.base2 T nP nF ψ))
      ((((ds ψ).take (nP + i)).map (·.2.2)).reverse)
      (mkPisAV ((ds ψ).drop (nP + i)) (ctorBodyAV mp.base2 T nP nF ψ)) := by
    have h := piTeleP_mkPisAV ((ds ψ).take (nP + i))
      (mkPisAV ((ds ψ).drop (nP + i)) (ctorBodyAV mp.base2 T nP nF ψ))
    rw [← mkPisAV_append, ← hsplitDs, List.length_take, hlenDs,
      show min (nP + i) (nP + nF) = nP + i from by omega] at h
    exact h
  have hpeel' := peelPis_of_piTeleP (nP + i) htele hlenVs
  rw [hpeel] at hpeel'
  have hdropDs : (ds ψ).drop (nP + i) = (ds ψ).getD (nP + i) default :: (ds ψ).drop (nP + i + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hdropDs] at hpeel'
  simp only [mkPisAV] at hpeel'
  obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ entryProjAVs i) (nP + i - 1)
    ((ds ψ).getD (nP + i) default).1 ((ds ψ).getD (nP + i) default).2.1
    ((ds ψ).getD (nP + i) default).2.2
    (mkPisAV ((ds ψ).drop (nP + i + 1)) (ctorBodyAV mp.base2 T nP nF ψ))
  rw [hB'] at hpeel'
  obtain ⟨-, -, hfdomA, -⟩ := AVExpr.pi.inj (Option.some.inj hpeel')
  -- the field's domain, named
  have hFi : (((ds ψ).drop nP).map (·.2.2)).getD i default = ((ds ψ).getD (nP + i) default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hFiBelow : VExpr.bvarsBelow (nP + i) ((ds ψ).getD (nP + i) default).2.2.erase := by
    have := DomsBelow.getD_below (nP + i) (hCD.below ψ) (by omega)
    rwa [Nat.zero_add] at this
  have hlenFs : (((ds ψ).drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
  -- the field's grading at the subject's projection spine, at every
  -- satisfying frame: in the graph regime the projections fit; at a
  -- squash instance they are the point spine, which differs from a
  -- fitting prefix only at unused slots, where the field is a lift
  have hokPre : ∀ ρ : Nat → V, Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ →
      AnnotOkP V (consList (projList i (ρ 0)) (fun j => ρ (j + 1)))
        ((((ds ψ).drop nP).map (·.2.2)).getD i default) := by
    intro ρ hρ
    obtain ⟨hx, hsat⟩ := hframe ρ hρ
    by_cases hw : resSort.eval ψ = 0
    · rw [hw] at hx
      obtain ⟨hpt, as', hfits⟩ := towerSet_zero_elim _ hx
      have hspAs := fitsS_teleOfFields.mp hfits
      obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
      rw [hpt, projList_pt]
      have hlenTake : (as'.take i).length = i := spineFit_take_length hspAs (by rw [hlenFs]; omega)
      rw [annotOkP_congr_lifts i
        (free_of_diff (hCD.len ψ) hi (hsorts ψ _ hsat) (hguard hw) hfree hspAs)
        (consList_prefix_agree hlenTake _).2]
      exact ⟨fieldsOkB_getD (hokB ψ _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
        fieldsValid_getD (hokB ψ _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
    · obtain ⟨hspAll, -⟩ := towerSet_elim_teleOfFields hw hx
      obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAll (by rw [hlenFs]; exact hi)
      rw [hlenFs, projList_take nF i _ (Nat.le_of_lt hi)] at hpre
      exact ⟨fieldsOkB_getD (hokB ψ _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
        fieldsValid_getD (hokB ψ _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
  -- the readings' gradings at a satisfying frame
  have hokArgs : ∀ ρ : Nat → V, Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ →
      ∀ w ∈ entryParamBvars nP ++ entryProjAVs i, AnnotOkP V ρ w := by
    intro ρ hρ w hw
    obtain ⟨hx, hsat⟩ := hframe ρ hρ
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
      exact ⟨trivial, trivial⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      have hj' : j < i := List.mem_range.mp hj
      refine ⟨?_, projAV_validV trivial⟩
      by_cases hw0 : resSort.eval ψ = 0
      · rw [hw0] at hx
        obtain ⟨hpt, -⟩ := towerSet_zero_elim _ hx
        exact annotOk2_projAV_pt trivial (by rw [interp2_bvar, hpt])
      · exact annotOk2_projAV_tower (hbound ψ _ hsat hw0) hx trivial (by rw [interp2_bvar])
          (by rw [hlenFs]; omega)
  have hokFd : ∀ ρ : Nat → V, Sat2 V (((eds ψ).map (·.2.2)).reverse) ρ → AnnotOkP V ρ fdomA := by
    intro ρ hρ
    rw [hfdomA]
    have hlen' : (entryParamBvars nP ++ entryProjAVs i).length - 1 = nP + i - 1 := by
      rw [hlenVs]
    rw [← hlen']
    refine annotOkP_instSeq _ (hokArgs ρ hρ) ?_
    rw [(AnnotOkP_congr_below _ (nP + i) _ _ hFiBelow (chainP_entry_agree nP i ρ))]
    rw [← hFi]
    exact hokPre ρ hρ
  -- the residual pin, at the claims
  have hCres := hR.ctx (i := nP + 1) (Nat.le_refl _) hR.bodyScoped.1 hR.bodyScoped.2.2.2
  rw [Nat.sub_self, List.drop_zero] at hCres
  have hCfd := hR.ctx (i := nP + 1) (Nat.le_refl _) hfdW hfdIn
  rw [Nat.sub_self, List.drop_zero] at hCfd
  have heq := hc.defEqRow hrdeq hR.bodyScoped.1 hR.bodyScoped.2.1 hR.bodyScoped.2.2.1
    hfdW hfdB hfdL hCres hCfd hR.body hfdA hR.okR hokFd
  intro ρ hρ
  have hlen' : (entryParamBvars nP ++ entryProjAVs i).length - 1 = nP + i - 1 := by
    rw [hlenVs]
  rw [heq ρ hρ, hfdomA, ← hlen', interp2_instSeq, hFi]
  exact interp2_congr_below V _ (nP + i) _ _ hFiBelow (chainP_entry_agree nP i ρ)

end Setlec.SetR.Interp2
