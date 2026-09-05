import Setlec.SetBase.Bridge.ProjRed

/-!
# The stuck-major rescues (task #148, T3, batch g)

`majorToCtor` (`Core.lean:1073-1188`) is three attempts and an
identity: for a K-flagged single-rule family fabricate the constructor
at the type's parameters and certify by proof irrelevance (R12); for an
eta-capable structure fabricate the constructor of the major's
projections and certify by structural eta (R13); at zero fields fall
through to proof irrelevance again (R14); otherwise leave the major
alone (`Red.refl`).

`majorToCtor_inv` maps onto the three rules premise-for-premise, and it
carries the fabrication's **frame conditions with it** (`wscopedB`, the
loose-bvar bound, and the leaf-subset fact) — which is why this clause
needs no scope bookkeeping of its own: the checker's own guards were
recorded by the inversion.

Two things are shared by all three branches and computed once: the
major's type reduced to the family's application (through
`inferShapeR`), and the constructor's stored type denoted
(`denote_declTypeR`).  The fabricated spines then denote by
`denote_mkAppN`; R13's needs the per-field projection-function lookups,
which come from re-inverting the same `structEtaCertWith` certificate
the rule's last premise consumes — `DenoteSpine.map_list` again, the
`projSpinesV` shape D10 introduced.

R13 is why `structEtaCertWith_stepR` was factored out of
`structEtaCert_stepR`: the certificate here is already stated at the
`tmaj` that `majorToCtor` computed, so the wrapper's own reduction step
must not be redone.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}

/-- The stuck-major rescue's contract. -/
def MajorStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {recName : Name} {rules : List RecRule}
    {cv : ConstantVal} {mI rP : Nat} {major major' : Expr} {vm : VExpr},
    env.find? recName = some (.recInfo cv mI rP rules) →
    majorToCtorP mode env fuel d recName rules major = .ok major' →
    Expr.WScoped d major → major.looseBVarsBounded 0 = true →
    Expr.LeavesBounded major → CtxOkR mode m.cval env φ d Δ major →
    denote m.cval env φ d major = some vm →
    ∃ w, denote m.cval env φ d major' = some w ∧
      Red mode env m.cval φ Δ vm w ∧
      Expr.WScoped d major' ∧ major'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded major' ∧ CtxOkR mode m.cval env φ d Δ major'

/-- **`MajorStepR`, proved** (R12/R13/R14, and the identity
fallthrough). -/
theorem majorToCtor_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hg : mode.betaGate = false)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    MajorStepR (mode := mode) m φ fuel := by
  intro d Δ recName rules cv mI rP major major' vm hfrec h hws hb hLb hC hvm
  rcases majorToCtor_inv h with rfl | ⟨hwsB, hbB, hleafB, rl, cvj, cnP, cnF,
    tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfcj, hpres, hfT, hitm,
    hwtm, hfnT, hcase⟩
  · exact ⟨vm, hvm, Red.refl, hws, hb, hLb, hC⟩
  · rw [Setlec.inferTypeIO_off hg] at hitm
    -- the fabrication's frame conditions come with the inversion
    have hwF : Expr.WScoped d major' := Expr.WScoped.of_wscopedB hwsB
    have hLF : Expr.LeavesBounded major' := fun l hl =>
      hLb l (by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)
    have hCF : CtxOkR mode m.cval env φ d Δ major' :=
      CtxOkR.of_subset (fun l hl => by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this) hC
    -- the major's type, reduced to the family's application (shared)
    obtain ⟨vm₀, W, hvm₀, hW, TMv, hmI, hmD⟩ :=
      inferShapeR m φ ihw ihi hitm hwtm hws hb hLb hC
    have hveq : vm₀ = vm := by rw [hvm₀] at hvm; exact Option.some.inj hvm
    rw [hveq] at hmI
    obtain ⟨htmw, htmb, htmL, htmC⟩ := frame_inferR m.wf hitm hws hb hLb hC
    have hwr : Expr.WScoped d tmaj := whnf_WScoped m.wf fuel hwtm htmw
    have hbr : tmaj.looseBVarsBounded 0 = true := whnf_looseBVars m.wf fuel hwtm htmb
    have hLr : Expr.LeavesBounded tmaj := fun l hl =>
      htmL l (whnf_fvarLeaves m.wf fuel hwtm l hl)
    have hCr : CtxOkR mode m.cval env φ d Δ tmaj :=
      CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwtm) htmC
    have hWsave := hW
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (Expr.mkAppN_getApp tmaj).symm, hfnT] at hW
    obtain ⟨vT, ts, hvT, hspt, rfl⟩ := denote_mkAppN_inv hW
    rw [denote_const, hfT] at hvT
    dsimp only at hvT
    split at hvT
    · next hlenT =>
      obtain rfl : vT = m.cval T (Level.substFn φ cvT.levelParams ust) :=
        (Option.some.inj hvT).symm
      obtain ⟨TVj, hTVj0, hTVjc, hTVjd⟩ := denote_declTypeR m φ hcl hfcj ust d
      obtain ⟨hVw, hVb, hVL, hVC⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfcj ust d
          hC.1
      have hfrT := frame_spineR (a := tmaj) hwr hbr hLr hCr
      rcases hcase with ⟨hK, hcnF, hlpj, hcnP, hstrip, rfl, hcerts, ⟨tfab,
        hitfab, hdefab⟩, hirr⟩ | ⟨heta, hectr, hproj, hnz, hlenP, hlenU,
        hlpj, hstrip, rfl, hcerts, hetacase⟩
      · rw [Setlec.inferTypeIO_off hg] at hitfab
        -- R12: the K-flagged rescue
        have hspK : DenoteSpine m.cval env φ d (tmaj.getAppArgs.take cnP)
            (ts.take cnP) := hspt.take cnP
        have hdF : denote m.cval env φ d
            (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
            = some (VExpr.mkAppN (m.cval rl.ctor
              (Level.substFn φ cvj.levelParams ust)) (ts.take cnP)) := by
          refine denote_mkAppN hspK ?_
          rw [denote_const, hfcj]
          dsimp only
          rw [if_pos (show ust.length
            = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
            from hlpj.symm)]
          rfl
        obtain ⟨vs', rest, hsp', htele⟩ :=
          certs_teleR m φ hg hcl ihd ihi _ (tmaj.getAppArgs.take cnP) TVj hcerts
            hVw hVb hVL hVC hTVjd
            (fun x hx => hfrT x (List.mem_of_mem_take hx))
        obtain rfl : vs' = ts.take cnP := DenoteSpine.det hsp' hspK
        -- the `to_cnstr_when_K` type check
        obtain ⟨vfab, vtfab, hvfab, hvtfab, TF, hFI, hFD⟩ :=
          ihi hitfab hwF hbB hLF hCF
        obtain rfl : vfab = VExpr.mkAppN (m.cval rl.ctor
            (Level.substFn φ cvj.levelParams ust)) (ts.take cnP) := by
          rw [hvfab] at hdF; exact Option.some.inj hdF
        obtain ⟨hfabw, hfabb, hfabL, hfabC⟩ :=
          frame_inferR m.wf hitfab hwF hbB hLF hCF
        have hDfab : DefEq mode env m.cval φ Δ
            (VExpr.mkAppN (m.cval T (Level.substFn φ cvT.levelParams ust)) ts)
            vtfab :=
          ihd hdefab hwr hbr hLr hfabw hfabb hfabL hCr hfabC hWsave hvtfab
        exact ⟨_, hdF, Red.rescueK (hrules ▸ hfrec) hfcj hpres hfT hK hcnF hlpj hlenT
          (by rw [hspt.length]; exact hcnP) hstrip rfl hTVj0 hTVjc hmI hmD
          htele hFI (hDfab.trans hFD.symm)
          (proofIrrel_stepR hg m φ ihw ihi hirr hwF hbB hLF hws hb hLb hCF hC
            hdF hvm),
          hwF, hbB, hLF, hCF⟩
      · -- R13/R14: the eta-capable rescue
        have hspM : DenoteSpine m.cval env φ d (tmaj.getAppArgs ++ [major])
            (ts ++ [vm]) := hspt.append (DenoteSpine.cons hvm DenoteSpine.nil)
        have hdenProj : ∀ j, (∃ ci, env.find? (projFnName T j) = some ci ∧
              ci.toConstantVal.levelParams = cvT.levelParams) →
            denote m.cval env φ d
                (Expr.mkAppN (.const (projFnName T j) ust)
                  (tmaj.getAppArgs ++ [major]))
              = some (VExpr.mkAppN (m.cval (projFnName T j)
                  (Level.substFn φ cvT.levelParams ust)) (ts ++ [vm])) := by
          intro j ⟨ci, hfp, hlpp⟩
          refine denote_mkAppN hspM ?_
          rw [denote_const, hfp]
          dsimp only
          rw [if_pos (show ust.length = ci.toConstantVal.levelParams.length by
            rw [hlpp]; exact hlenT), hlpp]
        have hfrM : ∀ x ∈ tmaj.getAppArgs ++ [major],
            Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
              Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
          intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hfrT x hx'
          · rcases List.mem_singleton.mp hx' with rfl
            exact ⟨hws, hb, hLb, hC⟩
        rcases hetacase with hcw | ⟨hnF0, hlpj', hirr⟩
        · -- R13
          obtain ⟨c', us'', cvc', cnP', cnF', T', us''', cvT', caps', hfna',
            hfc', hlena', hfnb', hfT', -, -, -, hefld', -, -, -, -, hlpc', -,
            hslots', -, -, hprojs, -, -, -⟩ := structEtaCertWith_inv hcw
          have hTeq : T' = T := by
            rw [hfnT] at hfnb'; exact (Expr.const.inj hfnb').1.symm
          have hUeq : us''' = ust := by
            rw [hfnT] at hfnb'; exact (Expr.const.inj hfnb').2.symm
          rw [hTeq, hUeq] at hprojs
          rw [hTeq] at hfT' hslots'
          have hcapseq : caps' = caps := by
            rw [hfT] at hfT'
            exact ((ConstantInfo.indInfo.inj (Option.some.inj hfT')).2).symm
          have hcvTeq : cvT' = cvT := by
            rw [hfT] at hfT'
            exact ((ConstantInfo.indInfo.inj (Option.some.inj hfT')).1).symm
          rw [hcvTeq] at hprojs
          rw [← hefld', hcapseq] at hslots'
          -- the fabricated projections, denoted by entry kind (task #175
          -- W4c: `.proj T j major` at an all-tower slot family, the
          -- projection functions' applications otherwise)
          have hspP : DenoteSpine m.cval env φ d
              (etaProjs env T ust tmaj.getAppArgs major caps.etaFields)
              (if towerSlotsAll env T caps.etaFields then
                (List.range caps.etaFields).map fun j => projNV j vm
              else projSpinesV m.cval T (Level.substFn φ cvT.levelParams ust)
                ts vm caps.etaFields) := by
            unfold etaProjs
            by_cases htow : towerSlotsAll env T caps.etaFields = true
            · rw [if_pos htow, if_pos htow]
              refine DenoteSpine.map_list _ (fun j hj => ?_)
              obtain ⟨e, hfe, hetw⟩ :=
                towerSlotsAll_slot htow j (by simpa using List.mem_range.mp hj)
              rw [denote_proj, hvm, hfe]
              dsimp only
              rw [if_pos hetw]
            · rw [if_neg htow, if_neg htow]
              have hrec : recSlotsAll env T caps.etaFields = true := by
                simpa [htow] using hslots'
              refine DenoteSpine.map_list _ (fun j hj => ?_)
              have hj' : j < caps.etaFields := by simpa using List.mem_range.mp hj
              rcases structEtaProjCerts_inv _ hprojs j (by
                  rw [List.mem_range, ← hefld', hcapseq]; exact hj') with
                ⟨cvp, mIp, rPp, rulesp, hfp, hlpj'', -, -⟩ |
                ⟨entry, hfp, -, -, -, -⟩
              · exact hdenProj j ⟨_, hfp, hlpj''⟩
              · exfalso
                obtain ⟨cv', mI', rP', rules', hfr⟩ := recSlotsAll_slot hrec j hj'
                rw [hfp] at hfr
                exact nomatch hfr
          have hspF : DenoteSpine m.cval env φ d
              (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
              (etaFabArgsVE m.cval env T (Level.substFn φ cvT.levelParams ust)
                ts vm caps.etaFields) :=
            hspt.append hspP
          have hdF : denote m.cval env φ d
              (Expr.mkAppN (.const caps.etaCtor ust)
                (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
              = some (VExpr.mkAppN (m.cval caps.etaCtor
                (Level.substFn φ cvj.levelParams ust))
                (etaFabArgsVE m.cval env T (Level.substFn φ cvT.levelParams ust)
                  ts vm caps.etaFields)) := by
            refine denote_mkAppN hspF ?_
            rw [← hectr, denote_const, hfcj]
            dsimp only
            rw [if_pos (show ust.length
              = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
              from hlpj.symm)]
            rfl
          have hfrF : ∀ x ∈ etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields,
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact hfrT x hx'
            · unfold etaProjs at hx'
              split at hx'
              · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
                exact ⟨by simpa [Expr.WScoped] using hws,
                  by simpa [Expr.looseBVarsBounded] using hb,
                  fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
                  ⟨hC.1, fun l hl => hC.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
              · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
                refine ⟨Expr.WScoped.mkAppN (Expr.WScoped.of_not_hasFvar rfl)
                    (fun y hy => (hfrM y hy).1),
                  looseBVarsBounded_mkAppN rfl (fun y hy => (hfrM y hy).2.1),
                  fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
                · rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
                  · exact absurd hl' (by simp [Expr.fvarLeaves])
                  · first
                    | exact (hfrM y hy).2.2.1 l hly
                    | exact (hfrM y hy).2.2.2.2 l hly
          obtain ⟨vs', rest, hsp', htele⟩ :=
            certs_teleR m φ hg hcl ihd ihi _
              (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) TVj
              hcerts hVw hVb hVL hVC hTVjd hfrF
          obtain rfl : vs' = etaFabArgsVE m.cval env T
              (Level.substFn φ cvT.levelParams ust) ts vm caps.etaFields :=
            DenoteSpine.det hsp' hspF
          refine ⟨_, hdF, Red.rescueEta (hrules ▸ hfrec) hfcj hpres hfT heta
            hectr hproj (by rw [hspt.length]; exact hlenP) hlenT hnz hlpj
            hstrip rfl hTVj0 hTVjc hmI hmD htele ?_, hwF, hbB, hLF, hCF⟩
          exact structEtaCertWith_stepR m φ hg hcl ihw ihd ihi hcw hwF hbB hLF hCF
            hws hb hLb hC hwr hbr hLr hCr hdF hvm hWsave hmI hmD
        · -- R14: the 0-field fallthrough
          have hEmpty : etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields
              = tmaj.getAppArgs := by
            rw [etaFabArgsE, etaProjs, hnF0]
            simp
          have hdF : denote m.cval env φ d
              (Expr.mkAppN (.const caps.etaCtor ust)
                (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
              = some (VExpr.mkAppN (m.cval caps.etaCtor
                (Level.substFn φ cvj.levelParams ust)) ts) := by
            rw [hEmpty]
            refine denote_mkAppN hspt ?_
            rw [← hectr, denote_const, hfcj]
            dsimp only
            rw [if_pos (show ust.length
              = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
              from hlpj.symm)]
            rfl
          obtain ⟨vs', rest, hsp', htele⟩ :=
            certs_teleR m φ hg hcl ihd ihi _
              (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) TVj
              hcerts hVw hVb hVL hVC hTVjd (by
                rw [hEmpty]; exact hfrT)
          rw [hEmpty] at hsp'
          obtain rfl : vs' = ts := DenoteSpine.det hsp' hspt
          refine ⟨_, hdF, Red.rescueUnit0 (hrules ▸ hfrec) hfcj hpres hfT heta
            hectr hproj hnF0 (by rw [hspt.length]; exact hlenP) hlenT hnz hlpj
            hstrip rfl hTVj0 hTVjc hmI hmD htele ?_, hwF, hbB, hLF, hCF⟩
          exact proofIrrel_stepR hg m φ ihw ihi hirr hwF hbB hLF hws hb hLb hCF hC
            hdF hvm
    · exact nomatch hvT

end Setlec.SetR
