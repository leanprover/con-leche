import Setlec.SetBase.Bridge.Stuck

/-!
# The two eta certificates (task #148, T3, batch d)

`PairEtaCertStepR` (D12) and `StructEtaCertStepR` (D10) — the two arms
of `stuckIrrel`'s cascade that were left named.  With them
`stuckIrrel_stepR` is unconditional, and so is `DefEqStuckStepR`.

**D12** is the pinned pair's eta law.  `pairEtaCert_inv` hands back the
four `isDefEqCore` certificates in the checker's order and the rule
takes them in that order; the only work is reading the constructor's
four-argument spine and the reduced type's two-argument spine off their
denotations (`denote_mkAppN_inv` twice) and denoting the two projection
comparands (`denote_proj`, whose `i < 2` guard is discharged by the
literal indices).  Task #130's `projParamCert` conjunct used to arrive
under `mode.ttChecks = true` and be discarded; the check itself was
deleted at task #161's de-gating round (item A, harvest site 23), so
the inversion no longer produces it — premise-exactness, now by
construction.

**D10** is the widest `DefEq` rule and the first consumer of
`certs_teleR` at *function-valued* data: `structEtaProjCerts_inv` gives
one existential per field index, and the rule quantifies six functions
of the index, so the bridge closes the gap with `choose_fun` (one
`Classical.choose` per index — the campaign's only use of choice so far,
and it is bookkeeping, not content).  Task #137's constructor-telescope
conjunct is likewise `mode.ttChecks`-gated and discarded.

The one genuinely new piece is `DenoteSpine.map_list`: the field
comparands are `(List.range cnF).map fun i => projFn_i applied to the
type's arguments and the stuck side`, and `projSpinesV` is the same map
on the `VExpr` side — so the spine's denotation is pointwise, which is
what that lemma says.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}

/-- A mapped spine denotes pointwise. -/
theorem DenoteSpine.map_list {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {g : Nat → Expr} {G : Nat → VExpr} :
    ∀ (l : List Nat), (∀ j ∈ l, denote cval env φ d (g j) = some (G j)) →
      DenoteSpine cval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteSpine.nil
  | cons x xs ih =>
    intro h
    exact DenoteSpine.cons (h x (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- Choice at `Nat`-indexed data: the form D10's function-valued
per-field quantifiers need. -/
theorem choose_fun {α : Type _} {P : Nat → α → Prop} (h : ∀ j, ∃ x, P j x) :
    ∃ f : Nat → α, ∀ j, P j (f j) :=
  ⟨fun j => Classical.choose (h j), fun j => Classical.choose_spec (h j)⟩

/-- **`StructEtaCertStepR`, proved** (D10). -/
theorem structEtaCertWith_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hg : mode.betaGate = false)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (_ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {a b wtb : Expr} {W TB : VExpr}
    (hcw : structEtaCertWithP mode env fuel d a b wtb = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOkR mode m.cval env φ d Δ a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b) (hCb : CtxOkR mode m.cval env φ d Δ b)
    (hwr : Expr.WScoped d wtb) (hbr : wtb.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded wtb) (hCr : CtxOkR mode m.cval env φ d Δ wtb)
    {va vb : VExpr} (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb)
    (hW : denote m.cval env φ d wtb = some W)
    (hbI : Infer mode env m.cval φ Δ vb TB)
    (hbD : DefEq mode env m.cval φ Δ TB W) :
    DefEq mode env m.cval φ Δ va vb := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps, hfna, hfc, hlena, hfnb,
    hfT, heta, hectr, hepar, hefld, hresT, hresc, hlenb, hlenus, hlpc,
    hstrip, hslots, hlev, hcertT, hprojs, hdefL1, -, hdefL2⟩ :=
    structEtaCertWith_inv hcw
  -- the constructor spine, denoted
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from (Expr.mkAppN_getApp a).symm,
    hfna] at hva
  obtain ⟨vf, as, hvf, hspa, rfl⟩ := denote_mkAppN_inv hva
  rw [denote_const, hfc] at hvf
  dsimp only at hvf
  split at hvf
  · next hlenc =>
    obtain rfl : vf = m.cval c (Level.substFn φ cvc.levelParams us) :=
      (Option.some.inj hvf).symm
    rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
      (Expr.mkAppN_getApp wtb).symm, hfnb] at hW
    obtain ⟨vT, ts, hvT, hspt, rfl⟩ := denote_mkAppN_inv hW
    rw [denote_const, hfT] at hvT
    dsimp only at hvT
    split at hvT
    · next hlenT =>
      obtain rfl : vT = m.cval T (Level.substFn φ cvT.levelParams us') :=
        (Option.some.inj hvT).symm
      -- the spine lengths
      have hlenTs : ts.length = cnP := by rw [hspt.length, hlenb]
      -- frames for the two argument spines
      have hfrA := frame_spineR (a := a) hwa hba hLa hCa
      have hfrT := frame_spineR (a := wtb) hwr hbr hLr hCr
      -- the type former's telescope certificate
      obtain ⟨TFv, hTF0, hTFc, hTFd⟩ := denote_declTypeR m φ hcl hfT us' d
      obtain ⟨hTFw, hTFb, hTFL, hTFC⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfT us' d hCa.1
      obtain ⟨ts', restT, hspt', hteleT⟩ :=
        certs_teleR m φ hg hcl ihd ihi _ wtb.getAppArgs TFv hcertT hTFw hTFb hTFL
          hTFC hTFd hfrT
      rw [DenoteSpine.det hspt' hspt] at hteleT
      -- the per-field data, made function-valued
      have hframeTb : ∀ x ∈ wtb.getAppArgs ++ [b],
          Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hfrT x hx'
        · rcases List.mem_singleton.mp hx' with rfl
          exact ⟨hwb, hbb, hLb, hCb⟩
      have hspTb : DenoteSpine m.cval env φ d (wtb.getAppArgs ++ [b]) (ts ++ [vb]) :=
        hspt.append (DenoteSpine.cons hvb DenoteSpine.nil)
      -- the slot discipline (task #175 W4c): every slot is a tower entry
      -- or every slot is a projection function
      by_cases htow : towerSlotsAll env T cnF = true
      · -- TOWER-BACKED SLOTS: the fabricated projections are `.proj T j b`
        -- nodes reading to `projNV j`, the certificates are the entries'
        -- stored types
        have hprojsT : ∀ j, j < cnF → ∃ entry : ProjEntry,
            env.find? (projFnName T j) = some (.projInfo entry) ∧
            entry.tower = true ∧ entry.levelParams = cvT.levelParams ∧
            (entry.ty.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
            iotaCertsP mode env fuel d
              (entry.ty.instantiateLevelParams entry.levelParams us')
              (wtb.getAppArgs ++ [b]) = .ok true := by
          intro j hj
          rcases structEtaProjCerts_inv _ hprojs j (by simpa using hj) with
            ⟨cvp, mIp, rPp, rulesp, hfp, -, -, -⟩ | h
          · exfalso
            obtain ⟨e, hfe, -⟩ := towerSlotsAll_slot htow j hj
            have := Env.findProj?_some hfe
            rw [hfp] at this
            exact nomatch this
          · exact h
        have hpf : ∀ j, ∃ z : ProjEntry × VExpr × VExpr,
            j < cnF →
              env.find? (projFnName T j) = some (.projInfo z.1) ∧
              z.1.tower = true ∧
              z.1.levelParams = cvT.levelParams ∧
              (z.1.ty.stripPis (cnP + 1)).isSome = true ∧
              denoteClosed m.cval env φ
                (z.1.ty.instantiateLevelParams z.1.levelParams us')
                = some z.2.1 ∧
              VExpr.Closed z.2.1 ∧
              Tele mode env m.cval φ Δ z.2.1 (ts ++ [vb]) z.2.2 := by
          intro j
          by_cases hj : j < cnF
          · obtain ⟨entry, hfp, htw, hlpj, hstrpj, hic⟩ := hprojsT j hj
            obtain ⟨TPj, hTP0, hTPc, hTPd⟩ := denote_declTypeR m φ hcl hfp us' d
            obtain ⟨hPw, hPb, hPL, hPC⟩ :=
              frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfp
                us' d hCa.1
            obtain ⟨vsj, restj, hspj, htelej⟩ :=
              certs_teleR m φ hg hcl ihd ihi _ (wtb.getAppArgs ++ [b]) TPj hic hPw
                hPb hPL hPC hTPd hframeTb
            obtain rfl : vsj = ts ++ [vb] := DenoteSpine.det hspj hspTb
            exact ⟨⟨entry, TPj, restj⟩, fun _ =>
              ⟨hfp, htw, hlpj, by rw [← hlenb]; exact hstrpj, hTP0, hTPc, htelej⟩⟩
          · exact ⟨⟨default, default, default⟩, fun hj' => absurd hj' hj⟩
        obtain ⟨F, hF⟩ := choose_fun hpf
        have hprojden : ∀ j, j < cnF →
            denote m.cval env φ d (.proj T j b) = some (projNV j vb) := by
          intro j hj
          obtain ⟨hfp, htw, -, -, -, -, -⟩ := hF j hj
          have hfe : env.findProj? T j = some (F j).1 := by
            unfold Env.findProj?
            rw [hfp]
          rw [denote_proj, hvb, hfe]
          dsimp only
          rw [if_pos htw]
        have hprojframe : ∀ x ∈ (List.range cnF).map (fun j => Expr.proj T j b),
            Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
              Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
          intro x hx
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
          exact ⟨by simpa [Expr.WScoped] using hwb,
            by simpa [Expr.looseBVarsBounded] using hbb,
            fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
            ⟨hCb.1, fun l hl => hCb.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
        rw [etaProjs, if_pos htow] at hdefL2
        exact DefEq.structEtaTower (ent := fun j => (F j).1)
          (TPv := fun j => (F j).2.1) (restP := fun j => (F j).2.2)
          hfc (by rw [hspa.length, hlena]) hfT heta hectr
          hepar hefld hresT hresc hlenTs hlenus hlpc hstrip hlev hTF0 hTFc
          (fun j hj => (hF j hj).1) (fun j hj => (hF j hj).2.1)
          (fun j hj => (hF j hj).2.2.1) (fun j hj => (hF j hj).2.2.2.1)
          (fun j hj => (hF j hj).2.2.2.2.1)
          (fun j hj => (hF j hj).2.2.2.2.2.1)
          hbI hbD hteleT (fun j hj => (hF j hj).2.2.2.2.2.2)
          (defEqL_of_defEqListR m φ ihd hdefL1
            (fun x hx => hfrA x (List.mem_of_mem_take hx)) hfrT (hspa.take cnP)
            hspt)
          (defEqL_of_defEqListR m φ ihd hdefL2
            (fun x hx => hfrA x (List.mem_of_mem_drop hx)) hprojframe
            (hspa.drop cnP)
            (DenoteSpine.map_list _ (fun j hj => hprojden j (by simpa using hj))))
      · -- PROJECTION-FUNCTION SLOTS: the modeled path's, as before
        have hrec : recSlotsAll env T cnF = true := by
          simpa [htow] using hslots
        rw [etaProjs, if_neg htow] at hdefL2
        have hpf : ∀ j, ∃ z : ConstantVal × Nat × Nat × List RecRule × VExpr × VExpr,
            j < cnF →
              env.find? (projFnName T j)
                = some (.recInfo z.1 z.2.1 z.2.2.1 z.2.2.2.1) ∧
              z.1.levelParams = cvT.levelParams ∧
              (z.1.type.stripPis (cnP + 1)).isSome = true ∧
              denoteClosed m.cval env φ
                (z.1.type.instantiateLevelParams z.1.levelParams us')
                = some z.2.2.2.2.1 ∧
              VExpr.Closed z.2.2.2.2.1 ∧
              Tele mode env m.cval φ Δ z.2.2.2.2.1 (ts ++ [vb]) z.2.2.2.2.2 := by
          intro j
          by_cases hj : j < cnF
          · obtain ⟨cvpj, mIpj, rPpj, rulespj, hfp, hlpj, hstrpj, hic⟩ :
                ∃ cvpj mIpj rPpj rulespj,
                  env.find? (projFnName T j)
                    = some (.recInfo cvpj mIpj rPpj rulespj) ∧
                  cvpj.levelParams = cvT.levelParams ∧
                  (cvpj.type.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
                  iotaCertsP mode env fuel d
                    (cvpj.type.instantiateLevelParams cvpj.levelParams us')
                    (wtb.getAppArgs ++ [b]) = .ok true := by
              rcases structEtaProjCerts_inv _ hprojs j (by simpa using hj) with
                h | ⟨entry, hfp, -, -, -, -⟩
              · exact h
              · exfalso
                obtain ⟨cv, mI, rP, rules, hfr⟩ := recSlotsAll_slot hrec j hj
                rw [hfr] at hfp
                exact nomatch hfp
            obtain ⟨TPj, hTP0, hTPc, hTPd⟩ := denote_declTypeR m φ hcl hfp us' d
            obtain ⟨hPw, hPb, hPL, hPC⟩ :=
              frame_declTypeR (cval := m.cval) (φ := φ) (mode := mode) m.wf hfp us' d
                hCa.1
            obtain ⟨vsj, restj, hspj, htelej⟩ :=
              certs_teleR m φ hg hcl ihd ihi _ (wtb.getAppArgs ++ [b]) TPj hic hPw hPb
                hPL hPC hTPd hframeTb
            obtain rfl : vsj = ts ++ [vb] := DenoteSpine.det hspj hspTb
            exact ⟨⟨cvpj, mIpj, rPpj, rulespj, TPj, restj⟩, fun _ =>
              ⟨hfp, hlpj, by rw [← hlenb]; exact hstrpj, hTP0, hTPc, htelej⟩⟩
          · exact ⟨⟨default, 0, 0, [], default, default⟩, fun hj' => absurd hj' hj⟩
        obtain ⟨F, hF⟩ := choose_fun hpf
        -- the projection spine's denotation
        have hprojden : ∀ j, j < cnF →
            denote m.cval env φ d
                (Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
              = some (VExpr.mkAppN
                  (m.cval (projFnName T j) (Level.substFn φ cvT.levelParams us'))
                  (ts ++ [vb])) := by
          intro j hj
          obtain ⟨hfp, hlpj, -, -, -, -⟩ := hF j hj
          refine denote_mkAppN hspTb ?_
          rw [denote_const, hfp]
          dsimp only
          rw [if_pos (show us'.length = (ConstantInfo.recInfo (F j).1 (F j).2.1
              (F j).2.2.1 (F j).2.2.2.1).toConstantVal.levelParams.length by
            show us'.length = (F j).1.levelParams.length
            rw [hlpj]; exact hlenus)]
          show some (m.cval (projFnName T j)
            (Level.substFn φ (F j).1.levelParams us')) = _
          rw [hlpj]
        have hprojframe : ∀ x ∈ (List.range cnF).map (fun i =>
              Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])),
            Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
              Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x := by
          intro x hx
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
          refine ⟨Expr.WScoped.mkAppN (Expr.WScoped.of_not_hasFvar rfl)
              (fun y hy => (hframeTb y hy).1),
            looseBVarsBounded_mkAppN rfl (fun y hy => (hframeTb y hy).2.1),
            fun l hl => ?_, ⟨hCa.1, fun l hl => ?_⟩⟩ <;>
          · rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
            · exact absurd hl' (by simp [Expr.fvarLeaves])
            · first
              | exact (hframeTb y hy).2.2.1 l hly
              | exact (hframeTb y hy).2.2.2.2 l hly
        exact DefEq.structEta (cvp := fun j => (F j).1)
          (mIp := fun j => (F j).2.1) (rPp := fun j => (F j).2.2.1)
          (rulesP := fun j => (F j).2.2.2.1) (TPv := fun j => (F j).2.2.2.2.1)
          (restP := fun j => (F j).2.2.2.2.2)
          hfc (by rw [hspa.length, hlena]) hfT heta hectr
          hepar hefld hresT hresc hlenTs hlenus hlpc hstrip hlev hTF0 hTFc
          (fun j hj => (hF j hj).1) (fun j hj => (hF j hj).2.1)
          (fun j hj => (hF j hj).2.2.1)
          (fun j hj => (hF j hj).2.2.2.1)
          (fun j hj => (hF j hj).2.2.2.2.1)
          hbI hbD hteleT (fun j hj => (hF j hj).2.2.2.2.2)
          (defEqL_of_defEqListR m φ ihd hdefL1
            (fun x hx => hfrA x (List.mem_of_mem_take hx)) hfrT (hspa.take cnP) hspt)
          (defEqL_of_defEqListR m φ ihd hdefL2
            (fun x hx => hfrA x (List.mem_of_mem_drop hx)) hprojframe
            (hspa.drop cnP) (DenoteSpine.map_list _ (fun j hj => hprojden j (by simpa using hj))))
    · exact nomatch hvT
  · exact nomatch hvf

/-- **`StructEtaCertStepR`, proved** (D10) — `structEtaCert` is
`structEtaCertWith` at the stuck side's own reduced type, so the wrapper
is that reduction plus the core.  R13 (`Red.rescueEta`) calls the core
directly, at the `tmaj` `majorToCtor` already computed. -/
theorem structEtaCert_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    StructEtaCertStepR (mode := mode) m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨tb, wtb, htb, hwtb, hcw⟩ := structEtaCert_inv h
  rw [Setlec.inferTypeIO_off hg] at htb
  obtain ⟨vb₀, W, hvb₀, hW, TB, hbI, hbD⟩ :=
    inferShapeR m φ ihw ihi htb hwtb hwb hbb hLb hCb
  have hveq : vb₀ = vb := by rw [hvb₀] at hvb; exact Option.some.inj hvb
  rw [hveq] at hbI
  obtain ⟨htbw, htbb, htbL, htbC⟩ := frame_inferR m.wf htb hwb hbb hLb hCb
  exact structEtaCertWith_stepR m φ hg hcl ihw ihd ihi hcw hwa hba hLa hCa
    hwb hbb hLb hCb
    (whnf_WScoped m.wf fuel hwtb htbw) (whnf_looseBVars m.wf fuel hwtb htbb)
    (fun l hl => htbL l (whnf_fvarLeaves m.wf fuel hwtb l hl))
    (CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwtb) htbC)
    hva hvb hW hbI hbD

/-- **`PairEtaCertStepR`, proved** (D12). -/
theorem pairEtaCert_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    PairEtaCertStepR (mode := mode) m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    mI, rP, rr, rfl, hfc, htb, hwtb, hfc', hfrec, hrct, hrnf, hmrp, hres,
    hlev, hdα, hdβ, hd₁, hd₂⟩ := pairEtaCert_inv h
  rw [Setlec.inferTypeIO_off hg] at htb
  -- the constructor spine's denotation, through `mkAppN`
  rw [show (Expr.app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂)
      = Expr.mkAppN (.const c us) [pα, pβ, s₁, s₂] from rfl] at hva hwa hba hLa hCa
  obtain ⟨vf, vs, hvf, hsp, rfl⟩ := denote_mkAppN_inv hva
  rw [denote_const, hfc] at hvf
  dsimp only at hvf
  split at hvf
  · next hlen =>
    obtain rfl : vf = m.cval c (Level.substFn φ cvm.levelParams us) :=
      (Option.some.inj hvf).symm
    cases hsp with | cons hpα hsp => ?_
    cases hsp with | cons hpβ hsp => ?_
    cases hsp with | cons hs₁ hsp => ?_
    cases hsp with | cons hs₂ hsp => ?_
    cases hsp
    obtain ⟨hfα, hfβ, hf₁, hf₂⟩ :
        (Expr.WScoped d pα ∧ pα.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded pα ∧ CtxOkR mode m.cval env φ d Δ pα) ∧
        (Expr.WScoped d pβ ∧ pβ.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded pβ ∧ CtxOkR mode m.cval env φ d Δ pβ) ∧
        (Expr.WScoped d s₁ ∧ s₁.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded s₁ ∧ CtxOkR mode m.cval env φ d Δ s₁) ∧
        (Expr.WScoped d s₂ ∧ s₂.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded s₂ ∧ CtxOkR mode m.cval env φ d Δ s₂) := by
      have hfr := frame_spineR (a := Expr.mkAppN (.const c us) [pα, pβ, s₁, s₂])
        hwa hba hLa hCa
      rw [show (Expr.mkAppN (.const c us) [pα, pβ, s₁, s₂]).getAppArgs
        = [pα, pβ, s₁, s₂] from by
          rw [Expr.getAppArgs_mkAppN]; rfl] at hfr
      exact ⟨hfr pα (by simp), hfr pβ (by simp), hfr s₁ (by simp),
        hfr s₂ (by simp)⟩
    -- `b`'s type, reduced to the pinned pair family at its two parameters
    obtain ⟨vb₀, W, hvb₀, hW, TB, hbI, hbD⟩ :=
      inferShapeR m φ ihw ihi htb hwtb hwb hbb hLb hCb
    have hveq : vb₀ = vb := by rw [hvb₀] at hvb; exact Option.some.inj hvb
    rw [hveq] at hbI
    obtain ⟨htbw, htbb, htbL, htbC⟩ := frame_inferR m.wf htb hwb hbb hLb hCb
    rw [show (Expr.app (.app (.const c' us') A) B)
        = Expr.mkAppN (.const c' us') [A, B] from rfl] at hwtb
    have hwr : Expr.WScoped d (Expr.mkAppN (.const c' us') [A, B]) :=
      whnf_WScoped m.wf fuel hwtb htbw
    have hbr : (Expr.mkAppN (.const c' us') [A, B]).looseBVarsBounded 0 = true :=
      whnf_looseBVars m.wf fuel hwtb htbb
    have hLr : Expr.LeavesBounded (Expr.mkAppN (.const c' us') [A, B]) :=
      fun l hl => htbL l (whnf_fvarLeaves m.wf fuel hwtb l hl)
    have hCr : CtxOkR mode m.cval env φ d Δ (Expr.mkAppN (.const c' us') [A, B]) :=
      CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwtb) htbC
    rw [show (Expr.app (.app (.const c' us') A) B)
        = Expr.mkAppN (.const c' us') [A, B] from rfl] at hW
    obtain ⟨vf', vs', hvf', hsp', rfl⟩ := denote_mkAppN_inv hW
    rw [denote_const, hfc'] at hvf'
    dsimp only at hvf'
    split at hvf'
    · next hlen' =>
      obtain rfl : vf' = m.cval c' (Level.substFn φ cvi.levelParams us') :=
        (Option.some.inj hvf').symm
      cases hsp' with | cons hVA hsp' => ?_
      cases hsp' with | cons hVB hsp' => ?_
      cases hsp'
      have hfr' := frame_spineR (a := Expr.mkAppN (.const c' us') [A, B])
        hwr hbr hLr hCr
      rw [show (Expr.mkAppN (.const c' us') [A, B]).getAppArgs = [A, B] from by
        rw [Expr.getAppArgs_mkAppN]; rfl] at hfr'
      obtain ⟨hwA, hbA, hLA, hCA⟩ := hfr' A (by simp)
      obtain ⟨hwB, hbB, hLB, hCB⟩ := hfr' B (by simp)
      obtain ⟨hwα, hbα, hLα, hCα⟩ := hfα
      obtain ⟨hwβ, hbβ, hLβ, hCβ⟩ := hfβ
      obtain ⟨hw₁, hb₁, hL₁, hC₁⟩ := hf₁
      obtain ⟨hw₂, hb₂, hL₂, hC₂⟩ := hf₂
      -- the two projection comparands
      have hpj : ∀ (i : Nat), i < 2 →
          denote m.cval env φ d (.proj c' i b) = some (.proj i vb) := by
        intro i hi
        rw [denote_proj_pair m.cval env φ d c' i b
          (fun entry hf => by
            -- the family's recursor is reserved, a tower former's is not
            cases htw : entry.tower
            · rfl
            · exfalso
              obtain ⟨-, -, hrecres, -⟩ := m.proj_ok.towerHead hf htw
              rw [(Env.findProj?_names hf).1, hres] at hrecres
              exact nomatch hrecres), hvb]
        dsimp only
        rw [if_pos hi]
      have hfpj : ∀ (i : Nat), Expr.WScoped d (.proj c' i b) ∧
          (Expr.proj c' i b).looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded (.proj c' i b) ∧
          CtxOkR mode m.cval env φ d Δ (.proj c' i b) := by
        intro i
        refine ⟨?_, ?_, fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
          CtxOkR.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl) hCb⟩
        · simpa [Expr.WScoped] using hwb
        · simpa [Expr.looseBVarsBounded] using hbb
      obtain ⟨hwp₀, hbp₀, hLp₀, hCp₀⟩ := hfpj 0
      obtain ⟨hwp₁, hbp₁, hLp₁, hCp₁⟩ := hfpj 1
      exact DefEq.pairEta hfc hfc' hfrec hrct hrnf hmrp hres hlev hlen hlen'
        hbI hbD
        (ihd hdα hwα hbα hLα hwA hbA hLA hCα hCA hpα hVA)
        (ihd hdβ hwβ hbβ hLβ hwB hbB hLB hCβ hCB hpβ hVB)
        (ihd hd₁ hw₁ hb₁ hL₁ hwp₀ hbp₀ hLp₀ hC₁ hCp₀ hs₁ (hpj 0 (by omega)))
        (ihd hd₂ hw₂ hb₂ hL₂ hwp₁ hbp₁ hLp₁ hC₂ hCp₁ hs₂ (hpj 1 (by omega)))
    · exact nomatch hvf'
  · exact nomatch hvf

end Setlec.SetR
