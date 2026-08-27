import Setlec.TTVerify.StrLitStep

/-!
# The projection clause of `infer`

`InferProjStepTT`, the last clause of `InferClaimsTT`.

**Unblocked by task #129**, which is §10.3's request granted.  The gap
was that `HasType.projFst`/`projSnd` carry three premises and
`inferBody`'s `.proj` clause supplied only the third; the parameters'
own typings were nowhere.

The implementer's shape is better than the one I asked for, and the
reason is §10.1's own law — *premises are supplied where the rule
fires, at the domains the rule names*.  I asked for two `ensureSort`s;
what landed is **one `iotaCerts` telescope walk on the entry's stored
type**, because `⊢ B : A → Sort v` is not a sort judgement at all, and
an `ensureSort` on `A` would have landed at the *inferred* level where
`projFst` names the *pinned* `u`.  The first two domains of
`pairFstTyA` are literally `Sort u` and `α → Sort v`, so the walk
delivers both premises in the shape the rule wants.

That makes this clause the same shape as `proj_tele_typed`
(`Setlec/TTVerify/WhnfCore.lean`) one level up: `projParamCert_inv` →
`certs_typed` → destructure the walk → apply the rule.
-/

namespace Setlec.TTVerify

/- Task #147: this file's lemmas are stated at the TT-lane mode — the
seven gated checks reduce definitionally at `.ttModel`, so the walks
below see the pre-#147 bodies (`CertifiedConfigTT` pins the running
mode to this value). -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-! ## The pinned entry's first two premises

Both entries share their first two binders — `α : Sort u` and
`β : ∀ (x : α), Sort v` — so one destructuring covers both.  It is
`psigmaMk_tele_premises`'s two-argument sibling. -/

/-- The parameter walk on a pinned projection entry yields exactly the
two premises `projFst`/`projSnd` are missing. -/
theorem projEntry_tele_premises {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} {Δ : List VExpr} {entry : ProjEntry}
    {us : List Level} {A B : Expr} {xs : List VExpr} {rest : Expr}
    (hpin : entry = pairFstEntry ∨ entry = pairSndEntry)
    (h : TeleTyped cval env φ d Δ
      (entry.ty.instantiateLevelParams entry.levelParams us) [A, B] xs
      rest) :
    ∃ VA VB, denote cval env φ d A = some VA ∧
      denote cval env φ d B = some VB ∧
      HasType Δ VA (.sort ((Level.subst entry.levelParams us
        (.param uN)).eval φ)) ∧
      HasType Δ VB (arrow VA (.sort ((Level.subst entry.levelParams us
        (.param vN)).eval φ))) := by
  rcases hpin with rfl | rfl <;>
  · simp only [pairFstEntry, pairSndEntry, pairFstTyA, pairSndTyA, uN, vN,
      Expr.instantiateLevelParams] at h ⊢
    cases h with | cons hty1 harg1 hx1 _ _ hbA h => ?_
    rw [denote_sort] at hty1
    obtain rfl := Option.some.inj hty1
    inst_simp at h
    cases h with | cons hty2 harg2 hx2 _ _ hbB h => ?_
    rw [denote_forallE, harg1] at hty2
    simp only [Expr.instantiate1, denote_sort] at hty2
    obtain rfl := Option.some.inj hty2
    exact ⟨_, _, harg1, harg2, hx1, hx2⟩

/-! ## The pinned entry type denotes

`certs_typed` takes the walked type's denotation as a hypothesis, so
the clause has to produce it.  For a *pinned* entry that is a closed
computation: three binders and a body, with `PSigma'` the only constant
and `EnvTT.proj_ok` supplying its lookup. -/

/-- The pinned entry's type denotes, at any depth. -/
theorem denote_projEntryTy {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {entry : ProjEntry} {us : List Level}
    (hpin : entry = pairFstEntry ∨ entry = pairSndEntry)
    (hpsig : env.find? psigmaName = some psigmaA)
    (husl : us.length = entry.levelParams.length) (d : Nat) :
    ∃ TT, denote m.cval env φ d
      (entry.ty.instantiateLevelParams entry.levelParams us) = some TT := by
  obtain ⟨u1, u2, rfl⟩ : ∃ u1 u2, us = [u1, u2] := by
    rcases hpin with rfl | rfl <;>
      (simp only [pairFstEntry, pairSndEntry] at husl
       match us, husl with
       | [u1, u2], _ => exact ⟨u1, u2, rfl⟩)
  have hpsigC : ∀ D : Nat, denote m.cval env φ D
      (.const psigmaName [u1, u2]) =
      some (m.cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [u1, u2])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  have hd0 : ∀ k : Nat, k + 1 - 1 - k = 0 := by intro k; omega
  have hd1 : ∀ k : Nat, k + 1 + 1 - 1 - k = 1 := by intro k; omega
  have hd2 : ∀ k : Nat, k + 1 + 1 + 1 - 1 - k = 2 := by intro k; omega
  rcases hpin with rfl | rfl <;>
  · simp +decide only [pairFstEntry, pairSndEntry, pairFstTyA, pairSndTyA,
      Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
      denote_forallE, denote_sort, denote_app, denote_proj, denote_fvar,
      hpsigC, Expr.instantiate1, Nat.reduceSub,
      reduceIte, hd0, hd1, hd2,
      List.map_cons, List.map_nil]
    exact ⟨_, rfl⟩

/-! ## The clause

Mirrors `Setlec/Model/Core/Infer.lean`'s `proj` case step for step —
the same `hidx`/`hT` identification, the same residual computation —
with the set model's `AnnotOk` source of the parameter premises
replaced by #129's certificate. -/

/-- **`InferProjStepTT`, discharged.** -/
theorem infer_proj_step {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) : InferProjStepTT m φ fuel := by
  intro d Δ sn i pe t h hws hb hLb hC
  obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hf, hnat, hlen, husl,
    hcert, hres⟩ := inferTypeCore_proj_inv h
  obtain ⟨hpin, hpsig, hpsigMk⟩ :=
    m.proj_ok.1 _ _ (Env.findProj?_some hf) hnat
  -- the entry's stored name pins the head and the index
  have hidx : entry.idx = i ∧ entry.structName = T := by
    have h1 := List.find?_some (Env.findProj?_some hf)
    have h2 : (ConstantInfo.projInfo entry).name = projFnName T i :=
      eq_of_beq (by simpa using h1)
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
    exact ⟨(projFnName_inj h2).2, (projFnName_inj h2).1⟩
  have hT : T = psigmaName := by
    rw [← hidx.2]
    rcases hpin with rfl | rfl <;> rfl
  subst hT
  -- the subject's frame conditions
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCpe : CtxOk m.cval env φ d Δ pe :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the subject is typed at its whnf'd inferred type
  obtain ⟨VP, vtpe, hVP, hvtpe, hpt⟩ := ihi hte hws hb hLpe hCpe
  obtain ⟨htpw, htpb, htpL, htpC⟩ := frame_infer m.wf hte hws hb hLpe hCpe
  obtain ⟨vte, hvte, hDte⟩ := ihw hwt htpw htpb htpL htpC hvtpe
  have hpte : HasType Δ VP vte := Deq.conv hpt hDte
  -- `te`'s frame conditions, and its spine
  have hwte : Expr.WScoped d te := whnf_WScoped m.wf fuel hwt htpw
  have hbte : te.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hwt htpb
  have hLte : Expr.LeavesBounded te := fun l hl =>
    htpL l (whnf_fvarLeaves m.wf fuel hwt l hl)
  have hCte : CtxOk m.cval env φ d Δ te :=
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwt) htpC
  have hlen2 : te.getAppArgs.length = 2 := by
    rw [hlen]
    rcases hpin with rfl | rfl <;> rfl
  obtain ⟨A, B, hargs2⟩ : ∃ A B, te.getAppArgs = [A, B] := by
    match hq : te.getAppArgs, hlen2 with
    | [A, B], _ => exact ⟨A, B, rfl⟩
  -- the parameters' frame conditions, from the spine's
  have hframe : ∀ x ∈ te.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOk m.cval env φ d Δ x := by
    intro x hx
    exact ⟨hwte.getAppArgs x hx,
      looseBVarsBounded_getAppArgs hbte x hx,
      fun l hl => hLte l (fvarLeaves_getAppArgs hx l hl),
      CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hCte⟩
  -- #129's certificate becomes the two premises `projFst` wants
  obtain ⟨TT, hTT⟩ := denote_projEntryTy m φ hpin hpsig husl d
  obtain ⟨xs, rest, hfit⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TT (projParamCert_inv (hcert rfl))
      (by rcases hpin with rfl | rfl <;> exact Expr.WScoped.of_not_hasFvar rfl)
      (by rcases hpin with rfl | rfl <;> rfl)
      (by rcases hpin with rfl | rfl <;>
        exact Expr.LeavesBounded.of_not_hasFvar rfl)
      (by
        refine ⟨hC.1, fun l hl => ?_⟩
        rcases hpin with rfl | rfl <;>
          simp [pairFstEntry, pairSndEntry, pairFstTyA, pairSndTyA,
            Expr.instantiateLevelParams, Expr.fvarLeaves] at hl)
      hTT (by rw [hargs2] at hframe; exact hargs2 ▸ hframe)
  rw [hargs2] at hfit
  obtain ⟨VA, VB, hVA, hVB, hAs, hBs⟩ := projEntry_tele_premises hpin hfit
  obtain ⟨-, hbA, -, -⟩ := hframe A (by rw [hargs2]; simp)
  obtain ⟨-, hbB, -, -⟩ := hframe B (by rw [hargs2]; simp)
  have husl2 : us.length = 2 := by
    rw [husl]; rcases hpin with rfl | rfl <;> rfl
  -- the scrutinee's type *is* a pair type
  have hlev : ∀ nm : Name, (Level.subst entry.levelParams us
      (.param nm)).eval φ =
      Level.substFn φ psigmaA.toConstantVal.levelParams us nm := by
    intro nm
    rw [Level.eval_subst]
    rcases hpin with rfl | rfl <;> rfl
  have hteEq : te = Expr.mkAppN (.const psigmaName us) [A, B] := by
    rw [← hargs2, ← hfn, Expr.mkAppN_getApp]
  have hvteEq : vte = psigmaT
      (Level.substFn φ psigmaA.toConstantVal.levelParams us uN)
      (Level.substFn φ psigmaA.toConstantVal.levelParams us vN) VA VB := by
    rw [hteEq] at hvte
    rw [denote_mkAppN (vf := m.cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams us))
      (DenoteSpine.cons hVA (DenoteSpine.cons hVB .nil))
      (by rw [denote_const, hpsig]
          simp [psigmaA, ConstantInfo.toConstantVal, husl2]),
      Option.some.injEq] at hvte
    have hpp : m.cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams us) =
        .const .psigma
          [Level.substFn φ psigmaA.toConstantVal.levelParams us uN,
           Level.substFn φ psigmaA.toConstantVal.levelParams us vN] :=
      cval_pinned m (n := psigmaName) (by decide) (by rw [hpsig]; rfl) _
        (by simp +decide [pinnedDirectT])
    rw [← hvte, psigmaT, hpp]
  rw [hvteEq] at hpte
  rw [hlev uN] at hAs
  rw [hlev vN] at hBs
  -- the residual, and the rule
  rcases hpin with rfl | rfl
  · obtain rfl : i = 0 := hidx.1.symm
    obtain rfl : t = A := by
      rw [hargs2] at hres
      simpa [pairFstEntry, pairFstTyA, piResidual,
        Expr.instantiateLevelParams, Expr.instantiate1, Level.subst,
        Level.subst.go, psigmaName, Expr.instantiate1_eq_self hbA,
        Expr.instantiate1_eq_self hbB,
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 1) hbA),
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 2) hbA),
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 1) hbB),
        eq_comm] using hres
    exact ⟨.proj 0 VP, VA, by simp [denote_proj, hVP],
      hVA, HasType.projFst hAs hBs hpte⟩
  · obtain rfl : i = 1 := hidx.1.symm
    obtain rfl : t = .app B (.proj psigmaName 0 pe) := by
      rw [hargs2] at hres
      simpa [pairSndEntry, pairSndTyA, piResidual,
        Expr.instantiateLevelParams, Expr.instantiate1, Level.subst,
        Level.subst.go, psigmaName, Expr.instantiate1_eq_self hbA,
        Expr.instantiate1_eq_self hbB,
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 1) hbA),
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 2) hbA),
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 1) hbB),
        Expr.instantiate1_eq_self
          (Expr.looseBVarsBounded_mono (Nat.zero_le 2) hbB),
        eq_comm] using hres
    refine ⟨.proj 1 VP, .app VB (.proj 0 VP),
      by simp [denote_proj, hVP], ?_, HasType.projSnd hAs hBs hpte⟩
    rw [denote_app, hVB]
    simp [denote_proj, hVP]

/-- **`InferClaimsTT` at `fuel + 1`, with no outstanding obligation.**
The fourth quarter of `CheckStepTT` is closed. -/
theorem infer_claimsTT_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) :
    InferClaimsTT mode m φ (fuel + 1) :=
  infer_claimsTT m φ hcl (infer_strLit_step m φ)
    (infer_proj_step m φ hcl ihw ihd ihi) ihw ihd ihi

/-! ## The `whnfCore` projection clause

`ProjStepTT` (`Setlec/TTVerify/WhnfCoreStep.lean`).  Its chain is
shorter than iota's — `whnf` the scrutinee, expand a string literal,
then either reduce or stay stuck — and the reduction half's content is
already proved (`proj_tele_typed`, `psigmaMk_tele_premises`,
`proj_reduction_step`).  One link is a checker function without a
proof, so it gets the obligation. -/

/-- **The string-literal scrutinee expansion.**  `projLitToCtor`
replaces a `String` literal by its constructor form and is the identity
otherwise. -/
def ProjLitToCtorStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {e e' : Expr} {v : VExpr},
    projLitToCtorP mode env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → CtxOk m.cval env φ d Δ e →
    denote m.cval env φ d e = some v → ReductOk m φ d Δ e' v

/-- **`ProjStepTT`**, modulo the literal-expansion link. -/
theorem proj_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT mode m φ fuel) (ihw : WhnfClaimsTT mode m φ fuel)
    (ihd : DefEqClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel)
    (hlitp : ProjLitToCtorStepTT m φ fuel) : ProjStepTT m φ fuel := by
  intro d Δ sn i pe e' v h hws hb hLb hC hv
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := whnf_proj_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCpe : CtxOk m.cval env φ d Δ pe :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  rw [denote_proj] at hv
  cases hP : denote m.cval env φ d pe with
  | none => rw [hP] at hv; exact nomatch hv
  | some P =>
    rw [hP] at hv
    by_cases hlt : i < 2
    · simp only [if_pos hlt, Option.some.injEq] at hv
      obtain rfl : v = .proj i P := hv.symm
      -- the two links of the scrutinee's chain
      obtain ⟨P₂, hP₂, hD₂, hw₂, hb₂, hL₂, hC₂⟩ :=
        whnf_reductOk m φ ihw hwpe hws hb hLpe hCpe hP
      obtain ⟨P₃, hP₃, hD₃, hw₃, hb₃, hL₃, hC₃⟩ :=
        hlitp hlit hw₂ hb₂ hL₂ hC₂ hP₂
      rcases hcase with rfl | ⟨us, entry, hfn, hfp, hnat, hilt, hlenA,
        husl, hwarg, hcert, htele⟩
      · -- stuck: the projection is rebuilt on the reduced scrutinee
        exact ⟨.proj i P₃, by rw [denote_proj, hP₃]; exact if_pos hlt,
          Deq.proj i (hD₂.trans hD₃)⟩
      · -- the reduction: the scrutinee is a pair constructor
        obtain ⟨hpin, hpsig, hpsigMk⟩ :=
          m.proj_ok.1 _ _ (Env.findProj?_some hfp) hnat
        have hctor : entry.ctor = psigmaMkName := by
          rcases hpin with rfl | rfl <;> rfl
        have hnP : entry.numParams = 2 := by
          rcases hpin with rfl | rfl <;> rfl
        have hnF : entry.numFields = 2 := by
          rcases hpin with rfl | rfl <;> rfl
        -- the constructor spine, certified by task #126
        have hargs : ∀ x ∈ e₃.getAppArgs, Expr.WScoped d x ∧
            x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
            CtxOk m.cval env φ d Δ x := by
          intro x hx
          exact ⟨hw₃.getAppArgs x hx, looseBVarsBounded_getAppArgs hb₃ x hx,
            fun l hl => hL₃ l (fvarLeaves_getAppArgs hx l hl),
            CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hC₃⟩
        obtain ⟨TC, hTC⟩ := denote_storedTy m φ hcl hpsigMk us d
        simp only [ConstantInfo.toConstantVal] at hTC
        obtain ⟨hnfC, -, -, hbdC, -⟩ := m.wf _ (find?_mem hpsigMk)
        simp only [ConstantInfo.toConstantVal] at hnfC hbdC
        obtain ⟨xs, rest, hfit⟩ :=
          proj_tele_typed m φ hcl ihd ihi (hctor ▸ htele rfl) hpsigMk
            (Expr.WScoped.of_not_hasFvar (by
              rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC))
            (by rw [Expr.looseBVarsBounded_instantiateLevelParams]
                exact hbdC)
            (Expr.LeavesBounded.of_not_hasFvar (by
              rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC))
            (⟨hC.1, fun l hl => by
              rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
                rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC)] at hl
              exact nomatch hl⟩)
            hTC hargs
        -- the spine has exactly four entries
        obtain ⟨A, B, a, b, hargs4⟩ :
            ∃ A B a b, e₃.getAppArgs = [A, B, a, b] := by
          rw [hnP, hnF] at hlenA
          match hq : e₃.getAppArgs, hlenA with
          | [A, B, a, b], _ => exact ⟨A, B, a, b, rfl⟩
        rw [hargs4] at hfit
        obtain ⟨VA, VB, Va, Vb, hVA, hVB, hVa, hVb, hAs, hBs, has, hbs⟩ :=
          psigmaMk_tele_premises hfit
        -- the scrutinee's denotation is a pair constructor application
        have he₃ : e₃ = Expr.mkAppN (.const psigmaMkName us) [A, B, a, b] := by
          rw [← hargs4, ← hctor, ← hfn, Expr.mkAppN_getApp]
        have hpp : m.cval psigmaMkName
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams us) =
            .const .psigmaMk
              [Level.substFn φ psigmaMkA.toConstantVal.levelParams us uN,
               Level.substFn φ psigmaMkA.toConstantVal.levelParams us vN] :=
          cval_pinned m (n := psigmaMkName) (by decide)
            (by rw [hpsigMk]; rfl) _ (by simp +decide [pinnedDirectT])
        have hP₃' : P₃ = psigmaMkT
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams us uN)
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams us vN)
            VA VB Va Vb := by
          rw [he₃] at hP₃
          rw [denote_mkAppN (vf := m.cval psigmaMkName
              (Level.substFn φ psigmaMkA.toConstantVal.levelParams us))
            (DenoteSpine.cons hVA (DenoteSpine.cons hVB
              (DenoteSpine.cons hVa (DenoteSpine.cons hVb .nil))))
            (by rw [denote_const, hpsigMk]
                simp [psigmaMkA, ConstantInfo.toConstantVal,
                  show us.length = 2 from by
                    rw [husl]
                    rcases hpin with rfl | rfl <;> rfl])] at hP₃
          rw [← Option.some.inj hP₃, psigmaMkT, hpp]
        -- the level identification, then the reduction rule
        have hlev : ∀ nm : Name, (Level.subst
            psigmaMkA.toConstantVal.levelParams us (.param nm)).eval φ =
            Level.substFn φ psigmaMkA.toConstantVal.levelParams us nm := by
          intro nm
          rw [Level.eval_subst]
          rfl
        rw [hlev uN] at hAs
        rw [hlev vN] at hBs
        obtain ⟨hred0, hred1⟩ := proj_reduction_step hAs hBs has hbs
        -- the selected field, and the recursive call on it
        have hidx : entry.idx = i := by
          have h1 := List.find?_some (Env.findProj?_some hfp)
          have h2 : (ConstantInfo.projInfo entry).name = projFnName sn i :=
            eq_of_beq (by simpa using h1)
          simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
          exact (projFnName_inj h2).2
        have hsel : e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0) =
            if i = 0 then a else b := by
          rw [hargs4, hnP]
          rcases hpin with rfl | rfl
          · have hi : i = 0 := hidx.symm
            subst hi; rfl
          · have hi : i = 1 := hidx.symm
            subst hi; rfl
        rw [hsel] at hwarg
        by_cases hi0 : i = 0
        · subst hi0
          obtain ⟨w, hw, hDw⟩ :=
            ihwc hwarg (hargs a (by rw [hargs4]; simp)).1
              (hargs a (by rw [hargs4]; simp)).2.1
              (hargs a (by rw [hargs4]; simp)).2.2.1
              (hargs a (by rw [hargs4]; simp)).2.2.2 hVa
          exact ⟨w, hw, ((Deq.proj 0 (hD₂.trans hD₃)).trans
            (hP₃' ▸ hred0)).trans hDw⟩
        · obtain rfl : i = 1 := by omega
          rw [if_neg hi0] at hwarg
          obtain ⟨w, hw, hDw⟩ :=
            ihwc hwarg (hargs b (by rw [hargs4]; simp)).1
              (hargs b (by rw [hargs4]; simp)).2.1
              (hargs b (by rw [hargs4]; simp)).2.2.1
              (hargs b (by rw [hargs4]; simp)).2.2.2 hVb
          exact ⟨w, hw, ((Deq.proj 1 (hD₂.trans hD₃)).trans
            (hP₃' ▸ hred1)).trans hDw⟩
    · simp [hlt] at hv

end Setlec.TTVerify
