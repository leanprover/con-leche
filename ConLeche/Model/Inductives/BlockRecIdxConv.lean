module

public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitInst

public section

/-!
# The recursor's INDEX binders ARE the member's index telescope — at the model

Stage (b'') (`checkBlockRecIdxDomsAt`, `Kernel/Inductives/BlockInstall.lean`)
compares each recursor's index binder domains, binder by
binder, with the eliminated member's index telescope opened at the
recursor's own numbering (`openPisParamsIdx`).  This file is that
check's model side: the CONVERSE of the recursor type's index clause
(`blockRecIdxFit_run` is the forward one), which is what the kit
regimes' `hconclTy` needs — a carrier element's index values fit the
MEMBER's telescope, and the recursor's conclusion is licensed only at a
fit of the RECURSOR's binder data.

Two pieces (the pass's inversion is the family record's `idxDoms`,
`checkBlockRecIdxDomsAt_inv`, `Verify/Inductives/BlockRecRun.lean`):

* `defeqDom_agree_at` — ONE position of a binder-by-binder `isDefEq`,
  read at a context that is NOT an opening of either compared type.
  §35's certified hop (`prefixDoms_agree`) reads at the first
  opening's own context; here the two telescopes live at different
  numberings, so the context is built from the recursor's prefix and
  the member's (lifted) indices, and both subjects are correlated with
  it through `ctxOk_of_openers_congr`;
* `blockRecIdxConv_run` — the converse at the run, by induction on the
  index position; the parameter positions are §35's hop
  (`prefixDoms_agree` at the parameter comparison stage (b) makes).

**The frame.**  A `DefEqClaim` concludes at the frames satisfying the
context it was run under and nowhere else, and the context here is the
recursor's rule PREFIX followed by the member's indices.  So the
converse is stated at a prefix that FITS the recursor's prefix domains
— which is exactly what every consumer has in hand (the kit's class
index set is guarded by that fit, `blockRecIs_fits`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 2. One position of a comparison, at a context of its own -/

section Step

/-- **ONE position of a binder-by-binder `isDefEq`, read at a context
that is an opening of NEITHER compared telescope.**

The context `dC` is any domain list the caller has a FITTING spine of;
the two subjects' lists `LA`/`LB` are fvar lists at their own positions
(`fvar i` at position `i`) whose readings `dA`/`dB` agree with the
context below the position (`hagA`/`hagB`) at the frames those fitting
spines reach.  The claim then equates the two readings AT the position,
at the same frames.  §35's `prefixDoms_agree` is the special case where
the context is the first subject's own opening. -/
theorem defeqDom_agree_at {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {fuel N : Nat}
    {LA LB : List Expr} {dA dB dC : List AnnotTerm}
    (hlenC : dC.length = N) (hlenLA : LA.length ≤ N) (hlenLB : LB.length ≤ N)
    (hshA : ∀ (i : Nat) (x : Expr), LA[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hshB : ∀ (i : Nat) (x : Expr), LB[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hwA : ∀ (i : Nat) (x : Expr), LA[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x))
    (hwB : ∀ (i : Nat) (x : Expr), LB[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x))
    (hlbA : ∀ x ∈ LA, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hlbB : ∀ x ∈ LB, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hdA : ∀ (i : Nat) (x : Expr), LA[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (dA.getD i default))
    (hdB : ∀ (i : Nat) (x : Expr), LB[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (dB.getD i default))
    {l : Nat} (hl : l < N) {xA xB : Expr} (hxA : LA[l]? = some xA) (hxB : LB[l]? = some xB)
    (hleafA : ∀ lf ∈ (Expr.fvarTypeD xA).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LA)
    (hleafB : ∀ lf ∈ (Expr.fvarTypeD xB).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LB)
    (hdeq : ConLeche.isDefEqCore μ envT fuel N (Expr.fvarTypeD xA) (Expr.fvarTypeD xB)
      = .ok true)
    (hagA : ∀ i, i < l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
      interp V (consList (ys.take i) ρ) (dA.getD i default)
        = interp V (consList (ys.take i) ρ) (dC.getD i default))
    (hagB : ∀ i, i < l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
      interp V (consList (ys.take i) ρ) (dB.getD i default)
        = interp V (consList (ys.take i) ρ) (dC.getD i default))
    (hokA : ∀ i, i ≤ l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
      WellDenotedV V (consList (ys.take i) ρ) (dA.getD i default))
    (hokB : ∀ i, i ≤ l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
      WellDenotedV V (consList (ys.take i) ρ) (dB.getD i default)) :
    ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
      interp V (consList (ys.take l) ρ) (dA.getD l default)
        = interp V (consList (ys.take l) ρ) (dB.getD l default) := by
  obtain ⟨-, -, ihd, -⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) fuel
  have hentC : ∀ i, i < N → dC.reverse[N - 1 - i]? = some (dC.getD i default) :=
    fun i hi => getElem?_reverse_entry hlenC hi
  have hwsL : ∀ (L : List Expr), L.length ≤ N →
      (∀ (i : Nat) (x : Expr), L[i]? = some x → ∃ ty, x = Expr.fvar i ty) →
      (∀ (i : Nat) (x : Expr), L[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x)) →
      ∀ x ∈ L, Expr.WScoped N x := by
    intro L hlen hsh hw x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    have hil : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
    have hwi := hw i x hi
    obtain ⟨ty, rfl⟩ := hsh i _ hi
    have hty : Expr.WScoped i ty := hwi
    simpa [Expr.WScoped] using And.intro (show i < N by omega) hty
  -- frames satisfying the context are fitting spines' frames
  have hctx : ∀ (dS : List AnnotTerm) (LS : List Expr), LS.length ≤ N →
      (∀ (i : Nat) (x : Expr), LS[i]? = some x → ∃ ty, x = Expr.fvar i ty) →
      (∀ (i : Nat) (x : Expr), LS[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x)) →
      (∀ (i : Nat) (x : Expr), LS[i]? = some x →
        denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (dS.getD i default)) →
      ∀ (x : Expr), LS[l]? = some x →
      (∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LS) →
      (∀ i, i < l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
        interp V (consList (ys.take i) ρ) (dS.getD i default)
          = interp V (consList (ys.take i) ρ) (dC.getD i default)) →
      (∀ i, i ≤ l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
        WellDenotedV V (consList (ys.take i) ρ) (dS.getD i default)) →
      CtxOk mp.base2 ψ N dC.reverse (Expr.fvarTypeD x) := by
    intro dS LS hlen hsh hw hd x hx hleaf hag hok
    have hlt : ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, lf.1 < l := fun lf h =>
      Expr.fvarLeaves_lt_of_wscoped (hw l x hx) lf h
    refine ctxOk_of_openers_congr mp.base2.acval_closed (Aa := fun i => dC.getD i default)
      (Ba := fun i => dS.getD i default) (by simp [hlenC]) hsh (hwsL LS hlen hsh hw) hd
      hleaf hlt (fun i hi => hentC i (by omega)) ?_ ?_
    · intro i hi _ ρ hρ
      obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenC hρ
      rw [shiftE_consList_take i hzlen]
      exact hag i hi ρ₂ zs hfitZ
    · intro i hi _ ρ hρ
      obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenC hρ
      rw [shiftE_consList_take i hzlen]
      exact hok i (by omega) ρ₂ zs hfitZ
  have hctxA := hctx dA LA hlenLA hshA hwA hdA xA hxA hleafA hagA hokA
  have hctxB := hctx dB LB hlenLB hshB hwB hdB xB hxB hleafB hagB hokB
  -- the readings and the gradings at the context's depth
  have hrd : ∀ (dS : List AnnotTerm) (LS : List Expr) (x : Expr), LS[l]? = some x →
      (∀ (i : Nat) (x : Expr), LS[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x)) →
      (∀ (i : Nat) (x : Expr), LS[i]? = some x →
        denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (dS.getD i default)) →
      denoteMeta mp.base2.acval envT ψ N (Expr.fvarTypeD x)
        = some ((dS.getD l default).liftN (N - l) 0) := by
    intro dS LS x hx hw hd
    rw [denoteMeta_lift mp.base2.acval_closed (hw l x hx) N (by omega), hd l x hx]
    rfl
  have hokL : ∀ (dS : List AnnotTerm),
      (∀ i, i ≤ l → ∀ (ρ : Nat → V) (ys : List V), SpineFit ρ dC ys →
        WellDenotedV V (consList (ys.take i) ρ) (dS.getD i default)) →
      ∀ ρ : Nat → V, Sat V dC.reverse ρ →
        WellDenotedV V ρ ((dS.getD l default).liftN (N - l) 0) := by
    intro dS hok ρ hρ
    refine (WellDenotedV_liftN V (N - l) _ 0 ρ).mpr ?_
    obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenC hρ
    rw [shiftE_consList_take l hzlen]
    exact hok l (Nat.le_refl _) ρ₂ zs hfitZ
  intro ρ ys hfit
  have hylen : ys.length = N := by rw [hfit.length_eq, hlenC]
  have hsat : Sat V dC.reverse (consList ys ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfit
  have heq := ihd hdeq ((hwA l xA hxA).mono (by omega)) (hlbA xA (List.mem_of_getElem? hxA))
    (leavesBounded_of_openers hlbA hleafA) ((hwB l xB hxB).mono (by omega))
    (hlbB xB (List.mem_of_getElem? hxB)) (leavesBounded_of_openers hlbB hleafB)
    hctxA hctxB (hrd dA LA xA hxA hwA hdA) (hrd dB LB xB hxB hwB hdB)
    (hokL dA hokA) (hokL dB hokB) (consList ys ρ) hsat
  rw [interp_liftN, interp_liftN, shiftE_consList_take l hylen] at heq
  exact heq

end Step

/-! ## 3. Small list and frame helpers -/

section Helpers

omit [SetTheory V] in
theorem getD_append_lt' {L₁ L₂ : List AnnotTerm} {i : Nat} (h : i < L₁.length) :
    (L₁ ++ L₂).getD i default = L₁.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

omit [SetTheory V] in
theorem getD_append_ge' {L₁ L₂ : List AnnotTerm} {i : Nat} (h : L₁.length ≤ i) :
    (L₁ ++ L₂).getD i default = L₂.getD (i - L₁.length) default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

omit [SetTheory V] in
theorem getD_take' {L : List AnnotTerm} {n i : Nat} (h : i < n) :
    (L.take n).getD i default = L.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

omit [SetTheory V] in
theorem getD_drop' {L : List AnnotTerm} {n i : Nat} :
    (L.drop n).getD i default = L.getD (n + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

omit [SetTheory V] in
/-- A `liftDomsK` entry is the entry lifted at its own cutoff. -/
theorem liftDomsK_getD (K : Nat) :
    ∀ (k : Nat) (Ds : List AnnotTerm) (l : Nat), l < Ds.length →
      (liftDomsK K k Ds).getD l default = (Ds.getD l default).liftN K (k + l)
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | k, D :: Ds, 0, _ => by simp [liftDomsK]
  | k, D :: Ds, l + 1, h => by
    show (liftDomsK K (k + 1) Ds).getD l default = _
    rw [liftDomsK_getD K (k + 1) Ds l (by simpa using h)]
    simp only [List.getD_cons_succ]
    rw [show k + 1 + l = k + (l + 1) from by omega]

omit [SetTheory V] in
theorem getD_map_of_getElem? {L : List Expr} {q : Nat} {x : Expr} (h : L[q]? = some x) :
    (L.map Expr.fvarTypeD).getD q default = Expr.fvarTypeD x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]; rfl

/-- **A fit crosses the recursor prefix's extra binders**: the member's
index telescope read at the parameter frame and its `rP − nP`-lifted
copy read at the whole prefix have the same fitting spines. -/
theorem spineFit_liftIdx {rP nP : Nat} {ρ : Nat → V} {xs vs : List V}
    (hxs : xs.length = rP) (Fs : List AnnotTerm) :
    SpineFit (consList xs ρ) (liftDomsK (rP - nP) 0 Fs) vs
      ↔ SpineFit (consList (xs.take nP) ρ) Fs vs := by
  have hsplit : consList xs ρ = consList (xs.drop nP) (consList (xs.take nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hlen : (xs.drop nP).length = rP - nP := by rw [List.length_drop, hxs]
  rw [hsplit, ← hlen]
  have hq := spineFit_liftDomsK_insert (us := xs.drop nP) (ρ := consList (xs.take nP) ρ)
    Fs [] vs
  simpa using hq

end Helpers

/-! ## 4. The converse at the run -/

section Run

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V}

set_option maxHeartbeats 2000000 in
/-- **THE INDEX CLAUSE'S CONVERSE, at the run** (stage (b'')'s check;
`blockRecIdxFit_run` is the forward direction).  At a prefix
that FITS the recursor's rule-prefix domains, index values fitting the
eliminated MEMBER's index telescope fit the RECURSOR's index binders.

The context the comparison is read at is the recursor's prefix
followed by the member's lifted indices (`dC` below); its fitting
spines are exactly `x⃗ ++ ı⃗` with the two hypotheses, which is why the
statement carries the prefix fit and nothing more. -/
theorem blockRecIdxConv_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs is : List V,
      SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take (p.toBlockShape.rulePrefixAt c)) xs →
      SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is →
      SpineFit (consList xs ρ)
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          (p.toBlockShape.rulePrefixAt c)).take
            (d.IdsM (p.toBlockShape.recTgtAt c) ψ).length) is := by
  intro xs is hxfit hisfit
  obtain ⟨hnPle, hmemk, hmI, hlenRds, -⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  have hlenIds := blockMembers_IdsM_length hmr hmemk ψ
  obtain ⟨hnPq, -, -, hcvF, -, -, -⟩ := hmr
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hcvTa := TE.hcvTa
  have hop := TE.hopen
  have hopT := TE.hopenT
  have htfl := TE.htfvs
  have hdeqP := TE.hparams
  obtain ⟨fvsL, conclL, hopL, -, hmk, -, -, hbind, -, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = TE.fvs := congrArg Prod.fst (Option.some.inj (hopL.symm.trans hop))
  rw [hfvE] at hbind
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvTa
  obtain ⟨hwR, hbR⟩ := recStage_tyClosed h hr
  have hwT : Expr.WScoped 0 TE.cvTa.type := Expr.WScoped.of_not_hasFvar hfvT
  -- names
  generalize hrP : p.toBlockShape.rulePrefixAt c = rP at *
  generalize hmm : p.toBlockShape.recTgtAt c = mm at *
  generalize hnI : d.nIdxAt mm = nI at *
  have hnP' : d.nP = p.nP := hnPq
  rw [hnP'] at hnPle hisfit
  -- the kernel's pass, at this recursor
  have hc : c < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨R⟩ := id h
  have hcR : c < R.cvRus.length := by rw [R.lenT, ← R.len]; exact hc
  obtain ⟨cvR, nIdx, u, cvTa', fvs', tfvs, concl', trest, hcu, hcvTa', hop', hopPI, -,
    hdeqI⟩ := R.fam.idxDoms c hcR
  obtain ⟨u', hcu'⟩ := R.stored_at hr
  obtain ⟨hr1, hnn, -⟩ : cvR = r.1 ∧ nIdx = r.2.2.1 ∧ u = u' := by
    simpa using Option.some.inj (hcu.symm.trans hcu')
  rw [hr1] at hop'
  obtain ⟨rfl, rfl⟩ : fvs' = TE.fvs ∧ concl' = TE.concl := by
    have := Option.some.inj (hop'.symm.trans hop)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  rw [hmm] at hcvTa'
  have hcvE : cvTa' = TE.cvTa := Option.some.inj (hcvTa'.symm.trans hcvTa)
  rw [hcvE] at hopPI
  obtain ⟨rc, u'', -, -, ⟨E⟩⟩ := R.tyAt hr
  have hmaj' := E.mI_eq
  have hnIdx : nIdx = nI := by
    have : p.toBlockShape.majorIdxAt c = rP + nI := hmI
    rw [hrP] at hmaj'
    omega
  rw [hnIdx, hrP] at hopPI hdeqI
  -- the member's opening at the recursor's numbering
  obtain ⟨ifvs, hopI, htfvs⟩ : ∃ ifvs, openPisAtFvars nI TE.trest rP = some (ifvs, trest) ∧
      tfvs = TE.tfvs ++ ifvs := by
    unfold ConLeche.openPisParamsIdx at hopPI
    rw [hopT] at hopPI
    cases h2 : openPisAtFvars nI TE.trest rP with
    | none => simp [h2] at hopPI
    | some pr =>
      obtain ⟨ifvs, tr⟩ := pr
      simp only [h2, Option.some.injEq, Prod.mk.injEq] at hopPI
      obtain ⟨rfl, rfl⟩ := hopPI
      exact ⟨ifvs, rfl, rfl⟩
  subst htfvs
  have hdropT : (TE.tfvs ++ ifvs).drop p.nP = ifvs := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
  rw [hdropT] at hdeqI
  have hlenF : TE.fvs.length = rP + nI + 1 := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop, hmI]
  have hlenIf : ifvs.length = nI := ConLeche.Verify.openPisAtFvars_length _ hopI
  rw [hmI] at hlenRds hop hdeqI
  -- the recursor's binder data, and its grading
  generalize hRds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c = rds at *
  generalize hCc : blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c = cc at hmk
  have hwdR : ∀ ρ' : Nat → V, WellDenotedV V ρ' (mkPisAV rds cc) := fun ρ' => by
    rw [← hmk]; exact hwdTy ρ'
  obtain ⟨dR, hdR⟩ : ∃ L, L = rds.map (·.2.2) := ⟨_, rfl⟩
  have hlR : dR.length = rP + nI + 1 := by rw [hdR, List.length_map, hlenRds]
  have gradR : ∀ i, i < rP + nI + 1 → ∀ (ρ' : Nat → V) (zs : List V),
      SpineFit ρ' (dR.take i) zs → WellDenotedV V (consList zs ρ') (dR.getD i default) := by
    intro i hi ρ' zs hzs
    have := prefixDoms_graded_of_tower (V := V) (rds := rds) (cc := cc) (rP := rds.length)
      (Nat.le_refl _) hwdR (l := i) (by omega) (ρ := ρ') (ys := zs)
      (by rw [List.take_length, ← hdR]; exact hzs)
    rwa [List.take_length, ← hdR] at this
  -- the member's telescope, its readings and its grading
  obtain ⟨ppsT, bT, hstT, hbT, -, hbindT⟩ := denoteMeta_openPis (acval := mpC.base2.acval)
    (env := envC) (φ := ψ) p.nP hopT (hFD.read ψ)
  have hppsLen : (d.ppsM mm ψ).length = p.nP + nI := by rw [hFD.len ψ, hnP']
  rw [stripPisAV_mkPisAV_take p.nP _ _ (by omega)] at hstT
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstT)
  rw [Nat.zero_add] at hbT
  have hwTo : Expr.WScoped p.nP TE.trest := by
    have := (ConLeche.openPisAtFvars_WScoped p.nP TE.cvTa.type 0 hopT hwT).2
    rwa [Nat.zero_add] at this
  have hopI' : openPisAtFvars nI TE.trest (p.nP + (rP - p.nP)) = some (ifvs, trest) := by
    rw [show p.nP + (rP - p.nP) = rP from by omega]; exact hopI
  obtain ⟨-, -, hrdI⟩ := readOpenedDoms_shift (m := mpC.base2) (ψ := ψ) (o := rP - p.nP)
    hbT hwTo hppsLen (Expr.ErasedEq.rfl _) hopI'
  have hIds : d.IdsM mm ψ = ((d.ppsM mm ψ).drop p.nP).map (·.2.2) := by
    rw [BlockData.IdsM, hnP']
  rw [← hIds] at hrdI
  obtain ⟨dPP, hdPP⟩ : ∃ L, L = (d.ppsM mm ψ).map (·.2.2) := ⟨_, rfl⟩
  have gradPP : ∀ i, i < p.nP + nI → ∀ (ρ' : Nat → V) (zs : List V),
      SpineFit ρ' (dPP.take i) zs → WellDenotedV V (consList zs ρ') (dPP.getD i default) := by
    intro i hi ρ' zs hzs
    have := prefixDoms_graded_of_tower (V := V) (rds := d.ppsM mm ψ)
      (cc := .sort (d.resSort.eval ψ)) (rP := (d.ppsM mm ψ).length) (Nat.le_refl _)
      (hFD.okTy ψ) (l := i) (by omega) (ρ := ρ') (ys := zs)
      (by rw [List.take_length, ← hdPP]; exact hzs)
    rwa [List.take_length, ← hdPP] at this
  obtain ⟨dP, hdP⟩ : ∃ L, L = dPP.take p.nP := ⟨_, rfl⟩
  have hdP' : ((d.ppsM mm ψ).take p.nP).map (·.2.2) = dP := by
    rw [hdP, hdPP, List.map_take]
  have hlP : dP.length = p.nP := by rw [hdP, List.length_take, hdPP, List.length_map]; omega
  have hIds' : d.IdsM mm ψ = dPP.drop p.nP := by rw [hIds, hdPP, List.map_drop]
  obtain ⟨dI, hdI⟩ : ∃ L, L = liftDomsK (rP - p.nP) 0 (d.IdsM mm ψ) := ⟨_, rfl⟩
  have hlI : dI.length = nI := by rw [hdI, liftDomsK_length, hlenIds]
  have hdIget : ∀ q, q < nI →
      dI.getD q default = (dPP.getD (p.nP + q) default).liftN (rP - p.nP) q := by
    intro q hq
    rw [hdI, liftDomsK_getD _ _ _ _ (by rw [hlenIds]; exact hq), hIds', getD_drop',
      Nat.zero_add]
  -- the context and the member's side
  obtain ⟨dC, hdC⟩ : ∃ L, L = dR.take rP ++ dI := ⟨_, rfl⟩
  obtain ⟨dM, hdM⟩ : ∃ L, L = dP ++ (dR.drop p.nP).take (rP - p.nP) ++ dI := ⟨_, rfl⟩
  have hlC : dC.length = rP + nI := by
    rw [hdC, List.length_append, List.length_take, hlR, hlI]; omega
  have hltake : (dR.take rP).length = rP := by rw [List.length_take, hlR]; omega
  have hlPM : (dP ++ (dR.drop p.nP).take (rP - p.nP)).length = rP := by
    rw [List.length_append, hlP, List.length_take, List.length_drop, hlR]; omega
  have C_lt : ∀ i, i < rP → dC.getD i default = dR.getD i default := fun i hi => by
    rw [hdC, getD_append_lt' (by rw [hltake]; exact hi), getD_take' hi]
  have C_ge : ∀ i, rP ≤ i → dC.getD i default = dI.getD (i - rP) default := fun i hi => by
    rw [hdC, getD_append_ge' (by rw [hltake]; exact hi), hltake]
  have M_lt : ∀ i, i < p.nP → dM.getD i default = dP.getD i default := fun i hi => by
    rw [hdM, getD_append_lt' (by rw [hlPM]; omega), getD_append_lt' (by rw [hlP]; exact hi)]
  have M_mid : ∀ i, p.nP ≤ i → i < rP → dM.getD i default = dR.getD i default :=
    fun i h1 h2 => by
      rw [hdM, getD_append_lt' (by rw [hlPM]; exact h2),
        getD_append_ge' (by rw [hlP]; exact h1), hlP, getD_take' (by omega), getD_drop',
        show p.nP + (i - p.nP) = i from by omega]
  have M_ge : ∀ i, rP ≤ i → dM.getD i default = dI.getD (i - rP) default := fun i hi => by
    rw [hdM, getD_append_ge' (by rw [hlPM]; exact hi), hlPM]
  have P_get : ∀ i, i < p.nP → dP.getD i default = dPP.getD i default := fun i hi => by
    rw [hdP, getD_take' hi]
  rw [← hdI] at hrdI
  -- the two fvar lists
  have hidxR := ConLeche.openPisAtFvars_index _ _ _ hop
  have hidxT := ConLeche.openPisAtFvars_index _ _ _ hopT
  have hidxI := ConLeche.openPisAtFvars_index _ _ _ hopI
  have hwsR := fun i x hx => openPisAtFvars_typeWScoped _ hop hwR i x hx
  have hwsT := fun i x hx => openPisAtFvars_typeWScoped _ hopT hwT i x hx
  have hwsI := fun i x hx => openPisAtFvars_typeWScoped _ hopI (hwTo.mono (by omega)) i x hx
  have hlbRl := (ConLeche.Verify.openPisAtFvars_bounded _ hop hbR).2
  have hlbTl := (ConLeche.Verify.openPisAtFvars_bounded _ hopT hbndT).2
  have hlbIl := (ConLeche.Verify.openPisAtFvars_bounded _ hopI
    (ConLeche.Verify.openPisAtFvars_bounded _ hopT hbndT).1).2
  obtain ⟨LR, hLR⟩ : ∃ L, L = TE.fvs.take (rP + nI) := ⟨_, rfl⟩
  obtain ⟨LM, hLM⟩ : ∃ L, L = TE.tfvs ++ (TE.fvs.drop p.nP).take (rP - p.nP) ++ ifvs := ⟨_, rfl⟩
  have hLRget : ∀ i x, LR[i]? = some x → i < rP + nI ∧ TE.fvs[i]? = some x := by
    intro i x hx
    rw [hLR, List.getElem?_take] at hx
    by_cases hi : i < rP + nI
    · rw [if_pos hi] at hx; exact ⟨hi, hx⟩
    · rw [if_neg hi] at hx; exact absurd hx (by simp)
  have hlenMid : ((TE.fvs.drop p.nP).take (rP - p.nP)).length = rP - p.nP := by
    rw [List.length_take, List.length_drop, hlenF]; omega
  have hLMget : ∀ i x, LM[i]? = some x →
      (i < p.nP ∧ TE.tfvs[i]? = some x) ∨ (p.nP ≤ i ∧ i < rP ∧ TE.fvs[i]? = some x) ∨
        (rP ≤ i ∧ ifvs[i - rP]? = some x) := by
    intro i x hx
    rw [hLM] at hx
    by_cases h1 : i < rP
    · rw [List.getElem?_append_left (by rw [List.length_append, htfl, hlenMid]; omega)] at hx
      by_cases h2 : i < p.nP
      · rw [List.getElem?_append_left (by rw [htfl]; exact h2)] at hx
        exact Or.inl ⟨h2, hx⟩
      · rw [List.getElem?_append_right (by rw [htfl]; omega), htfl, List.getElem?_take,
          if_pos (by omega), List.getElem?_drop,
          show p.nP + (i - p.nP) = i from by omega] at hx
        exact Or.inr (Or.inl ⟨by omega, h1, hx⟩)
    · rw [List.getElem?_append_right (by rw [List.length_append, htfl, hlenMid]; omega),
        List.length_append, htfl, hlenMid, show p.nP + (rP - p.nP) = rP from by omega] at hx
      exact Or.inr (Or.inr ⟨by omega, hx⟩)
  have hlenLR : LR.length ≤ rP + nI := by rw [hLR, List.length_take]; omega
  have hlenLM : LM.length ≤ rP + nI := by
    rw [hLM, List.length_append, List.length_append, htfl, hlenMid, hlenIf]; omega
  have shR : ∀ i x, LR[i]? = some x → ∃ ty, x = Expr.fvar i ty := fun i x hx => by
    obtain ⟨ty, h⟩ := hidxR i x (hLRget i x hx).2; exact ⟨ty, by simpa using h⟩
  have shM : ∀ i x, LM[i]? = some x → ∃ ty, x = Expr.fvar i ty := fun i x hx => by
    rcases hLMget i x hx with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨h1, h⟩
    · obtain ⟨ty, h'⟩ := hidxT i x h; exact ⟨ty, by simpa using h'⟩
    · obtain ⟨ty, h'⟩ := hidxR i x h; exact ⟨ty, by simpa using h'⟩
    · obtain ⟨ty, h'⟩ := hidxI _ x h; exact ⟨ty, by rw [h']; congr 1; omega⟩
  have wR : ∀ i x, LR[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x) := fun i x hx => by
    simpa using hwsR i x (hLRget i x hx).2
  have wM : ∀ i x, LM[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x) := fun i x hx => by
    rcases hLMget i x hx with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨h1, h⟩
    · simpa using hwsT i x h
    · simpa using hwsR i x h
    · have := hwsI _ x h; rwa [show rP + (i - rP) = i from by omega] at this
  have lbR : ∀ x ∈ LR, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := fun x hx =>
    hlbRl x (by rw [hLR] at hx; exact List.mem_of_mem_take hx)
  have lbM : ∀ x ∈ LM, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rw [hLM] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hlbTl x hx
      · exact hlbRl x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    · exact hlbIl x hx
  have rdR : ∀ i x, LR[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (dR.getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hbind i x (hLRget i x hx).2
    rw [hrd, hdR, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  have rdM : ∀ i x, LM[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (dM.getD i default) := by
    intro i x hx
    rcases hLMget i x hx with ⟨h1, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h⟩
    · obtain ⟨pd, hpd, -, hrd⟩ := hbindT i x h
      rw [Nat.zero_add] at hrd
      rw [hrd, M_lt i h1, ← hdP', List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
    · obtain ⟨pd, hpd, -, hrd⟩ := hbind i x h
      rw [hrd, M_mid i h1 h2, hdR, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
    · have := hrdI _ x h
      rw [show p.nP + (rP - p.nP) + (i - rP) = i from by omega] at this
      rw [this, M_ge i h1]
  -- the parameter comparison (stage (b)), as §35's READING half
  obtain ⟨fvsA, fvsRest, oA, hopA, -, hfvsplit⟩ :=
    openPisAtFvars_split (e := r.1.type) (d := 0) p.nP
      (by rw [show p.nP + (rP + nI + 1 - p.nP) = rP + nI + 1 from by omega]; exact hop)
  have hlenA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hfvsA : TE.fvs.take p.nP = fvsA := by
    rw [hfvsplit, List.take_append_of_le_length (Nat.le_of_eq hlenA.symm),
      List.take_of_length_le (Nat.le_of_eq hlenA)]
  have hdA0 : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((dR.take p.nP).getD i default) := by
    intro i x hx
    have hi : i < p.nP := by have := (List.getElem?_eq_some_iff.mp hx).1; omega
    have hx' : TE.fvs[i]? = some x := by
      rw [← hfvsA, List.getElem?_take, if_pos hi] at hx; exact hx
    obtain ⟨pd, hpd, -, hrd⟩ := hbind i x hx'
    rw [hrd, getD_take' hi, hdR, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  have hdB0 : ∀ (i : Nat) (x : Expr), TE.tfvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (dP.getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hbindT i x hx
    rw [Nat.zero_add] at hrd
    rw [hrd, ← hdP', List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  have hokA0 : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((dR.take p.nP).take i) ys →
      WellDenotedV V (consList ys ρ') ((dR.take p.nP).getD i default) := by
    intro i hi ρ' ys hys
    rw [getD_take' hi]
    rw [List.take_take, show min i p.nP = i from by omega] at hys
    exact gradR i (by omega) ρ' ys hys
  have hokB0 : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' (dP.take i) ys → WellDenotedV V (consList ys ρ') (dP.getD i default) := by
    intro i hi ρ' ys hys
    rw [P_get i hi]
    rw [hdP, List.take_take, show min i p.nP = i from by omega] at hys
    exact gradPP i (by omega) ρ' ys hys
  have PA0 := prefixDoms_agree (V := V) hμ mpC hopA hopT hwR hwT hbR hbndT
    (by rw [List.length_take, hlR]; omega) hlP hdA0 hdB0 hokA0 hokB0
    (fun l hl => Or.inr (by rw [← hfvsA]; exact hdeqP l hl))
  have hCtake : dC.take p.nP = dR.take p.nP := by
    rw [hdC, List.take_append_of_le_length (by rw [hltake]; omega), List.take_take,
      show min p.nP rP = p.nP from by omega]
  have PA : ∀ i, i < p.nP → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
      interp V (consList (ys.take i) ρ₁) (dP.getD i default)
        = interp V (consList (ys.take i) ρ₁) (dR.getD i default) := by
    intro i hi ρ₁ ys hfit
    have hfit' : SpineFit ρ₁ (dR.take p.nP) (ys.take p.nP) := by
      rw [← hCtake]; exact spineFit_take hfit (by rw [hlC]; omega)
    have := PA0 i hi ρ₁ (ys.take p.nP) hfit'
    rw [List.take_take, show min i p.nP = i from by omega, getD_take' hi] at this
    exact this.symm
  -- the context splits into the prefix and the member's indices
  have hsplitC : ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
      SpineFit (consList (ys.take p.nP) ρ₁) (d.IdsM mm ψ) (ys.drop rP) := by
    intro ρ₁ ys hfit
    rw [hdC] at hfit
    obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split hfit
    have hl1 : as₁.length = rP := by rw [h1.length_eq, hltake]
    have e1 : ys.take rP = as₁ := by rw [heq]; exact List.take_left' hl1
    have e2 : ys.drop rP = as₂ := by rw [heq]; exact List.drop_left' hl1
    rw [e2, show ys.take p.nP = as₁.take p.nP from by
      rw [← e1, List.take_take, show min p.nP rP = p.nP from by omega]]
    rw [hdI] at h2
    exact (spineFit_liftIdx hl1 _).mp h2
  -- leaves
  have leafI : ∀ (q : Nat) (x : Expr), ifvs[q]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LM := by
    intro q x hx lf hlf
    obtain ⟨ty, hty⟩ := hidxI q x hx
    have hxx : lf ∈ x.fvarLeaves := by
      rw [hty] at hlf ⊢
      simp only [Expr.fvarTypeD] at hlf
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hlf
    rcases openPisAtFvars_leaves nI hopI lf (Or.inr ⟨x, List.mem_of_getElem? hx, hxx⟩) with
      h' | h'
    · rcases openPisAtFvars_leaves p.nP hopT lf (Or.inl h') with h'' | h''
      · exact absurd (Expr.fvarLeaves_lt_of_wscoped hwT lf h'') (Nat.not_lt_zero _)
      · rw [hLM]; exact List.mem_append_left _ (List.mem_append_left _ h'')
    · rw [hLM]; exact List.mem_append_right _ h'
  have leafR : ∀ (i : Nat) (x : Expr), i < rP + nI → TE.fvs[i]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LR := by
    intro i x hi hx lf hlf
    have hm := openerType_leaves hop hwR hx lf hlf
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
    obtain ⟨ty, hty⟩ := hidxR k _ hk
    have hkl : lf.1 = 0 + k := by injection hty
    have hlt : lf.1 < i := Expr.fvarLeaves_lt_of_wscoped (by simpa using hwsR i x hx) lf hlf
    rw [hLR]
    exact List.mem_of_getElem? (show (TE.fvs.take (rP + nI))[k]? = some _ from by
      rw [List.getElem?_take, if_pos (by omega)]; exact hk)
  -- THE INDUCTION on the index position
  have agreeI : ∀ q, q < nI → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
      interp V (consList (ys.take (rP + q)) ρ₁) (dC.getD (rP + q) default)
        = interp V (consList (ys.take (rP + q)) ρ₁) (dR.getD (rP + q) default) := by
    intro q
    induction q using Nat.strongRecOn with
    | _ q IH =>
    intro hq
    have hbelow : ∀ i, i < rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        interp V (consList (ys.take i) ρ₁) (dR.getD i default)
          = interp V (consList (ys.take i) ρ₁) (dC.getD i default) := by
      intro i hi ρ₁ ys hfit
      by_cases h1 : i < rP
      · rw [C_lt i h1]
      · have := IH (i - rP) (by omega) (by omega) ρ₁ ys hfit
        rw [show rP + (i - rP) = i from by omega] at this
        exact this.symm
    have fitR : ∀ i, i ≤ rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        SpineFit ρ₁ (dR.take i) (ys.take i) := by
      intro i hi ρ₁ ys hfit
      refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlC, hlR]; omega)
        ?_ (spineFit_take hfit (by rw [hlC]; omega))
      intro l hl
      rw [List.length_take] at hl
      rw [getD_take' (show l < i by omega), getD_take' (show l < i by omega), List.take_take,
        show min l i = l from by omega]
      exact (hbelow l (by omega) ρ₁ ys hfit).symm
    have fitP : ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        SpineFit ρ₁ dP (ys.take p.nP) := by
      intro ρ₁ ys hfit
      have h0 := fitR p.nP (by omega) ρ₁ ys hfit
      refine spineFit_congr_walk (by rw [List.length_take, hlR, hlP]; omega) ?_ h0
      intro l hl
      rw [List.length_take] at hl
      rw [getD_take' (show l < p.nP by omega), List.take_take, show min l p.nP = l from by omega]
      exact (PA l (by omega) ρ₁ ys hfit).symm
    -- the two subjects
    obtain ⟨xA, hxA⟩ : ∃ x, ifvs[q]? = some x :=
      ⟨ifvs[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨xB, hxB⟩ : ∃ x, TE.fvs[rP + q]? = some x :=
      ⟨TE.fvs[rP + q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hxA' : LM[rP + q]? = some xA := by
      rw [hLM, List.getElem?_append_right (by rw [List.length_append, htfl, hlenMid]; omega),
        List.length_append, htfl, hlenMid, show rP + q - (p.nP + (rP - p.nP)) = q from by omega]
      exact hxA
    have hxB' : LR[rP + q]? = some xB := by
      rw [hLR, List.getElem?_take, if_pos (by omega)]; exact hxB
    have hdeq : ConLeche.isDefEqCore μ envC F (rP + nI) (Expr.fvarTypeD xA)
        (Expr.fvarTypeD xB) = .ok true := by
      have h0 := hdeqI q (by rw [List.length_map, hlenIf]; exact hq)
      rw [getD_map_of_getElem? hxA, getD_map_of_getElem? (show
        (List.take nI (List.drop rP TE.fvs))[q]? = some xB from by
          rw [List.getElem?_take, if_pos hq, List.getElem?_drop]; exact hxB)] at h0
      exact h0
    -- the member's side agrees with the context below the position
    have hagM : ∀ i, i < rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        interp V (consList (ys.take i) ρ₁) (dM.getD i default)
          = interp V (consList (ys.take i) ρ₁) (dC.getD i default) := by
      intro i hi ρ₁ ys hfit
      by_cases h1 : i < p.nP
      · rw [M_lt i h1, C_lt i (by omega)]; exact PA i h1 ρ₁ ys hfit
      · by_cases h2 : i < rP
        · rw [M_mid i (by omega) h2, C_lt i h2]
        · rw [M_ge i (by omega), C_ge i (by omega)]
    have hagR : ∀ i, i < rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        interp V (consList (ys.take i) ρ₁) (dR.getD i default)
          = interp V (consList (ys.take i) ρ₁) (dC.getD i default) := hbelow
    have hokR : ∀ i, i ≤ rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        WellDenotedV V (consList (ys.take i) ρ₁) (dR.getD i default) := fun i hi ρ₁ ys hfit =>
      gradR i (by omega) ρ₁ (ys.take i) (fitR i hi ρ₁ ys hfit)
    have hokM : ∀ i, i ≤ rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        WellDenotedV V (consList (ys.take i) ρ₁) (dM.getD i default) := by
      intro i hi ρ₁ ys hfit
      by_cases h1 : i < p.nP
      · rw [M_lt i h1, P_get i h1]
        have h0 := spineFit_take (fitP ρ₁ ys hfit) (i := i) (by rw [hlP]; omega)
        rw [hdP, List.take_take, show min i p.nP = i from by omega, List.take_take,
          show min i p.nP = i from by omega] at h0
        exact gradPP i (by omega) ρ₁ (ys.take i) h0
      · by_cases h2 : i < rP
        · rw [M_mid i (by omega) h2]
          exact gradR i (by omega) ρ₁ (ys.take i) (fitR i (by omega) ρ₁ ys hfit)
        · -- an index position: the member's own index domain, lifted
          have hq' : i - rP < nI := by omega
          rw [M_ge i (by omega), hdIget _ hq']
          refine (WellDenotedV_liftN V (rP - p.nP) _ (i - rP) _).mpr ?_
          have hylen : ys.length = rP + nI := by rw [hfit.length_eq, hlC]
          have hsplitY : ys.take i
              = (ys.take p.nP ++ (ys.take rP).drop p.nP) ++ (ys.drop rP).take (i - rP) := by
            rw [show (ys.take p.nP) = (ys.take rP).take p.nP from by
                rw [List.take_take, show min p.nP rP = p.nP from by omega],
              List.take_append_drop]
            rw [show i = rP + (i - rP) from by omega, List.take_add]
            rw [show rP + (i - rP) - rP = i - rP from by omega]
          have hlenB : ((ys.drop rP).take (i - rP)).length = i - rP := by
            rw [List.length_take, List.length_drop, hylen]; omega
          have hlenD : ((ys.take rP).drop p.nP).length = rP - p.nP := by
            rw [List.length_drop, List.length_take, hylen]; omega
          rw [hsplitY, consList_append, consList_append, shiftE_consList_ih hlenB hlenD,
            ← consList_append]
          refine gradPP (p.nP + (i - rP)) (by omega) ρ₁ _ ?_
          have hdPPsplit : dPP.take (p.nP + (i - rP)) = dP ++ (d.IdsM mm ψ).take (i - rP) := by
            rw [List.take_add, hdP, hIds']
          rw [hdPPsplit]
          exact SpineFit.append (fitP ρ₁ ys hfit)
            (spineFit_take_any (hsplitC ρ₁ ys hfit) (i - rP))
    have key := defeqDom_agree_at (V := V) hμ mpC (fuel := F) (N := rP + nI)
      (LA := LM) (LB := LR) (dA := dM) (dB := dR) (dC := dC) hlC hlenLM hlenLR shM shR wM wR
      lbM lbR rdM rdR (l := rP + q) (by omega) hxA' hxB' (leafI q xA hxA)
      (leafR (rP + q) xB (by omega) hxB) hdeq hagM hagR hokM hokR
    intro ρ₁ ys hfit
    have h0 := key ρ₁ ys hfit
    rw [M_ge _ (by omega), Nat.add_sub_cancel_left] at h0
    rw [C_ge _ (by omega), Nat.add_sub_cancel_left]
    exact h0
  -- the spine `x⃗ ++ ı⃗` fits the context, and the walk
  have hxlen : xs.length = rP := by
    rw [hxfit.length_eq, List.length_take, List.length_map, hlenRds]; omega
  have hisI : SpineFit (consList xs ρ) dI is := by
    rw [hdI]; exact (spineFit_liftIdx hxlen _).mpr hisfit
  have hfitC : SpineFit ρ dC (xs ++ is) := by
    rw [hdC]
    exact SpineFit.append (by rw [hdR]; exact hxfit) hisI
  rw [hlenIds, ← hdR]
  refine spineFit_congr_walk (by rw [hlI, List.length_take, List.length_drop, hlR]; omega)
    ?_ hisI
  intro q hq
  rw [hlI] at hq
  have e1 : consList (is.take q) (consList xs ρ) = consList ((xs ++ is).take (rP + q)) ρ := by
    rw [← hxlen, List.take_length_add_append, consList_append]
  rw [e1, getD_take' hq, getD_drop', ← Nat.add_sub_cancel_left (n := rP) (m := q),
    ← C_ge (rP + q) (by omega), Nat.add_sub_cancel_left]
  exact agreeI q hq ρ (xs ++ is) hfitC

end Run

/-! ## 5. The graph kit's `hconclTy`, from the converse

The graph kit's bound (`blockGraphKit`'s `hB`) asks that the recursor's
conclusion, read at a prefix `x⃗`, at a carrier element's index values
and at the element, lie in the family's universe.  The element's class
index set carries the prefix's FIT (`blockRecIs_fits`) — the frame the
comparison is certified at — its index tuple unpacks to a fit of the
MEMBER's telescope (`mem_idxSet_elim`), the converse carries that to
the RECURSOR's index binders, the element lies in the member's former
applied there (`BlockModelAt.leaf`), which is the major's reading
(`interp_of_major_reading`), and the whole spine fits the recursor's
binder data, where the check's own inferred sort licenses the
conclusion (`blockRecConcl_univ`). -/

section ConclTy

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V} {names : List Name}

/-- **The graph kit's `hconclTy`, at the run**: the conclusion read at
any class element is a set of the CHECKED elimination level. -/
theorem blockRecConclTy_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    {uOf : Nat → Level}
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V, ∀ c, c < rs.length →
      ∀ i, i ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ)
            (d.nIdxAt (p.toBlockShape.recTgtAt c)) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
          p.toBlockShape.large)) : V) := by
  intro xs c hc i hi x hx
  obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
  obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
  rw [blockRecIs_pos hpar hpref] at hi
  obtain ⟨hnPle, hmemk, hmI, hlenRds, hmajRead⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  have hlenIds := blockMembers_IdsM_length hmr hmemk ψ
  have hmemN : p.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hi' : i ∈ˢ idxSet (d.uM (p.toBlockShape.recTgtAt c) ψ) (consList (xs.take d.nP) ρ)
      (d.IdsM (p.toBlockShape.recTgtAt c) ψ) := hi
  obtain ⟨is, hisfit, rfl⟩ := mem_idxSet_elim hi'
  have hIdx := hM.idxOk ψ _ (d.satOfSpine hpar) _ hmemN
  have hisOf : isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ) (d.nIdxAt (p.toBlockShape.recTgtAt c))
      (tupW (d.uM (p.toBlockShape.recTgtAt c) ψ) is) = is := by
    rw [← hlenIds]; exact isOfW_tupW hIdx hisfit
  rw [hisOf, ← List.append_assoc]
  -- the element lies in the member's former applied
  have hx' : x ∈ˢ (xs.take d.nP ++ is).foldl app
      (interp V ρ (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)) := by
    rw [hM.leaf _ hmemk ψ ρ (xs.take d.nP) is hpar hisfit]
    exact hx
  -- the prefix fits the recursor's own prefix domains
  have hprefR : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c)) xs := by
    rw [← List.map_take]; exact hpref
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt c := by
    rw [hprefR.length_eq, List.length_take, List.length_map, hlenRds]; omega
  have hislen : is.length = d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [hisfit.length_eq, hlenIds]
  -- THE CONVERSE: the index values fit the recursor's index binders
  have hidxR := blockRecIdxConv_run hμ mpC h hmr hr ψ ρ xs is hprefR hisfit
  rw [hlenIds] at hidxR
  -- the major
  have hmaj : x ∈ˢ interp V (consList (xs ++ is) ρ)
      (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).getD
        (p.toBlockShape.majorIdxAt c) default) := by
    have hget : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).getD (p.toBlockShape.majorIdxAt c) default
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD
          (p.toBlockShape.majorIdxAt c) default).2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenRds]; omega)]
      rfl
    rw [hget, hmajRead, hmI, interp_of_major_reading hxlen hislen hnPle
      (fun ρ₁ ρ₂ => acval_interp_closed mpC.base2 _ ψ ρ₁ ρ₂)]
    exact hx'
  -- the whole spine fits the recursor's binder data
  have hsplitL : (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)
      = ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take
          (p.toBlockShape.rulePrefixAt c))
        ++ ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          (p.toBlockShape.rulePrefixAt c)).take (d.nIdxAt (p.toBlockShape.recTgtAt c))))
        ++ [((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).getD
          (p.toBlockShape.majorIdxAt c) default] := by
    have hlen : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).length = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c)
          + 1 := by
      rw [List.length_map, hlenRds, hmI]
    rw [hmI]
    generalize ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)) = L
      at hlen ⊢
    generalize p.toBlockShape.rulePrefixAt c = a at hlen ⊢
    generalize d.nIdxAt (p.toBlockShape.recTgtAt c) = b at hlen ⊢
    rw [← List.take_add]
    have hd : L.drop (a + b) = [L.getD (a + b) default] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [← hd, List.take_append_drop]
  have hfull : SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)) (xs ++ is ++ [x]) := by
    rw [hsplitL]
    exact SpineFit.append (SpineFit.append hprefR hidxR) ⟨hmaj, trivial⟩
  have hsat : Sat V (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)).reverse) (consList (xs ++ is ++ [x]) ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfull
  obtain ⟨fvs, conclE, sty, hop, hinf, hens⟩ := hruns c hc
  have hrd : rs.getD c default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  rw [hrd] at hop
  have hu := blockRecConcl_univ hμ mpC h hr ψ hop hinf hens _ hsat
  rwa [blockRecElimPin_run h hruns ψ hc] at hu

end ConclTy

end ConLeche.Model
