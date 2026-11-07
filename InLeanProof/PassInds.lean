module

public import InLeanProof.IndBasis

/-!
# O7-stages: the formers' stage against master's (task #451, lane O7-stages)

`checkBlockIndsFSimI` (`checkBlockIndsS_spec`'s twin): InLean's
`checkBlockIndsF` at `fe` answers master's `checkBlockInds` at `L` on the
translated shape, from the former's constant check (`CheckConstantValFSimI`,
O6's) and the job's operations (`OpsSimI`).  Below it: the telescope opener
at interned variables (`openPisAtFvarsI_run`, master's pure `openPisAtFvars`
at the translation, read at the final state), the variable's type
(`fvarTypeDI_run`), the result sort (`checkSumTele_tr`), and the members'
agreement (`checkBlockDomsAtFI_run`, `checkBlockAgreeFI_run`).

The proofs are functional (`bindI_ok`, `pureI_ok`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## The telescope opener -/

/-- **Opening a telescope at interned variables** (master's `openPisAtFvars` at
the translation): an answer reads, at the final state, as master's on the
translated term. -/
theorem openPisAtFvarsI_run :
    ∀ (n i : Nat) {e : Lean.Expr} {s₀ : InLean.CState} {r : Option (List Lean.Expr × Lean.Expr)}
      {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.openPisAtFvarsM n e i s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ fvs b, r = some (fvs, b) → OkSL s' fvs = true ∧ OkS s' b = true ∧
          ConLeche.openPisAtFvars n (TrS s₀ e) i = some (TrSL s' fvs, TrS s' b)
  | 0, i, e, s₀, r, s', hs, hok, _, h => by
    rw [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro fvs b ⟨⟩
    exact ⟨rfl, hok, rfl⟩
  | n + 1, i, .mdata _ e, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hc ⊢
    exact openPisAtFvarsI_run (n + 1) i hs hok hc h
  | n + 1, i, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    obtain ⟨x, s₂, hx, h⟩ := bindI_ok h
    obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs i hok.1 hc.1) x s₂ hx
    obtain ⟨r', s₃, hr, h⟩ := bindI_ok h
    have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
    have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
    have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
    have hTI : TrS s₂ (body.inst1I x) =
        (TrS s₀ body).instantiate1 (.fvar i (TrS s₀ dom)) 0 := by
      rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht₂ hok.2]
    obtain ⟨hs₃, ht₃, hR⟩ := openPisAtFvarsI_run n (i + 1) hs₂ hokI
      (by rw [hTI]; exact lbb_instantiate1 rfl hc.2) hr
    have ht23 : TabLe s₀ s₃ := ht₂.trans ht₃
    cases r' with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      exact ⟨hs₃, ht23, by rintro _ _ ⟨⟩⟩
    | some q =>
      obtain ⟨fvs', b'⟩ := q
      obtain ⟨rfl, rfl⟩ := pureI_ok h
      refine ⟨hs₃, ht23, ?_⟩
      rintro fvs b ⟨⟩
      obtain ⟨hokf, hokb, hm⟩ := hR fvs' b' rfl
      refine ⟨?_, hokb, ?_⟩
      · simp only [OkSL, List.all_cons, Bool.and_eq_true]
        exact ⟨okS_of_tabLe ht₃ hokx, hokf⟩
      · rw [TrS_forallE]
        simp only [ConLeche.openPisAtFvars]
        rw [← hTI, hm]
        simp only [TrSL, List.map_cons, TrS_of_tabLe ht₃ hokx, htx]
  | _ + 1, _, .bvar _, _, _, _, hs, _, _, h | _ + 1, _, .fvar _, _, _, _, hs, _, _, h
  | _ + 1, _, .mvar _, _, _, _, hs, _, _, h | _ + 1, _, .sort _, _, _, _, hs, _, _, h
  | _ + 1, _, .const _ _, _, _, _, hs, _, _, h | _ + 1, _, .app _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lam _ _ _ _, _, _, _, hs, _, _, h | _ + 1, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lit _, _, _, _, hs, _, _, h | _ + 1, _, .proj _ _ _, _, _, _, hs, _, _, h => by
    simp only [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, by rintro _ _ ⟨⟩⟩

/-! ## A variable's type -/

/-- **An interned variable's type** (master's `fvarTypeD` at the
translation): the recorded type, read at the same state, closed. -/
theorem fvarTypeDI_run {s₀ s' : InLean.CState} {x v : Lean.Expr} (hs : CSOKI mode eager env s₀)
    (hx : OkS s₀ x = true) {i : Nat} {ty : ConLeche.Expr} (hf : TrS s₀ x = .fvar i ty)
    (h : InLean.fvarTypeD x s₀ = .ok (v, s')) :
    s' = s₀ ∧ OkS s₀ v = true ∧ TrS s₀ v = ty ∧ ty.looseBVarsBounded 0 = true := by
  unfold InLean.fvarTypeD at h
  rw [← TrS_stripTop] at hf
  rw [← OkS_stripTop] at hx
  generalize hy : EO.stripTop x = y at h hf hx
  cases y with
  | fvar id =>
    simp only at h
    obtain ⟨o, s₁, ho, hk⟩ := bindI_ok h
    obtain ⟨rfl, hok, htr, hcl⟩ := tripleI_iff_run.1 (fvarTypeM_specI hs hx) o s₁ ho
    obtain ⟨rfl, rfl⟩ := pureI_ok hk
    rw [TrS_fvar hx] at hf
    injection hf with _ hty
    subst hty
    cases o with
    | none => simp [TrO] at htr
    | some t =>
      simp only [TrO, Option.some.injEq] at htr
      simp only [OkO] at hok
      simp only [OptClosed, TrO, htr] at hcl
      exact ⟨rfl, hok, htr, hcl⟩
  | mdata => exact (stripTop_ne_mdata hy).elim
  | bvar | mvar | sort | const | app | lam | forallE | letE | lit | proj =>
    simp [TrS, trE] at hf

/-! ## One former -/

theorem trMember_cvT (ms : InLean.MemberShape) : (trMember ms).cvT = trCV ms.cvT := rfl
theorem trMember_nIdx (ms : InLean.MemberShape) : (trMember ms).nIdx = ms.nIdx := rfl

/-- **One member's former** (`checkBlockTeleS_spec`'s twin). -/
theorem checkBlockTeleFI_run (hC : CheckConstantValFSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {nP : Nat} {ms : InLean.MemberShape} {s₀ s' : InLean.CState}
    {r : Lean.ConstantVal × Lean.Level}
    (hs : CSOKI .verified false L s₀) (hok : okC ms.cvT.type = true)
    (h : InLean.checkBlockTeleF (sharedOpsC .verified fe) fe nP ms s₀ = .ok (r, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ r.1 = ms.cvT ∧ okL r.2 = true ∧
      (trC ms.cvT.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.checkBlockTele (ConLeche.fueledOpsM .verified) L nP (trMember ms))
        (trCV r.1, trL r.2) := by
  unfold InLean.checkBlockTeleF at h
  obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hcl, hR1⟩ := hC fe L ms.cvT s₀ s₁ hJ hs hok h1
  obtain ⟨⟨cvTa, u⟩, s₂, h2, h⟩ := bindI_ok h
  unfold InLean.checkSumTele at h2
  cases hsp : InLean.stripPis (nP + ms.nIdx) ms.cvT.type with
  | none => rw [hsp] at h2; exact (throwI_ok h2).elim
  | some q =>
    obtain ⟨ds, rb⟩ := q
    rw [hsp] at h2
    simp only [Option.map_some] at h2
    generalize hst : EO.stripTop rb = st at h2
    cases st with
    | sort w =>
      obtain ⟨hpq, rfl⟩ := pureI_ok h2
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨rfl, rfl⟩ := hpq
      simp only [hsp] at h
      obtain ⟨_, s₃, h3, hk⟩ := bindI_ok h
      simp only [InLean.unwrapOr] at h3
      obtain ⟨rfl, rfl⟩ := pureI_ok h3
      simp only at hk
      split at hk
      case isFalse =>
        obtain ⟨_, _, h4, -⟩ := bindI_ok hk
        exact (throwI_ok h4).elim
      obtain ⟨rfl, rfl⟩ := pureI_ok hk
      have hokr : okC rb = true := stripPis_okC hok hsp
      have hrb : trC rb = .sort (trL w) := by
        rw [← trC_stripTop, hst]; rfl
      have hokw : okL w = true := by
        apply okL_of_okC_sort; rw [← hst, okC_stripTop]; exact hokr
      refine ⟨hs₁, ht₁, rfl, hokw, hcl, ?_⟩
      have hsp' : (trC ms.cvT.type).stripPis (nP + ms.nIdx) = some (ds.map trC, .sort (trL w)) := by
        rw [stripPis_tr, hsp]; simp [hrb]
      unfold ConLeche.checkBlockTele
      refine Runs.bind hR1 ?_
      simp only [trMember_cvT, trMember_nIdx, ConLeche.checkSumTele, trCV_type, hsp']
      refine Runs.bind (Runs.pure _) ?_
      simp only [trCV_type, hsp', ConLeche.unwrapOr]
      refine Runs.bind (Runs.pure _) ?_
      have hbe : (ConLeche.Expr.sort (trL w) == ConLeche.Expr.sort (trL w)) = true := by simp
      simp only [hbe, ↓reduceIte]
      exact Runs.pure _
    | _ => exact (throwI_ok h2).elim

/-- The formers' results, translated. -/
@[expose] def trTele (x : Lean.ConstantVal × Lean.Level) : ConLeche.ConstantVal × ConLeche.Level :=
  (trCV x.1, trL x.2)

/-- **The other members' formers** (`checkBlockTelesS_spec`'s twin). -/
theorem checkBlockTelesFI_run (hC : CheckConstantValFSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {nP : Nat} :
    ∀ {mss : List InLean.MemberShape} {s₀ s' : InLean.CState}
      {r : List (Lean.ConstantVal × Lean.Level)},
      CSOKI .verified false L s₀ → (∀ ms ∈ mss, okC ms.cvT.type = true) →
      InLean.checkBlockTelesF (sharedOpsC .verified fe) fe nP mss s₀ = .ok (r, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ r.map Prod.fst = mss.map (·.cvT) ∧
        (∀ x ∈ r, okC x.1.type = true ∧ (trC x.1.type).looseBVarsBounded 0 = true ∧
          okL x.2 = true) ∧
        Runs (ConLeche.checkBlockTeles (ConLeche.fueledOpsM .verified) L nP (mss.map trMember))
          (r.map trTele)
  | [], s₀, s', r, hs, _, h => by
    unfold InLean.checkBlockTelesF at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, rfl, by simp, Runs.pure _⟩
  | ms :: rest, s₀, s', r, hs, hok, h => by
    unfold InLean.checkBlockTelesF at h
    obtain ⟨x, s₁, h1, h⟩ := bindI_ok h
    obtain ⟨hs₁, ht₁, hx1, hl, hcl, hR1⟩ :=
      checkBlockTeleFI_run hC hJ hs (hok ms (List.mem_cons_self ..)) h1
    obtain ⟨xs, s₂, h2, h⟩ := bindI_ok h
    obtain ⟨hs₂, ht₂, hxs, hall, hR2⟩ :=
      checkBlockTelesFI_run hC hJ hs₁ (fun m hm => hok m (List.mem_cons_of_mem _ hm)) h2
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    refine ⟨hs₂, ht₁.trans ht₂, by simp [hx1, hxs], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hx1]; exact ⟨hok ms (List.mem_cons_self ..), hcl, hl⟩
      · exact hall y hy
    · unfold ConLeche.checkBlockTeles
      exact Runs.bind hR1 (Runs.bind hR2 (Runs.pure _))

/-! ## The members' agreement -/

/-- **The opened variables' types** (`mapM fvarTypeD`), read at the same
state. -/
theorem mapM_fvarTypeDI_run {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) :
    ∀ {xs ds : List Lean.Expr} {s' : InLean.CState}, OkSL s₀ xs = true →
      (∀ x ∈ TrSL s₀ xs, ∃ k ty, x = .fvar k ty) →
      xs.mapM InLean.fvarTypeD s₀ = .ok (ds, s') →
      s' = s₀ ∧ OkSL s₀ ds = true ∧ TrSL s₀ ds = (TrSL s₀ xs).map ConLeche.Expr.fvarTypeD
  | [], ds, s', _, _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨rfl, rfl, rfl⟩
  | x :: xs, ds, s', hok, hf, h => by
    simp only [List.mapM_cons] at h
    simp only [OkSL, List.all_cons, Bool.and_eq_true] at hok
    simp only [TrSL, List.map_cons, List.mem_cons, forall_eq_or_imp] at hf
    obtain ⟨⟨k, ty, hx⟩, hf⟩ := hf
    obtain ⟨d, s₁, h1, hk1⟩ := bindI_ok h
    obtain ⟨rfl, hokd, htd, -⟩ := fvarTypeDI_run hs hok.1 hx h1
    obtain ⟨ds', s₂, h2, hk2⟩ := bindI_ok hk1
    obtain ⟨rfl, hokds, htds⟩ := mapM_fvarTypeDI_run hs hok.2 hf h2
    obtain ⟨rfl, rfl⟩ := pureI_ok hk2
    refine ⟨rfl, ?_, ?_⟩
    · simp only [OkSL] at hokds
      simp only [OkSL, List.all_cons, hokd, hokds, Bool.and_self]
    · simp only [TrSL] at htds
      simp only [TrSL, List.map_cons, htd, hx, htds, ConLeche.Expr.fvarTypeD]

theorem okS_getElem? {s : InLean.CState} {l : List Lean.Expr} (h : OkSL s l = true) {j : Nat}
    {x : Lean.Expr} (hx : l[j]? = some x) : OkS s x = true := by
  simp only [OkSL, List.all_eq_true] at h
  exact h x (List.mem_of_getElem? hx)

theorem TrSL_getElem? {s : InLean.CState} {l : List Lean.Expr} {j : Nat} {x : Lean.Expr}
    (hx : l[j]? = some x) : (TrSL s l)[j]? = some (TrS s x) := by
  simp [TrSL, hx]

/-- **The parameter domains against member 0's** (`checkBlockDomsAtS_spec`'s
twin). -/
theorem checkBlockDomsAtFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {off : Nat} {fvs doms : List Lean.Expr} {cfvs cdoms : List ConLeche.Expr}
    (hcf : ∀ (i : Nat) (x : ConLeche.Expr), cfvs[i]? = some x →
      (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (off + i) x.fvarTypeD)
    (hcd : ∀ (i : Nat) (x : ConLeche.Expr), cdoms[i]? = some x →
      ConLeche.Expr.WScoped (off + i) x ∧ x.looseBVarsBounded 0 = true) :
    ∀ (j : Nat) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ fvs = true → OkSL s₀ doms = true →
      TrSL s₀ fvs = cfvs → TrSL s₀ doms = cdoms →
      InLean.checkBlockDomsAtF (sharedOpsC .verified fe) fe off fvs doms j s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkBlockDomsAt (ConLeche.fueledOpsM .verified) L off cfvs cdoms j) ()
  | 0, s₀, s', u, hs, _, _, _, _, h => by
    unfold InLean.checkBlockDomsAtF at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | j + 1, s₀, s', u, hs, hokf, hokd, htf, htd, h => by
    unfold InLean.checkBlockDomsAtF at h
    obtain ⟨a, s₁, h1, hk1⟩ := bindI_ok h
    cases ha : fvs[j]? with
    | none => simp only [ha, InLean.unwrapOr] at h1; exact (throwI_ok h1).elim
    | some a' =>
    simp only [ha, InLean.unwrapOr] at h1
    obtain ⟨rfl, rfl⟩ := pureI_ok h1
    obtain ⟨b, s₂, h2, hk2⟩ := bindI_ok hk1
    cases hb : doms[j]? with
    | none => simp only [hb, InLean.unwrapOr] at h2; exact (throwI_ok h2).elim
    | some b' =>
    simp only [hb, InLean.unwrapOr] at h2
    obtain ⟨rfl, rfl⟩ := pureI_ok h2
    have hoka := okS_getElem? hokf ha
    have hokb := okS_getElem? hokd hb
    have hca : cfvs[j]? = some (TrS s₀ a') := htf ▸ TrSL_getElem? ha
    have hcb : cdoms[j]? = some (TrS s₀ b') := htd ▸ TrSL_getElem? hb
    obtain ⟨⟨k, ty, hfa⟩, hwa⟩ := hcf j _ hca
    obtain ⟨hwb, hcbb⟩ := hcd j _ hcb
    obtain ⟨t, s₄, h4, hk4⟩ := bindI_ok hk2
    obtain ⟨rfl, hokt, htt, hct⟩ := fvarTypeDI_run hs hoka hfa h4
    obtain ⟨c, s₃, h3, hk3⟩ := bindI_ok hk4
    rw [hfa] at hwa
    have hD := tripleI_iff_run.1 (hO.defeq (d := off + j) (i := t) (j := b') hs hokt hokb
      (by rw [htt]; exact hwa) hwb (by rw [htt]; exact hct) hcbb) c s₃ h3
    obtain ⟨hs₃, ht₃, hR3⟩ := hD
    rw [htt] at hR3
    cases c with
    | false =>
      simp only at hk3
      obtain ⟨_, _, h5, -⟩ := bindI_ok hk3
      exact (throwI_ok h5).elim
    | true =>
    simp only [↓reduceIte] at hk3
    obtain ⟨hs', ht', hR⟩ := checkBlockDomsAtFI_run hO hcf hcd j hs₃ (okSL_of_tabLe ht₃ hokf)
      (okSL_of_tabLe ht₃ hokd) (by rw [TrSL_of_tabLe ht₃ hokf, htf])
      (by rw [TrSL_of_tabLe ht₃ hokd, htd]) hk3
    refine ⟨hs', ht₃.trans ht', ?_⟩
    unfold ConLeche.checkBlockDomsAt
    simp only [hca, hcb, ConLeche.unwrapOr]
    refine Runs.bind (Runs.pure _) (Runs.bind (Runs.pure _) ?_)
    rw [hfa]
    simp only [ConLeche.Expr.fvarTypeD]
    refine Runs.bind hR3 ?_
    simp only [↓reduceIte]
    exact Runs.bind (Runs.pure _) hR

end InLeanProof
