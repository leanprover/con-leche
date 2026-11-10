module

public import InLeanProof.IndBasis
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-stages: the formers' stage against master's (task #451, lane O7-stages)

`checkBlockIndsFSimI` (`checkBlockIndsS_spec`'s twin): InLean's
`checkBlockIndsC` at `fe` answers master's `checkBlockInds` at `L` on the
translated shape, from the former's constant check (`CheckConstantValCSimI`,
O6's) and the job's operations (`OpsSimI`).  Below it: the variable's type
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
theorem checkBlockTeleFI_run (hC : CheckConstantValCSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {nP : Nat} {ms : InLean.MemberShape} {s₀ s' : InLean.CState}
    {r : Lean.ConstantVal × Lean.Level}
    (hs : CSOKI .verified false L s₀) (hok : okC ms.cvT.type = true)
    (h : InLean.checkBlockTeleC .verified fe nP ms s₀ = .ok (r, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ r.1 = ms.cvT ∧ okL r.2 = true ∧
      (trC ms.cvT.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.checkBlockTele (ConLeche.fueledOpsM .verified) L nP (trMember ms))
        (trCV r.1, trL r.2) := by
  unfold InLean.checkBlockTeleC at h
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
theorem checkBlockTelesFI_run (hC : CheckConstantValCSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {nP : Nat} :
    ∀ {mss : List InLean.MemberShape} {s₀ s' : InLean.CState}
      {r : List (Lean.ConstantVal × Lean.Level)},
      CSOKI .verified false L s₀ → (∀ ms ∈ mss, okC ms.cvT.type = true) →
      InLean.checkBlockTelesC .verified fe nP mss s₀ = .ok (r, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ r.map Prod.fst = mss.map (·.cvT) ∧
        (∀ x ∈ r, okC x.1.type = true ∧ (trC x.1.type).looseBVarsBounded 0 = true ∧
          okL x.2 = true) ∧
        Runs (ConLeche.checkBlockTeles (ConLeche.fueledOpsM .verified) L nP (mss.map trMember))
          (r.map trTele)
  | [], s₀, s', r, hs, _, h => by
    unfold InLean.checkBlockTelesC at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, rfl, by simp, Runs.pure _⟩
  | ms :: rest, s₀, s', r, hs, hok, h => by
    unfold InLean.checkBlockTelesC at h
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
      InLean.checkBlockDomsAtC .verified fe off fvs doms j s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkBlockDomsAt (ConLeche.fueledOpsM .verified) L off cfvs cdoms j) ()
  | 0, s₀, s', u, hs, _, _, _, _, h => by
    unfold InLean.checkBlockDomsAtC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | j + 1, s₀, s', u, hs, hokf, hokd, htf, htd, h => by
    unfold InLean.checkBlockDomsAtC at h
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

/-- A closed term's telescope, opened by InLean, read at a later state. -/
theorem openClosedI_run {s₀ s' s'' : InLean.CState} {n : Nat} {e : Lean.Expr}
    {fvs : List Lean.Expr} {b : Lean.Expr} (hs : CSOKI mode eager env s₀) (hok : okC e = true)
    (hc : (trC e).looseBVarsBounded 0 = true)
    (h : InLean.openPisAtFvars n e 0 s₀ = .ok (some (fvs, b), s')) (ht : TabLe s' s'') :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' fvs = true ∧
      ConLeche.openPisAtFvarsC n (trC e) 0 = some (TrSL s'' fvs, TrS s' b) ∧
      ∀ (i : Nat) (x : ConLeche.Expr), (TrSL s'' fvs)[i]? = some x →
        (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped i x.fvarTypeD ∧
          x.fvarTypeD.looseBVarsBounded 0 = true := by
  unfold InLean.openPisAtFvars at h
  obtain ⟨hs', ht', hR⟩ := openPisAtFvarsI_run n 0 hs (OkS_of_okC _ hok)
    (by rw [TrS_of_okC _ hok]; exact hc) h
  obtain ⟨hokf, -, hm⟩ := hR fvs b rfl
  rw [TrS_of_okC _ hok, ← TrSL_of_tabLe ht hokf] at hm
  refine ⟨hs', ht', hokf, hm, fun i x hx => ⟨?_, ?_, ?_⟩⟩ <;>
    rw [ConLeche.Cached.openPisAtFvarsC_eq] at hm
  · obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index n _ 0 hm i x hx
    exact ⟨_, _, rfl⟩
  · have := ConLeche.openPisAtFvars_typeWScoped n hm (trC_wscoped 0 e) i x hx
    rwa [Nat.zero_add] at this
  · exact (ConLeche.Verify.openPisAtFvars_bounded n hm hc).2 x (List.mem_of_getElem? hx)

/-- **The members' agreement** (`checkBlockAgreeS_spec`'s twin). -/
theorem checkBlockAgreeFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L) {nP : Nat}
    {cvTa0 : Lean.ConstantVal} {s0 : Lean.Level} (h0 : okC cvTa0.type = true)
    (hc0 : (trC cvTa0.type).looseBVarsBounded 0 = true) (hl0 : okL s0 = true) :
    ∀ {cvs : List (Lean.ConstantVal × Lean.Level)} {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ →
      (∀ x ∈ cvs, okC x.1.type = true ∧ (trC x.1.type).looseBVarsBounded 0 = true ∧
        okL x.2 = true) →
      InLean.checkBlockAgreeC .verified fe nP cvTa0 s0 cvs s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkBlockAgree (ConLeche.fueledOpsM .verified) L nP (trCV cvTa0) (trL s0)
          (cvs.map trTele)) ()
  | [], s₀, s', u, hs, _, h => by
    unfold InLean.checkBlockAgreeC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | (cvTa, sx) :: rest, s₀, s', u, hs, hall, h => by
    obtain ⟨hokx, hcx, hlx⟩ := hall _ (List.mem_cons_self ..)
    unfold InLean.checkBlockAgreeC at h
    obtain ⟨r0, s₁, h1, hk1⟩ := bindI_ok h
    obtain ⟨tq0, s₁', h1', hk1'⟩ := bindI_ok hk1
    cases r0 with
    | none => simp only [InLean.unwrapOr] at h1'; exact (throwI_ok h1').elim
    | some tq0' =>
    simp only [InLean.unwrapOr] at h1'
    obtain ⟨rfl, rfl⟩ := pureI_ok h1'
    obtain ⟨r, s₂, h2, hk2⟩ := bindI_ok hk1'
    obtain ⟨tq, s₂', h2', hk2'⟩ := bindI_ok hk2
    cases r with
    | none => simp only [InLean.unwrapOr] at h2'; exact (throwI_ok h2').elim
    | some tq' =>
    simp only [InLean.unwrapOr] at h2'
    obtain ⟨rfl, rfl⟩ := pureI_ok h2'
    obtain ⟨fvs0, b0⟩ := tq0'
    obtain ⟨fvs, b⟩ := tq'
    simp only at hk2'
    split at hk2'
    case isFalse =>
      obtain ⟨_, _, h, -⟩ := bindI_ok hk2'; exact (throwI_ok h).elim
    rename_i hlen
    obtain ⟨ds, s₄, h4, hk4⟩ := bindI_ok hk2'
    -- the two telescopes, read at the state after the second
    obtain ⟨hs₁, ht₁, hokf0, hm0, hfv0⟩ := openClosedI_run hs h0 hc0 h1 (TabLe.refl _)
    obtain ⟨hs₂, ht₂, hokf, hm, hfv⟩ := openClosedI_run hs₁ hokx hcx h2 (TabLe.refl _)
    rw [ConLeche.Cached.openPisAtFvarsC_eq] at hm0 hm
    have hT0 : TrSL s₂ fvs0 = TrSL s₁ fvs0 := TrSL_of_tabLe ht₂ hokf0
    have hokf0₂ : OkSL s₂ fvs0 = true := okSL_of_tabLe ht₂ hokf0
    obtain ⟨hs42, hokds, htds⟩ := mapM_fvarTypeDI_run hs₂ hokf0₂
      (by
        intro x hx
        obtain ⟨i, hi⟩ := List.getElem?_of_mem (hT0 ▸ hx)
        exact (hfv0 i x hi).1)
      h4
    subst s₄
    obtain ⟨_, s₅, h5, hk5⟩ := bindI_ok hk4
    obtain ⟨hs₅, ht₅, hR5⟩ := checkBlockDomsAtFI_run hO
      (cfvs := TrSL s₂ fvs) (cdoms := (TrSL s₁ fvs0).map ConLeche.Expr.fvarTypeD)
      (fun i x hx => by
        obtain ⟨h1, h2, -⟩ := hfv i x hx
        exact ⟨h1, by rw [Nat.zero_add]; exact h2⟩)
      (fun i x hx => by
        rw [List.getElem?_map] at hx
        cases hy : (TrSL s₁ fvs0)[i]? with
        | none => rw [hy] at hx; cases hx
        | some y =>
          rw [hy] at hx
          obtain rfl := Option.some.inj hx
          obtain ⟨-, h2, h3⟩ := hfv0 i y hy
          exact ⟨by rw [Nat.zero_add]; exact h2, h3⟩)
      nP hs₂ hokf hokds rfl (by rw [htds, hT0]) h5
    obtain ⟨b', s₆, h6, hk6⟩ := bindI_ok hk5
    obtain ⟨hs₆, ht₆, hb'⟩ := tripleI_iff_run.1 (liftFueled_specI hs₅ _ _) b' s₆ h6
    cases b' with
    | false =>
      split at hk6
      · contradiction
      obtain ⟨_, _, h, -⟩ := bindI_ok hk6
      exact (throwI_ok h).elim
    | true =>
    simp only [↓reduceIte] at hk6
    obtain ⟨hs', ht', hR⟩ := checkBlockAgreeFI_run hO h0 hc0 hl0 hs₆
      (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hk6
    refine ⟨hs', ht₁.trans (ht₂.trans (ht₅.trans (ht₆.trans ht'))), ?_⟩
    have hlen' : ((TrSL s₂ fvs).length == (TrSL s₁ fvs0).length) = true := by
      simpa [TrSL] using hlen
    have heq : ConLeche.Level.isEquiv (trL sx) (trL s0) = some true := by
      rw [← isEquiv_trL hlx hl0]; exact hb'
    unfold ConLeche.checkBlockAgree
    simp only [List.map_cons, trTele, trCV_type, hm0, hm, ConLeche.unwrapOr, heq,
      ConLeche.liftFueled]
    refine Runs.bind (Runs.pure _) (Runs.bind (Runs.pure _) ?_)
    dsimp only
    simp only [hlen', ↓reduceIte]
    refine Runs.bind hR5 (Runs.bind (Runs.pure _) ?_)
    simp only [↓reduceIte]
    exact hR

/-! ## The formers' stage -/

theorem trShape_withSort (p : InLean.BlockShape) {s : Lean.Level} (h : okL s = true) :
    trShape (p.withSort s) = (trShape p).withSort (trL s) := by
  simp only [trShape, InLean.BlockShape.withSort, ConLeche.BlockShape.withSort, isEquiv_zero_tr h]

/-- **The formers' stage** (`checkBlockIndsS_spec`'s twin): InLean's run at
`fe` answers master's `checkBlockInds` at `L` on the translated shape; the
formers' environment is `fe` marked with the block and the formers pushed. -/
theorem checkBlockIndsFI_run (hC : CheckConstantValCSimI) {fe : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {p : InLean.BlockShape} {isRec : Bool} {s₀ s' : InLean.CState}
    {fe₁ : InLean.FEnv} {p₁ : InLean.BlockShape}
    (hs : CSOKI .verified false L s₀) (hok : ∀ ms ∈ p.members, okC ms.cvT.type = true)
    (h : InLean.checkBlockIndsC .verified fe p isRec s₀ = .ok ((fe₁, p₁), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ ∃ s0, okL s0 = true ∧ p₁ = p.withSort s0 ∧
      fe₁ = InLean.consBlockIndsF p₁ isRec (p.members.map (·.declared)) 0
        { fe with pending := InLean.blockMarks p₁ ++ fe.pending } ∧
      (∀ ms ∈ p.members, (trC ms.cvT.type).looseBVarsBounded 0 = true) ∧
      Runs (ConLeche.checkBlockInds (ConLeche.fueledOpsM .verified) L (trShape p) isRec)
        (ConLeche.consBlockInds (trShape p₁) isRec ((trShape p).members.map (·.declared)) 0 L,
          trShape p₁) := by
  unfold InLean.checkBlockIndsC at h
  generalize hm : p.members = mems at h hok
  cases mems with
  | nil => exact (throwI_ok h).elim
  | cons ms0 rest =>
  simp only at h
  obtain ⟨⟨cvTa0, s0⟩, s₁, h1, hk1⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hc1, hl0, hcl0, hR1⟩ :=
    checkBlockTeleFI_run hC hJ hs (hok ms0 (List.mem_cons_self ..)) h1
  simp only at hc1
  subst hc1
  obtain ⟨cvs, s₂, h2, hk2⟩ := bindI_ok hk1
  obtain ⟨hs₂, ht₂, hcvs, hall, hR2⟩ :=
    checkBlockTelesFI_run hC hJ hs₁ (fun m hm' => hok m (List.mem_cons_of_mem _ hm')) h2
  obtain ⟨_, s₃, h3, hk3⟩ := bindI_ok hk2
  obtain ⟨hs₃, ht₃, hR3⟩ := checkBlockAgreeFI_run hJ.ops (hok ms0 (List.mem_cons_self ..)) hcl0
    hl0 hs₂ hall h3
  have hclAll : ∀ ms ∈ ms0 :: rest, (trC ms.cvT.type).looseBVarsBounded 0 = true := by
    intro m hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact hcl0
    · have hmem : m.cvT ∈ cvs.map Prod.fst := by rw [hcvs]; exact List.mem_map_of_mem hm'
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
      rw [← hxe]; exact (hall x hx).2.1
  obtain ⟨hp, rfl⟩ := pureI_ok hk3
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  refine ⟨hs₃, ht₁.trans (ht₂.trans ht₃), s0, hl0, rfl, rfl, hclAll, ?_⟩
  have hmC : (trShape p).members = trMember ms0 :: rest.map trMember := by
    simp [trShape, hm]
  unfold ConLeche.checkBlockInds
  rw [hmC]
  simp only
  refine Runs.bind hR1 (Runs.bind hR2 (Runs.bind hR3 ?_))
  rw [← trShape_withSort p hl0]
  exact Runs.pure _

end InLeanProof
