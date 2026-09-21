module

public import ConLeche.Verify.BetaSpine
public import ConLeche.Verify.InferLemmas
public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.MutualInv

public section

/-!
# The `whnf` head inversion (task #315 WIDE (f3), the fourth concession)

`ordHeadRed` (`Kernel/Inductives/NestedInstall.lean`) is the mint's
ENVIRONMENT-FREE head normal form — head β and ζ, nothing else.  The
reading half of the pin identification needs the install's own
positivity-walk result to BE it (`w = ordHeadRed W`), and that is an
inversion of the checker's `whnf`: a run whose pure head normal form is
headed by a stored INDUCTIVE either returns that normal form, or is
stuck at a λ-redex the per-redex certificate refused.

**The `indInfo` hypothesis is not decoration.**  At a head that is a
recursor the run ι-reduces where `ordHeadRed` does not; at a head that
is a definition the loop δ-unfolds where `ordHeadRed` does not; in both
cases the answer is constant-headed at a DIFFERENT constant.  Official
(Lean v4.29.1) rejects every nested-occurrence shape whose container
head needs δ, ι or a projection to appear, so the narrowing costs the
route nothing an accepted input buys (DESIGN, "the fourth concession's
object STATED before it is proved").
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

private theorem bind_ok' {alpha beta : Type} {x : Except CheckError alpha}
    {f : alpha → Except CheckError beta} {b : beta}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; exact nomatch h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

private theorem ok_bind' {alpha beta : Type} (a : alpha)
    (f : alpha → Except CheckError beta) :
    ((Except.ok a : Except CheckError alpha) >>= f) = f a := rfl

/-- **A `let` at the head of an application spine makes the run an
error**: `whnfCoreBody`'s `letE` clause throws (task #241 — a `let` in
an annotated expression is an invariant violation), and the throw
propagates out through every spine level. -/
theorem whnfCore_letEApp_error {env : Env} {d : Nat} {ty val bd : Expr} :
    ∀ (fuel : Nat) (args : List Expr) (r : Expr),
      whnfCore mode env fuel d (Expr.mkAppN (.letE ty val bd) args) = .ok r → False := by
  intro fuel
  induction fuel with
  | zero => intro args r h; rw [whnfCore_zero] at h; exact nomatch h
  | succ fuel ih =>
    intro args r h
    rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
    · rw [whnfCore_succ] at h
      simp only [whnfCoreBody] at h
      exact nomatch h
    · rw [List.concat_eq_append, Expr.mkAppN_append_one, whnfCore_succ] at h
      simp only [whnfCoreBody, Bind.bind, Except.bind, whnfCore_def] at h
      cases hx : whnfCore mode env fuel d (Expr.mkAppN (.letE ty val bd) as) with
      | error e => rw [hx] at h; exact nomatch h
      | ok u => exact ih as u hx

/-- An application chain over an application base is never a lambda
(`BetaSpine`'s twin is private to that file). -/
private theorem mkAppN_app_ne_lam' :
    ∀ (ys : List Expr) (f a₀ : Expr) (ty body : Expr)
      (mb : BinderMeta), Expr.mkAppN (.app f a₀) ys ≠ .lam ty body mb
  | [], _, _, _, _, _ => by exact fun h => nomatch h
  | y :: ys, f, a₀, ty, body, mb => by
    rw [show Expr.mkAppN (.app f a₀) (y :: ys)
      = Expr.mkAppN (.app (.app f a₀) y) ys from rfl]
    exact mkAppN_app_ne_lam' ys (.app f a₀) y ty body mb

/-- `appStep` on a stuck application chain with a non-constant head
(`BetaSpine`'s twin is private to that file). -/
private theorem appStep_stuck' {env : Env} (F d : Nat) (kF : Expr → CheckM Expr)
    {w : Expr} (a : Expr)
    (hnl : ∀ ty body mb, w ≠ Expr.lam ty body mb)
    (hnc : ∀ c us, w.getAppFn ≠ Expr.const c us) :
    appStep mode (pureFns mode env F) env d kF w a = .ok (.app w a) := by
  have hiota : iotaRec mode (pureFns mode env F) env d (.app w a) = pure none :=
    iotaRec_head_not_const _ env d (fun c us h => hnc c us h)
  cases w with
  | lam ty body mb => exact absurd rfl (hnl ty body mb)
  | _ =>
    unfold appStep
    dsimp only
    rw [hiota]
    rfl

/-- `appStep` at a λ, as an equation (the definition's `match` on the
head, reduced once). -/
private theorem appStep_lam' {env : Env} (F d : Nat) (kF : Expr → CheckM Expr)
    (tyL body : Expr) (mb : BinderMeta) (a : Expr) :
    appStep mode (pureFns mode env F) env d kF (.lam tyL body mb) a
      = (if betaGateFires mode mb.pw then kF (body.instantiate1 a)
         else do
           let ta ← (pureFns mode env F).inferIO d a
           if ← (pureFns mode env F).defeq d ta tyL then kF (body.instantiate1 a)
           else pure (.app (.lam tyL body mb) a)) := rfl

/-- **`whnfCore` IS THE IDENTITY AT A CONSTANT-HEADED SPINE, INVERTED**:
`whnfCore_constApp_eq` read off a run at an arbitrary fuel (a fuel too
small errors, which makes the hypothesis vacuous). -/
theorem whnfCore_constApp_inv {env : Env} {d : Nat} {c : Name} {us : List Level}
    (hnr : ∀ cv mI rP rules, env.find? c ≠ some (.recInfo cv mI rP rules))
    {fuel : Nat} {args : List Expr} {r : Expr}
    (h : whnfCore mode env fuel d (Expr.mkAppN (.const c us) args) = .ok r) :
    r = Expr.mkAppN (.const c us) args := by
  have h1 := whnfCore_mono (Nat.le_max_left fuel (args.length + 1)) h
  have h2 := whnfCore_constApp_eq (mode := mode) (env := env) (d := d) (us := us) hnr
    (max fuel (args.length + 1)) args
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  rw [h1] at h2
  exact Except.ok.inj h2

/-- **ONE HEAD β, INVERTED ACROSS A SPINE** (task #315 WIDE (f3), the
fourth concession's one real step): a run over an application whose
head is a λ-redex either hands the redex back VERBATIM — the arm where
the per-redex certificate did not pass, and the only way `whnfCore` can
stop short of the pure head normal form — or is a run over the redex's
CONTRACTUM at some fuel. -/
theorem whnfCore_betaSpine_inv {env : Env} {d : Nat} {ty bd : Expr}
    {bm : BinderMeta} {a : Expr} :
    ∀ (fuel : Nat) (rest : List Expr) (v : Expr),
      whnfCore mode env fuel d (Expr.mkAppN (.app (.lam ty bd bm) a) rest) = .ok v →
      v = Expr.mkAppN (.app (.lam ty bd bm) a) rest ∨
        ∃ fuel', whnfCore mode env fuel' d
          (Expr.mkAppN (bd.instantiate1 a) rest) = .ok v := by
  intro fuel
  induction fuel with
  | zero => intro rest v h; rw [whnfCore_zero] at h; exact nomatch h
  | succ fuel ih =>
    intro rest v h
    rcases List.eq_nil_or_concat rest with rfl | ⟨as, b, rfl⟩
    · show v = Expr.app (.lam ty bd bm) a ∨ _
      rw [show Expr.mkAppN (Expr.app (.lam ty bd bm) a) [] = Expr.app (.lam ty bd bm) a
        from rfl, whnfCore_succ, whnfCoreBody_app, whnfCore_def] at h
      cases fuel with
      | zero => rw [whnfCore_zero] at h; exact nomatch h
      | succ g =>
        rw [whnfCore_lam g d ty bd bm, ok_bind', appStep_lam'] at h
        by_cases hgate : betaGateFires mode bm.pw = true
        · rw [if_pos hgate, whnfCore_def] at h
          exact Or.inr ⟨g + 1, h⟩
        rw [if_neg hgate] at h
        obtain ⟨ta, -, h⟩ := bind_ok' h
        obtain ⟨bb, -, h⟩ := bind_ok' h
        cases bb with
        | true =>
          simp only [↓reduceIte, whnfCore_def] at h
          exact Or.inr ⟨g + 1, h⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact Or.inl (Except.ok.inj h).symm
    · rw [List.concat_eq_append] at h ⊢
      rw [Expr.mkAppN_append_one, whnfCore_succ,
        whnfCoreBody_app, whnfCore_def] at h
      obtain ⟨u, hx, h⟩ := bind_ok' h
      rcases ih as u hx with hL | ⟨f', hf'⟩
      · subst hL
        refine Or.inl ?_
        rw [Expr.mkAppN_append_one]
        refine Except.ok.inj (h.symm.trans (appStep_stuck' fuel d _ b
          (mkAppN_app_ne_lam' as _ a) ?_))
        intro c us hc
        rw [Expr.getAppFn_mkAppN] at hc
        exact nomatch hc
      · refine Or.inr ⟨max f' fuel + 1, ?_⟩
        rw [Expr.mkAppN_append_one, whnfCore_succ, whnfCoreBody_app, whnfCore_def,
          whnfCore_mono (Nat.le_max_left f' fuel) hf', ok_bind']
        exact appStep_mono ((fueledFns mode env).whnfCore d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right f' fuel) h

/-- **AT A CONSTANT INDUCTIVE HEAD THE RUN IS THE IDENTITY**, whatever
the spine: `whnfCore_constApp_inv` read off `getAppFn`. -/
private theorem whnfCore_headConst_inv {env : Env} {d : Nat}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hJ : env.find? J = some (.indInfo cv caps))
    {X v : Expr} {fuel : Nat}
    (hhd : X.getAppFn = .const J lvls)
    (h : whnfCore mode env fuel d X = .ok v) : v = X := by
  have hnr : ∀ cv' mI rP rules, env.find? J ≠ some (.recInfo cv' mI rP rules) := by
    intro cv' mI rP rules; simp [hJ]
  have hX : Expr.mkAppN (.const J lvls) X.getAppArgs = X := by
    rw [← hhd]; exact Expr.mkAppN_getApp X
  rw [← hX] at h ⊢
  exact whnfCore_constApp_inv hnr h

/-- **THE HEAD INVERSION, AT `ordHeadRedGo`'s OWN RECURSION** (task
#315 WIDE (f3), the fourth concession).  A `whnfCore` run over a spine
whose pure head β/ζ normal form is headed by a stored INDUCTIVE either
IS that normal form, or is stuck at a λ-redex the per-redex certificate
refused — and nothing else. -/
theorem whnfCore_ordHeadRedGo {env : Env} {d : Nat}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hJ : env.find? J = some (.indInfo cv caps)) :
    ∀ (n : Nat) (e : Expr) (args : List Expr) (fuel : Nat) (v : Expr),
      e.looseBVarsBounded 0 = true →
      (∀ x ∈ args, x.looseBVarsBounded 0 = true) →
      (ordHeadRedGo n e args).getAppFn = .const J lvls →
      whnfCore mode env fuel d (Expr.mkAppN e args) = .ok v →
      v = ordHeadRedGo n e args ∨ ∃ ty bd bm, v.getAppFn = .lam ty bd bm := by
  intro n
  induction n with
  | zero =>
    intro e args fuel v _ _ hred h
    exact Or.inl (whnfCore_headConst_inv hJ hred h)
  | succ n ih =>
    intro e args fuel v hbe hbargs hred h
    cases e with
    | bvar i => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | fvar i t => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | sort u => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | const c us => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | lit l => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | proj sn i x => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | forallE t b m => exact Or.inl (whnfCore_headConst_inv hJ hred h)
    | letE t vl b => exact (whnfCore_letEApp_error fuel args v h).elim
    | app f a0 =>
      obtain ⟨hbf, hba0⟩ : f.looseBVarsBounded 0 = true ∧ a0.looseBVarsBounded 0 = true := by
        simpa only [Expr.looseBVarsBounded, Bool.and_eq_true] using hbe
      exact ih f (a0 :: args) fuel v hbf
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hba0
          · exact hbargs x hx')
        hred h
    | lam tyL bdL mbL =>
      cases args with
      | nil => exact Or.inl (whnfCore_headConst_inv hJ hred h)
      | cons a rest =>
        have hba : a.looseBVarsBounded 0 = true := hbargs a List.mem_cons_self
        obtain ⟨-, hbdL⟩ : tyL.looseBVarsBounded 0 = true ∧ bdL.looseBVarsBounded 1 = true := by
          simpa only [Expr.looseBVarsBounded, Bool.and_eq_true] using hbe
        have hlift : bdL.instantiate1Lift a = bdL.instantiate1 a :=
          Expr.instantiate1Lift_eq_instantiate1 hba bdL 0
        rcases whnfCore_betaSpine_inv (mode := mode) (env := env) (d := d)
            (ty := tyL) (bd := bdL) (bm := mbL) (a := a) fuel rest v h with hL | ⟨f', hf'⟩
        · refine Or.inr ⟨tyL, bdL, mbL, ?_⟩
          rw [hL, Expr.getAppFn_mkAppN]
          rfl
        · have hb' : (bdL.instantiate1 a).looseBVarsBounded 0 = true :=
            Expr.looseBVarsBounded_instantiate1_gen hba hbdL
          have hred' : (ordHeadRedGo n (bdL.instantiate1 a) rest).getAppFn
              = .const J lvls := by rw [← hlift]; exact hred
          have := ih (bdL.instantiate1 a) rest f' v hb'
            (fun x hx => hbargs x (List.mem_cons_of_mem _ hx)) hred' hf'
          rcases this with hE | hR
          · exact Or.inl (by rw [hE, ← hlift]; rfl)
          · exact Or.inr hR

/-- Literal acceleration cannot fire at a λ-headed application: both of
its redex shapes have a CONSTANT at the head of the spine. -/
private theorem reduceNat_lamHead_none {env : Env} {fuel d : Nat} {e : Expr}
    {tyL bdL : Expr} {mbL : BinderMeta} (hv : e.getAppFn = .lam tyL bdL mbL) :
    reduceNatFueled mode env fuel d e = .ok none := by
  show reduceNat (pureFns mode env fuel) env d e = _
  unfold reduceNat
  split
  · exact nomatch (hv : Expr.const _ [] = Expr.lam tyL bdL mbL)
  · exact nomatch (hv : Expr.const _ [] = Expr.lam tyL bdL mbL)
  · rfl

/-- **THE HEAD INVERSION AT `ordHeadRed`** — `whnfCore_ordHeadRedGo` at
the full fuel and the empty spine. -/
theorem whnfCore_ordHeadRed {env : Env} {F d : Nat} {W v : Expr}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hb : W.looseBVarsBounded 0 = true)
    (hJ : env.find? J = some (.indInfo cv caps))
    (hred : (ordHeadRed W).getAppFn = .const J lvls)
    (h : whnfCore mode env F d W = .ok v) :
    v = ordHeadRed W ∨ ∃ ty bd bm, v.getAppFn = .lam ty bd bm :=
  whnfCore_ordHeadRedGo hJ ordHeadRedFuel W [] F v hb (by simp) hred h

/-- **THE HEAD INVERSION AT THE REDUCTION LOOP**: in both arms the loop
stops at `whnfCore`'s answer, because neither an inductive-headed
application nor a λ-headed one is touched by literal acceleration or by
`unfoldDefinition`. -/
theorem whnf_ordHeadRed {env : Env} {F d : Nat} {W w : Expr}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hb : W.looseBVarsBounded 0 = true)
    (hJ : env.find? J = some (.indInfo cv caps))
    (hred : (ordHeadRed W).getAppFn = .const J lvls)
    (h : whnf mode env F d W = .ok w) :
    w = ordHeadRed W ∨ ∃ ty bd bm, w.getAppFn = .lam ty bd bm := by
  cases F with
  | zero => rw [whnf_zero] at h; exact nomatch h
  | succ F =>
    obtain ⟨k, hk⟩ := whnfLoopFuel_succ
    rw [whnf_succ] at h
    replace h : whnfLoop (pureFns mode env F) env d whnfLoopFuel W = .ok w := h
    rw [hk] at h
    replace h : whnfStep (pureFns mode env F) env d
        (whnfLoop (pureFns mode env F) env d k) W = .ok w := h
    obtain ⟨e₁, hcore, hcase⟩ := whnfStep_inv h
    rcases whnfCore_ordHeadRed hb hJ hred hcore with hE | ⟨tyL, bdL, mbL, hlam⟩
    · -- the pure normal form: stuck at a stored inductive former
      have hhd : e₁.getAppFn = .const J lvls := by rw [hE]; exact hred
      have hfull : e₁ = Expr.mkAppN (.const J lvls) e₁.getAppArgs := by
        rw [← hhd]; exact (Expr.mkAppN_getApp e₁).symm
      have hsucc : J = natSuccName → natLitSupported env = false := by
        rintro rfl; simp [natLitSupported, natSuccOk, hJ]
      have hop : natOpStored env J = false := by simp [natOpStored, hJ]
      have hnat : ∀ r, reduceNatFueled mode env F d e₁ ≠ .ok (some r) := by
        intro r; rw [hfull]; exact reduceNat_constApp_ne_some hsucc hop
      have hunf : unfoldDefinition env e₁ = none := by
        rw [hfull]
        exact unfoldDefinition_constApp_none hJ (by intro cv' v hint hh; exact nomatch hh)
      rcases hcase with ⟨e₂, hr, -⟩ | ⟨-, e₂, hu, -⟩ | ⟨-, -, hw⟩
      · exact absurd hr (hnat e₂)
      · rw [hunf] at hu; exact nomatch hu
      · exact Or.inl (hw.trans hE)
    · -- the stuck certificate: a λ at the head, and the loop is done
      have hnat : ∀ r, reduceNatFueled mode env F d e₁ ≠ .ok (some r) := by
        intro r hr; rw [reduceNat_lamHead_none hlam] at hr; exact nomatch hr
      have hunf : unfoldDefinition env e₁ = none := by
        simp only [unfoldDefinition, hlam]
      rcases hcase with ⟨e₂, hr, -⟩ | ⟨-, e₂, hu, -⟩ | ⟨-, -, hw⟩
      · exact absurd hr (hnat e₂)
      · rw [hunf] at hu; exact nomatch hu
      · exact Or.inr ⟨tyL, bdL, mbL, by rw [hw]; exact hlam⟩

/-! ## The positivity walk's one `whnf` call -/

/-- **THE READING HALF'S OWED FACT** (task #315 WIDE (f3), the fourth
concession): the install's positivity-walk result at a minted domain IS
the domain's pure head β/ζ normal form.

`normPosDomM` runs `ops.whnf` exactly ONCE before its `forallE` case
(`Kernel/Inductives/MutualInstall.lean`), so the object is about one
`whnf` call and not about a walk; the walk's other two arms are the
member-free early return (where the result is the input, and `hwc`
makes `ordHeadRed` the identity on it) and the `Π` arm (whose result is
a `∀`, which `hwc` excludes).

`hwc` — the RESULT's constant head — is what kills the stuck-certificate
arm, and the reading site holds it: `replaceAllNested` rewrote this very
term into the copy's field domain, whose head is a block member. -/
theorem normPosDomM_eq_ordHeadRed {env : Env} {memberNames : List Name}
    {F fuel d : Nat} {W w : Expr}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    {K : Name} {us : List Level}
    (hb : W.looseBVarsBounded 0 = true)
    (hJ : env.find? J = some (.indInfo cv caps))
    (hred : (ordHeadRed W).getAppFn = .const J lvls)
    (hwc : w.getAppFn = .const K us)
    (h : normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel W = .ok w) :
    w = ordHeadRed W := by
  rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨v, hv, hcase⟩
  · exact (ordHeadRed_const hwc).symm
  · rcases hcase with rfl | ⟨dom, body, bmP, body', fuel', -, -, -, -, rfl⟩
    · rcases whnf_ordHeadRed hb hJ hred hv with hE | ⟨tyS, bdS, mbS, hlam⟩
      · exact hE
      · rw [hwc] at hlam; exact nomatch hlam
    · exact nomatch
        (hwc : Expr.forallE dom (body'.abstract1 d) bmP = Expr.const K us)

end ConLeche
