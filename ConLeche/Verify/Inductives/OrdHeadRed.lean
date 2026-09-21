module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Verify.Subst
import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Shift
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

/-- `whnfCore` is the identity on a `∀` (at nonzero fuel) —
`whnfCore_lam`'s twin, and `whnfCoreBody`'s own clause. -/
private theorem whnfCore_forallE {env : Env} (F d : Nat) (ty body : Expr)
    (bm : BinderMeta) :
    whnfCore mode env (F + 1) d (.forallE ty body bm)
      = .ok (.forallE ty body bm) := rfl

/-- **THE TWO SHAPES AT WHICH THE PURE REDUCTION AND THE RUN BOTH STOP**
(task #315 WIDE (f3), the reduce-then-open inversion).

`ordHeadRed` performs head β and ζ and nothing else, so it stops at a
term that is neither a β- nor a ζ-redex at the head.  The RUN stops
there too at exactly two of those shapes, and the two are what a
container's minted field domain can be:

* an application whose head is a STORED INDUCTIVE — `whnfCore` is the
  identity at such a spine, literal acceleration declines and
  `unfoldDefinition` is `none` (this is the narrowing the module's
  header explains: at a recursor head the run ι-reduces, at a
  definition head the loop δ-unfolds, and in both cases the answer is
  headed by a DIFFERENT constant);
* a `∀` — `whnfCoreBody` hands a binder straight back, and neither the
  literal path nor `unfoldDefinition` can fire on one.

The second disjunct is what the REDEX-TOWER mint needs
(`tests/e2e/nested_redex_tower.ndjson`): its field domain's head normal
form is a `Π`, so the first disjunct says nothing about it and the
inversion would not reach. -/
@[expose] def OrdHeadStop (env : Env) (X : Expr) : Prop :=
  (∃ (J : Name) (lvls : List Level) (cv : ConstantVal) (caps : IndCaps),
      X.getAppFn = .const J lvls ∧ env.find? J = some (.indInfo cv caps))
    ∨ (∃ (ty bo : Expr) (bm : BinderMeta), X = .forallE ty bo bm)

/-- **AND AT EITHER OF THEM `whnfCore` IS THE IDENTITY** — the constant
arm is `whnfCore_headConst_inv`, the binder arm `whnfCore_forallE` (a
fuel too small errors, which makes the hypothesis vacuous). -/
private theorem whnfCore_stop_inv {env : Env} {d : Nat} {X v : Expr} {fuel : Nat}
    (hst : OrdHeadStop env X)
    (h : whnfCore mode env fuel d X = .ok v) : v = X := by
  rcases hst with ⟨J, lvls, cv, caps, hhd, hJ⟩ | ⟨ty, bo, bm, rfl⟩
  · exact whnfCore_headConst_inv hJ hhd h
  · cases fuel with
    | zero => rw [whnfCore_zero] at h; exact nomatch h
    | succ F => rw [whnfCore_forallE] at h; exact (Except.ok.inj h).symm

/-- **THE HEAD INVERSION, AT `ordHeadRedGo`'s OWN RECURSION** (task
#315 WIDE (f3), the fourth concession).  A `whnfCore` run over a spine
whose pure head β/ζ normal form is headed by a stored INDUCTIVE either
IS that normal form, or is stuck at a λ-redex the per-redex certificate
refused — and nothing else. -/
theorem whnfCore_ordHeadRedGo {env : Env} {d : Nat} :
    ∀ (n : Nat) (e : Expr) (args : List Expr) (fuel : Nat) (v : Expr),
      e.looseBVarsBounded 0 = true →
      (∀ x ∈ args, x.looseBVarsBounded 0 = true) →
      OrdHeadStop env (ordHeadRedGo n e args) →
      whnfCore mode env fuel d (Expr.mkAppN e args) = .ok v →
      v = ordHeadRedGo n e args ∨ ∃ ty bd bm, v.getAppFn = .lam ty bd bm := by
  intro n
  induction n with
  | zero =>
    intro e args fuel v _ _ hst h
    exact Or.inl (whnfCore_stop_inv hst h)
  | succ n ih =>
    intro e args fuel v hbe hbargs hst h
    cases e with
    | bvar i => exact Or.inl (whnfCore_stop_inv hst h)
    | fvar i t => exact Or.inl (whnfCore_stop_inv hst h)
    | sort u => exact Or.inl (whnfCore_stop_inv hst h)
    | const c us => exact Or.inl (whnfCore_stop_inv hst h)
    | lit l => exact Or.inl (whnfCore_stop_inv hst h)
    | proj sn i x => exact Or.inl (whnfCore_stop_inv hst h)
    | forallE t b m => exact Or.inl (whnfCore_stop_inv hst h)
    | letE t vl b => exact (whnfCore_letEApp_error fuel args v h).elim
    | app f a0 =>
      obtain ⟨hbf, hba0⟩ : f.looseBVarsBounded 0 = true ∧ a0.looseBVarsBounded 0 = true := by
        simpa only [Expr.looseBVarsBounded, Bool.and_eq_true] using hbe
      exact ih f (a0 :: args) fuel v hbf
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hba0
          · exact hbargs x hx')
        hst h
    | lam tyL bdL mbL =>
      cases args with
      | nil => exact Or.inl (whnfCore_stop_inv hst h)
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
          have hst' : OrdHeadStop env (ordHeadRedGo n (bdL.instantiate1 a) rest) := by
            rw [← hlift]; exact hst
          have := ih (bdL.instantiate1 a) rest f' v hb'
            (fun x hx => hbargs x (List.mem_cons_of_mem _ hx)) hst' hf'
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

/-- Nor at a `∀`-headed one, for the same reason. -/
private theorem reduceNat_forallEHead_none {env : Env} {fuel d : Nat} {e : Expr}
    {tyP boP : Expr} {bmP : BinderMeta} (hv : e.getAppFn = .forallE tyP boP bmP) :
    reduceNatFueled mode env fuel d e = .ok none := by
  show reduceNat (pureFns mode env fuel) env d e = _
  unfold reduceNat
  split
  · exact nomatch (hv : Expr.const _ [] = Expr.forallE tyP boP bmP)
  · exact nomatch (hv : Expr.const _ [] = Expr.forallE tyP boP bmP)
  · rfl

/-- **THE HEAD INVERSION AT `ordHeadRed`** — `whnfCore_ordHeadRedGo` at
the full fuel and the empty spine. -/
theorem whnfCore_ordHeadRed {env : Env} {F d : Nat} {W v : Expr}
    (hb : W.looseBVarsBounded 0 = true)
    (hst : OrdHeadStop env (ordHeadRed W))
    (h : whnfCore mode env F d W = .ok v) :
    v = ordHeadRed W ∨ ∃ ty bd bm, v.getAppFn = .lam ty bd bm :=
  whnfCore_ordHeadRedGo ordHeadRedFuel W [] F v hb (by simp) hst h

/-- **THE HEAD INVERSION AT THE REDUCTION LOOP**: in both arms the loop
stops at `whnfCore`'s answer, because neither an inductive-headed
application nor a λ-headed one is touched by literal acceleration or by
`unfoldDefinition`. -/
theorem whnf_ordHeadRed {env : Env} {F d : Nat} {W w : Expr}
    (hb : W.looseBVarsBounded 0 = true)
    (hst : OrdHeadStop env (ordHeadRed W))
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
    rcases whnfCore_ordHeadRed hb hst hcore with hE | ⟨tyL, bdL, mbL, hlam⟩
    · -- the pure normal form, at either of the two stopping shapes
      have hnat : ∀ r, reduceNatFueled mode env F d e₁ ≠ .ok (some r) := by
        rcases hst with ⟨J, lvls, cv, caps, hred, hJ⟩ | ⟨tyP, boP, bmP, hpi⟩
        · have hhd : e₁.getAppFn = .const J lvls := by rw [hE]; exact hred
          have hfull : e₁ = Expr.mkAppN (.const J lvls) e₁.getAppArgs := by
            rw [← hhd]; exact (Expr.mkAppN_getApp e₁).symm
          have hsucc : J = natSuccName → natLitSupported env = false := by
            rintro rfl; simp [natLitSupported, natSuccOk, hJ]
          have hop : natOpStored env J = false := by simp [natOpStored, hJ]
          intro r; rw [hfull]; exact reduceNat_constApp_ne_some hsucc hop
        · intro r hr
          have hhd : e₁.getAppFn = Expr.forallE tyP boP bmP := by rw [hE, hpi]; rfl
          rw [reduceNat_forallEHead_none hhd] at hr
          exact nomatch hr
      have hunf : unfoldDefinition env e₁ = none := by
        rcases hst with ⟨J, lvls, cv, caps, hred, hJ⟩ | ⟨tyP, boP, bmP, hpi⟩
        · have hhd : e₁.getAppFn = .const J lvls := by rw [hE]; exact hred
          have hfull : e₁ = Expr.mkAppN (.const J lvls) e₁.getAppArgs := by
            rw [← hhd]; exact (Expr.mkAppN_getApp e₁).symm
          rw [hfull]
          exact unfoldDefinition_constApp_none hJ (by intro cv' v hint hh; exact nomatch hh)
        · have hhd : e₁.getAppFn = Expr.forallE tyP boP bmP := by rw [hE, hpi]; rfl
          simp only [unfoldDefinition, hhd]
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
    · rcases whnf_ordHeadRed hb (Or.inl ⟨_, _, _, _, hred, hJ⟩) hv with hE | ⟨tyS, bdS, mbS, hlam⟩
      · exact hE
      · rw [hwc] at hlam; exact nomatch hlam
    · exact nomatch
        (hwc : Expr.forallE dom (body'.abstract1 d) bmP = Expr.const K us)

/-! ## The head normal form at a `Π` (task #315 WIDE (f3) step 4, lane WHNF)

`ordHeadRedGo` has no rule for a binder: it peels an application spine
and reduces a β- or ζ-redex at the head, and a `∀` is none of those, so
the reduction hands a `Π` straight back.  That is the one fact the
REFLEXIVE reading rows need on top of the finitary ones.  A guard of
the form "the head normal form is headed by a CONSTANT" therefore
excludes a `Π` outright, and that is what keeps a reflexive field's
tower — and so the recomputation's CUT — the container's own: whatever
the mint's components plant, they plant it under a head the guard has
already said is not a binder. -/

/-- `ordHeadRedGo` is the spine re-application at a `∀`. -/
theorem ordHeadRedGo_forallE (ty bo : Expr) (bm : BinderMeta) :
    ∀ (n : Nat) (args : List Expr),
      ordHeadRedGo n (Expr.forallE ty bo bm) args
        = Expr.mkAppN (Expr.forallE ty bo bm) args := by
  intro n args
  cases n <;> rfl

/-- `ordHeadRed` is the identity on a `∀`. -/
theorem ordHeadRed_forallE {ty bo : Expr} {bm : BinderMeta} :
    ordHeadRed (Expr.forallE ty bo bm) = Expr.forallE ty bo bm :=
  ordHeadRedGo_forallE ty bo bm ordHeadRedFuel []

/-- **A HEAD-NORMAL-FORM GUARD EXCLUDES A BINDER**: `ordHeadRed` is the
identity on a `∀` and a `∀` is its own `getAppFn`, so a term whose head
normal form is constant-headed is not a `∀`. -/
theorem not_forallE_of_ordHeadRed_const {W : Expr} {c : Name} {us : List Level}
    (h : (ordHeadRed W).getAppFn = Expr.const c us) :
    ∀ (ty bo : Expr) (bm : BinderMeta), W ≠ Expr.forallE ty bo bm := by
  intro ty bo bm hW
  rw [hW, ordHeadRed_forallE] at h
  simp only [Expr.getAppFn] at h
  exact nomatch h

/-- **AND A SUBSTITUTION CANNOT HIDE ONE**: `instSeq` carries a `∀`
through to a `∀`, so a head-normal-form guard on the SUBSTITUTED term
says the substituted-into term is not a binder either.  That is how the
guard on the block's recomputation — which is the stored leaf under the
mint's components and the field's openers — reaches the leaf. -/
theorem notPi_of_ordHeadRed_const_instSeq {vs : List Expr} {t : Nat} {Y : Expr}
    (hlen : vs.length ≤ t + 1) {c : Name} {us : List Level}
    (h : (ordHeadRed (Expr.instSeq vs t Y)).getAppFn = Expr.const c us) :
    ∀ (ty bo : Expr) (bm : BinderMeta), Y ≠ Expr.forallE ty bo bm := by
  intro ty bo bm hY
  refine absurd ?_ (not_forallE_of_ordHeadRed_const h (Expr.instSeq vs t ty)
    (Expr.instSeq vs (t + 1) bo) bm)
  rw [hY, Expr.instSeq_forallE vs t ty bo bm hlen]

/-- **AND THE WALK'S RESULT IS NOT A BINDER EITHER** (task #315 WIDE
(f3) step 4): `normPosDomM_eq_ordHeadRed`'s case split, read for its
SHAPE rather than for the identification — and this one needs no
hypothesis about the result, which is what makes it usable one
telescope up, where the result's head is not yet known.

Each of the walk's three arms is a term that is not a `∀`: the
member-free early return hands back `W`, which the guard excludes; the
`whnf` arm lands on `ordHeadRed W` (constant-headed) or is stuck under
a λ; and the `Π` arm cannot be reached at all, since its own `whnf`
answered with a `∀` and the guard says that answer is not one. -/
theorem normPosDomM_not_forallE {env : Env} {memberNames : List Name}
    {F fuel d : Nat} {W w : Expr}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hb : W.looseBVarsBounded 0 = true)
    (hJ : env.find? J = some (.indInfo cv caps))
    (hred : (ordHeadRed W).getAppFn = .const J lvls)
    (h : normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel W = .ok w) :
    ∀ (ty bo : Expr) (bm : BinderMeta), w ≠ Expr.forallE ty bo bm := by
  rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨v, hv, hcase⟩
  · exact not_forallE_of_ordHeadRed_const hred
  · rcases hcase with rfl | ⟨dom, body, bmP, body', fuel', -, hvE, -, -, rfl⟩
    · rcases whnf_ordHeadRed hb (Or.inl ⟨_, _, _, _, hred, hJ⟩) hv with hE | ⟨tyS, bdS, mbS, hlam⟩
      · rw [hE]
        intro ty bo bm hw
        rw [hw] at hred
        simp only [Expr.getAppFn] at hred
        exact nomatch hred
      · intro ty bo bm hw
        rw [hw] at hlam
        simp only [Expr.getAppFn] at hlam
        exact nomatch hlam
    · -- the `Π` arm: its own `whnf` answered with a `∀`, which the
      -- guard's two possible answers both refuse
      exfalso
      rcases whnf_ordHeadRed hb (Or.inl ⟨_, _, _, _, hred, hJ⟩) hv with hE | ⟨tyS, bdS, mbS, hlam⟩
      · rw [hE] at hvE
        rw [hvE] at hred
        simp only [Expr.getAppFn] at hred
        exact nomatch hred
      · rw [hvE] at hlam
        simp only [Expr.getAppFn] at hlam
        exact nomatch hlam

/-! ## `ordHeadRed` is a congruence for `ErasedEq` (task #315 WIDE (f3))

The reading site holds its recomputation and the install's minted
domain only up to the `fvar` ANNOTATIONS an interpretation never reads
(`hEr`), so the head reduction has to cross that relation.  It does:
`ordHeadRedGo` peels an application spine and substitutes, and both
operations are congruences for `Expr.ErasedEq`. -/

/-- `liftLooseBVars` is a congruence for `ErasedEq`. -/
theorem ErasedEq.liftLooseBVars {amount : Nat} :
    ∀ {e e' : Expr} {c : Nat}, Expr.ErasedEq e e' →
      Expr.ErasedEq (Expr.liftLooseBVars amount c e) (Expr.liftLooseBVars amount c e') := by
  intro e
  induction e with
  | bvar i =>
    intro e' c he
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.liftLooseBVars]
      split <;> simp [Expr.ErasedEq]
  | fvar idx ty =>
    intro e' c he
    match e', he with
    | .fvar j ty', he => simpa [Expr.liftLooseBVars, Expr.ErasedEq] using he
  | sort u =>
    intro e' c he
    match e', he with
    | .sort u', he => simpa [Expr.liftLooseBVars, Expr.ErasedEq] using he
  | const n us =>
    intro e' c he
    match e', he with
    | .const n' us', he => simpa [Expr.liftLooseBVars, Expr.ErasedEq] using he
  | lit l =>
    intro e' c he
    match e', he with
    | .lit l', he => simpa [Expr.liftLooseBVars, Expr.ErasedEq] using he
  | app f x ihf ihx =>
    intro e' c he
    match e', he with
    | .app g y, he => exact ⟨ihf he.1, ihx he.2⟩
  | lam ty b m iht ihb =>
    intro e' c he
    match e', he with
    | .lam ty' b' m', he => exact ⟨he.1, iht he.2.1, ihb he.2.2⟩
  | forallE ty b m iht ihb =>
    intro e' c he
    match e', he with
    | .forallE ty' b' m', he => exact ⟨he.1, iht he.2.1, ihb he.2.2⟩
  | letE ty vl b iht ihv ihb =>
    intro e' c he
    match e', he with
    | .letE ty' vl' b', he => exact ⟨iht he.1, ihv he.2.1, ihb he.2.2⟩
  | proj sn i x ihx =>
    intro e' c he
    match e', he with
    | .proj sn' i' x', he => exact ⟨he.1, he.2.1, ihx he.2.2⟩

/-- The capture-avoiding substitution is a congruence for `ErasedEq`
(`ErasedEq.instantiate1`'s twin, for the open-argument spelling
`ordHeadRedGo` uses). -/
theorem ErasedEq.instantiate1Lift :
    ∀ {e e' v v' : Expr} {k : Nat}, Expr.ErasedEq e e' → Expr.ErasedEq v v' →
      Expr.ErasedEq (e.instantiate1Lift v k) (e'.instantiate1Lift v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1Lift]
      split
      · exact ErasedEq.liftLooseBVars hv
      · split <;> simp [Expr.ErasedEq]
  | fvar idx ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j ty', he => simpa [Expr.instantiate1Lift, Expr.ErasedEq] using he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => simpa [Expr.instantiate1Lift, Expr.ErasedEq] using he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => simpa [Expr.instantiate1Lift, Expr.ErasedEq] using he
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => simpa [Expr.instantiate1Lift, Expr.ErasedEq] using he
  | app f x ihf ihx =>
    intro e' v v' k he hv
    match e', he with
    | .app g y, he => exact ⟨ihf he.1 hv, ihx he.2 hv⟩
  | lam ty b m iht ihb =>
    intro e' v v' k he hv
    match e', he with
    | .lam ty' b' m', he => exact ⟨he.1, iht he.2.1 hv, ihb he.2.2 hv⟩
  | forallE ty b m iht ihb =>
    intro e' v v' k he hv
    match e', he with
    | .forallE ty' b' m', he => exact ⟨he.1, iht he.2.1 hv, ihb he.2.2 hv⟩
  | letE ty vl b iht ihv ihb =>
    intro e' v v' k he hv
    match e', he with
    | .letE ty' vl' b', he => exact ⟨iht he.1 hv, ihv he.2.1 hv, ihb he.2.2 hv⟩
  | proj sn i x ihx =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' x', he => exact ⟨he.1, he.2.1, ihx he.2.2 hv⟩

/-- Pointwise `ErasedEq` on the peeled spine — `ordHeadRedGo`'s own
accumulator, so the relation is stated at lists and not at indices. -/
def ErasedEqs : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => Expr.ErasedEq a b ∧ ErasedEqs as bs
  | _, _ => False

theorem ErasedEqs.rfl : ∀ (as : List Expr), ErasedEqs as as
  | [] => trivial
  | a :: as => ⟨Expr.ErasedEq.rfl a, ErasedEqs.rfl as⟩

theorem ErasedEq.mkAppN :
    ∀ (as as' : List Expr) {f f' : Expr}, Expr.ErasedEq f f' → ErasedEqs as as' →
      Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN f' as')
  | [], [], _, _, hf, _ => hf
  | a :: as, a' :: as', _, _, hf, has =>
    ErasedEq.mkAppN as as' (show Expr.ErasedEq (.app _ a) (.app _ a') from ⟨hf, has.1⟩) has.2
  | [], _ :: _, _, _, _, has => nomatch has
  | _ :: _, [], _, _, _, has => nomatch has

/-- **THE HEAD REDUCTION CROSSES `ErasedEq`**: every step of
`ordHeadRedGo` is a peel, a `mkAppN`, or an `instantiate1Lift`, and all
three are congruences. -/
theorem ErasedEq.ordHeadRedGo :
    ∀ (n : Nat) {e e' : Expr} (args args' : List Expr),
      Expr.ErasedEq e e' → ErasedEqs args args' →
      Expr.ErasedEq (ordHeadRedGo n e args) (ordHeadRedGo n e' args') := by
  intro n
  induction n with
  | zero => intro e e' args args' he has; exact ErasedEq.mkAppN args args' he has
  | succ n ih =>
    intro e e' args args' he has
    match e, e', he with
    | .app f x, .app g y, he =>
      exact ih (x :: args) (y :: args') he.1 ⟨he.2, has⟩
    | .letE ty vl b, .letE ty' vl' b', he =>
      exact ih args args' (ErasedEq.instantiate1Lift he.2.2 he.2.1) has
    | .lam ty b m, .lam ty' b' m', he =>
      match args, args', has with
      | [], [], _ => exact ⟨he.1, he.2.1, he.2.2⟩
      | a :: rest, a' :: rest', has =>
        exact ih rest rest' (ErasedEq.instantiate1Lift he.2.2 has.1) has.2
    | .bvar i, .bvar j, he => exact ErasedEq.mkAppN args args' he has
    | .fvar i t, .fvar j t', he => exact ErasedEq.mkAppN args args' he has
    | .sort u, .sort u', he => exact ErasedEq.mkAppN args args' he has
    | .const c us, .const c' us', he => exact ErasedEq.mkAppN args args' he has
    | .lit l, .lit l', he => exact ErasedEq.mkAppN args args' he has
    | .proj sn i x, .proj sn' i' x', he => exact ErasedEq.mkAppN args args' he has
    | .forallE ty b m, .forallE ty' b' m', he => exact ErasedEq.mkAppN args args' he has

/-- `ordHeadRed` itself, at the empty spine. -/
theorem ErasedEq.ordHeadRed {a b : Expr} (h : Expr.ErasedEq a b) :
    Expr.ErasedEq (ConLeche.ordHeadRed a) (ConLeche.ordHeadRed b) :=
  ErasedEq.ordHeadRedGo ordHeadRedFuel [] [] h trivial

/-- **`ErasedEq` KEEPS A BINDER A BINDER**: the relation is structural
everywhere but at a `fvar`'s annotation, so a term erased-equal to a
`∀` is one.  This is how a guard read on the RECOMPUTATION reaches the
minted domain, whose components carry the run's own annotations. -/
theorem ErasedEq.forallE_right {a ty bo : Expr} {bm : BinderMeta}
    (h : Expr.ErasedEq a (Expr.forallE ty bo bm)) :
    ∃ (ty' bo' : Expr) (bm' : BinderMeta), a = Expr.forallE ty' bo' bm' := by
  cases a with
  | forallE ty' bo' bm' => exact ⟨ty', bo', bm', rfl⟩
  | _ => exact (h : False).elim

/-! ## The REDUCE-THEN-OPEN telescope (task #315 WIDE (f3), object (2))

`openPisAtFvars` peels a `∀` prefix and nothing else.  The positivity
walk peels a different tower: at EVERY level it head-reduces first
(`normPosDomM` calls `ops.whnf` before its `forallE` case) and only
then looks for a binder.  So a container field whose minted domain is a
λ-REDEX whose contractum is a `Π` — `tests/e2e/nested_redex_tower.ndjson`
— has a walk output ONE binder deep while the input's own `Π`-depth is
`0`, and no statement about `openPisAtFvars` of the input can reach it.

`openRedPisAtFvars` is that tower, purely: `openPisAtFvars` with one
`ordHeadRed` per binder.  It reads no environment, which is what lets a
READING row carry it — the guard it states is the same "one `whnf`
claim per binder" the walk itself makes, and where every level is a
plain `∀` already it IS `openPisAtFvars`
(`openRedPisAtFvars_eq_openPisAtFvars`). -/

/-- `openPisAtFvars` with a HEAD REDUCTION at every binder. -/
@[expose] def openRedPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e)
  | n + 1, e, i =>
    match ordHeadRed e with
    | .forallE dom body _ =>
      let fv : Expr := .fvar i dom
      match openRedPisAtFvars n (body.instantiate1 fv) (i + 1) with
      | some (fvs, e') => some (fv :: fvs, e')
      | none => none
    | _ => none

/-- The step equation at a binder: where the head reduction lands on a
`∀`, the reduce-then-open tower peels it. -/
theorem openRedPisAtFvars_forallE {e : Expr} {d n : Nat} {ty bo : Expr} {bm : BinderMeta}
    (h : ordHeadRed e = Expr.forallE ty bo bm) :
    openRedPisAtFvars (n + 1) e d =
      (openRedPisAtFvars n (bo.instantiate1 (Expr.fvar d ty) 0) (d + 1)).map
        (fun r => (Expr.fvar d ty :: r.1, r.2)) := by
  simp only [openRedPisAtFvars, h]
  cases openRedPisAtFvars n (bo.instantiate1 (Expr.fvar d ty) 0) (d + 1) <;> rfl

/-- And where it lands on a constant-headed application the tower is
already at its leaf: one more binder is `none`. -/
theorem openRedPisAtFvars_succ_const {e : Expr} {d n : Nat} {K : Name} {us : List Level}
    (h : (ordHeadRed e).getAppFn = Expr.const K us) :
    openRedPisAtFvars (n + 1) e d = none := by
  rw [openRedPisAtFvars]
  cases hh : ordHeadRed e with
  | bvar i => rfl
  | fvar i t => rfl
  | sort u => rfl
  | const c us' => rfl
  | lit l => rfl
  | proj a b c => rfl
  | app f a => rfl
  | lam t b m => rfl
  | letE t v b => rfl
  | forallE t b m =>
    rw [hh] at h
    simp only [Expr.getAppFn] at h
    exact nomatch h

/-- **WHERE NEITHER LEAF IS A REDEX THE TWO TOWERS ARE ONE** — the
counts, the openers and the leaves all agree.

The guards are the ones the reading rows hold: on the reduce-then-open
side the leaf's head NORMAL FORM is a stored inductive's application,
on the plain side the leaf is already constant-headed.  Each excludes a
`∀` at its own leaf, and that is what pins the two counts together: at
a level where the term is not a binder the plain opening must stop, and
`ordHeadRed` being the identity there (`ordHeadRed_const`) makes the
reduced one stop with it. -/
theorem openRedPisAtFvars_eq_openPisAtFvars :
    ∀ (n₂ n : Nat) {e : Expr} {d : Nat} {fvsE fvsW : List Expr} {lE lw : Expr}
      {J K : Name} {lvls us : List Level},
      openRedPisAtFvars n e d = some (fvsE, lE) →
      (ordHeadRed lE).getAppFn = Expr.const J lvls →
      openPisAtFvars n₂ e d = some (fvsW, lw) →
      lw.getAppFn = Expr.const K us →
      n₂ = n ∧ fvsW = fvsE ∧ lw = lE := by
  intro n₂
  induction n₂ with
  | zero =>
    intro n e d fvsE fvsW lE lw J K lvls us hR hJ hP hK
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    cases n with
    | zero =>
      simp only [openRedPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hR
      obtain ⟨rfl, rfl⟩ := hR
      exact ⟨rfl, rfl, rfl⟩
    | succ n =>
      rw [openRedPisAtFvars_succ_const (by rw [ordHeadRed_const hK]; exact hK)] at hR
      exact nomatch hR
  | succ n₂ ih =>
    intro n e d fvsE fvsW lE lw J K lvls us hR hJ hP hK
    match e, hP with
    | .forallE ty rest bm, hP =>
      cases n with
      | zero =>
        simp only [openRedPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hR
        obtain ⟨rfl, rfl⟩ := hR
        rw [ordHeadRed_forallE] at hJ
        simp only [Expr.getAppFn] at hJ
        exact nomatch hJ
      | succ n =>
        simp only [openPisAtFvars] at hP
        cases hq : openPisAtFvars n₂ (rest.instantiate1 (Expr.fvar d ty) 0) (d + 1) with
        | none => rw [hq] at hP; exact nomatch hP
        | some q =>
          obtain ⟨pfvs, pleaf⟩ := q
          rw [hq] at hP
          simp only [Option.some.injEq, Prod.mk.injEq] at hP
          obtain ⟨rfl, rfl⟩ := hP
          rw [openRedPisAtFvars_forallE ordHeadRed_forallE] at hR
          cases hq2 : openRedPisAtFvars n (rest.instantiate1 (Expr.fvar d ty) 0) (d + 1) with
          | none => rw [hq2] at hR; exact nomatch hR
          | some q2 =>
            obtain ⟨rfvs, rleaf⟩ := q2
            rw [hq2] at hR
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at hR
            obtain ⟨rfl, rfl⟩ := hR
            obtain ⟨h1, h2, h3⟩ := ih n hq2 hJ hq hK
            exact ⟨congrArg (· + 1) h1, by rw [h2], h3⟩

end ConLeche
