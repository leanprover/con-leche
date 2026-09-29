module

public import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The recursor stage's class kit, inverted

Run records for the class kit of `ConLeche/Kernel/Inductives/RecCheck.lean`
that the generated recursor stage (`genRecCheck`,
`Verify/Inductives/GenRecRun.lean`) uses: a class resolved
(`TargetMajorRun` / `targetMajorOf_run`, one constructor per arm of
`targetMajorOf`: `member`, and `outside` — a nested block's container),
an outside class's parameters typed (`targetMajorPins_run`), node
agreement (`targetK53_true`).  The records are stated at the fueled pure
instantiation.
-/

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-! ## The major -/

/-- **The major's resolution, as run**: the arm `targetMajorOf` took.
One constructor per arm: `member` and `outside` (a nested block's
containers). -/
inductive TargetMajorRun (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) :
    TargetMajor → Type where
  /-- a MEMBER of the block, at the block's levels and parameters -/
  | member (I : Name) (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat))
      (hfn : mty.getAppFn = .const I (p.lps.map .param))
      (ht : p.memberNames.findIdx? (· == I) = some t)
      (hms : p.members[t]? = some ms)
      (hctors : ctorsAs[t]? = some ctorsA)
      (hpar : mty.getAppArgs.take p.nP = fvs.take p.nP) (nfs : List NestCtorNf) :
      TargetMajorRun fe p ctorsAs pfvs fvs mty
        { ind := I, lvls := p.lps.map .param, ds := fvs.take p.nP, nPc := p.nP,
          nIdx := ms.nIdx, ctors := ctorsA, member := some t, nfs := nfs, pfvs := pfvs }
  /-- an OUTSIDE inductive (a nested block's container), at its own
  levels `us` and parameters `ds` (the major type's first `nPc`
  arguments, mentioning only the recursor's parameter binders), in the
  block's universe -/
  | outside (I : Name) (us : List Level) (nPc nIdx : Nat) (ctors : List (ConstantVal × Nat))
      (sI : Level)
      (hfn : mty.getAppFn = .const I us)
      (ht : p.memberNames.findIdx? (· == I) = none)
      (hnq : I ≠ quotName)
      (hctors : targetCtorsOf fe I = some (nPc, ctors))
      (hdsLen : (mty.getAppArgs.take nPc).length = nPc)
      (hdsSc : ∀ x ∈ mty.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ p.nP)
      (hment : ∃ x ∈ mty.getAppArgs.take nPc, x.nestOcc p.memberNames 0 0 = true)
      (hinst : targetOutsideInst (m := CheckM) fe I us (mty.getAppArgs.take nPc)
        = .ok (nIdx, sI))
      (hsort : Level.isEquiv sI p.resSort = some true) (nfs : List NestCtorNf) :
      TargetMajorRun fe p ctorsAs pfvs fvs mty
        { ind := I, lvls := us, ds := mty.getAppArgs.take nPc, nPc := nPc, nIdx := nIdx,
          ctors := ctors, member := none, nfs := nfs, pfvs := pfvs }

/-- **An OUTSIDE major, at its run**: the major type is the stored
inductive `M.ind` at the major's levels, not a member, not `Quot`; its
parameters are the major type's first `nPc` arguments, mentioning only
the parameter binders; its constructors and parameter count are the
environment's; its instantiated type former has `nIdx` indices and ends
in the block's universe.  (`TargetTyEntry.outside_of` at the entry's
major; the generated stage's `ClassMajorRun.major` at a class.) -/
theorem TargetMajorRun.outside_facts {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {M : TargetMajor} (R : TargetMajorRun fe p ctorsAs pfvs fvs mty M)
    (hM : M.member = none) :
    ∃ sI, mty.getAppFn = .const M.ind M.lvls ∧
      p.memberNames.findIdx? (· == M.ind) = none ∧ M.ind ≠ quotName ∧
      targetCtorsOf fe M.ind = some (M.nPc, M.ctors) ∧
      M.ds = mty.getAppArgs.take M.nPc ∧ M.ds.length = M.nPc ∧
      (∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      targetOutsideInst (m := CheckM) fe M.ind M.lvls M.ds = .ok (M.nIdx, sI) ∧
      Level.isEquiv sI p.resSort = some true := by
  cases R with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl hsc _ hinst hs =>
    exact ⟨sI, hfn, ht, hnq, hct, rfl, hl, hsc, hinst, hs⟩

/-- **A MEMBER major, at its run**: the member `t`, its shape and its
stored constructors, at the block's parameter count. -/
theorem TargetMajorRun.member_facts {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {M : TargetMajor} (R : TargetMajorRun fe p ctorsAs pfvs fvs mty M) {t : Nat}
    (hM : M.member = some t) :
    ctorsAs[t]? = some M.ctors ∧ M.nPc = p.nP := by
  cases R with
  | member I t' ms ctorsA hfn ht hms hctors hpar =>
    obtain rfl : t' = t := Option.some.inj hM
    exact ⟨hctors, rfl⟩
  | outside => exact nomatch hM

/-- **`targetMajorOf`, inverted**: the arm it took and the class's
parameter openers. -/
theorem targetMajorOf_run {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {M : TargetMajor}
    (h : targetMajorOf (m := CheckM) fe p ctorsAs pfvs fvs mty = .ok M) :
    Nonempty (TargetMajorRun fe p ctorsAs pfvs fvs mty M) ∧ M.pfvs = pfvs := by
  unfold targetMajorOf at h
  simp only at h
  split at h
  · next I us hfn =>
    split at h
    · next t ht =>
      obtain ⟨ms, hms, h⟩ := exceptBind_ok h
      obtain ⟨ctorsA, hctorsA, h⟩ := exceptBind_ok h
      by_cases hc : (us == p.lps.map .param && mty.getAppArgs.take p.nP == fvs.take p.nP) = true
      case neg => rw [if_neg hc] at h; close_throw h
      rw [if_pos hc] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hpar⟩ := hc
      exact ⟨⟨.member I t ms ctorsA hfn ht (unwrapOr_ok hms) (unwrapOr_ok hctorsA) hpar _⟩, rfl⟩
    · next ht =>
      split at h
      · close_throw h
      · next hq =>
        split at h
        · next nPc ctors hct =>
          split at h
          · next hds =>
            split at h
            case isFalse => close_throw h
            next hment =>
            obtain ⟨⟨nIdx, sI⟩, hinst, h⟩ := exceptBind_ok h
            obtain ⟨bq, hbq, h⟩ := exceptBind_ok h
            split at h
            · next hs =>
              have hs : sI.isEquiv p.resSort = some true := by
                unfold liftFueled at hbq
                split at hbq
                · next a ha =>
                  simp only [pure, Except.pure, Except.ok.injEq] at hbq
                  subst hbq; subst hs; exact ha
                · simp [throw, throwThe, MonadExceptOf.throw] at hbq
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
                at hds
              simp only [List.any_eq_true] at hment
              exact ⟨⟨.outside I us nPc nIdx ctors sI hfn ht (by simpa using hq) hct hds.1
                (fun x hx => by simpa using hds.2 x hx) hment hinst (by simpa using hs) _⟩,
                rfl⟩
            · close_throw h
          · close_throw h
        · close_throw h
  · close_throw h

/-- **A resolved major with its recorded normal forms replaced**: the
arm it took is the same (the forms are no input of the resolution). -/
def TargetMajorRun.withNfs {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr} :
    {M : TargetMajor} → TargetMajorRun fe p ctorsAs pfvs fvs mty M → (x : List NestCtorNf) →
      TargetMajorRun fe p ctorsAs pfvs fvs mty { M with nfs := x }
  | _, .member I t ms ctorsA hfn ht hms hctors hpar _, x =>
    .member I t ms ctorsA hfn ht hms hctors hpar x
  | _, .outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort _, x =>
    .outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort x

/-- **The parameter typing at an outside major, inverted**: every parameter
`D_i` of the major is typed at the rule
prefix, and so is the instantiation `I.{us} D⃗` — the `D⃗` satisfy the
container's parameter telescope there (official's `tc.check` of the
replaced nested application, `inductive.cpp` v4.33.0 :1223–1231). -/
theorem targetPinTys_run {env : Env} {d F : Nat} :
    ∀ {xs : List Expr}, targetPinTys (fueledOps mode F) env d xs = .ok () →
      ∀ x ∈ xs, ∃ ty, inferTypeCore mode env F d x = .ok ty
  | [], _, x, hx => nomatch hx
  | y :: ys, h, x, hx => by
    unfold targetPinTys at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨ty, hty⟩
    · exact targetPinTys_run h x hx

theorem targetMajorPins_run {env : Env} {rP F : Nat} {M : TargetMajor}
    (h : targetMajorPins (fueledOps mode F) env rP M = .ok ()) (hout : M.member = none) :
    (∀ x ∈ M.ds, ∃ ty, inferTypeCore mode env F rP x = .ok ty) ∧
      ∃ ty, inferTypeCore mode env F rP (Expr.mkAppN (.const M.ind M.lvls) M.ds) = .ok ty := by
  unfold targetMajorPins at h
  rw [if_pos (by rw [hout]; rfl)] at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨ty, hty, -⟩ := exceptBind_ok h
  exact ⟨targetPinTys_run (by cases u; exact hu), ty, hty⟩

/-! ## Node agreement (K.53′) -/

/-- **K.53′ at one recorded field, inverted** (`targetK53`): the field
is a telescope, up to the free variables' annotations the call's, over a
leaf headed by the callee major's constant, its indices the major's up to
the annotations, its class matching the callee's (`targetClassMatch`). -/
theorem targetK53_true {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys : List Expr} {Mc : TargetMajor} {tele : List (Expr × BinderMeta)}
    {majDom f : Expr}
    (h : targetK53 ops env p formerTys Mc tele majDom f = .ok true) :
    ∃ (teleW : List (Expr × BinderMeta)) (leafW : Expr) (I : Name) (us' us : List Level),
      f.stripPis tele.length = some (teleW, leafW) ∧
      teleW.map (fun b => (b.1.eraseFVarTys, b.2)) = tele.map (fun b => (b.1.eraseFVarTys, b.2)) ∧
      leafW.getAppFn = .const I us' ∧ majDom.getAppFn = .const I us ∧
      leafW.getAppArgs.length = majDom.getAppArgs.length ∧
      (leafW.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys
        = (majDom.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys ∧
      (Expr.mkAppN (.const I us') (leafW.getAppArgs.take Mc.nPc)).nestOcc p.memberNames 0 0
        = true ∧
      targetClassMatch ops env p formerTys Mc.pfvs Mc.lvls Mc.ds us'
        (leafW.getAppArgs.take Mc.nPc) = .ok true := by
  unfold targetK53 at h
  split at h
  · simp [pure, Except.pure] at h
  rename_i teleW leafW hstrip
  split at h
  · simp [pure, Except.pure] at h
  rename_i htele
  split at h
  · rename_i I' us' I us hW hM
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, hl⟩, hidx⟩, hment⟩ := hc
      exact ⟨teleW, leafW, I', us', us, hstrip, by simpa using htele, hW, hM, hl, hidx, hment, h⟩
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-! ## Telescope facts -/

section RunFacts

variable {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {block : List ConstantInfo}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- `instPisWith` is `instPisAt`'s residual. -/
theorem instPisWith_eq_instPisAt :
    ∀ (as : List Expr) (e : Expr), instPisWith as e = (Expr.instPisAt as e).map (·.2)
  | [], e => by simp [instPisWith, Expr.instPisAt]
  | a :: as, e => by
    cases e with
    | forallE dom body bm =>
      simp only [instPisWith, Expr.instPisAt, Option.map_map]
      rw [instPisWith_eq_instPisAt as]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
    | _ => simp [instPisWith, Expr.instPisAt]

/-- Opening fewer binders opens a prefix of the same variables. -/
theorem openPisAtFvars_prefix :
    ∀ (k n : Nat) (e : Expr) (d : Nat) {fvs : List Expr} {o : Expr}, k ≤ n →
      openPisAtFvars n e d = some (fvs, o) →
      ∃ o', openPisAtFvars k e d = some (fvs.take k, o')
  | 0, _, e, _, _, _, _, _ => ⟨e, rfl⟩
  | k + 1, 0, _, _, _, _, hk, _ => absurd hk (by omega)
  | k + 1, n + 1, e, d, fvs, o, hk, h => by
    cases e with
    | forallE dom body bm =>
      simp only [openPisAtFvars] at h ⊢
      split at h
      · next fvs' e' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨o', ho'⟩ := openPisAtFvars_prefix k n _ (d + 1) (by omega) h'
        rw [ho']
        exact ⟨o', by simp⟩
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

end RunFacts

end ConLeche
