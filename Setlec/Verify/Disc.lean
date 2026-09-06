import Setlec.Verify.Scoped
import Setlec.Verify.InstSpine

/-!
# The call-discipline walks

Per core body and record-parameterized helper: a successful run at the
(real, unguarded) cached record on well-scoped inputs is reproduced by
the guarded record `gFns` — i.e. every record call the body makes is on
well-scoped arguments at the ambient depth.  One `DiscV` walk per
function, mirroring the body structure; the scoping of intermediate
values flows out of the site lemmas (`ScopedSim.site_*`), the scoping
of syntactically constructed arguments out of the `WScoped` toolkit
(`Setlec/Verify/Shift.lean`, `Setlec/Verify/InferLemmas.lean`) — the
same per-site facts the depth-invariance bisimulation
(`Setlec/Verify/Deep.lean`) established, with a one-sided conclusion.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr

/-- Scoping of an optional result. -/
def WScopedO (d : Nat) (o : Option Expr) : Prop :=
  ∀ x, o = some x → WScoped d x

theorem WScopedO.none {d : Nat} : WScopedO d none := fun _ h => nomatch h

theorem WScopedO.some {d : Nat} {x : Expr} (h : WScoped d x) :
    WScopedO d (some x) := fun _ hx => by cases hx; exact h

section Walks

variable {env : Env} {f : Nat}

/-- Shorthand for the two records every walk relates. -/
local notation "C" => cachedFns mode env f
local notation "G" => gFns mode env f

/-! Task #161 P5: the ∀/λ clauses' untrusted `pw` write.  Both helpers
are `infer` + `ensureSort` calls — the very calls the `letE` and `proj`
clauses already make — so the scoped-call discipline they need is the
existing one, site by site. -/

theorem ensureSort_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (fun _ => True) (ensureSort C env d e)
      (ensureSort G env d e) := by
  show DiscV mode env _
    ((C : CoreFns CheckSM).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
    ((G : CoreFns CheckSM).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
  refine DiscV.bind (ih.site_whnf henv hw) (fun w _ => ?_)
  cases w <;> first
    | exact DiscV.pure trivial
    | exact DiscV.throw _

/-- The ∀ node's datum: the chain read is pure, the leaf path is one
`infer` and an `ensureSort`. -/
theorem annotPwPi_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (fun _ => True) (annotPwPi C env d e)
      (annotPwPi G env d e) := by
  unfold annotPwPi
  split
  · exact DiscV.pure trivial
  · refine DiscV.bind (ih.site_inferIO henv hw) (fun t ht => ?_)
    refine DiscV.bind (ensureSort_disc ih henv ht) (fun v _ => ?_)
    exact DiscV.pure trivial

/-- The λ node's datum: the chain read is pure, the leaf path is two
`infer`s and an `ensureSort`. -/
theorem annotPwLam_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (fun _ => True) (annotPwLam C env d e)
      (annotPwLam G env d e) := by
  unfold annotPwLam
  split
  · exact DiscV.pure trivial
  · refine DiscV.bind (ih.site_inferIO henv hw) (fun bt hbt => ?_)
    refine DiscV.bind (ih.site_inferIO henv hbt) (fun btt hbtt => ?_)
    refine DiscV.bind (ensureSort_disc ih henv hbtt) (fun vb _ => ?_)
    exact DiscV.pure trivial

theorem reduceNat_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScopedO d) (reduceNat C env d e)
      (reduceNat G env d e) := by
  match e with
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    exact DiscV.pure WScopedO.none
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    match g' with
    | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
    | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact DiscV.pure WScopedO.none
    | .const c us =>
      match us with
      | _ :: _ => exact DiscV.pure WScopedO.none
      | [] =>
        simp only [reduceNat]
        split
        · refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
          cases rawNatLit? w with
          | some n => exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          | none => exact DiscV.pure WScopedO.none
        · split
          · refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
            cases rawNatLit? w with
            | none => exact DiscV.pure WScopedO.none
            | some n =>
              dsimp only
              cases hres : natOpResult c n 0 with
              | none => exact DiscV.pure WScopedO.none
              | some r =>
                rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                  exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          · split
            · -- the certified `log2` branch mirrors `pred`'s
              refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
              cases rawNatLit? w with
              | none => exact DiscV.pure WScopedO.none
              | some n =>
                dsimp only
                cases hres : natOpResult c n 0 with
                | none => exact DiscV.pure WScopedO.none
                | some r =>
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                    exact DiscV.pure (WScopedO.some (by simp [WScoped]))
            · split
              · refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
                cases rawNatLit? w with
                | none => exact DiscV.pure WScopedO.none
                | some _ => exact DiscV.throw _
              · exact DiscV.pure WScopedO.none
    | .app g b =>
      have hwgb : WScoped d g ∧ WScoped d b := by
        simpa only [WScoped] using hwfa.1
      match g with
      | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
      | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .app _ _ =>
        exact DiscV.pure WScopedO.none
      | .const c us =>
        match us with
        | _ :: _ => exact DiscV.pure WScopedO.none
        | [] =>
          simp only [reduceNat]
          split
          · -- first argument first; the second only behind a literal (D15)
            refine DiscV.bind (ih.site_whnf henv hwgb.2) (fun w₁ _ => ?_)
            cases rawNatLit? w₁ with
            | none => exact DiscV.pure WScopedO.none
            | some n₁ =>
              refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
              cases rawNatLit? w₂ with
              | none => exact DiscV.pure WScopedO.none
              | some n₂ =>
                dsimp only
                cases hres : natOpResult c n₁ n₂ with
                | none => exact DiscV.pure WScopedO.none
                | some r =>
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ |
                    ⟨bn, rfl⟩ <;>
                    exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          · split
            · refine DiscV.bind (ih.site_whnf henv hwgb.2) (fun w₁ _ => ?_)
              cases rawNatLit? w₁ with
              | none => exact DiscV.pure WScopedO.none
              | some _ =>
                refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
                cases rawNatLit? w₂ with
                | none => exact DiscV.pure WScopedO.none
                | some _ => exact DiscV.throw _
            · exact DiscV.pure WScopedO.none

/-- `reduceNat_disc` under the defeq-side fvar guard (the guard is the
same pure `Bool` on both records, so the pruned branch is `pure none`
twinned). -/
theorem reduceNatIf_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) (g : Bool) :
    DiscV mode env (WScopedO d)
      (if g then reduceNat C env d e else pure none)
      (if g then reduceNat G env d e else pure none) := by
  cases g
  · exact DiscV.pure WScopedO.none
  · exact reduceNat_disc ih henv hw

theorem iotaCerts_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {lic : Bool} :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      DiscV mode env (fun _ => True) (iotaCerts C env d lic ty args)
        (iotaCerts G env d lic ty args) := by
  intro args
  induction args with
  | nil => intro ty _ _; exact DiscV.pure trivial
  | cons arg rest ihrest =>
    intro ty hwty hwargs
    have hwarg : WScoped d arg := hwargs arg (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ rest, WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE n ty body mb =>
      have hwtb : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hwty
      show DiscV mode env _
        (if lic && mb.pw.isNever then
          iotaCerts C env d lic (body.instantiate1 arg) rest
        else
          (C : CoreFns CheckSM).inferIO d arg >>= fun ta =>
          (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts C env d lic (body.instantiate1 arg) rest
          else pure false)
        (if lic && mb.pw.isNever then
          iotaCerts G env d lic (body.instantiate1 arg) rest
        else
          (G : CoreFns CheckSM).inferIO d arg >>= fun ta =>
          (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts G env d lic (body.instantiate1 arg) rest
          else pure false)
      by_cases hg : (lic && mb.pw.isNever) = true
      · rw [if_pos hg, if_pos hg]
        exact ihrest (WScoped.instantiate1_gen hwarg 0 hwtb.2) hwrest
      · rw [if_neg hg, if_neg hg]
        refine DiscV.bind (ih.site_inferIO henv hwarg) (fun ta hta => ?_)
        refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact ihrest (WScoped.instantiate1_gen hwarg 0 hwtb.2) hwrest
        | false => exact DiscV.pure trivial
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ => exact DiscV.pure trivial

theorem defEqList_disc (ih : ScopedSim mode env f) {d : Nat} :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      DiscV mode env (fun _ => True) (defEqList C env d as bs)
        (defEqList G env d as bs) := by
  intro as
  induction as with
  | nil =>
    intro bs _ _
    cases bs with
    | nil => exact DiscV.pure trivial
    | cons b bs => exact DiscV.pure trivial
  | cons a as ihas =>
    intro bs hwas hwbs
    cases bs with
    | nil => exact DiscV.pure trivial
    | cons b bs =>
      show DiscV mode env _
        ((C : CoreFns CheckSM).defeq d a b >>= fun r =>
          if r then defEqList C env d as bs else pure false)
        ((G : CoreFns CheckSM).defeq d a b >>= fun r =>
          if r then defEqList G env d as bs else pure false)
      refine DiscV.bind (ih.site_defeq (hwas a (List.mem_cons_self ..))
        (hwbs b (List.mem_cons_self ..))) (fun r _ => ?_)
      cases r with
      | true =>
        simp only [↓reduceIte]
        exact ihas (fun x hx => hwas x (List.mem_cons_of_mem _ hx))
          (fun x hx => hwbs x (List.mem_cons_of_mem _ hx))
      | false => exact DiscV.pure trivial

theorem defeqSpine_disc (ih : ScopedSim mode env f) {d : Nat} {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (defeqSpine C env d a b)
      (defeqSpine G env d a b) := by
  unfold defeqSpine
  split
  · split
    · split
      · split
        · exact defEqList_disc ih hwa.getAppArgs hwb.getAppArgs
        · exact DiscV.pure trivial
      · exact DiscV.pure trivial
    · exact DiscV.pure trivial
  · exact DiscV.pure trivial

theorem wscoped_getD {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x (List.mem_cons_self ..)
    | succ n =>
      simpa [List.getD] using
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- A level-instantiated `fvar`-free expression (e.g. a stored type or
rule right-hand side) is well-scoped at any depth. -/
theorem wscoped_instLevels_of_not_hasFvar {e : Expr}
    (h : e.hasFvar = false) (ps : List Name) (us : List Level) {d : Nat} :
    WScoped d (e.instantiateLevelParams ps us) :=
  WScoped.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact h)

theorem proofIrrel_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (proofIrrel C env d a b)
      (proofIrrel G env d a b) := by
  unfold proofIrrel
  refine DiscV.bind (ih.site_inferIO henv hwa) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_whnf henv hta) (fun w₁ _ => ?_)
  split
  · refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
    refine DiscV.bind (ih.site_whnf henv htb) (fun w₂ _ => ?_)
    split
    · exact DiscV.pure trivial
    · exact DiscV.pure trivial
  · refine DiscV.bind (ih.site_inferIO henv hta) (fun tta htta => ?_)
    refine DiscV.bind (ih.site_whnf henv htta) (fun w _ => ?_)
    cases w <;> try exact DiscV.pure trivial
    case sort uT =>
      refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okA _ => ?_)
      refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
      refine DiscV.bind (ih.site_inferIO henv htb) (fun ttb httb => ?_)
      refine DiscV.bind (ih.site_whnf henv httb) (fun w' _ => ?_)
      cases w' <;> try exact DiscV.pure trivial
      case sort vT =>
        refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okB _ => ?_)
        exact DiscV.pure trivial

/-- The hoisted `Prop`-branch test (task #168): the fast arm is a pure
read on both sides. -/
theorem propIrrel_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (propIrrel mode C env d a b)
      (propIrrel mode G env d a b) := by
  unfold propIrrel
  split
  · exact DiscV.pure trivial
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (ih.site_inferIO henv hwa) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_inferIO henv hta) (fun tta htta => ?_)
  refine DiscV.bind (ih.site_whnf henv htta) (fun w _ => ?_)
  cases w <;> try exact DiscV.pure trivial
  case sort uT =>
    refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okA _ => ?_)
    refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
    refine DiscV.bind (ih.site_inferIO henv htb) (fun ttb httb => ?_)
    refine DiscV.bind (ih.site_whnf henv httb) (fun w' _ => ?_)
    cases w' <;> try exact DiscV.pure trivial
    case sort vT =>
      refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okB _ => ?_)
      exact DiscV.pure trivial

theorem structEtaProjCerts_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} (T : Name) (us' : List Level) {targs : List Expr} {b : Expr}
    (lpsT : List Name) (hwt : ∀ x ∈ targs, WScoped d x)
    (hwb : WScoped d b) :
    ∀ (idxs : List Nat),
      DiscV mode env (fun _ => True)
        (structEtaProjCerts C env d T us' targs b lpsT idxs)
        (structEtaProjCerts G env d T us' targs b lpsT idxs) := by
  intro idxs
  induction idxs with
  | nil => exact DiscV.pure trivial
  | cons i rest ihrest =>
    simp only [structEtaProjCerts]
    cases hf : env.find? (projFnName T i) with
    | none => exact DiscV.pure trivial
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · have htyw : WScoped d
              (cvp.type.instantiateLevelParams cvp.levelParams us') := by
            obtain ⟨htf, -⟩ := henv _ (find?_mem hf)
            exact wscoped_instLevels_of_not_hasFvar htf _ _
          have hargs : ∀ x ∈ targs ++ [b], WScoped d x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hwt x hx
            · rcases List.mem_singleton.mp hx with rfl
              exact hwb
          refine DiscV.bind (iotaCerts_disc ih henv htyw hargs)
            (fun r _ => ?_)
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact ihrest
          | false => exact DiscV.pure trivial
        · exact DiscV.pure trivial
      | projInfo entry => exact DiscV.pure trivial
      | axiomInfo cv => exact DiscV.pure trivial
      | defnInfo cv value hint => exact DiscV.pure trivial
      | thmInfo cv value => exact DiscV.pure trivial
      | indInfo cv caps => exact DiscV.pure trivial
      | ctorInfo cv nP nF => exact DiscV.pure trivial

theorem structEtaCertWith_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b wtb : Expr} (hwa : WScoped d a) (hwb : WScoped d b)
    (hwwtb : WScoped d wtb) :
    DiscV mode env (fun _ => True) (structEtaCertWith mode C env d a b wtb)
      (structEtaCertWith mode G env d a b wtb) := by
  unfold structEtaCertWith
  split <;> try exact DiscV.pure trivial
  rename_i c us heqa
  split <;> try exact DiscV.pure trivial
  rename_i cvc cnP cnF hfc
  split <;> try exact DiscV.pure trivial
  split <;> try exact DiscV.pure trivial
  rename_i T us' heqw
  split <;> try exact DiscV.pure trivial
  rename_i cvT caps hfT
  split <;> try exact DiscV.pure trivial
  refine DiscV.bind (DiscV.liftFueled_true _ _) (fun ok _ => ?_)
  split <;> try exact DiscV.pure trivial
  have htyw : WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine DiscV.bind
    (iotaCerts_disc ih henv htyw hwwtb.getAppArgs)
    (fun r₁ _ => ?_)
  split <;> try exact DiscV.pure trivial
  -- the per-slot certificates run at a projection-function family
  -- only (task #175 S1)
  refine DiscV.bind (P := fun _ => True) ?_ (fun r₂ _ => ?_)
  · split
    · exact DiscV.pure trivial
    · exact structEtaProjCerts_disc ih henv T us' cvT.levelParams
        hwwtb.getAppArgs hwb _
  split <;> try exact DiscV.pure trivial
  refine DiscV.bind (defEqList_disc ih
    (fun x hx => hwa.getAppArgs x (List.mem_of_mem_take hx))
    hwwtb.getAppArgs) (fun r₃ _ => ?_)
  split <;> try exact DiscV.pure trivial
  have hwprojs : ∀ x ∈ etaProjs env T us' wtb.getAppArgs b cnF,
      WScoped d x := by
    intro x hx
    unfold etaProjs at hx
    split at hx
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      simpa [WScoped] using hwb
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hwwtb.getAppArgs y hy
      · rcases List.mem_singleton.mp hy with rfl
        exact hwb
  -- task #137: the constructor-telescope certificate
  have htycw : WScoped d
      (cvc.type.instantiateLevelParams cvc.levelParams us) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine DiscV.bind (P := fun _ => True) ?_ (fun r₄ _ => ?_)
  · -- task #147: the certificate is mode-gated
    split
    · exact iotaCerts_disc ih henv htycw (args := wtb.getAppArgs ++ _)
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hwwtb.getAppArgs x hx
          · exact hwprojs x hx)
    · exact DiscV.pure trivial
  · split <;> try exact DiscV.pure trivial
    exact defEqList_disc ih
      (fun x hx => hwa.getAppArgs x (List.mem_of_mem_drop hx)) hwprojs

theorem structEtaCert_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (structEtaCert mode C env d a b)
      (structEtaCert mode G env d a b) := by
  unfold structEtaCert
  split
  · refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
    refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
    exact structEtaCertWith_disc ih henv hwa hwb hwtb
  · exact DiscV.pure trivial

theorem structUnitCert_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (structUnitCert C env d a b)
      (structUnitCert G env d a b) := by
  unfold structUnitCert
  refine DiscV.bind (ih.site_inferIO henv hwa) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_whnf henv hta) (fun wta hwta => ?_)
  split <;> try exact DiscV.pure trivial
  rename_i T us' heqw
  split <;> try exact DiscV.pure trivial
  rename_i cvT caps hfT
  split <;> try exact DiscV.pure trivial
  refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
  refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
  refine DiscV.bind (ih.site_defeq hwta hwtb) (fun r _ => ?_)
  split <;> try exact DiscV.pure trivial
  have htyw : WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  exact iotaCerts_disc ih henv htyw hwta.getAppArgs

theorem etaCert_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {n₁ : Name} {ty₁ body₁ : Expr} {m₁ : BinderMeta} {b : Expr}
    (hwty : WScoped d ty₁) (hwbody : WScoped d body₁)
    (hwb : WScoped d b) :
    DiscV mode env (fun _ => True)
      (etaCert mode C env d n₁ ty₁ body₁ m₁ b)
      (etaCert mode G env d n₁ ty₁ body₁ m₁ b) := by
  unfold etaCert
  refine DiscV.bind (ih.site_inferIO henv hwb) (fun tb htb => ?_)
  refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
  split <;> try exact DiscV.pure trivial
  rename_i n₂ ty₂ body₂ m₂
  have hwty₂ : WScoped d ty₂ := by
    simp only [WScoped] at hwtb
    exact hwtb.1
  refine DiscV.bind (ih.site_defeq hwty₂ hwty) (fun r _ => ?_)
  split <;> try exact DiscV.pure trivial
  have hwapp : WScoped (d + 1) (.app b (.fvar d n₁ ty₁)) := by
    simp only [WScoped]
    exact ⟨WScoped.mono (Nat.le_succ d) hwb, Nat.lt_succ_self d, hwty⟩
  refine DiscV.bind (ih.site_defeq
    (WScoped.instantiate1 hwty 0 hwbody) hwapp) (fun r₂ _ => ?_)
  split
  · split
    · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
        (fun _ h => h.elim)
    · exact DiscV.pure trivial
  · exact DiscV.pure trivial

theorem projCert_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {lic : Bool} {c : Name} {us : List Level} {args : List Expr}
    (hwargs : ∀ x ∈ args, WScoped d x) :
    DiscV mode env (fun _ => True)
      (projCert C env d lic c us args) (projCert G env d lic c us args) := by
  unfold projCert
  split
  · rename_i cvC nP nF hf
    have hnf : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar = false :=
      const_ty_hasFvar henv hf us
    exact iotaCerts_disc ih henv (WScoped.of_not_hasFvar hnf) hwargs
  · exact DiscV.pure trivial

theorem projCertAt_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {v lic : Bool} {c : Name} {us : List Level} {args : List Expr}
    (hwargs : ∀ x ∈ args, WScoped d x) :
    DiscV mode env (fun _ => True)
      (projCertAt C env d v lic c us args) (projCertAt G env d v lic c us args) := by
  unfold projCertAt
  split
  · exact projCert_disc ih henv hwargs
  · exact DiscV.pure trivial

theorem stuckIrrel_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (stuckIrrel mode C env d a b)
      (stuckIrrel mode G env d a b) := by
  unfold stuckIrrel
  refine DiscV.bind (structEtaCert_disc ih henv hwa hwb) (fun r₃ _ => ?_)
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (structEtaCert_disc ih henv hwb hwa) (fun r₄ _ => ?_)
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (structUnitCert_disc ih henv hwa hwb) (fun r₅ _ => ?_)
  split
  · exact DiscV.pure trivial
  exact proofIrrel_disc ih henv hwa hwb

theorem majorToCtor_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {major : Expr}
    (hmaj : WScoped d major) :
    DiscV mode env (WScoped d) (majorToCtor mode C env d recName rules major)
      (majorToCtor mode G env d recName rules major) := by
  unfold majorToCtor
  -- outer casing peeled by hand (the body outgrew the splitter's
  -- internal simp budget)
  by_cases hca : isCtorApp env major = true
  · rw [if_pos hca, if_pos hca]; exact DiscV.pure hmaj
  rw [if_neg hca, if_neg hca]
  match rules with
  | [] => exact DiscV.pure hmaj
  | _ :: _ :: _ => exact DiscV.pure hmaj
  | [rl] =>
    dsimp only
    cases hfr : env.find? rl.ctor <;> try exact DiscV.pure hmaj
    case some ci =>
    cases ci <;> try exact DiscV.pure hmaj
    case ctorInfo cvj cnP cnF =>
    dsimp only
    cases (cvj.type.piResult).getAppFn <;> try exact DiscV.pure hmaj
    case const T us₀ =>
    dsimp only
    cases env.find? T <;> try exact DiscV.pure hmaj
    case some ciT =>
    cases ciT <;> try exact DiscV.pure hmaj
    case indInfo cvT caps =>
    dsimp only
    have htfC : cvj.type.hasFvar = false := (henv _ (find?_mem hfr)).1
    split
    · -- K branch
      refine DiscV.bind (ih.site_inferIO henv hmaj) (fun tm htm => ?_)
      refine DiscV.bind (ih.site_whnf henv htm) (fun tmaj htmaj => ?_)
      split <;> try exact DiscV.pure hmaj
      split <;> try exact DiscV.pure hmaj
      split <;> try exact DiscV.pure hmaj
      try dsimp only []
      split
      · rename_i hguard
        have hwfab := WScoped.of_wscopedB
          (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)
        refine DiscV.bind (iotaCerts_disc ih henv
          (wscoped_instLevels_of_not_hasFvar htfC _ _)
          (fun x hx => htmaj.getAppArgs x (List.mem_of_mem_take hx)))
          (fun rc _ => ?_)
        split
        · refine DiscV.bind (ih.site_inferIO henv hwfab)
            (fun tfab htfab => ?_)
          refine DiscV.bind (ih.site_defeq htmaj htfab) (fun rde _ => ?_)
          split
          · refine DiscV.bind (proofIrrel_disc ih henv hwfab hmaj)
              (fun r _ => ?_)
            split
            · exact DiscV.pure hwfab
            · exact DiscV.pure hmaj
          · exact DiscV.pure hmaj
        · exact DiscV.pure hmaj
      · exact DiscV.pure hmaj
    split
    · -- eta branch
      refine DiscV.bind (ih.site_inferIO henv hmaj) (fun tm htm => ?_)
      refine DiscV.bind (ih.site_whnf henv htm) (fun tmaj htmaj => ?_)
      split <;> try exact DiscV.pure hmaj
      split <;> try exact DiscV.pure hmaj
      split <;> try exact DiscV.pure hmaj
      try dsimp only []
      split
      · rename_i hguard
        have hwfab := WScoped.of_wscopedB
          (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)
        refine DiscV.bind (iotaCerts_disc ih henv
          (wscoped_instLevels_of_not_hasFvar htfC _ _)
          (fun x hx => ?_)) (fun rc _ => ?_)
        · unfold etaFabArgsE at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact htmaj.getAppArgs x hx
          · unfold etaProjs at hx
            split at hx
            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
              simpa [WScoped] using hmaj
            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
              refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
              intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · exact htmaj.getAppArgs y hy
              · rw [List.mem_singleton.mp hy]; exact hmaj
        split
        · refine DiscV.bind
            (structEtaCertWith_disc ih henv hwfab hmaj htmaj)
            (fun r _ => ?_)
          split
          · exact DiscV.pure hwfab
          · split
            · refine DiscV.bind (proofIrrel_disc ih henv hwfab hmaj)
                (fun r' _ => ?_)
              split
              · exact DiscV.pure hwfab
              · exact DiscV.pure hmaj
            · exact DiscV.pure hmaj
        · exact DiscV.pure hmaj
      · exact DiscV.pure hmaj
    · exact DiscV.pure hmaj

theorem isPropType_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {ty : Expr} (hwty : WScoped d ty) :
    DiscV mode env (fun _ => True) (isPropType C env d ty)
      (isPropType G env d ty) := by
  unfold isPropType
  refine DiscV.bind (ih.site_annotate hwty) (fun ty' hty' => ?_)
  refine DiscV.bind (ih.site_inferIO henv hty') (fun s hs => ?_)
  refine DiscV.bind (ensureSort_disc ih henv hs) (fun u _ => ?_)
  exact DiscV.liftFueled_true _ _

theorem litMajorToCtor_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (litMajorToCtor C env d e)
      (litMajorToCtor G env d e) := by
  unfold litMajorToCtor
  split
  · split
    · exact ih.site_whnf henv (strLitToConstructor_WScoped _ d)
    · exact DiscV.pure hw
  · exact DiscV.pure (litToCtorIfNat_WScoped hw)

theorem projLitToCtor_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (projLitToCtor C env d e)
      (projLitToCtor G env d e) := by
  unfold projLitToCtor
  split
  · split
    · exact ih.site_whnf henv (strLitToConstructor_WScoped _ d)
    · exact DiscV.pure hw
  · exact DiscV.pure hw

theorem iotaIndexOk_disc (ih : ScopedSim mode env f) {d : Nat}
    {mI rP cnP : Nat} {tyCtor : Expr} {margs idx : List Expr}
    (hwty : WScoped d tyCtor) (hwm : ∀ x ∈ margs, WScoped d x)
    (hwi : ∀ x ∈ idx, WScoped d x) :
    DiscV mode env (fun _ => True)
      (iotaIndexOk C env d mI rP cnP tyCtor margs idx)
      (iotaIndexOk G env d mI rP cnP tyCtor margs idx) := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, if_pos hmr]; exact DiscV.pure trivial
  · simp only [iotaIndexOk, if_neg hmr]
    cases hres : piResidual tyCtor margs with
    | none => exact DiscV.pure trivial
    | some residual =>
      exact defEqList_disc ih
        (fun x hx => (piResidual_WScoped hres hwty hwm).getAppArgs x
          (List.mem_of_mem_drop hx)) hwi

/-- The major chain's discipline, in either order. -/
theorem prepareMajor_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {major : Expr}
    (hmaj : WScoped d major) :
    DiscV mode env (WScoped d) (prepareMajor mode C env d recName rules major)
      (prepareMajor mode G env d recName rules major) := by
  unfold prepareMajor
  by_cases hk : recRuleK env rules = true
  · rw [if_pos hk, if_pos hk]
    refine DiscV.bind (majorToCtor_disc ih henv hmaj) (fun m₁ hm₁ => ?_)
    refine DiscV.bind (ih.site_whnf henv hm₁) (fun m₂ hm₂ => ?_)
    exact litMajorToCtor_disc ih henv hm₂
  · rw [if_neg hk, if_neg hk]
    refine DiscV.bind (ih.site_whnf henv hmaj) (fun m₀ hm₀ => ?_)
    refine DiscV.bind (litMajorToCtor_disc ih henv hm₀) (fun m₁ hm₁ => ?_)
    exact majorToCtor_disc ih henv hm₁

theorem iotaRec_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScopedO d) (iotaRec mode C env d e)
      (iotaRec mode G env d e) := by
  unfold iotaRec
  split <;> try exact DiscV.pure WScopedO.none
  rename_i c us heqfn
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cv mI rP rules hfc
  dsimp only []
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind
    (prepareMajor_disc ih henv (wscoped_getD hw.getAppArgs _))
    (fun major hmaj => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cj usj heqmfn
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cvj cnP cnF hfj
  split <;> try exact DiscV.pure WScopedO.none
  rename_i rl hrule
  split <;> try exact DiscV.pure WScopedO.none
  split
  · exact DiscV.throw _
  refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okl _ => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (defEqList_disc ih
    (fun x hx => hmaj.getAppArgs x (List.mem_of_mem_take hx))
    (recFireComparands_snd_WScoped rl cv.levelParams us
      cvj.levelParams e.getAppArgs rP
      (fun x hx => hw.getAppArgs x hx)
      (fun lvls pins hf' pin hpin => by
        obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
        obtain ⟨-, -, -, -, g5⟩ := hrules cv mI rP rules rfl rl
          (List.mem_of_find?_eq_some hrule)
        exact ((g5 lvls pins hf').2.2.1 pin hpin).1)))
    (fun r₁ _ => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  have hwrecty : WScoped d
      (cv.type.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  have hwctorty : WScoped d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine DiscV.bind (iotaCerts_disc ih henv hwrecty ?_) (fun r₂ _ => ?_)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw.getAppArgs x (List.mem_of_mem_take hx)
    · rcases List.mem_singleton.mp hx with rfl
      exact hmaj
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (iotaCerts_disc ih henv hwctorty hmaj.getAppArgs)
    (fun r₃ _ => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (iotaIndexOk_disc ih hwctorty hmaj.getAppArgs
    (fun x hx => hw.getAppArgs x
      (List.mem_of_mem_take (List.mem_of_mem_drop hx))))
    (fun r₄ _ => ?_)
  split
  · refine DiscV.pure (WScopedO.some ?_)
    refine Expr.WScoped.mkAppN ?_ ?_
    · obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
      obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl rl
        (List.mem_of_find?_eq_some hrule)
      exact wscoped_instLevels_of_not_hasFvar hrf _ _
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hw.getAppArgs x (List.mem_of_mem_take hx)
      · exact hmaj.getAppArgs x (List.mem_of_mem_drop hx)
  · exact DiscV.pure WScopedO.none

theorem whnfCoreBody_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (whnfCoreBody mode C env d e)
      (whnfCoreBody mode G env d e) := by
  match e with
  | .sort u | .fvar _ _ _ | .forallE _ _ _ _ | .lam _ _ _ _
  | .const _ _ | .lit _ =>
    exact DiscV.pure hw
  | .bvar _ => exact DiscV.throw _
  | .letE _ ty v b =>
    have hwtvb : WScoped d ty ∧ WScoped d v ∧ WScoped d b := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).whnfCore d (b.instantiate1 v))
      ((G : CoreFns CheckSM).whnfCore d (b.instantiate1 v))
    exact ih.site_whnfCore henv
      (WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).whnfCore d g' >>= fun f' =>
        match f' with
        | .lam n ty body mb =>
          if betaGateFires mode mb.pw then
            (C : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
          else
          (C : CoreFns CheckSM).inferIO d a >>= fun ta =>
          (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then
            (C : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
          else pure (.app (.lam n ty body mb) a)
        | f' =>
          iotaRec mode C env d (.app f' a) >>= fun o =>
          match o with
          | some e'' => (C : CoreFns CheckSM).whnfCore d e''
          | none => pure (.app f' a))
      ((G : CoreFns CheckSM).whnfCore d g' >>= fun f' =>
        match f' with
        | .lam n ty body mb =>
          if betaGateFires mode mb.pw then
            (G : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
          else
          (G : CoreFns CheckSM).inferIO d a >>= fun ta =>
          (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then
            (G : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
          else pure (.app (.lam n ty body mb) a)
        | f' =>
          iotaRec mode G env d (.app f' a) >>= fun o =>
          match o with
          | some e'' => (G : CoreFns CheckSM).whnfCore d e''
          | none => pure (.app f' a))
    refine DiscV.bind (ih.site_whnfCore henv hwfa.1) (fun f' hf' => ?_)
    split
    · -- beta
      rename_i n ty body mb
      have hwtb : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hf'
      have hwapp : WScoped d (Expr.app (.lam n ty body mb) a) := by
        simp only [WScoped]
        exact ⟨hwtb, hwfa.2⟩
      have hwred : WScoped d (body.instantiate1 a) :=
        WScoped.instantiate1_gen hwfa.2 0 hwtb.2
      -- task #161: the β gate's two arms — the fired one is the reduct
      -- site, the other is the pre-gate clause verbatim
      split
      · exact ih.site_whnfCore henv hwred
      refine DiscV.bind (ih.site_inferIO henv hwfa.2) (fun ta hta => ?_)
      refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
      split
      · exact ih.site_whnfCore henv hwred
      · exact DiscV.pure hwapp
    · -- iota / stuck
      rename_i hnolam
      have hwapp : WScoped d (Expr.app f' a) := by
        simp only [WScoped]
        exact ⟨hf', hwfa.2⟩
      refine DiscV.bind (iotaRec_disc ih henv hwapp) (fun o ho => ?_)
      cases o with
      | some e'' => exact ih.site_whnfCore henv (ho e'' rfl)
      | none => exact DiscV.pure hwapp
  | .proj sn i pe =>
    have hwpe : WScoped d pe := by simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).whnf d pe >>= fun e' =>
        projLitToCtor C env d e' >>= fun e' =>
        match env.findProj? sn i with
        | some entry =>
          match e'.getAppFn with
          | .const c us =>
            if entry.tower ∧ c = entry.ctor ∧ i < entry.numFields ∧
                e'.getAppArgs.length = entry.numParams + entry.numFields ∧
                us.length = entry.levelParams.length ∧
                entry.fireOk us = true then
              projCertAt C env d mode.verified mode.betaGate c us e'.getAppArgs >>= fun b =>
              if b then
                (C : CoreFns CheckSM).whnfCore d
                  (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
              else pure (.proj sn i e')
            else pure (.proj sn i e')
          | _ => pure (.proj sn i e')
        | none => pure (.proj sn i e'))
      ((G : CoreFns CheckSM).whnf d pe >>= fun e' =>
        projLitToCtor G env d e' >>= fun e' =>
        match env.findProj? sn i with
        | some entry =>
          match e'.getAppFn with
          | .const c us =>
            if entry.tower ∧ c = entry.ctor ∧ i < entry.numFields ∧
                e'.getAppArgs.length = entry.numParams + entry.numFields ∧
                us.length = entry.levelParams.length ∧
                entry.fireOk us = true then
              projCertAt G env d mode.verified mode.betaGate c us e'.getAppArgs >>= fun b =>
              if b then
                (G : CoreFns CheckSM).whnfCore d
                  (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
              else pure (.proj sn i e')
            else pure (.proj sn i e')
          | _ => pure (.proj sn i e')
        | none => pure (.proj sn i e'))
    refine DiscV.bind (ih.site_whnf henv hwpe) (fun e0 he0 => ?_)
    refine DiscV.bind (projLitToCtor_disc ih henv he0) (fun e' he' => ?_)
    have hwproj : WScoped d (Expr.proj sn i e') := by
      simpa only [WScoped] using he'
    have hwarg : ∀ nP : Nat,
        WScoped d (e'.getAppArgs.getD (nP + i) (.bvar 0)) :=
      fun nP => wscoped_getD he'.getAppArgs _
    split <;> try exact DiscV.pure hwproj
    split <;> try exact DiscV.pure hwproj
    split <;> try exact DiscV.pure hwproj
    refine DiscV.bind (projCertAt_disc ih henv (fun x hx => he'.getAppArgs x hx))
      (fun b _ => ?_)
    split
    · exact ih.site_whnfCore henv (hwarg _)
    · exact DiscV.pure hwproj

/-- One iteration of the reduction loop, with the continuation
abstracted (task #106). -/
theorem whnfStep_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} {kC kG : Expr → _}
    (hk : ∀ {x : Expr}, WScoped d x → DiscV mode env (WScoped d) (kC x) (kG x))
    (hw : WScoped d e) :
    DiscV mode env (WScoped d) (whnfStep C env d kC e)
      (whnfStep G env d kG e) := by
  unfold whnfStep
  refine DiscV.bind (ih.site_whnfCore henv hw) (fun e₁ he₁ => ?_)
  refine DiscV.bind (reduceNat_disc ih henv he₁) (fun o ho => ?_)
  split
  · exact hk (ho _ rfl)
  · split
    · rename_i e₂ hunf
      exact hk (unfoldDefinition_WScoped henv hunf he₁)
    · exact DiscV.pure he₁

theorem whnfLoop_disc (ih : ScopedSim mode env f) (henv : EnvWF env) :
    ∀ (n : Nat) {d : Nat} {e : Expr}, WScoped d e →
      DiscV mode env (WScoped d) (whnfLoop C env d n e) (whnfLoop G env d n e)
  | 0, _, _, _ => DiscV.throw _
  | n + 1, _, _, hw =>
    whnfStep_disc ih henv (fun hx => whnfLoop_disc ih henv n hx) hw

theorem whnfBody_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (whnfBody C env d e)
      (whnfBody G env d e) :=
  whnfLoop_disc ih henv whnfLoopFuel hw

set_option maxHeartbeats 1600000 in
theorem annotateBody_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (annotateBody mode C env d e)
      (annotateBody mode G env d e) := by
  match e with
  | .bvar i => exact DiscV.pure (by simp [WScoped])
  | .fvar idx n ty =>
    show DiscV mode env _
      (if idx < d then pure (Expr.fvar idx n ty)
       else throw (.invalid "free variable out of scope"))
      (if idx < d then pure (Expr.fvar idx n ty)
       else throw (.invalid "free variable out of scope"))
    split
    · exact DiscV.pure hw
    · exact DiscV.throw _
  | .sort u => exact DiscV.pure (by simp [WScoped])
  | .const n us => exact DiscV.pure (by simp [WScoped])
  | .lit (.natVal n) =>
    show DiscV mode env _
      (if natLitSupported env then pure (Expr.lit (.natVal n))
       else throw (.invalid "Nat literal without the Nat basis declarations"))
      (if natLitSupported env then pure (Expr.lit (.natVal n))
       else throw (.invalid "Nat literal without the Nat basis declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .lit (.strVal s) =>
    show DiscV mode env _
      (if strLitSupported env then pure (Expr.lit (.strVal s))
       else throw (.notImplemented
         "string literals before the String support declarations"))
      (if strLitSupported env then pure (Expr.lit (.strVal s))
       else throw (.notImplemented
         "string literals before the String support declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .letE n ty v b =>
    have hwtvb : WScoped d ty ∧ WScoped d v ∧ WScoped d b := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).annotate d ty >>= fun _ =>
        (C : CoreFns CheckSM).annotate d v >>= fun _ =>
          (C : CoreFns CheckSM).annotate d (b.instantiate1 v))
      ((G : CoreFns CheckSM).annotate d ty >>= fun _ =>
        (G : CoreFns CheckSM).annotate d v >>= fun _ =>
          (G : CoreFns CheckSM).annotate d (b.instantiate1 v))
    refine DiscV.bind (ih.site_annotate hwtvb.1) (fun ty' hty' => ?_)
    refine DiscV.bind (ih.site_annotate hwtvb.2.1) (fun v' hv' => ?_)
    exact ih.site_annotate
      (WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).annotate d g' >>= fun f' =>
        (C : CoreFns CheckSM).annotate d a >>= fun a' =>
        pure (Expr.app f' a'))
      ((G : CoreFns CheckSM).annotate d g' >>= fun f' =>
        (G : CoreFns CheckSM).annotate d a >>= fun a' =>
        pure (Expr.app f' a'))
    refine DiscV.bind (ih.site_annotate hwfa.1) (fun f' hf' => ?_)
    refine DiscV.bind (ih.site_annotate hwfa.2) (fun a' ha' => ?_)
    exact DiscV.pure (by simp only [WScoped]; exact ⟨hf', ha'⟩)
  | .forallE n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (C : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        if mode.verified && !pwWritten mb.pw then
          annotPwPi C env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, pw⟩)
        else pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, mb.pw⟩))
      ((G : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (G : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        if mode.verified && !pwWritten mb.pw then
          annotPwPi G env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, pw⟩)
        else pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, mb.pw⟩))
    refine DiscV.bind (ih.site_annotate hwtb.1) (fun ty' hty' => ?_)
    refine DiscV.bind (ih.site_annotate
      (WScoped.instantiate1 hty' 0 hwtb.2)) (fun body' hbody' => ?_)
    -- task #161 P5: the write is one more scoped call on the annotated
    -- body; the node's scoping does not depend on the datum, so both
    -- branches close the same way.
    have hnode : WScoped d ty' ∧ WScoped d (body'.abstract1 d) :=
      ⟨hty', WScoped.abstract1 0 hbody'⟩
    split
    · refine DiscV.bind (annotPwPi_disc ih henv hbody') (fun pw _ => ?_)
      exact DiscV.pure (by simp only [WScoped]; exact hnode)
    · exact DiscV.pure (by simp only [WScoped]; exact hnode)
  | .lam n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (C : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        if mode.verified && !pwWritten mb.pw then
          annotPwLam C env (d + 1) body' >>= fun pw =>
            pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, pw⟩)
        else pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, mb.pw⟩))
      ((G : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (G : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        if mode.verified && !pwWritten mb.pw then
          annotPwLam G env (d + 1) body' >>= fun pw =>
            pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, pw⟩)
        else pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, mb.pw⟩))
    refine DiscV.bind (ih.site_annotate hwtb.1) (fun ty' hty' => ?_)
    refine DiscV.bind (ih.site_annotate
      (WScoped.instantiate1 hty' 0 hwtb.2)) (fun body' hbody' => ?_)
    -- task #161 P5: the write is one more scoped call on the annotated
    -- body; the node's scoping does not depend on the datum, so both
    -- branches close the same way.
    have hnode : WScoped d ty' ∧ WScoped d (body'.abstract1 d) :=
      ⟨hty', WScoped.abstract1 0 hbody'⟩
    split
    · refine DiscV.bind (annotPwLam_disc ih henv hbody') (fun pw _ => ?_)
      exact DiscV.pure (by simp only [WScoped]; exact hnode)
    · exact DiscV.pure (by simp only [WScoped]; exact hnode)
  | .proj sn i pe =>
    have hwpe : WScoped d pe := by simpa only [WScoped] using hw
    show DiscV mode env _
      ((C : CoreFns CheckSM).annotate d pe >>= fun e' =>
        (C : CoreFns CheckSM).inferIO d e' >>= fun te₀ =>
        (C : CoreFns CheckSM).whnf d te₀ >>= fun te =>
        match te.getAppFn with
        | .const T _ =>
          match env.findProj? T i with
          | some entry =>
            if entry.tower then
              if te.getAppArgs.length = entry.numParams then
                pure (Expr.proj T i e')
              else throw (.invalid "projection parameter mismatch")
            else throw (.invalid
              "projection from a propositional structure must be a proposition")
          | none => throw (if (env.findProj? T 0).isSome then
              CheckError.invalid "projection index out of range"
            else .notImplemented "projection on a non-structure-like type")
        | _ => throw (.notImplemented "projection on a non-structure type"))
      ((G : CoreFns CheckSM).annotate d pe >>= fun e' =>
        (G : CoreFns CheckSM).inferIO d e' >>= fun te₀ =>
        (G : CoreFns CheckSM).whnf d te₀ >>= fun te =>
        match te.getAppFn with
        | .const T _ =>
          match env.findProj? T i with
          | some entry =>
            if entry.tower then
              if te.getAppArgs.length = entry.numParams then
                pure (Expr.proj T i e')
              else throw (.invalid "projection parameter mismatch")
            else throw (.invalid
              "projection from a propositional structure must be a proposition")
          | none => throw (if (env.findProj? T 0).isSome then
              CheckError.invalid "projection index out of range"
            else .notImplemented "projection on a non-structure-like type")
        | _ => throw (.notImplemented "projection on a non-structure type"))
    refine DiscV.bind (ih.site_annotate hwpe) (fun e' he' => ?_)
    refine DiscV.bind (ih.site_inferIO henv he') (fun te₀ hte₀ => ?_)
    refine DiscV.bind (ih.site_whnf henv hte₀) (fun te hte => ?_)
    split <;> try exact DiscV.throw _
    split <;> try exact DiscV.throw _
    split
    · split
      · refine DiscV.pure ?_
        show WScoped d (Expr.proj _ i e')
        simpa only [WScoped] using he'
      · exact DiscV.throw _
    · exact DiscV.throw _

set_option maxHeartbeats 1600000 in
theorem inferBody_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) (inferBody mode C env d e)
      (inferBody mode G env d e) := by
  match e with
  | .bvar _ => exact DiscV.throw _
  | .letE _ ty v b =>
    have hwtvb : WScoped d ty ∧ WScoped d v ∧ WScoped d b := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_infer henv hwtvb.1) (fun tty htty => ?_)
    refine DiscV.bind (ensureSort_disc ih henv htty) (fun u _ => ?_)
    refine DiscV.bind (ih.site_infer henv hwtvb.2.1) (fun tv htv => ?_)
    refine DiscV.bind (ih.site_defeq htv hwtvb.1) (fun r _ => ?_)
    split
    · exact ih.site_infer henv
        (WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
    · exact DiscV.throw _
  | .lit (.strVal s) =>
    show DiscV mode env _
      (if strLitSupported env then pure (Expr.const stringName [])
       else throw (.notImplemented
         "string literals before the String support declarations"))
      (if strLitSupported env then pure (Expr.const stringName [])
       else throw (.notImplemented
         "string literals before the String support declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .sort u => exact DiscV.pure (by simp [WScoped])
  | .fvar idx n ty =>
    have h' : idx < d ∧ WScoped idx ty := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      (if idx < d then pure ty
       else throw (.invalid "free variable out of scope"))
      (if idx < d then pure ty
       else throw (.invalid "free variable out of scope"))
    split
    · exact DiscV.pure (WScoped.mono (Nat.le_of_lt h'.1) h'.2)
    · exact DiscV.throw _
  | .lit (.natVal n) =>
    show DiscV mode env _
      (if natLitSupported env then pure (Expr.const natName [])
       else throw (.invalid "Nat literal without the Nat basis declarations"))
      (if natLitSupported env then pure (Expr.const natName [])
       else throw (.invalid "Nat literal without the Nat basis declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .const n us =>
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    split <;> try exact DiscV.throw _
    rename_i ci hfn
    split
    · split
      · refine DiscV.pure ?_
        obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
        exact wscoped_instLevels_of_not_hasFvar htf _ _
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
        (fun _ h => h.elim)
  | .forallE n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_infer henv hwtb.1) (fun tty htty => ?_)
    refine DiscV.bind (ih.site_whnf henv htty) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_infer henv
      (WScoped.instantiate1 hwtb.1 0 hwtb.2)) (fun bt hbt => ?_)
    refine DiscV.bind (ensureSort_disc ih henv hbt) (fun v _ => ?_)
    split
    · split
      · exact DiscV.pure (by simp [WScoped])
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact DiscV.pure (by simp [WScoped])
  | .lam n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_infer henv hwtb.1) (fun tty htty => ?_)
    refine DiscV.bind (ih.site_whnf henv htty) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_infer henv
      (WScoped.instantiate1 hwtb.1 0 hwtb.2)) (fun bt hbt => ?_)
    -- the λ-annotation validation (tasks #152/#161), at the verified
    -- modes: chain rule at outer binders, sort computation at the
    -- innermost
    have hpure : DiscV mode env
        (fun r => Expr.WScoped d r)
        (pure (Expr.forallE n ty (bt.abstract1 d) mb))
        (pure (Expr.forallE n ty (bt.abstract1 d) mb)) :=
      DiscV.pure (by
        simp only [WScoped]
        exact ⟨hwtb.1, WScoped.abstract1 0 hbt⟩)
    split
    · cases body.lamPw with
      | some pwI =>
        dsimp only
        split
        · exact hpure
        · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
      | none =>
        dsimp only
        refine DiscV.bind (ih.site_inferIO henv hbt) (fun btt hbtt => ?_)
        refine DiscV.bind (ensureSort_disc ih henv hbtt) (fun v _ => ?_)
        split
        · exact hpure
        · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
    · exact hpure
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_infer henv hwfa.1) (fun tf htf => ?_)
    refine DiscV.bind (ih.site_whnf henv htf) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    rename_i nw tyw bodyw mbw
    have hwtb : WScoped d tyw ∧ WScoped d bodyw := by
      simpa only [WScoped] using hww
    refine DiscV.bind (ih.site_infer henv hwfa.2) (fun ta hta => ?_)
    refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
    split
    · exact DiscV.pure (WScoped.instantiate1_gen hwfa.2 0 hwtb.2)
    · first
        | exact DiscV.throw _
        | exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
  | .proj sn i pe =>
    have hwpe : WScoped d pe := by simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_infer henv hwpe) (fun tpe htpe => ?_)
    refine DiscV.bind (ih.site_whnf henv htpe) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    rename_i Tw usw hfnw
    split <;> try exact DiscV.throw _
    rename_i entry hfpw
    split <;> try exact DiscV.throw _
    rename_i hcond
    -- task #175 S1: the body at the spine and the subject — scoped
    -- because the stored body is fvar-free and the spine and subject are
    have hres : DiscV mode env (WScoped d)
        (pure (entry.typeAt usw w.getAppArgs pe) : CheckSM Expr)
        (pure (entry.typeAt usw w.getAppArgs pe) : CheckSM Expr) :=
      DiscV.pure (projEntry_typeAt_WScoped henv hfpw usw hcond.2.2.1
        (fun a ha => hww.getAppArgs a ha) hwpe)
    -- the Prop guard (task #175 W4c) runs no walk of its own
    split
    · split
      · exact hres
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact hres

/-- The io inference body's walk (task #172 B4): `inferBody_disc` over
the io-grade views — the recursion sites are the io slot
(`site_inferIO`), the reduction/conversion sites are the shared knot's,
and the application clause splits on the (data-only) gate; the gated
arm consumes no certificate site at all. -/
theorem inferBodyIO_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d)
      (inferBodyIO mode (CoreFns.ioView C) env d e)
      (inferBodyIO mode (CoreFns.ioView G) env d e) := by
  match e with
  | .bvar _ => exact DiscV.throw _
  | .letE _ ty v b =>
    have hwtvb : WScoped d ty ∧ WScoped d v ∧ WScoped d b := by
      simpa only [WScoped] using hw
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_inferIO henv hwtvb.1) (fun tty htty => ?_)
    refine DiscV.bind (ensureSort_disc ih henv htty) (fun u _ => ?_)
    refine DiscV.bind (ih.site_inferIO henv hwtvb.2.1) (fun tv htv => ?_)
    refine DiscV.bind (ih.site_defeq htv hwtvb.1) (fun r _ => ?_)
    split
    · exact ih.site_inferIO henv
        (WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
    · exact DiscV.throw _
  | .lit (.strVal s) =>
    show DiscV mode env _
      (if strLitSupported env then pure (Expr.const stringName [])
       else throw (.notImplemented
         "string literals before the String support declarations"))
      (if strLitSupported env then pure (Expr.const stringName [])
       else throw (.notImplemented
         "string literals before the String support declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .sort u => exact DiscV.pure (by simp [WScoped])
  | .fvar idx n ty =>
    have h' : idx < d ∧ WScoped idx ty := by
      simpa only [WScoped] using hw
    show DiscV mode env _
      (if idx < d then pure ty
       else throw (.invalid "free variable out of scope"))
      (if idx < d then pure ty
       else throw (.invalid "free variable out of scope"))
    split
    · exact DiscV.pure (WScoped.mono (Nat.le_of_lt h'.1) h'.2)
    · exact DiscV.throw _
  | .lit (.natVal n) =>
    show DiscV mode env _
      (if natLitSupported env then pure (Expr.const natName [])
       else throw (.invalid "Nat literal without the Nat basis declarations"))
      (if natLitSupported env then pure (Expr.const natName [])
       else throw (.invalid "Nat literal without the Nat basis declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .const n us =>
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    split <;> try exact DiscV.throw _
    rename_i ci hfn
    split
    · split
      · refine DiscV.pure ?_
        obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
        exact wscoped_instLevels_of_not_hasFvar htf _ _
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
        (fun _ h => h.elim)
  | .forallE n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_inferIO henv hwtb.1) (fun tty htty => ?_)
    refine DiscV.bind (ih.site_whnf henv htty) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_inferIO henv
      (WScoped.instantiate1 hwtb.1 0 hwtb.2)) (fun bt hbt => ?_)
    refine DiscV.bind (ensureSort_disc ih henv hbt) (fun v _ => ?_)
    split
    · split
      · exact DiscV.pure (by simp [WScoped])
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact DiscV.pure (by simp [WScoped])
  | .lam n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    -- task #168 stage 2: no domain-sort run at the io λ clause
    refine DiscV.bind (ih.site_inferIO henv
      (WScoped.instantiate1 hwtb.1 0 hwtb.2)) (fun bt hbt => ?_)
    have hpure : DiscV mode env
        (fun r => Expr.WScoped d r)
        (pure (Expr.forallE n ty (bt.abstract1 d) mb))
        (pure (Expr.forallE n ty (bt.abstract1 d) mb)) :=
      DiscV.pure (by
        simp only [WScoped]
        exact ⟨hwtb.1, WScoped.abstract1 0 hbt⟩)
    split
    · cases body.lamPw with
      | some pwI =>
        dsimp only
        split
        · exact hpure
        · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
      | none =>
        dsimp only
        refine DiscV.bind (ih.site_inferIO henv hbt) (fun btt hbtt => ?_)
        refine DiscV.bind (ensureSort_disc ih henv hbtt) (fun v _ => ?_)
        split
        · exact hpure
        · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
    · exact hpure
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_inferIO henv hwfa.1) (fun tf htf => ?_)
    refine DiscV.bind (ih.site_whnf henv htf) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    rename_i nw tyw bodyw mbw
    have hwtb : WScoped d tyw ∧ WScoped d bodyw := by
      simpa only [WScoped] using hww
    -- the io gate: data only; the fired arm consumes no site
    split
    · exact DiscV.pure (WScoped.instantiate1_gen hwfa.2 0 hwtb.2)
    · refine DiscV.bind (ih.site_inferIO henv hwfa.2) (fun ta hta => ?_)
      refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
      split
      · exact DiscV.pure (WScoped.instantiate1_gen hwfa.2 0 hwtb.2)
      · first
          | exact DiscV.throw _
          | exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
              (fun _ h => h.elim)
  | .proj sn i pe =>
    have hwpe : WScoped d pe := by simpa only [WScoped] using hw
    unfold inferBodyIO
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    refine DiscV.bind (ih.site_inferIO henv hwpe) (fun tpe htpe => ?_)
    refine DiscV.bind (ih.site_whnf henv htpe) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    rename_i Tw usw hfnw
    split <;> try exact DiscV.throw _
    rename_i entry hfpw
    split <;> try exact DiscV.throw _
    rename_i hcond
    -- task #175 S1: the body at the spine and the subject — scoped
    -- because the stored body is fvar-free and the spine and subject are
    have hres : DiscV mode env (WScoped d)
        (pure (entry.typeAt usw w.getAppArgs pe) : CheckSM Expr)
        (pure (entry.typeAt usw w.getAppArgs pe) : CheckSM Expr) :=
      DiscV.pure (projEntry_typeAt_WScoped henv hfpw usw hcond.2.2.1
        (fun a ha => hww.getAppArgs a ha) hwpe)
    -- the Prop guard (task #175 W4c) runs no walk of its own
    split
    · split
      · exact hres
      · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
          (fun _ h => h.elim)
    · exact hres

set_option maxHeartbeats 1600000 in
/-- The eq-true shortcut (the audit's E2) runs one `whnf` on both records. -/
theorem boolTrueShortcut_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a : Expr} (hwa : WScoped d a) :
    DiscV mode env (fun _ => True) (boolTrueShortcut C d a)
      (boolTrueShortcut G d a) := by
  unfold boolTrueShortcut
  exact DiscV.bind (ih.site_whnf henv hwa) (fun w _ => DiscV.pure trivial)

/-- `boolTrueShortcut_disc` under its guard. -/
theorem boolTrueShortcutIf_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a : Expr} (hwa : WScoped d a) (g : Bool) :
    DiscV mode env (fun _ => True)
      (if g then boolTrueShortcut C d a else pure false)
      (if g then boolTrueShortcut G d a else pure false) := by
  cases g
  · exact DiscV.pure trivial
  · exact boolTrueShortcut_disc ih henv hwa

/-- `propIrrel_disc` under the once-per-entry gate (the audit's D3): the
pruned branch is `pure false` on both records. -/
theorem propIrrelIf_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) (g : Bool) :
    DiscV mode env (fun _ => True)
      (if g then propIrrel mode C env d a b else pure false)
      (if g then propIrrel mode G env d a b else pure false) := by
  cases g
  · exact DiscV.pure trivial
  · exact propIrrel_disc ih henv hwa hwb

theorem defeqStep_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} {kC kG : Bool → Expr → Expr → _}
    (hk : ∀ (pi : Bool) {x y : Expr}, WScoped d x → WScoped d y →
      DiscV mode env (fun _ => True) (kC pi x y) (kG pi x y))
    (pi : Bool) (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (defeqStep mode C env d kC pi a b)
      (defeqStep mode G env d kG pi a b) := by
  unfold defeqStep
  -- (the two leading conditionals by `DiscV.ite`: `split` on the grown
  -- body exceeds the simp step budget)
  refine DiscV.ite (fun _ => DiscV.pure trivial) (fun _ => ?_)
  refine DiscV.bind (boolTrueShortcutIf_disc ih henv hwa _) (fun rbt _ => ?_)
  refine DiscV.ite (fun _ => DiscV.pure trivial) (fun _ => ?_)
  refine DiscV.bind (ih.site_whnfCore henv hwa) (fun a' ha' => ?_)
  refine DiscV.bind (ih.site_whnfCore henv hwb) (fun b' hb' => ?_)
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (propIrrelIf_disc ih henv ha' hb' _) (fun rpi _ => ?_)
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (reduceNatIf_disc ih henv ha' _) (fun o₁ ho₁ => ?_)
  split
  · exact hk _ (ho₁ _ rfl) hb'
  refine DiscV.bind (reduceNatIf_disc ih henv hb' _) (fun o₂ ho₂ => ?_)
  split
  · exact hk _ ha' (ho₂ _ rfl)
  -- lazy delta: the decision first, each unfolding materialized only
  -- inside the branch that consumes it (task #106)
  split
  case h_1 =>
    split
    · rename_i a₂ hua
      exact hk _ (unfoldDefinition_WScoped henv hua ha') hb'
    · exact DiscV.pure trivial
  case h_2 =>
    split
    · rename_i b₂ hub
      exact hk _ ha' (unfoldDefinition_WScoped henv hub hb')
    · exact DiscV.pure trivial
  case h_3 =>
    have hboth : DiscV mode env (fun _ => True)
        (match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => kC false a₂ b₂
          | _, _ => pure false)
        (match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => kG false a₂ b₂
          | _, _ => pure false) := by
      split
      · rename_i a₂ b₂ hua hub
        exact hk _ (unfoldDefinition_WScoped henv hua ha')
          (unfoldDefinition_WScoped henv hub hb')
      · exact DiscV.pure trivial
    dsimp only []
    split
    · split
      · rename_i a₂ hua
        exact hk _ (unfoldDefinition_WScoped henv hua ha') hb'
      · exact DiscV.pure trivial
    split
    · split
      · rename_i b₂ hub
        exact hk _ ha' (unfoldDefinition_WScoped henv hub hb')
      · exact DiscV.pure trivial
    split
    · refine DiscV.bind (defeqSpine_disc ih ha' hb') (fun sp _ => ?_)
      split
      · exact DiscV.pure trivial
      · exact hboth
    · exact hboth
  case h_4 =>
    rename_i hua hub
    split
    case h_1 => exact DiscV.liftFueled_true _ _
    case h_2 => exact DiscV.pure trivial
    case h_3 =>
      split
      · exact DiscV.pure trivial
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_4 =>
      split
      · exact DiscV.pure trivial
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_5 =>
      rename_i nn f1 x hne
      split
      case h_1 =>
        rename_i k c
        have hx : WScoped d (Expr.const c []) ∧ WScoped d x := by
          simpa only [WScoped] using hb'
        split
        · exact ih.site_defeq (by simp [WScoped]) hx.2
        · exact stuckIrrel_disc ih henv ha' hb'
      case h_2 => exact stuckIrrel_disc ih henv ha' hb'
    case h_6 =>
      rename_i f1 x nn hne
      split
      case h_1 =>
        rename_i k c
        have hx : WScoped d (Expr.const c []) ∧ WScoped d x := by
          simpa only [WScoped] using ha'
        split
        · exact ih.site_defeq hx.2 (by simp [WScoped])
        · exact stuckIrrel_disc ih henv ha' hb'
      case h_2 => exact stuckIrrel_disc ih henv ha' hb'
    case h_7 =>
      rename_i st cO usO x hne
      split
      · exact ih.site_defeq (strLitToConstructor_WScoped st d) hb'
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_8 =>
      rename_i cO usO x st hne
      split
      · exact ih.site_defeq ha' (strLitToConstructor_WScoped st d)
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_9 =>
      split
      · exact DiscV.pure trivial
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_10 =>
      split
      · refine DiscV.bind (DiscV.liftFueled_true _ _) (fun ok _ => ?_)
        split
        · exact DiscV.pure trivial
        · exact stuckIrrel_disc ih henv ha' hb'
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_11 =>
      rename_i n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ hne
      have h1 : WScoped d ty₁ ∧ WScoped d body₁ := by
        simpa only [WScoped] using ha'
      have h2 : WScoped d ty₂ ∧ WScoped d body₂ := by
        simpa only [WScoped] using hb'
      refine DiscV.bind (ih.site_defeq h1.1 h2.1) (fun r₁ _ => ?_)
      split
      · refine DiscV.bind (ih.site_defeq
          (WScoped.instantiate1 h1.1 0 h1.2)
          (WScoped.instantiate1 h2.1 0 h2.2)) (fun r₂ _ => ?_)
        split
        · split
          · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
              (fun _ h => h.elim)
          · exact DiscV.pure trivial
        · exact DiscV.pure trivial
      · exact DiscV.pure trivial
    case h_12 =>
      rename_i n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ hne
      have h1 : WScoped d ty₁ ∧ WScoped d body₁ := by
        simpa only [WScoped] using ha'
      have h2 : WScoped d ty₂ ∧ WScoped d body₂ := by
        simpa only [WScoped] using hb'
      refine DiscV.bind (ih.site_defeq h1.1 h2.1) (fun r₁ _ => ?_)
      split
      · refine DiscV.bind (ih.site_defeq
          (WScoped.instantiate1 h1.1 0 h1.2)
          (WScoped.instantiate1 h2.1 0 h2.2)) (fun r₂ _ => ?_)
        split
        · split
          · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
              (fun _ h => h.elim)
          · exact DiscV.pure trivial
        · exact DiscV.pure trivial
      · exact DiscV.pure trivial
    case h_13 =>
      -- spine-wise congruence (task #106)
      rename_i f₁ a₁ f₂ a₂ hne
      have hwa' : WScoped d (Expr.app f₁ a₁) := ha'
      have hwb' : WScoped d (Expr.app f₂ a₂) := hb'
      split
      · refine DiscV.bind (ih.site_defeq hwa'.getAppFn hwb'.getAppFn)
          (fun r₁ _ => ?_)
        split
        · refine DiscV.bind
            (defEqList_disc ih hwa'.getAppArgs hwb'.getAppArgs)
            (fun r₂ _ => ?_)
          split
          · exact DiscV.pure trivial
          · exact stuckIrrel_disc ih henv ha' hb'
        · exact stuckIrrel_disc ih henv ha' hb'
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_14 =>
      rename_i s₁ i₁ e₁ s₂ i₂ e₂ hne
      have h1 : WScoped d e₁ := by simpa only [WScoped] using ha'
      have h2 : WScoped d e₂ := by simpa only [WScoped] using hb'
      split
      · refine DiscV.bind (ih.site_defeq h1 h2) (fun r₁ _ => ?_)
        split
        · exact DiscV.pure trivial
        · exact stuckIrrel_disc ih henv ha' hb'
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_15 =>
      rename_i n₁ ty₁ body₁ m₁ hne hx₁
      have h1 : WScoped d ty₁ ∧ WScoped d body₁ := by
        simpa only [WScoped] using ha'
      refine DiscV.bind (etaCert_disc ih henv h1.1 h1.2 hb')
        (fun r₁ _ => ?_)
      split
      · exact DiscV.pure trivial
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_16 =>
      rename_i n₂ ty₂ body₂ m₂ hne hx₁
      have h2 : WScoped d ty₂ ∧ WScoped d body₂ := by
        simpa only [WScoped] using hb'
      refine DiscV.bind (etaCert_disc ih henv h2.1 h2.2 ha')
        (fun r₁ _ => ?_)
      split
      · exact DiscV.pure trivial
      · exact stuckIrrel_disc ih henv ha' hb'
    case h_17 => exact stuckIrrel_disc ih henv ha' hb'

theorem defeqLoop_disc (ih : ScopedSim mode env f) (henv : EnvWF env) :
    ∀ (n : Nat) {d : Nat} (pi : Bool) {a b : Expr}, WScoped d a → WScoped d b →
      DiscV mode env (fun _ => True) (defeqLoop mode C env d n pi a b)
        (defeqLoop mode G env d n pi a b)
  | 0, _, _, _, _, _, _ => DiscV.throw _
  | n + 1, _, pi, _, _, hwa, hwb =>
    defeqStep_disc ih henv
      (fun pi' {_ _} hx hy => defeqLoop_disc ih henv n pi' hx hy) pi hwa hwb

theorem defeqBody_disc (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) (defeqBody mode C env d a b)
      (defeqBody mode G env d a b) :=
  defeqLoop_disc ih henv defeqLoopFuel true hwa hwb

end Walks

end Setlec
