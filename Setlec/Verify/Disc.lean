import Setlec.Verify.Scoped

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
local notation "C" => cachedFns env f
local notation "G" => gFns env f

theorem ensureSort_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (fun _ => True) (ensureSort C env d e)
      (ensureSort G env d e) := by
  show DiscV env _
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

theorem reduceNat_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScopedO d) (reduceNat C env d e)
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
        · cases rawNatLit? a with
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
          · refine DiscV.bind (ih.site_whnf henv hwgb.2) (fun w₁ _ => ?_)
            refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
            cases rawNatLit? w₁ with
            | none =>
              cases rawNatLit? w₂ <;> exact DiscV.pure WScopedO.none
            | some n₁ =>
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
              refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
              cases rawNatLit? w₁ with
              | none =>
                cases rawNatLit? w₂ <;> exact DiscV.pure WScopedO.none
              | some _ =>
                cases rawNatLit? w₂ with
                | none => exact DiscV.pure WScopedO.none
                | some _ => exact DiscV.throw _
            · exact DiscV.pure WScopedO.none

theorem iotaCerts_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      DiscV env (fun _ => True) (iotaCerts C env d ty args)
        (iotaCerts G env d ty args) := by
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
      show DiscV env _
        ((C : CoreFns CheckSM).infer d arg >>= fun ta =>
          (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts C env d (body.instantiate1 arg) rest
          else pure false)
        ((G : CoreFns CheckSM).infer d arg >>= fun ta =>
          (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts G env d (body.instantiate1 arg) rest
          else pure false)
      refine DiscV.bind (ih.site_infer henv hwarg) (fun ta hta => ?_)
      refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact ihrest (WScoped.instantiate1_gen hwarg 0 hwtb.2) hwrest
      | false => exact DiscV.pure trivial
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ => exact DiscV.pure trivial

theorem defEqList_disc (ih : ScopedSim env f) {d : Nat} :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      DiscV env (fun _ => True) (defEqList C env d as bs)
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
      show DiscV env _
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

theorem defeqSpine_disc (ih : ScopedSim env f) {d : Nat} {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (defeqSpine C env d a b)
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

theorem proofIrrel_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (proofIrrel C env d a b)
      (proofIrrel G env d a b) := by
  unfold proofIrrel
  refine DiscV.bind (ih.site_infer henv hwa) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_whnf henv hta) (fun w₁ _ => ?_)
  split
  · refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
    refine DiscV.bind (ih.site_whnf henv htb) (fun w₂ _ => ?_)
    split
    · exact DiscV.pure trivial
    · exact DiscV.pure trivial
  · refine DiscV.bind (ih.site_infer henv hta) (fun tta htta => ?_)
    refine DiscV.bind (ih.site_whnf henv htta) (fun w _ => ?_)
    cases w <;> try exact DiscV.pure trivial
    case sort uT =>
      refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okA _ => ?_)
      refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
      refine DiscV.bind (ih.site_infer henv htb) (fun ttb httb => ?_)
      refine DiscV.bind (ih.site_whnf henv httb) (fun w' _ => ?_)
      cases w' <;> try exact DiscV.pure trivial
      case sort vT =>
        refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okB _ => ?_)
        exact DiscV.pure trivial

theorem pairEtaCert_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (pairEtaCert C env d a b)
      (pairEtaCert G env d a b) := by
  unfold pairEtaCert
  split
  case _ c us pα pβ s₁ s₂ =>
    have hws : WScoped d s₁ ∧ WScoped d s₂ := by
      simp only [WScoped] at hwa
      exact ⟨hwa.1.2, hwa.2⟩
    split
    case _ cvm =>
      refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
      refine DiscV.bind (ih.site_whnf henv htb) (fun wtb _ => ?_)
      split
      case _ c' us' A B =>
        split
        case _ =>
          split
          case _ rr =>
            split
            · refine DiscV.bind (DiscV.liftFueled_true _ _)
                (fun ok _ => ?_)
              split
              · refine DiscV.bind (ih.site_defeq hws.1 ?_)
                  (fun r₁ _ => ?_)
                · simpa only [WScoped] using hwb
                · split
                  · refine ih.site_defeq hws.2 ?_
                    simpa only [WScoped] using hwb
                  · exact DiscV.pure trivial
              · exact DiscV.pure trivial
            · exact DiscV.pure trivial
          all_goals exact DiscV.pure trivial
        all_goals exact DiscV.pure trivial
      all_goals exact DiscV.pure trivial
    all_goals exact DiscV.pure trivial
  all_goals exact DiscV.pure trivial

theorem structEtaProjCerts_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} (T : Name) (us' : List Level) {targs : List Expr} {b : Expr}
    (lpsT : List Name) (hwt : ∀ x ∈ targs, WScoped d x)
    (hwb : WScoped d b) :
    ∀ (idxs : List Nat),
      DiscV env (fun _ => True)
        (structEtaProjCerts C env d T us' targs b lpsT idxs)
        (structEtaProjCerts G env d T us' targs b lpsT idxs) := by
  intro idxs
  induction idxs with
  | nil => exact DiscV.pure trivial
  | cons i rest ihrest =>
    show DiscV env _
      (match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            iotaCerts C env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) >>= fun r =>
              if r then structEtaProjCerts C env d T us' targs b lpsT rest
              else pure false
          else pure false
        | _ => pure false)
      (match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            iotaCerts G env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) >>= fun r =>
              if r then structEtaProjCerts G env d T us' targs b lpsT rest
              else pure false
          else pure false
        | _ => pure false)
    cases hf : env.find? (projFnName T i) with
    | none => exact DiscV.pure trivial
    | some ci =>
      cases ci with
      | recInfo cvp nP nM nm ni rules =>
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
      | axiomInfo cv => exact DiscV.pure trivial
      | defnInfo cv value hint => exact DiscV.pure trivial
      | thmInfo cv value => exact DiscV.pure trivial
      | indInfo cv caps => exact DiscV.pure trivial
      | ctorInfo cv nP nF => exact DiscV.pure trivial

theorem structEtaCertWith_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b wtb : Expr} (hwa : WScoped d a) (hwb : WScoped d b)
    (hwwtb : WScoped d wtb) :
    DiscV env (fun _ => True) (structEtaCertWith C env d a b wtb)
      (structEtaCertWith G env d a b wtb) := by
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
  refine DiscV.bind (structEtaProjCerts_disc ih henv T us'
    cvT.levelParams hwwtb.getAppArgs hwb _) (fun r₂ _ => ?_)
  split <;> try exact DiscV.pure trivial
  refine DiscV.bind (defEqList_disc ih
    (fun x hx => hwa.getAppArgs x (List.mem_of_mem_take hx))
    hwwtb.getAppArgs) (fun r₃ _ => ?_)
  split <;> try exact DiscV.pure trivial
  refine defEqList_disc ih
    (fun x hx => hwa.getAppArgs x (List.mem_of_mem_drop hx)) ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hwwtb.getAppArgs y hy
  · rcases List.mem_singleton.mp hy with rfl
    exact hwb

theorem structEtaCert_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (structEtaCert C env d a b)
      (structEtaCert G env d a b) := by
  unfold structEtaCert
  refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
  refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
  exact structEtaCertWith_disc ih henv hwa hwb hwtb

theorem structUnitCert_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (structUnitCert C env d a b)
      (structUnitCert G env d a b) := by
  unfold structUnitCert
  refine DiscV.bind (ih.site_infer henv hwa) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_whnf henv hta) (fun wta hwta => ?_)
  split <;> try exact DiscV.pure trivial
  rename_i T us' heqw
  split <;> try exact DiscV.pure trivial
  rename_i cvT caps hfT
  split <;> try exact DiscV.pure trivial
  refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
  refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
  refine DiscV.bind (ih.site_defeq hwta hwtb) (fun r _ => ?_)
  split <;> try exact DiscV.pure trivial
  have htyw : WScoped d
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  exact iotaCerts_disc ih henv htyw hwta.getAppArgs

theorem etaCert_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {n₁ : Name} {ty₁ body₁ : Expr} {m₁ : BinderMeta} {b : Expr}
    (hwty : WScoped d ty₁) (hwbody : WScoped d body₁)
    (hwb : WScoped d b) :
    DiscV env (fun _ => True) (etaCert C env d n₁ ty₁ body₁ m₁ b)
      (etaCert G env d n₁ ty₁ body₁ m₁ b) := by
  unfold etaCert
  refine DiscV.bind (ih.site_infer henv hwb) (fun tb htb => ?_)
  refine DiscV.bind (ih.site_whnf henv htb) (fun wtb hwtb => ?_)
  split <;> try exact DiscV.pure trivial
  rename_i n₂ ty₂ body₂ m₂
  have hwty₂ : WScoped d ty₂ := by
    simp only [WScoped] at hwtb
    exact hwtb.1
  cases hc₁ : m₁.cod with
  | none => exact DiscV.pure trivial
  | some v₁ =>
    cases hc₂ : m₂.cod with
    | none => exact DiscV.pure trivial
    | some v₂ =>
      refine DiscV.bind (DiscV.liftFueled_true _ _) (fun ok _ => ?_)
      split <;> try exact DiscV.pure trivial
      refine DiscV.bind (ih.site_defeq hwty₂ hwty) (fun r _ => ?_)
      split <;> try exact DiscV.pure trivial
      refine ih.site_defeq (WScoped.instantiate1 hwty 0 hwbody) ?_
      show WScoped (d + 1) (.app b (.fvar d n₁ ty₁))
      simp only [WScoped]
      exact ⟨WScoped.mono (Nat.le_succ d) hwb, Nat.lt_succ_self d, hwty⟩

theorem projCert_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e₂ : Expr} {i : Nat} {us : List Level} {nP : Nat}
    (hwe : WScoped d e₂) :
    DiscV env (fun _ => True) (projCert C env d e₂ i us nP)
      (projCert G env d e₂ i us nP) := by
  unfold projCert
  have hwarg : WScoped d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) :=
    wscoped_getD hwe.getAppArgs _
  refine DiscV.bind (ih.site_infer henv hwarg) (fun ta hta => ?_)
  refine DiscV.bind (ih.site_infer henv hta) (fun tta htta => ?_)
  refine DiscV.bind (ih.site_whnf henv htta) (fun w _ => ?_)
  cases w <;> try exact DiscV.pure trivial
  case sort uT =>
    refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okT _ => ?_)
    refine DiscV.bind (ih.site_infer henv hwe) (fun te hte => ?_)
    refine DiscV.bind (ih.site_infer henv hte) (fun tte htte => ?_)
    refine DiscV.bind (ih.site_whnf henv htte) (fun w' _ => ?_)
    cases w' <;> try exact DiscV.pure trivial
    case sort wT =>
      refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okW _ => ?_)
      exact DiscV.pure trivial

theorem stuckIrrel_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (stuckIrrel C env d a b)
      (stuckIrrel G env d a b) := by
  unfold stuckIrrel
  refine DiscV.bind (pairEtaCert_disc ih henv hwa hwb) (fun r₁ _ => ?_)
  split
  · exact DiscV.pure trivial
  refine DiscV.bind (pairEtaCert_disc ih henv hwb hwa) (fun r₂ _ => ?_)
  split
  · exact DiscV.pure trivial
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

theorem majorToCtor_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {major : Expr}
    (hmaj : WScoped d major) :
    DiscV env (WScoped d) (majorToCtor C env d recName rules major)
      (majorToCtor G env d recName rules major) := by
  unfold majorToCtor
  split
  · exact DiscV.pure hmaj
  split <;> try exact DiscV.pure hmaj
  split <;> try exact DiscV.pure hmaj
  split <;> try exact DiscV.pure hmaj
  split <;> try exact DiscV.pure hmaj
  split
  · -- K branch
    refine DiscV.bind (ih.site_infer henv hmaj) (fun tm htm => ?_)
    refine DiscV.bind (ih.site_whnf henv htm) (fun tmaj htmaj => ?_)
    split <;> try exact DiscV.pure hmaj
    split <;> try exact DiscV.pure hmaj
    dsimp only []
    split
    · rename_i hguard
      have hwfab := WScoped.of_wscopedB
        (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)
      refine DiscV.bind (proofIrrel_disc ih henv hwfab hmaj)
        (fun r _ => ?_)
      split
      · exact DiscV.pure hwfab
      · exact DiscV.pure hmaj
    · exact DiscV.pure hmaj
  split
  · -- eta branch
    refine DiscV.bind (ih.site_infer henv hmaj) (fun tm htm => ?_)
    refine DiscV.bind (ih.site_whnf henv htm) (fun tmaj htmaj => ?_)
    split <;> try exact DiscV.pure hmaj
    split <;> try exact DiscV.pure hmaj
    dsimp only []
    split
    · rename_i hguard
      have hwfab := WScoped.of_wscopedB
        (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)
      refine DiscV.bind
        (structEtaCertWith_disc ih henv hwfab hmaj htmaj)
        (fun r _ => ?_)
      split
      · exact DiscV.pure hwfab
      · exact DiscV.pure hmaj
    · exact DiscV.pure hmaj
  · exact DiscV.pure hmaj

theorem isPropType_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {ty : Expr} (hwty : WScoped d ty) :
    DiscV env (fun _ => True) (isPropType C env d ty)
      (isPropType G env d ty) := by
  unfold isPropType
  refine DiscV.bind (ih.site_annotate hwty) (fun ty' hty' => ?_)
  refine DiscV.bind (ih.site_infer henv hty') (fun s hs => ?_)
  refine DiscV.bind (ensureSort_disc ih henv hs) (fun u _ => ?_)
  exact DiscV.liftFueled_true _ _

theorem projFieldDom_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {structProp : Bool} {sn : Name} {e' : Expr}
    (hwe : WScoped d e') :
    ∀ (k j : Nat) {tel : Expr}, WScoped d tel →
      DiscV env (WScoped d)
        (projFieldDom C env d structProp sn e' j k tel)
        (projFieldDom G env d structProp sn e' j k tel) := by
  intro k
  induction k with
  | zero =>
    intro j tel hwtel
    cases tel <;> try exact DiscV.throw _
    case forallE n dom rest mb =>
      have hw' : WScoped d dom ∧ WScoped d rest := by
        simpa only [WScoped] using hwtel
      exact DiscV.pure hw'.1
  | succ k ihk =>
    intro j tel hwtel
    cases tel <;> try exact DiscV.throw _
    case forallE n dom rest mb =>
      have hw' : WScoped d dom ∧ WScoped d rest := by
        simpa only [WScoped] using hwtel
      have hwrest' : WScoped d (rest.instantiate1 (.proj sn j e')) :=
        WScoped.instantiate1_gen
          (show WScoped d (.proj sn j e') by
            simpa only [WScoped] using hwe) 0 hw'.2
      dsimp only [projFieldDom]
      split
      · exact ihk (j + 1) hw'.2
      · split
        · refine DiscV.bind (isPropType_disc ih henv hw'.1)
            (fun b _ => ?_)
          split
          · exact ihk (j + 1) hwrest'
          · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
              (fun _ h => h.elim)
        · exact ihk (j + 1) hwrest'

theorem annotateProjRec_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {sn : Name} {i : Nat} {te e' : Expr} {us : List Level}
    (hwte : WScoped d te) (hwe : WScoped d e') :
    DiscV env (WScoped d) (annotateProjRec C env d sn i te e' us)
      (annotateProjRec G env d sn i te e' us) := by
  unfold annotateProjRec
  split <;> try exact DiscV.throw _
  rename_i cvR nP rule cvI capsI hfR hfI
  split <;> try exact DiscV.throw _
  rename_i cvC cnFdummy cnF hfC
  dsimp only []
  split <;> try exact DiscV.throw _
  split <;> try exact DiscV.throw _
  rename_i tel htel
  refine DiscV.bind (isPropType_disc ih henv hwte)
    (fun structProp _ => ?_)
  have hwtel : WScoped d tel := by
    refine instPis_WScoped htel ?_ hwte.getAppArgs
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfC)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine DiscV.bind (projFieldDom_disc ih henv hwe i 0 hwtel)
    (fun fi hfi => ?_)
  split <;> try exact DiscV.throw _
  refine DiscV.bind (ih.site_annotate hfi) (fun fi' hfi' => ?_)
  refine DiscV.bind (ih.site_infer henv hfi') (fun sfi₀ hsfi₀ => ?_)
  refine DiscV.bind (ensureSort_disc ih henv hsfi₀) (fun sfi _ => ?_)
  split
  · -- Prop structure: the field-sort check runs, then (under the
    -- inlined motive-level `if`) the scope guard
    refine DiscV.bind (DiscV.liftFueled_true _ _) (fun ok _ => ?_)
    split
    · split <;> split <;> first
        | exact DiscV.throw _
        | (rename_i hguard
           exact ih.site_annotate (WScoped.of_wscopedB
             (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)))
    · first
        | exact DiscV.throw _
        | exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
  · split <;> split <;> first
      | exact DiscV.throw _
      | (rename_i hguard
         exact ih.site_annotate (WScoped.of_wscopedB
           (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1)))

theorem annotateProjElim_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {sn : Name} {i : Nat} {te e' : Expr}
    (hwte : WScoped d te) (hwe : WScoped d e') :
    DiscV env (WScoped d) (annotateProjElim C env d sn i te e')
      (annotateProjElim G env d sn i te e') := by
  unfold annotateProjElim
  split <;> try exact DiscV.throw _
  split <;> try exact DiscV.throw _
  · split
    · dsimp only []
      split
      · split
        · rename_i hguard
          exact ih.site_annotate (WScoped.of_wscopedB
            (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1))
        · exact DiscV.throw _
      · exact DiscV.throw _
    · exact annotateProjRec_disc ih henv hwte hwe

theorem iotaRec_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScopedO d) (iotaRec C env d e)
      (iotaRec G env d e) := by
  unfold iotaRec
  split <;> try exact DiscV.pure WScopedO.none
  rename_i c us heqfn
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cv nP nM nm ni rules hfc
  dsimp only []
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind
    (ih.site_whnf henv (wscoped_getD hw.getAppArgs _))
    (fun major₀ hmaj₀ => ?_)
  refine DiscV.bind
    (majorToCtor_disc ih henv (litToCtorIfNat_WScoped hmaj₀))
    (fun major hmaj => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cj usj heqmfn
  split <;> try exact DiscV.pure WScopedO.none
  rename_i cvj cnP cnF hfj
  split <;> try exact DiscV.pure WScopedO.none
  rename_i rl hrule
  split <;> try exact DiscV.pure WScopedO.none
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (DiscV.liftFueled_true _ _) (fun okl _ => ?_)
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (defEqList_disc ih
    (fun x hx => hmaj.getAppArgs x (List.mem_of_mem_take hx))
    (fun x hx => hw.getAppArgs x (List.mem_of_mem_take hx)))
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
  split <;> try exact DiscV.pure WScopedO.none
  rename_i hstrip hresid
  split <;> try exact DiscV.pure WScopedO.none
  refine DiscV.bind (defEqList_disc ih
    (fun x hx => (piResidual_WScoped hresid hwctorty
      hmaj.getAppArgs).getAppArgs x (List.mem_of_mem_drop hx))
    (fun x hx => hw.getAppArgs x
      (List.mem_of_mem_take (List.mem_of_mem_drop hx))))
    (fun r₄ _ => ?_)
  split
  · refine DiscV.pure (WScopedO.some ?_)
    refine Expr.WScoped.mkAppN ?_ ?_
    · obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
      obtain ⟨hrf, -, -, -⟩ := hrules cv nP nM nm ni rules rfl rl
        (List.mem_of_find?_eq_some hrule)
      exact wscoped_instLevels_of_not_hasFvar hrf _ _
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hw.getAppArgs x (List.mem_of_mem_take hx)
      · exact hmaj.getAppArgs x (List.mem_of_mem_drop hx)
  · exact DiscV.pure WScopedO.none

theorem whnfCoreBody_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScoped d) (whnfCoreBody C env d e)
      (whnfCoreBody G env d e) := by
  match e with
  | .sort u | .fvar _ _ _ | .forallE _ _ _ _ | .lam _ _ _ _
  | .const _ _ | .lit _ =>
    exact DiscV.pure hw
  | .bvar _ | .letE _ _ _ _ => exact DiscV.throw _
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    show DiscV env _
      ((C : CoreFns CheckSM).whnfCore d g' >>= fun f' =>
        match f' with
        | .lam n ty body mb =>
          match mb.cod with
          | some v =>
            if v.isNonZero then
              (C : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
            else
              (C : CoreFns CheckSM).infer d a >>= fun ta =>
              (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
              if b then
                (C : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
              else pure (.app (.lam n ty body mb) a)
          | none => pure (.app (.lam n ty body mb) a)
        | f' =>
          iotaRec C env d (.app f' a) >>= fun o =>
          match o with
          | some e'' => (C : CoreFns CheckSM).whnfCore d e''
          | none => pure (.app f' a))
      ((G : CoreFns CheckSM).whnfCore d g' >>= fun f' =>
        match f' with
        | .lam n ty body mb =>
          match mb.cod with
          | some v =>
            if v.isNonZero then
              (G : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
            else
              (G : CoreFns CheckSM).infer d a >>= fun ta =>
              (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
              if b then
                (G : CoreFns CheckSM).whnfCore d (body.instantiate1 a)
              else pure (.app (.lam n ty body mb) a)
          | none => pure (.app (.lam n ty body mb) a)
        | f' =>
          iotaRec G env d (.app f' a) >>= fun o =>
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
      split <;> try exact DiscV.pure hwapp
      split
      · exact ih.site_whnfCore henv hwred
      · refine DiscV.bind (ih.site_infer henv hwfa.2) (fun ta hta => ?_)
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
    show DiscV env _
      ((C : CoreFns CheckSM).whnf d pe >>= fun e' =>
        match e'.getAppFn with
        | .const c us =>
          match env.find? c with
          | some (.ctorInfo _ nP nF) =>
            if c = psigmaMkName ∧ i < nF ∧
                e'.getAppArgs.length = nP + nF ∧ us.length = 2 then
              if (Level.max (us.getD 0 .zero) (us.getD 1 .zero)).isNonZero
                  then
                (C : CoreFns CheckSM).whnfCore d
                  (e'.getAppArgs.getD (nP + i) (.bvar 0))
              else
                projCert C env d e' i us nP >>= fun b =>
                if b then
                  (C : CoreFns CheckSM).whnfCore d
                    (e'.getAppArgs.getD (nP + i) (.bvar 0))
                else pure (.proj sn i e')
            else pure (.proj sn i e')
          | _ => pure (.proj sn i e')
        | _ => pure (.proj sn i e'))
      ((G : CoreFns CheckSM).whnf d pe >>= fun e' =>
        match e'.getAppFn with
        | .const c us =>
          match env.find? c with
          | some (.ctorInfo _ nP nF) =>
            if c = psigmaMkName ∧ i < nF ∧
                e'.getAppArgs.length = nP + nF ∧ us.length = 2 then
              if (Level.max (us.getD 0 .zero) (us.getD 1 .zero)).isNonZero
                  then
                (G : CoreFns CheckSM).whnfCore d
                  (e'.getAppArgs.getD (nP + i) (.bvar 0))
              else
                projCert G env d e' i us nP >>= fun b =>
                if b then
                  (G : CoreFns CheckSM).whnfCore d
                    (e'.getAppArgs.getD (nP + i) (.bvar 0))
                else pure (.proj sn i e')
            else pure (.proj sn i e')
          | _ => pure (.proj sn i e')
        | _ => pure (.proj sn i e'))
    refine DiscV.bind (ih.site_whnf henv hwpe) (fun e' he' => ?_)
    have hwproj : WScoped d (Expr.proj sn i e') := by
      simpa only [WScoped] using he'
    have hwarg : ∀ nP : Nat,
        WScoped d (e'.getAppArgs.getD (nP + i) (.bvar 0)) :=
      fun nP => wscoped_getD he'.getAppArgs _
    split <;> try exact DiscV.pure hwproj
    split <;> try exact DiscV.pure hwproj
    split <;> try exact DiscV.pure hwproj
    split
    · exact ih.site_whnfCore henv (hwarg _)
    · refine DiscV.bind (projCert_disc ih henv he') (fun b _ => ?_)
      split
      · exact ih.site_whnfCore henv (hwarg _)
      · exact DiscV.pure hwproj

theorem whnfBody_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScoped d) (whnfBody C env d e)
      (whnfBody G env d e) := by
  unfold whnfBody
  refine DiscV.bind (ih.site_whnfCore henv hw) (fun e₁ he₁ => ?_)
  refine DiscV.bind (reduceNat_disc ih henv he₁) (fun o ho => ?_)
  split
  · exact ih.site_whnf henv (ho _ rfl)
  · split
    · rename_i e₂ hunf
      exact ih.site_whnf henv (unfoldDefinition_WScoped henv hunf he₁)
    · exact DiscV.pure he₁

set_option maxHeartbeats 1600000 in
theorem annotateBody_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScoped d) (annotateBody C env d e)
      (annotateBody G env d e) := by
  match e with
  | .bvar i => exact DiscV.pure (by simp [WScoped])
  | .fvar idx n ty => exact DiscV.pure hw
  | .sort u => exact DiscV.pure (by simp [WScoped])
  | .const n us => exact DiscV.pure (by simp [WScoped])
  | .lit (.natVal n) =>
    show DiscV env _
      (if natLitSupported env then pure (Expr.lit (.natVal n))
       else throw (.invalid "Nat literal without the Nat basis declarations"))
      (if natLitSupported env then pure (Expr.lit (.natVal n))
       else throw (.invalid "Nat literal without the Nat basis declarations"))
    split
    · exact DiscV.pure (by simp [WScoped])
    · exact DiscV.throw _
  | .lit (.strVal s) => exact DiscV.throw _
  | .letE _ _ _ _ => exact DiscV.throw _
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    show DiscV env _
      ((C : CoreFns CheckSM).annotate d g' >>= fun f' =>
        (C : CoreFns CheckSM).annotate d a >>= fun a' =>
        (C : CoreFns CheckSM).infer d f' >>= fun tf =>
        (C : CoreFns CheckSM).whnf d tf >>= fun w =>
        match w with
        | .forallE _ ty _ _ =>
          (C : CoreFns CheckSM).infer d a' >>= fun ta =>
          (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then pure (Expr.app f' a')
          else throw (.invalid "application argument type mismatch")
        | _ => throw (.invalid "function expected"))
      ((G : CoreFns CheckSM).annotate d g' >>= fun f' =>
        (G : CoreFns CheckSM).annotate d a >>= fun a' =>
        (G : CoreFns CheckSM).infer d f' >>= fun tf =>
        (G : CoreFns CheckSM).whnf d tf >>= fun w =>
        match w with
        | .forallE _ ty _ _ =>
          (G : CoreFns CheckSM).infer d a' >>= fun ta =>
          (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then pure (Expr.app f' a')
          else throw (.invalid "application argument type mismatch")
        | _ => throw (.invalid "function expected"))
    refine DiscV.bind (ih.site_annotate hwfa.1) (fun f' hf' => ?_)
    refine DiscV.bind (ih.site_annotate hwfa.2) (fun a' ha' => ?_)
    refine DiscV.bind (ih.site_infer henv hf') (fun tf htf => ?_)
    refine DiscV.bind (ih.site_whnf henv htf) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    rename_i nw tyw bodyw mbw
    have hwty : WScoped d tyw := by
      simp only [WScoped] at hww
      exact hww.1
    refine DiscV.bind (ih.site_infer henv ha') (fun ta hta => ?_)
    refine DiscV.bind (ih.site_defeq hta hwty) (fun b _ => ?_)
    split
    · exact DiscV.pure (by simp only [WScoped]; exact ⟨hf', ha'⟩)
    · exact DiscV.throw _
  | .forallE n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    show DiscV env _
      ((C : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (C : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        (C : CoreFns CheckSM).infer (d + 1) body' >>= fun tb =>
        ensureSort C env (d + 1) tb >>= fun v =>
        pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩))
      ((G : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (G : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        (G : CoreFns CheckSM).infer (d + 1) body' >>= fun tb =>
        ensureSort G env (d + 1) tb >>= fun v =>
        pure (Expr.forallE n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩))
    refine DiscV.bind (ih.site_annotate hwtb.1) (fun ty' hty' => ?_)
    refine DiscV.bind (ih.site_annotate
      (WScoped.instantiate1 hty' 0 hwtb.2)) (fun body' hbody' => ?_)
    refine DiscV.bind (ih.site_infer henv hbody') (fun tb htb => ?_)
    refine DiscV.bind (ensureSort_disc ih henv htb) (fun v _ => ?_)
    refine DiscV.pure ?_
    simp only [WScoped]
    exact ⟨hty', WScoped.abstract1 0 hbody'⟩
  | .lam n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    show DiscV env _
      ((C : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (C : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        (C : CoreFns CheckSM).infer (d + 1) body' >>= fun bt =>
        (C : CoreFns CheckSM).infer (d + 1) bt >>= fun tbt =>
        ensureSort C env (d + 1) tbt >>= fun v =>
        pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩))
      ((G : CoreFns CheckSM).annotate d ty >>= fun ty' =>
        (G : CoreFns CheckSM).annotate (d + 1)
            (body.instantiate1 (.fvar d n ty')) >>= fun body' =>
        (G : CoreFns CheckSM).infer (d + 1) body' >>= fun bt =>
        (G : CoreFns CheckSM).infer (d + 1) bt >>= fun tbt =>
        ensureSort G env (d + 1) tbt >>= fun v =>
        pure (Expr.lam n ty' (body'.abstract1 d) ⟨mb.bi, some v⟩))
    refine DiscV.bind (ih.site_annotate hwtb.1) (fun ty' hty' => ?_)
    refine DiscV.bind (ih.site_annotate
      (WScoped.instantiate1 hty' 0 hwtb.2)) (fun body' hbody' => ?_)
    refine DiscV.bind (ih.site_infer henv hbody') (fun bt hbt => ?_)
    refine DiscV.bind (ih.site_infer henv hbt) (fun tbt htbt => ?_)
    refine DiscV.bind (ensureSort_disc ih henv htbt) (fun v _ => ?_)
    refine DiscV.pure ?_
    simp only [WScoped]
    exact ⟨hty', WScoped.abstract1 0 hbody'⟩
  | .proj sn i pe =>
    have hwpe : WScoped d pe := by simpa only [WScoped] using hw
    show DiscV env _
      ((C : CoreFns CheckSM).annotate d pe >>= fun e' =>
        (C : CoreFns CheckSM).infer d e' >>= fun te₀ =>
        (C : CoreFns CheckSM).whnf d te₀ >>= fun te =>
        match te with
        | .app (.app (.const c _) _) _ =>
          if c = psigmaName then
            match env.find? c with
            | some (.indInfo _ _) =>
              if i < 2 then pure (Expr.proj sn i e')
              else throw (.invalid "projection index out of range")
            | _ => annotateProjElim C env d sn i te e'
          else annotateProjElim C env d sn i te e'
        | _ => annotateProjElim C env d sn i te e')
      ((G : CoreFns CheckSM).annotate d pe >>= fun e' =>
        (G : CoreFns CheckSM).infer d e' >>= fun te₀ =>
        (G : CoreFns CheckSM).whnf d te₀ >>= fun te =>
        match te with
        | .app (.app (.const c _) _) _ =>
          if c = psigmaName then
            match env.find? c with
            | some (.indInfo _ _) =>
              if i < 2 then pure (Expr.proj sn i e')
              else throw (.invalid "projection index out of range")
            | _ => annotateProjElim G env d sn i te e'
          else annotateProjElim G env d sn i te e'
        | _ => annotateProjElim G env d sn i te e')
    refine DiscV.bind (ih.site_annotate hwpe) (fun e' he' => ?_)
    refine DiscV.bind (ih.site_infer henv he') (fun te₀ hte₀ => ?_)
    refine DiscV.bind (ih.site_whnf henv hte₀) (fun te hte => ?_)
    have hwproj : WScoped d (Expr.proj sn i e') := by
      simpa only [WScoped] using he'
    split <;> try exact annotateProjElim_disc ih henv hte he'
    split <;> try exact annotateProjElim_disc ih henv hte he'
    split <;> try exact annotateProjElim_disc ih henv hte he'
    split
    · exact DiscV.pure hwproj
    · exact DiscV.throw _

/-- Throw-with-inlined-continuation branches (the `unless`/`guard`
desugaring): both sides start with the same `throw`. -/
private def discThrowSeq {α : Type} {P : α → Prop} {x g : CheckSM α}
    (e : CheckError) (hx : x = throw e) (hg : g = throw e) :
    DiscV env P x g := by
  subst hx; subst hg
  exact DiscV.throw e

set_option maxHeartbeats 1600000 in
theorem inferBody_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScoped d) (inferBody C env d e)
      (inferBody G env d e) := by
  match e with
  | .bvar _ | .letE _ _ _ _ | .lit (.strVal _) => exact DiscV.throw _
  | .sort u => exact DiscV.pure (by simp [WScoped])
  | .fvar idx n ty =>
    have h' : idx < d ∧ WScoped idx ty := by
      simpa only [WScoped] using hw
    exact DiscV.pure (WScoped.mono (Nat.le_of_lt h'.1) h'.2)
  | .lit (.natVal n) =>
    show DiscV env _
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
    · refine DiscV.pure ?_
      obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
      exact wscoped_instLevels_of_not_hasFvar htf _ _
    · exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
        (fun _ h => h.elim)
  | .forallE n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_infer henv hwtb.1) (fun tty htty => ?_)
    refine DiscV.bind (ih.site_whnf henv htty) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    exact DiscV.pure (by simp [WScoped])
  | .lam n ty body mb =>
    have hwtb : WScoped d ty ∧ WScoped d body := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    simp only [pure_bind]
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_infer henv hwtb.1) (fun tty htty => ?_)
    refine DiscV.bind (ih.site_whnf henv htty) (fun w hww => ?_)
    split <;> try exact DiscV.throw _
    refine DiscV.bind (ih.site_infer henv
      (WScoped.instantiate1 hwtb.1 0 hwtb.2)) (fun bt hbt => ?_)
    refine DiscV.bind (ih.site_infer henv hbt) (fun tbt htbt => ?_)
    refine DiscV.bind (ih.site_whnf henv htbt) (fun w' hww' => ?_)
    split <;> try exact DiscV.throw _
    refine DiscV.bind (DiscV.liftFueled_true _ _) (fun ok _ => ?_)
    split
    · exact DiscV.pure (by
        simp only [WScoped]
        exact ⟨hwtb.1, WScoped.abstract1 0 hbt⟩)
    · first
        | exact DiscV.throw _
        | exact DiscV.bind (P := fun _ => False) (DiscV.throw _)
            (fun _ h => h.elim)
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
    rename_i cw usw Aw Bw
    have hwAB : (WScoped d (Expr.const cw usw) ∧ WScoped d Aw) ∧
        WScoped d Bw := by
      simpa only [WScoped] using hww
    split <;> try exact DiscV.throw _
    split <;> try exact DiscV.throw _
    split <;> try exact DiscV.throw _
    · exact DiscV.pure hwAB.1.2
    · refine DiscV.pure ?_
      simp only [WScoped]
      exact ⟨hwAB.2, hwpe⟩

end Walks

end Setlec
