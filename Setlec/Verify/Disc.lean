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

end Walks

end Setlec
