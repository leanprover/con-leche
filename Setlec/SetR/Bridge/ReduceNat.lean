import Setlec.SetR.Bridge.DefEq
import Setlec.Verify.EnvGuards

/-!
# `ReduceNatStepR`, discharged (task #148, T3, batch f)

The literal-acceleration obligation of `Setlec/SetR/Bridge/WhnfCore.lean`:
`reduceNat` replaces an operation applied to literals by the literal of
its value, and the rules R8 (`natSucc`), R9 (`natOp1`) and R10
(`natOp2`) are exactly those three branch families.

**This batch is the clearest single measurement of what premise-exactness
buys.**  The TT lane's counterpart (`Setlec/TTVerify/NatOpsStep.lean`) is
~1 900 lines, and almost all of it is *content*: each operation's stored
recurrence equations have to be transported to the layer's numerals by
meta-induction (`natOps_{add,sub,mul,pow,beq,ble,div,mod,gcd,land,lor,
xor,shiftLeft,shiftRight,pred,log2}_closed`), because `HasType`/`Deq`
only knows the operation through its `EnvTT.nat_ops` equations, and the
literal `natLitT` has to be *identified* with `numeral` through the
pinned basis valuations first.

Here there is none of that.  R9/R10 are stated over `cval` and
`natLitV` directly — `natLitV cval φ n` **is** `denote`'s own literal
clause, and the fold's result enters as the side condition
`denoteClosed cval env φ (natOpResult c n₁ n₂) = some V`, which the
bridge *computes* rather than proves.  The recurrences are not the
bridge's business at all: they are the soundness tier's, where
`EnvS.nat_ops` will consume them exactly once.  So the whole batch is
the branch dispatch plus four small denotation facts.

That is design §0's "premises are read off, not hunted" at its most
extreme, and it is worth quoting when sizing the remaining batches.

Everything below is **repair-independent**: R8–R10 have no `Infer`
premise, so the `Red`-at-an-inferred-type finding
(`Setlec/SetR/DESIGN.md`) cannot touch them.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-! ## Denotation facts about literals and fold results -/

/-- A `Nat` literal denotes to the rule's own `natLitV`.  On this lane
the two are the *same term* — `denote`'s `.lit (.natVal n)` clause is
`natLitT` at the `Nat.zero`/`Nat.succ` valuations, which is what
`natLitV` abbreviates — so no basis pinning and no numeral
identification is needed. -/
theorem denote_natLitV {cval : TConstVal} {φ : Name → Nat}
    (hg : natLitSupported env = true) (d n : Nat) :
    denote cval env φ d (.lit (.natVal n)) = some (natLitV cval φ n) := by
  rw [denote_natLit, if_pos hg]
  rfl

/-- Whatever `rawNatLit?` accepts denotes to the literal it reports —
its two shapes are the literal itself and the `Nat.zero` constant, and
`natLitV … 0` *is* the `Nat.zero` valuation. -/
theorem denote_rawNatLitR {cval : TConstVal} {φ : Name → Nat}
    (hg : natLitSupported env = true) {d : Nat} {a0 : Expr} {n : Nat}
    (h : rawNatLit? a0 = some n) :
    denote cval env φ d a0 = some (natLitV cval φ n) := by
  match a0, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denote_natLitV hg d k
  | .const c [], h =>
    simp only [rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      -- `Nat.zero` is stored with no level parameters (`natZeroOk`)
      simp only [natLitSupported, Bool.and_eq_true] at hg
      obtain ⟨⟨-, h2⟩, -⟩ := hg
      cases hf : env.find? natZeroName with
      | none => rw [hf] at h2; exact nomatch h2
      | some ci =>
        rw [hf] at h2
        have hlp : ci.toConstantVal.levelParams = [] := by
          cases ci with
          | ctorInfo cv p q =>
            simp only [natZeroOk, Bool.and_eq_true] at h2
            simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h2.1
          | _ => simp [natZeroOk] at h2
        simp [denote_const, hf, hlp, natLitV, natLitT]
    · exact nomatch h

/-- **A fold result denotes, closedly, at every depth.**  The three
side conditions R9/R10 ask for, in one package: `natOpResult` returns
either a `Nat` literal (guarded by `natLitSupported`, which
`natOpGuard` implies) or one of the two `Bool` constructors (which
`natOpGuard` pins for exactly the two comparison names). -/
theorem denote_natOpResultR {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {c : Name} {n₁ n₂ : Nat}
    {r : Expr} (hguard : natOpGuard env c = true)
    (hres : natOpResult c n₁ n₂ = some r) :
    ∃ V, denoteClosed cval env φ r = some V ∧ VExpr.Closed V ∧
      ∀ d, denote cval env φ d r = some V := by
  obtain ⟨hnat, -⟩ := natOpGuard_deps hguard
  rcases natOpResult_atom hres with ⟨k, rfl⟩ | ⟨hc, hbool⟩
  · exact ⟨natLitV cval φ k, denote_natLitV hnat 0 k,
      natLitV_closed hcl k, fun d => denote_natLitV hnat d k⟩
  · -- a `Bool` constructor, pinned with no level parameters by the guard
    have hc' : c = natBeqName ∨ c = natBleName ∨
        natDivModNames.contains c = true := by
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    obtain ⟨⟨ciT, hfT, hlpT⟩, ciF, hfF, hlpF⟩ := natOpGuard_bools hguard hc'
    have atom : ∀ (bn : Name) (ci : ConstantInfo),
        env.find? bn = some ci → ci.toConstantVal.levelParams = [] →
        ∃ V, denoteClosed cval env φ (.const bn []) = some V ∧
          VExpr.Closed V ∧
          ∀ d, denote cval env φ d (.const bn []) = some V := by
      intro bn ci hf hlp
      exact ⟨cval bn (Level.substFn φ [] []), by simp [denoteClosed,
        denote_const, hf, hlp], hcl _ _,
        fun d => by simp [denote_const, hf, hlp]⟩
    rcases hbool with rfl | rfl
    · exact atom _ _ hfT hlpT
    · exact atom _ _ hfF hlpF

/-! ## Denotations of the two application shapes -/

/-- A unary application's denotation, split — with the head's level
substitution in the rules' own spelling (`Level.substFn φ [] []`). -/
theorem denote_app1_invR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {c : Name} {a : Expr} {v : VExpr}
    (h : denote cval env φ d (.app (.const c []) a) = some v) :
    ∃ ci va, env.find? c = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      denote cval env φ d a = some va ∧
      v = .app (cval c (Level.substFn φ [] [])) va := by
  rw [denote_app] at h
  split at h
  · next vf va hf ha =>
    rw [denote_const] at hf
    cases hfc : env.find? c with
    | none => rw [hfc] at hf; exact nomatch hf
    | some ci =>
      rw [hfc] at hf
      dsimp only at hf
      split at hf
      · next hlen =>
        have hlp : ci.toConstantVal.levelParams = [] := by
          cases hx : ci.toConstantVal.levelParams with
          | nil => rfl
          | cons p ps => rw [hx] at hlen; exact nomatch hlen
        refine ⟨ci, va, rfl, hlp, ha, ?_⟩
        rw [← Option.some.inj h, ← Option.some.inj hf, hlp]
      · exact nomatch hf
  · exact nomatch h

/-- A binary application's denotation, split. -/
theorem denote_app2_invR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {c : Name} {a b : Expr} {v : VExpr}
    (h : denote cval env φ d (.app (.app (.const c []) a) b) = some v) :
    ∃ ci va vb, env.find? c = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      denote cval env φ d a = some va ∧
      denote cval env φ d b = some vb ∧
      v = .app (.app (cval c (Level.substFn φ [] [])) va) vb := by
  rw [denote_app] at h
  split at h
  · next vf vb hf hb =>
    obtain ⟨ci, va, hfc, hlp, ha, rfl⟩ := denote_app1_invR hf
    exact ⟨ci, va, vb, hfc, hlp, ha, hb, by rw [← Option.some.inj h]⟩
  · exact nomatch h

/-! ## Frame conditions and the argument premise -/

/-- The frame conditions of a `reduceNat` reduct are free: it is a
literal or a `Bool` constructor, so it has no free variables and no
loose bound ones. -/
theorem reduceNat_frameR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {e e₂ : Expr}
    (h : reduceNatP mode env fuel d e = .ok (some e₂))
    (hC : CtxOkR mode m.cval env φ d Δ e) :
    Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOkR mode m.cval env φ d Δ e₂ := by
  have hnf : e₂.hasFvar = false := by
    rcases reduceNat_inv h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
  have hleaf : e₂.fvarLeaves = [] := by
    rcases reduceNat_inv h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> simp [Expr.fvarLeaves]
  refine ⟨Expr.WScoped.of_not_hasFvar hnf, ?_,
    Expr.LeavesBounded.of_not_hasFvar hnf, ⟨hC.1, ?_⟩⟩
  · rcases reduceNat_inv h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl
  · intro l hl
    rw [hleaf] at hl
    exact nomatch hl

/-- An argument whose reduct `reduceNat` reads as a literal `Red`uces to
that literal — R8/R9/R10's argument premise, in one lemma. -/
theorem arg_natLitR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {a a0 : Expr} {n : Nat} {va : VExpr}
    (ihw : WhnfClaimsR mode m φ fuel) (hg : natLitSupported env = true)
    (hwa : whnf mode env fuel d a = .ok a0) (hraw : rawNatLit? a0 = some n)
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkR mode m.cval env φ d Δ a)
    (hva : denote m.cval env φ d a = some va) :
    Red mode env m.cval φ Δ va (natLitV m.cval φ n) := by
  obtain ⟨v', hv', hD⟩ := ihw hwa hws hb hLb hC hva
  rw [denote_rawNatLitR hg hraw] at hv'
  obtain rfl : v' = natLitV m.cval φ n := (Option.some.inj hv').symm
  exact hD

/-- The frame conditions of a unary application's argument. -/
theorem frame_app1R {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {c : Name} {a : Expr}
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOkR mode cval env φ d Δ (.app (.const c []) a)) :
    Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a ∧ CtxOkR mode cval env φ d Δ a := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]),
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC⟩

/-- The frame conditions of a binary application's two arguments. -/
theorem frame_app2R {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {c : Name} {a b : Expr}
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOkR mode cval env φ d Δ (.app (.app (.const c []) a) b)) :
    (Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a ∧ CtxOkR mode cval env φ d Δ a) ∧
      (Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b ∧ CtxOkR mode cval env φ d Δ b) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨⟨hws.1.2, hb.1.2, fun l hl => hLb l ?_,
      CtxOkR.of_subset (fun l hl => ?_) hC⟩,
    hws.2, hb.2, fun l hl => hLb l ?_,
      CtxOkR.of_subset (fun l hl => ?_) hC⟩ <;>
    simp [Expr.fvarLeaves, hl]

/-! ## The unary clause (R8, R9)

`Nat.succ` folding, `Nat.pred` and `Nat.log2`.  The fourth branch — a
capless `log2` on a literal — throws, so it cannot reach here; without a
literal it returns `none`, likewise unreachable. -/

/-- The `.app (.const c []) a` clause. -/
theorem reduceNat_unary_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {c : Name} {a e₂ : Expr} {v : VExpr}
    (h : reduceNatP mode env fuel d (.app (.const c []) a) = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOkR mode m.cval env φ d Δ (.app (.const c []) a))
    (hv : denote m.cval env φ d (.app (.const c []) a) = some v) :
    ∃ w, denote m.cval env φ d e₂ = some w ∧
      Red mode env m.cval φ Δ v w := by
  obtain ⟨hwsa, hba, hLa, hCa⟩ := frame_app1R hws hb hLb hC
  obtain ⟨ci, va, hfc, hlpc, hva, rfl⟩ := denote_app1_invR hv
  simp only [reduceNatP, reduceNat, Bind.bind, Except.bind, whnf_def] at h
  split at h
  · -- `Nat.succ` folding (R8)
    next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : whnf mode env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n =>
      rw [hra] at h
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      refine ⟨natLitV m.cval φ (n + 1), denote_natLitV hnat d (n + 1), ?_⟩
      exact Red.natSucc hnat
        (arg_natLitR m φ ihw hnat hwa hra hwsa hba hLa hCa hva)
  · split at h
    · -- `Nat.pred` (R9)
      next hcond =>
      obtain ⟨rfl, hguard⟩ := hcond
      obtain ⟨hnat, -⟩ := natOpGuard_deps hguard
      cases hwa : whnf mode env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n =>
        rw [hra] at h
        dsimp only at h
        cases hres : natOpResult natPredName n 0 with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h
          subst h
          obtain ⟨V, hV0, hVc, hVd⟩ :=
            denote_natOpResultR (φ := φ) hcl hguard hres
          exact ⟨V, hVd d, Red.natOp1 (Or.inl rfl) hguard hres hV0 hVc
            (arg_natLitR m φ ihw hnat hwa hra hwsa hba hLa hCa hva)⟩
    · split at h
      · -- the certified `Nat.log2` (R9)
        next hcond =>
        obtain ⟨rfl, hguard⟩ := hcond
        obtain ⟨hnat, -⟩ := natOpGuard_deps hguard
        cases hwa : whnf mode env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok a0 =>
        rw [hwa] at h
        dsimp only at h
        cases hra : rawNatLit? a0 with
        | none => rw [hra] at h; simp [pure, Except.pure] at h
        | some n =>
          rw [hra] at h
          dsimp only at h
          cases hres : natOpResult natLog2Name n 0 with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            subst h
            obtain ⟨V, hV0, hVc, hVd⟩ :=
              denote_natOpResultR (φ := φ) hcl hguard hres
            exact ⟨V, hVd d, Red.natOp1 (Or.inr rfl) hguard hres hV0 hVc
              (arg_natLitR m φ ihw hnat hwa hra hwsa hba hLa hCa hva)⟩
      · split at h
        · -- the capless `log2` safety net: throws on a literal, `none`
          -- otherwise, so it never hands back a reduct
          cases hwa : whnf mode env fuel d a with
          | error err => rw [hwa] at h; exact nomatch h
          | ok a0 =>
          rw [hwa] at h
          dsimp only at h
          cases hra : rawNatLit? a0 with
          | none => rw [hra] at h; simp [pure, Except.pure] at h
          | some n =>
            rw [hra] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [pure, Except.pure] at h

/-! ## The binary clause (R10)

The fourteen certified arithmetic and comparison operations; the
WF-pin safety net throws on literal arguments and returns `none`
otherwise, so it never hands back a reduct either. -/

/-- The `.app (.app (.const c []) a) b` clause. -/
theorem reduceNat_binary_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {c : Name} {a b e₂ : Expr} {v : VExpr}
    (h : reduceNatP mode env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOkR mode m.cval env φ d Δ (.app (.app (.const c []) a) b))
    (hv : denote m.cval env φ d (.app (.app (.const c []) a) b) = some v) :
    ∃ w, denote m.cval env φ d e₂ = some w ∧
      Red mode env m.cval φ Δ v w := by
  obtain ⟨⟨hwsa, hba, hLa, hCa⟩, hwsb, hbb, hLb', hCb⟩ :=
    frame_app2R hws hb hLb hC
  obtain ⟨ci, va, vb, hfc, hlpc, hva, hvb, rfl⟩ := denote_app2_invR hv
  simp only [reduceNatP, reduceNat, Bind.bind, Except.bind, whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨hnames, hguard⟩ := hcond
    obtain ⟨hnat, -⟩ := natOpGuard_deps hguard
    cases hwa : whnf mode env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hwb : whnf mode env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hra : rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    cases hrb : rawNatLit? b0 with
    | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hra, hrb] at h
      dsimp only at h
      cases hres : natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        subst h
        obtain ⟨V, hV0, hVc, hVd⟩ :=
          denote_natOpResultR (φ := φ) hcl hguard hres
        exact ⟨V, hVd d, Red.natOp2 hnames hguard hres hV0 hVc
          (arg_natLitR m φ ihw hnat hwa hra hwsa hba hLa hCa hva)
          (arg_natLitR m φ ihw hnat hwb hrb hwsb hbb hLb' hCb hvb)⟩
  · split at h
    · -- the WF-pin safety net
      cases hwa : whnf mode env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hwb : whnf mode env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hra : rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      cases hrb : rawNatLit? b0 with
      | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hra, hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-- **`ReduceNatStepR`, proved.** -/
theorem reduceNat_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) :
    ReduceNatStepR (mode := mode) m φ fuel := by
  intro d Δ e e₂ v h hws hb hLb hC hv
  obtain ⟨h1, h2, h3, h4⟩ := reduceNat_frameR m φ h hC
  suffices heq : ∃ w, denote m.cval env φ d e₂ = some w ∧
      Red mode env m.cval φ Δ v w by
    obtain ⟨w, hw, hD⟩ := heq
    exact ⟨w, hw, hD, h1, h2, h3, h4⟩
  match e, h, hws, hb, hLb, hC, hv with
  | .app (.const c []) a, h, hws, hb, hLb, hC, hv =>
    exact reduceNat_unary_claimR m φ hcl ihw h hws hb hLb hC hv
  | .app (.app (.const c []) a) b, h, hws, hb, hLb, hC, hv =>
    exact reduceNat_binary_claimR m φ hcl ihw h hws hb hLb hC hv
  | .bvar _, h, _, _, _, _, _ | .fvar _ _ _, h, _, _, _, _, _
  | .sort _, h, _, _, _, _, _ | .lam _ _ _ _, h, _, _, _, _, _
  | .forallE _ _ _ _, h, _, _, _, _, _ | .letE _ _ _ _, h, _, _, _, _, _
  | .lit _, h, _, _, _, _, _ | .proj _ _ _, h, _, _, _, _, _
  | .const _ _, h, _, _, _, _, _ =>
    simp [reduceNatP, reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h, _, _, _, _, _
  | .app (.fvar _ _ _) _, h, _, _, _, _, _
  | .app (.sort _) _, h, _, _, _, _, _
  | .app (.lam _ _ _ _) _, h, _, _, _, _, _
  | .app (.forallE _ _ _ _) _, h, _, _, _, _, _
  | .app (.letE _ _ _ _) _, h, _, _, _, _, _
  | .app (.lit _) _, h, _, _, _, _, _
  | .app (.proj _ _ _) _, h, _, _, _, _, _ =>
    simp [reduceNatP, reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h, _, _, _, _, _ =>
    simp [reduceNatP, reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h, _, _, _, _, _
  | .app (.app (.fvar _ _ _) _) _, h, _, _, _, _, _
  | .app (.app (.sort _) _) _, h, _, _, _, _, _
  | .app (.app (.app _ _) _) _, h, _, _, _, _, _
  | .app (.app (.lam _ _ _ _) _) _, h, _, _, _, _, _
  | .app (.app (.forallE _ _ _ _) _) _, h, _, _, _, _, _
  | .app (.app (.letE _ _ _ _) _) _, h, _, _, _, _, _
  | .app (.app (.lit _) _) _, h, _, _, _, _, _
  | .app (.app (.proj _ _ _) _) _, h, _, _, _, _, _ =>
    simp [reduceNatP, reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h, _, _, _, _, _ =>
    simp [reduceNatP, reduceNat, pure, Except.pure] at h

/-- **`WhnfClaimsR` at `fuel + 1`, with no outstanding obligation.**
The second quarter of `CheckStepR` is closed. -/
theorem whnf_claimsR_closed {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel) (ihw : WhnfClaimsR mode m φ fuel) :
    WhnfClaimsR mode m φ (fuel + 1) :=
  whnf_claimsR m φ hcl ihwc (reduceNat_stepR m φ hcl ihw)

end Setlec.SetR
