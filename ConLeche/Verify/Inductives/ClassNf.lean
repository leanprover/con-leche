module

public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Verify.Inductives.PosNf

public section

/-!
# A class's recomputed normal form is the walk's record (PRIMREC / NESTHOME)

The frame tie at depth 1 (DESIGN "PRIMREC / FRAME", F1–F3; the one-stage
helper ruling): the recursor check's own recomputation of a class's
constructor normal forms (`nestMemberCtorNf`, `nestFrameCtorNf`,
`Kernel/Inductives/FieldNf.lean`) IS the positivity walk's record at
every node derived in the same layout — the members' node `0`, and every
frame derived at the EMPTY stack.

* `nestNf_fuel_mono` / `nestTeleNf_fuel_mono`: a successful run of the
  helper answers the same at every larger fuel (its fuel only bounds the
  `Π` nesting it descends).
* `nestTeleNf_agree_derived`: a successful run at any fuel and any
  environment that agrees with the walk's (on this input, at every fuel)
  returns the derivation's normal forms (`posD_nfOk`).
* `nestMemberCtorNf_eq` / `nestFrameCtorNf_eq`: the helpers' results at a
  derived telescope are `nestClassCtorNfOf` of the derivation's normal
  forms — whose entry is exactly what `FrameRec` / `nestMemberNfs`
  record.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Fuel -/

section Fuel

variable {ops : CheckerOps CheckM} {env : Env} {names : List Name} {nP hi : Nat}

/-- `nestNf` one step in. -/
theorem nestNf_succ_eq (fuel dep : Nat) (e : Expr) :
    nestNf ops env names nP hi (fuel + 1) dep e =
      ops.whnf env dep e >>= nestNfAt names nP hi (nestNf ops env names nP hi fuel) dep e :=
  rfl

/-- **`nestNf` is fuel-monotone**: a success answers the same one fuel
higher (hence at every higher fuel). -/
theorem nestNf_fuel_succ :
    ∀ (fuel dep : Nat) (e : Expr) {r : Expr},
      nestNf ops env names nP hi fuel dep e = .ok r →
      nestNf ops env names nP hi (fuel + 1) dep e = .ok r
  | 0, _, _, _, h => nomatch h
  | fuel + 1, dep, e, r, h => by
    rw [nestNf_succ_eq] at h ⊢
    cases hw : ops.whnf env dep e with
    | error err => rw [hw] at h; exact nomatch h
    | ok w =>
      rw [hw] at h
      change nestNfAt names nP hi (nestNf ops env names nP hi fuel) dep e w = .ok r at h
      change nestNfAt names nP hi (nestNf ops env names nP hi (fuel + 1)) dep e w = .ok r
      unfold nestNfAt at h ⊢
      split
      · rename_i hocc; rw [if_pos hocc] at h; exact h
      · rename_i hocc
        rw [if_neg hocc] at h
        split
        · rename_i a b bm
          simp only at h
          cases hb : nestNf ops env names nP hi fuel (dep + 1) (b.instantiate1 (.fvar dep a)) with
          | error err => rw [hb] at h; exact nomatch h
          | ok nb =>
            rw [hb] at h
            show (do
              let nb ← nestNf ops env names nP hi (fuel + 1) (dep + 1) (b.instantiate1 (.fvar dep a))
              pure (Expr.forallE a (nb.abstract1 dep) bm) : CheckM Expr) = _
            rw [nestNf_fuel_succ fuel (dep + 1) _ hb]
            exact h
        · rename_i hnp
          split at h
          · exact absurd rfl (hnp _ _ _)
          · exact h

theorem nestNf_fuel_mono {fuel fuel' dep : Nat} {e r : Expr} (hle : fuel ≤ fuel')
    (h : nestNf ops env names nP hi fuel dep e = .ok r) :
    nestNf ops env names nP hi fuel' dep e = .ok r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih => exact nestNf_fuel_succ _ _ _ (ih (Nat.le_add_right _ _))

theorem nestTeleNf_fuel_mono {fuel fuel' base : Nat} (hle : fuel ≤ fuel') :
    ∀ (nF j : Nat) (cur : Expr) {r : List (Expr × BinderMeta) × Expr},
      nestTeleNf ops env names nP hi fuel base nF j cur = .ok r →
      nestTeleNf ops env names nP hi fuel' base nF j cur = .ok r
  | 0, _, _, _, h => by simpa [nestTeleNf] using h
  | nF + 1, j, cur, r, h => by
    simp only [nestTeleNf] at h ⊢
    split at h
    · rename_i a b bm
      cases hd : nestNf ops env names nP hi fuel (base + j) a with
      | error err =>
        rw [hd] at h; exact nomatch h
      | ok nd =>
        rw [hd] at h
        cases ht : nestTeleNf ops env names nP hi fuel base nF (j + 1)
            (b.instantiate1 (.fvar (base + j) a)) with
        | error err =>
          simp only [ht] at h; exact nomatch h
        | ok q =>
          simp only [ht] at h
          show (do
            let nd ← nestNf ops env names nP hi fuel' (base + j) a
            let (nds, res) ← nestTeleNf ops env names nP hi fuel' base nF (j + 1)
              (b.instantiate1 (.fvar (base + j) a))
            pure ((nd, bm) :: nds, res) : CheckM _) = _
          rw [nestNf_fuel_mono hle hd, nestTeleNf_fuel_mono hle nF (j + 1) _ ht]
          exact h
    · exact nomatch h

end Fuel

/-! ## The recomputation is the derivation's -/

section Derived

variable {ops opsR : CheckerOps CheckM} {env envR : Env} {ctx : NestCtx}

/-- **A successful recomputation returns the derivation's normal
forms**: at any fuel, at operations and an environment that agree with
the walk's on this input at every fuel. -/
theorem nestTeleNf_agree_derived {prog : List NestHole} {base nF j : Nat} {cur res : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts : List PosTree}
    (hd : PosD ops env ctx (.tele prog base nF j cur ks nds res) ts)
    (hag : ∀ fuel, nestTeleNf opsR envR ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF j cur
      = nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF j cur)
    {fuel : Nat} {r : List (Expr × BinderMeta) × Expr}
    (hr : nestTeleNf opsR envR ctx.names ctx.nP (ctx.hiAt prog.length) fuel base nF j cur = .ok r) :
    r = (nds, res) := by
  obtain ⟨F, hF⟩ := hd.tele_nestTeleNf
  have h1 := nestTeleNf_fuel_mono (Nat.le_max_left fuel F) nF j cur hr
  rw [hag, hF _ (Nat.le_max_right _ _)] at h1
  cases h1
  rfl

/-- **A member constructor's recomputation is the walk's**: at the
member layout's derived telescope. -/
theorem nestMemberCtorNf_eq {holes : List Expr} {cv : ConstantVal} {nF : Nat} {crest cur : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts : List PosTree}
    (hcr : instPisWith ctx.params (nestAbstract ctx holes cv.type) = some crest)
    (hd : PosD ops env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts)
    (hag : ∀ fuel, nestTeleNf opsR envR ctx.names ctx.nP (ctx.hiAt 0) fuel (ctx.hiAt 0) nF 0 crest
      = nestTeleNf ops env ctx.names ctx.nP (ctx.hiAt 0) fuel (ctx.hiAt 0) nF 0 crest)
    {r : NestClassCtorNf} (hr : nestMemberCtorNf opsR envR ctx holes cv nF = .ok r) :
    r = nestClassCtorNfOf ctx [] (ctx.hiAt 0) (ctx.lps.map .param) ctx.params cv nds cur := by
  simp only [nestMemberCtorNf, hcr, unwrapOr, pure_bind] at hr
  cases ht : nestTeleNf opsR envR ctx.names ctx.nP (ctx.hiAt 0) (whnfWalkFuel crest) (ctx.hiAt 0)
      nF 0 crest with
  | error err => rw [ht] at hr; exact nomatch hr
  | ok q =>
    rw [ht] at hr
    have := nestTeleNf_agree_derived (prog := []) hd hag ht
    subst this
    cases hr
    rfl

/-- **A frame constructor's recomputation is the walk's**: at a frame
derived at the EMPTY stack (its group `grp`, the key's parameters `ds`
in the walk's representation). -/
theorem nestFrameCtorNf_eq {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {cv : ConstantVal} {nF : Nat} {crest cur : Expr}
    {ks : List PosKind} {nds : List (Expr × BinderMeta)} {ts : List PosTree}
    (hcr : instPisWith ds ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      (grpSub us (ctx.hiAt 0) grp)) = some crest)
    (hd : PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt 0) grp).reverse ++ [])
      (ctx.hiAt 0 + grp.length) nF 0 crest ks nds cur) ts)
    (hag : ∀ fuel, nestTeleNf opsR envR ctx.names ctx.nP
        (ctx.hiAt (grpNews us ds (ctx.hiAt 0) grp).reverse.length) fuel
        (ctx.hiAt 0 + grp.length) nF 0 crest
      = nestTeleNf ops env ctx.names ctx.nP
        (ctx.hiAt (grpNews us ds (ctx.hiAt 0) grp).reverse.length) fuel
        (ctx.hiAt 0 + grp.length) nF 0 crest)
    {r : NestClassCtorNf} (hr : nestFrameCtorNf opsR envR ctx us ds grp cv nF = .ok r) :
    r = nestClassCtorNfOf ctx (grpNews us ds (ctx.hiAt 0) grp).reverse (ctx.hiAt 0 + grp.length)
      us ds cv nds cur := by
  rw [List.append_nil] at hd
  simp only [nestFrameCtorNf, hcr, unwrapOr, pure_bind] at hr
  cases ht : nestTeleNf opsR envR ctx.names ctx.nP
      (ctx.hiAt (grpNews us ds (ctx.hiAt 0) grp).reverse.length) (whnfWalkFuel crest)
      (ctx.hiAt 0 + grp.length) nF 0 crest with
  | error err => rw [ht] at hr; exact nomatch hr
  | ok q =>
    rw [ht] at hr
    have := nestTeleNf_agree_derived hd hag ht
    subst this
    cases hr
    rfl

/-- The recomputed entry is the recorded one (`FrameRec.entry`'s form,
at the empty stack). -/
theorem nestClassCtorNfOf_entry (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (cv : ConstantVal) (nds : List (Expr × BinderMeta)) (cur : Expr) :
    (nestClassCtorNfOf ctx prog hi us ds cv nds cur).entry = nestCtorNf ctx prog hi us ds cv nds cur :=
  rfl

end Derived

end ConLeche
