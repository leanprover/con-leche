module

public import ConLeche.Verify.BoostRed.BVEval
import ConLeche.Verify.InstLevels

/-!
# The reductions the `bv_decide` gate means (task #368)

Where `bvUnsatHit` accepts `U E C a`:

* `2 ^ k` reduces to its literal (`pow2_red`: the boost lemmas of `HPow`
  and its instances);
* `E` is related to its reading `e` (`read_rel`: the reader's every step
  is a constructor of the boost relation, a δ or a numeral's reduction);
* every quoted assignment is related to its assignment (`quote_rel`);
* so `eval (quoteAssign x) E` reduces to `eval x e` (`bvEval_good`), which
  is `false`: Std's `unsat_of_verifyBVExpr_eq_true` at the native check.
-/

public section

namespace ConLeche.Rules.BoostRed

open ConLeche ConLeche.BVUnsat Std.Tactic.BVDecide

variable {env : Env} {d : Nat}

local notation "gate" => BVUnsat.pinsOk env.find? env.findProj? = true

/-- A numeral `OfNat.ofNat Nat n (instOfNatNat n)` is related to `n`. -/
theorem ofNat_rel (hg : gate) (n : Nat) :
    (Nat_R env d).rel
      (Expr.mkAppN (.const ofNatN [.zero]) [.const natN [], .lit (.natVal n),
        .app (.const instOfNatNatN []) (.lit (.natVal n))]) n :=
  bvOfNat_good env d hg (.const natN []) rfl (Nat_R env d) (.lit (.natVal n)) rfl n
    (natLit_R env d n) (.app (.const instOfNatNatN []) (.lit (.natVal n))) rfl
    (bvInstOfNatNat_good env d hg (.lit (.natVal n)) rfl n (natLit_R env d n))

/-- `2 ^ k`, as `BitVec`'s type spells it, is related to `2 ^ k`. -/
theorem pow2_rel (hg : gate) (k : Nat) :
    (Nat_R env d).rel (pow2E (.lit (.natVal k))) (2 ^ k) :=
  bvHPow_good env d hg (.const natN []) rfl (Nat_R env d) (.const natN []) rfl (Nat_R env d)
    (.const natN []) rfl (Nat_R env d) _ rfl
    (bvInstHPow_good env d hg (.const natN []) rfl (Nat_R env d) (.const natN []) rfl (Nat_R env d)
      _ rfl (bvInstPowNat_good env d hg (.const natN []) rfl (Nat_R env d) _ rfl
        (bvInstNatPowNat_good env d hg)))
    _ rfl 2 (ofNat_rel hg 2) (.lit (.natVal k)) rfl k (natLit_R env d k)

/-- **`2 ^ k` reduces to its literal.** -/
theorem pow2_red (hg : gate) (k : Nat) :
    Red env d (pow2E (.lit (.natVal k))) (.lit (.natVal (2 ^ k))) := by
  obtain ⟨e₀, hr, he⟩ := pow2_rel (env := env) (d := d) hg k
  unfold natCore rawNatLit? at he
  split at he
  · rename_i n
    obtain rfl := Option.some.inj he
    exact hr
  · split at he
    · obtain h := Option.some.inj he
      exact absurd h.symm (Nat.ne_of_gt (Nat.two_pow_pos k))
    · exact nomatch he
  · exact nomatch he

/-- A quoted packed bit-vector is related to it. -/
theorem quotePacked_rel (p : Std.Tactic.BVDecide.BVExpr.PackedBitVec) :
    (BoostLem.Std.Tactic.BVDecide.BVExpr.PackedBitVec.T191958766 env d).rel (quotePacked p) p := by
  cases p with
  | @mk w bv =>
  cases bv with
  | ofFin fin =>
  cases fin with
  | mk v hv =>
  refine ⟨_, Red.refl, ?_⟩
  refine ⟨.lit (.natVal w), _, Red.refl, ⟨rfl, ?_⟩, natLit_R env d w, ?_⟩
  · simp [Expr.looseBVarsBounded]
  · refine ⟨_, Red.refl, ?_⟩
    refine ⟨.lit (.natVal w), _, Red.refl, ?_, ?_⟩
    · simp [Expr.looseBVarsBounded]
    · refine ⟨_, Red.refl, ?_⟩
      exact ⟨.lit (.natVal (2 ^ w)), .lit (.natVal v), .const trueIntroName' [], Red.refl,
        ⟨rfl, rfl⟩, natLit_R env d v, trivial⟩

/-- **A quoted assignment is related to it.** -/
theorem quote_rel : ∀ x : Std.Tactic.BVDecide.BVExpr.Assignment,
    (BoostLem.Std.Tactic.BVDecide.BVExpr.Assignment.T191958766 env d).rel (quoteAssign x) x
  | .leaf p => ⟨_, Red.refl, .zero, .const packedBVName [], quotePacked p, Red.refl,
      (quotePacked_closed p).1, quotePacked_rel p⟩
  | .branch i l r =>
    ⟨_, Red.refl, .zero, .const packedBVName [], .lit (.natVal i), quoteAssign l, quoteAssign r,
      Red.refl, ⟨rfl, (quoteAssign_closed l).1, (quoteAssign_closed r).1⟩, natLit_R env d i,
      quote_rel l, quote_rel r⟩

/-! ## The reader's steps -/

theorem mkAppN_closed_parts {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    (Expr.mkAppN f xs).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ x ∈ xs, x.looseBVarsBounded k = true
  | [], _, h => ⟨h, by simp⟩
  | x :: xs, f, h => by
    obtain ⟨hfx, hxs⟩ := mkAppN_closed_parts (xs := xs) (f := .app f x) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hfx
    exact ⟨hfx.1, fun y hy => (List.mem_cons.1 hy).elim (fun h => h ▸ hfx.2) (hxs y)⟩

theorem mkAppN_getApp' : ∀ (e : Expr), Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  intro e
  induction e with
  | app f a ih _ =>
    simp only [Expr.getAppFn, Expr.getAppArgs]
    have : ∀ (g : Expr) (l : List Expr), Expr.mkAppN g (l ++ [a]) = .app (Expr.mkAppN g l) a := by
      intro g l
      induction l generalizing g with
      | nil => rfl
      | cons x xs ih' => exact ih' _
    rw [this, ih]
  | _ => rfl

theorem ctorApp?_eq {e : Expr} {c : Name} {args : List Expr}
    (h : ctorApp? e = some (c, args)) : e = Expr.mkAppN (.const c []) args := by
  unfold ctorApp? at h
  split at h
  · rename_i n hn
    cases h
    rw [← hn]; exact (mkAppN_getApp' e).symm
  · cases h

theorem unfold?_red {e v : Expr} (h : unfold? env.find? e = some v) :
    Red env d e v ∧ v.looseBVarsBounded 0 = true := by
  unfold unfold? at h
  split at h
  · rename_i n
    split at h
    · rename_i cv v' hint hf
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
        refine ⟨?_, hc.2⟩
        have h1 := Red.deltaPin (d := d) ⟨cv, hint, hf, hc.1⟩ (.const n []) [] rfl rfl
        have h0 := Expr.instantiateLevelParams_self [] v
        simp only [List.map_nil] at h0
        simpa [Expr.getAppArgs, Expr.mkAppN, h0] using h1
      · cases h
    · cases h
  · cases h

theorem readNat_rel (hg : gate) {e : Expr} {n : Nat} (h : readNat e = some n) :
    (Nat_R env d).rel e n := by
  unfold readNat at h
  split at h
  · cases h; exact natLit_R env d _
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hc
      exact ofNat_rel hg _
    · cases h
  · cases h

theorem readEnum_some {α : Type} {t : List (Name × α)} {e : Expr} {a : α}
    (h : readEnum t e = some a) : ∃ c, e = .const c [] ∧ (c, a) ∈ t := by
  unfold readEnum at h
  split at h
  · rename_i c hc
    obtain ⟨⟨c', a'⟩, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have h1 := List.find?_some hp
    have hm := List.mem_of_find?_eq_some hp
    simp only [beq_iff_eq] at h1
    subst h1
    exact ⟨c', by simpa [Expr.mkAppN] using ctorApp?_eq hc, hm⟩
  · cases h

theorem readGate_rel {e : Expr} {g : Gate} (h : readGate e = some g) :
    (BoostLem.Std.Tactic.BVDecide.Gate.T191958766 env d).rel e g := by
  obtain ⟨c, rfl, hm⟩ := readEnum_some h
  simp only [gateTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, Red.refl, Red.refl, trivial, trivial⟩

theorem readBool_rel {e : Expr} {b : Bool} (h : readBool e = some b) :
    (Bool_R env d).rel e b := by
  obtain ⟨c, rfl, hm⟩ := readEnum_some h
  simp only [boolTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, Red.refl, rfl⟩

theorem readBinOp_rel {e : Expr} {o : BVBinOp} (h : readBinOp e = some o) :
    (BoostLem.Std.Tactic.BVDecide.BVBinOp.T191958766 env d).rel e o := by
  obtain ⟨c, rfl, hm⟩ := readEnum_some h
  simp only [binOpTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> exact ⟨_, Red.refl, Red.refl, trivial, trivial⟩

theorem readBinPred_rel {e : Expr} {o : BVBinPred} (h : readBinPred e = some o) :
    (BoostLem.Std.Tactic.BVDecide.BVBinPred.T191958766 env d).rel e o := by
  obtain ⟨c, rfl, hm⟩ := readEnum_some h
  simp only [binPredTable, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, Red.refl, Red.refl, trivial, trivial⟩

theorem readUnOp_rel (hg : gate) {e : Expr} {o : BVUnOp} (h : readUnOp e = some o)
    (he : e.looseBVarsBounded 0 = true) :
    (BoostLem.Std.Tactic.BVDecide.BVUnOp.T191958766 env d).rel e o := by
  unfold readUnOp at h
  split at h
  · rename_i c hc
    have heq : e = .const c [] := by simpa [Expr.mkAppN] using ctorApp?_eq hc
    subst heq
    obtain ⟨⟨c', a'⟩, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have h1 := List.find?_some hp
    have hm := List.mem_of_find?_eq_some hp
    simp only [beq_iff_eq] at h1
    subst h1
    simp only [unOpTable0, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, Red.refl, Red.refl, trivial, trivial⟩
  · rename_i c n hc
    split at h
    · rename_i x f k hf hk
      cases h
      have heq := ctorApp?_eq hc
      subst heq
      have hcl := (mkAppN_closed_parts he).2 n (by simp)
      have hm := List.mem_of_find?_eq_some hf
      have h1 := List.find?_some hf
      simp only [beq_iff_eq] at h1
      subst h1
      have hn := readNat_rel (d := d) hg hk
      simp only [unOpTable1, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨_, Red.refl, n, Red.refl, hcl, hn⟩
    · cases h
  · cases h

theorem readBitVec_rel (hg : gate) {w : Nat} {e : Expr} {b : BitVec w}
    (h : readBitVec w e = some b) (he : e.looseBVarsBounded 0 = true) :
    (BoostLem.BitVec.T191958766 env d w).rel e b := by
  unfold readBitVec at h
  split at h
  · rename_i c w' n hc
    have heq := ctorApp?_eq hc
    subst heq
    have hcl := (mkAppN_closed_parts he).2
    split at h
    · rename_i hcn
      simp only [beq_iff_eq] at hcn
      subst hcn
      split at h
      · rename_i w'' k hw hk
        split at h
        · rename_i hww
          cases h
          simp only [beq_iff_eq] at hww
          subst hww
          exact bvBitVecOfNat_good env d hg w' (hcl _ (by simp)) _ (readNat_rel hg hw) n
            (hcl _ (by simp)) k (readNat_rel hg hk)
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## The reading -/

local notation "ExprR" => BoostLem.Std.Tactic.BVDecide.BVExpr.T191958766

-- one fuel step's nine constructor arms, each split through the reader's
-- `do` blocks, in one declaration
set_option maxHeartbeats 400000 in
theorem readExpr_rel (hg : gate) : ∀ (fuel w : Nat) (e : Expr) (x : BVExpr w),
    readExpr env.find? fuel w e = some x → e.looseBVarsBounded 0 = true →
      (ExprR env d w).rel e x
  | 0, _, _, _, h, _ => by simp [readExpr] at h
  | fuel + 1, w, e, x, h, he => by
    unfold readExpr at h
    split at h
    · rename_i v hv
      obtain ⟨hr, hvc⟩ := unfold?_red (d := d) hv
      exact (ExprR env d w).sat _ _ _ hr (readExpr_rel hg fuel w v x h hvc)
    · split at h
      · rename_i c args hc
        have heq := ctorApp?_eq hc
        subst heq
        have hcl := (mkAppN_closed_parts he).2
        have IH := fun w e x h he => readExpr_rel hg fuel w e x h he
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w'', hw, k, hk, h⟩ := h
            split at h
            · rename_i hww; cases h; simp only [beq_iff_eq] at hww; subst hww
              exact ⟨_, Red.refl, _, _, Red.refl, ⟨hcl _ (by simp), hcl _ (by simp)⟩,
                readNat_rel hg hw, readNat_rel hg hk⟩
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w'', hw, h⟩ := h
            split at h
            · rename_i hww; simp only [beq_iff_eq] at hww; subst hww
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨b, hb, h⟩ := h
              cases h
              exact ⟨_, Red.refl, _, _, Red.refl, ⟨hcl _ (by simp), hcl _ (by simp)⟩,
                readNat_rel hg hw, readBitVec_rel hg hb (hcl _ (by simp))⟩
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w0', hw0, s', hs, l', hl, x', hx, h⟩ := h
            split at h
            · rename_i hlw; cases h; subst hlw
              exact ⟨_, Red.refl, _, _, _, _, Red.refl,
                ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
                readNat_rel hg hw0, readNat_rel hg hs, readNat_rel hg hl,
                IH _ _ _ hx (hcl _ (by simp))⟩
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w'', hw, h⟩ := h
            split at h
            · rename_i hww; simp only [beq_iff_eq] at hww; subst hww
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨lx, hlx, o, ho, rx, hrx, h⟩ := h
              cases h
              exact ⟨_, Red.refl, _, _, _, _, Red.refl,
                ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
                readNat_rel hg hw, IH _ _ _ hlx (hcl _ (by simp)), readBinOp_rel ho,
                IH _ _ _ hrx (hcl _ (by simp))⟩
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w'', hw, h⟩ := h
            split at h
            · rename_i hww; simp only [beq_iff_eq] at hww; subst hww
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨o, ho, ox, hox, h⟩ := h
              cases h
              exact ⟨_, Red.refl, _, _, _, Red.refl,
                ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
                readNat_rel hg hw, readUnOp_rel hg ho (hcl _ (by simp)),
                IH _ _ _ hox (hcl _ (by simp))⟩
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨l', hl, r', hr, w'', hw, h⟩ := h
            split at h
            · rename_i hww; simp only [beq_iff_eq] at hww; subst hww
              split at h
              · simp only [Option.bind_eq_some_iff] at h
                obtain ⟨xx, hxx, yy, hyy, h⟩ := h
                cases h
                exact ⟨_, Red.refl, _, _, _, _, _, _, Red.refl,
                  ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp),
                    hcl _ (by simp), hcl _ (by simp)⟩,
                  readNat_rel hg hl, readNat_rel hg hr, readNat_rel hg hw,
                  IH _ _ _ hxx (hcl _ (by simp)), IH _ _ _ hyy (hcl _ (by simp)), trivial⟩
              · cases h
            · cases h
          · cases h
        split at h
        · rename_i h1
          simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨w0', hw0, w'', hw, n', hn, h⟩ := h
            split at h
            · rename_i hww; simp only [beq_iff_eq] at hww; subst hww
              split at h
              · simp only [Option.bind_eq_some_iff] at h
                obtain ⟨xx, hxx, h⟩ := h
                cases h
                exact ⟨_, Red.refl, _, _, _, _, _, Red.refl,
                  ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp),
                    hcl _ (by simp)⟩,
                  readNat_rel hg hw0, readNat_rel hg hw, readNat_rel hg hn,
                  IH _ _ _ hxx (hcl _ (by simp)), trivial⟩
              · cases h
            · cases h
          · cases h
        split at h
        · rename_i h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨m', hm, n', hn, h⟩ := h
            split at h
            · rename_i hmw
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨x', hx', y', hy', h⟩ := h
              cases h
              subst hmw
              have hx := IH _ _ _ hx' (hcl _ (by simp))
              have hy := IH _ _ _ hy' (hcl _ (by simp))
              have hm' := readNat_rel (d := d) hg hm
              have hn' := readNat_rel (d := d) hg hn
              simp only [Bool.or_eq_true, beq_iff_eq] at h1
              rcases h1 with (rfl | rfl) | rfl
              · exact ⟨_, Red.refl, _, _, _, _, Red.refl,
                  ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩, hm', hn', hx, hy⟩
              · have h12 : (exShrN == exShlN) = false := by decide
                simp only [h12, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
                exact ⟨_, Red.refl, _, _, _, _, Red.refl,
                  ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩, hm', hn', hx, hy⟩
              · have h13 : (exAshrN == exShlN) = false := by decide
                have h23 : (exAshrN == exShrN) = false := by decide
                simp only [h13, h23, Bool.false_eq_true, ite_false]
                exact ⟨_, Red.refl, _, _, _, _, Red.refl,
                  ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩, hm', hn', hx, hy⟩
            · cases h
          · cases h
        · cases h
      · cases h

local notation "PredR" => BoostLem.Std.Tactic.BVDecide.BVPred.T191958766
local notation "LogR" => BoostLem.Std.Tactic.BVDecide.BVLogicalExpr.T191958766

theorem readPred_rel (hg : gate) : ∀ (fuel : Nat) (e : Expr) (p : BVPred),
    readPred env.find? fuel e = some p → e.looseBVarsBounded 0 = true →
      (PredR env d).rel e p
  | fuel, e, p, h, he => by
    unfold readPred at h
    split at h
    · rename_i v hv
      obtain ⟨hr, hvc⟩ := unfold?_red (d := d) hv
      split at h
      · cases h
      · rename_i f
        exact (PredR env d).sat _ _ _ hr (readPred_rel hg f v p h hvc)
    · split at h
      · rename_i c w l op r hc
        have heq := ctorApp?_eq hc
        subst heq
        have hcl := (mkAppN_closed_parts he).2
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨w', hw, lx, hlx, o, ho, rx, hrx, h⟩ := h
          cases h
          exact ⟨_, Red.refl, _, _, _, _, Red.refl,
            ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
            readNat_rel hg hw, readExpr_rel hg _ _ _ _ hlx (hcl _ (by simp)), readBinPred_rel ho,
            readExpr_rel hg _ _ _ _ hrx (hcl _ (by simp))⟩
        · cases h
      · rename_i c w x i hc
        have heq := ctorApp?_eq hc
        subst heq
        have hcl := (mkAppN_closed_parts he).2
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨w', hw, xx, hxx, k, hk, h⟩ := h
          cases h
          exact ⟨_, Red.refl, _, _, _, Red.refl,
            ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
            readNat_rel hg hw, readExpr_rel hg _ _ _ _ hxx (hcl _ (by simp)), readNat_rel hg hk⟩
        · cases h
      · cases h
  termination_by fuel => fuel
  decreasing_by all_goals simp_all

theorem readLogical_rel (hg : gate) : ∀ (fuel : Nat) (e : Expr) (x : BVLogicalExpr),
    readLogical env.find? fuel e = some x → e.looseBVarsBounded 0 = true →
      (LogR env d).rel e x
  | 0, _, _, h, _ => by simp [readLogical] at h
  | fuel + 1, e, x, h, he => by
    have IH := fun e x h he => readLogical_rel hg fuel e x h he
    unfold readLogical at h
    split at h
    · rename_i v hv
      obtain ⟨hr, hvc⟩ := unfold?_red (d := d) hv
      exact (LogR env d).sat _ _ _ hr (IH v x h hvc)
    · split at h
      · rename_i c args hc
        have heq := ctorApp?_eq hc
        subst heq
        have hcl := (mkAppN_closed_parts he).2
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          split at h
          · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
            exact ⟨_, Red.refl, _, _, Red.refl, hcl _ (by simp),
              readPred_rel hg _ _ _ hp (hcl _ (by simp))⟩
          · cases h
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          split at h
          · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
            exact ⟨_, Red.refl, _, _, Red.refl, hcl _ (by simp), readBool_rel hb⟩
          · cases h
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          split at h
          · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
            exact ⟨_, Red.refl, _, _, Red.refl, hcl _ (by simp), IH _ _ hy (hcl _ (by simp))⟩
          · cases h
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨g, hgt, y, hy, z, hz, h⟩ := h
            cases h
            exact ⟨_, Red.refl, _, _, _, _, Red.refl,
              ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩, readGate_rel hgt,
              IH _ _ hy (hcl _ (by simp)), IH _ _ hz (hcl _ (by simp))⟩
          · cases h
        split at h
        · rename_i h1; simp only [beq_iff_eq] at h1; subst h1
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨y0, hy0, y, hy, z, hz, h⟩ := h
            cases h
            exact ⟨_, Red.refl, _, _, _, _, Red.refl,
              ⟨hcl _ (by simp), hcl _ (by simp), hcl _ (by simp)⟩,
              IH _ _ hy0 (hcl _ (by simp)), IH _ _ hy (hcl _ (by simp)), IH _ _ hz (hcl _ (by simp))⟩
          · cases h
        · cases h
      · cases h

/-- **The reductions the gate means**: where `bvUnsatOk` accepts `E C`,
`eval (quoteAssign x) E` reduces to `false` at every assignment `x`. -/
theorem bvUnsatOk_evalFalse {E C : Expr} (h : bvUnsatOk env.find? env.findProj? E C = true)
    (x : BVExpr.Assignment) :
    Red env d (.app (.app (.const bvEvalName []) (quoteAssign x)) E) (.const boolFalseName []) := by
  unfold bvUnsatOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hE, -⟩, -⟩, hg⟩, hm⟩ := h
  split at hm
  · rename_i e c he hc
    have hrel := readLogical_rel (d := d) hg _ _ _ he hE
    obtain ⟨e₀, hr, hcore⟩ := bvEval_good env d hg (quoteAssign x) (quoteAssign_closed x).1 x
      (quote_rel x) E hE e hrel
    have hf : BVLogicalExpr.eval x e = false :=
      Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true e c hm x
    rw [hf] at hcore
    subst hcore
    exact hr
  · cases hm

end ConLeche.Rules.BoostRed
