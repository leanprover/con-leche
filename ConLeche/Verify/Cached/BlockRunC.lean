module

public import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.SumWF

public section

/-!
# The cached uniform install at k members, bridged (lane FLIP1)

`checkBlockKS` (`ConLeche/Cached/CheckerC.lean`), the cached mirror of
the uniform installer at any number of members, is reproduced by the
pure fueled `checkBlock` — the k-ary twin of `checkNativeS_run`
(`ConLeche/Verify/Cached/BridgeCSDecl.lean`), at the recursor stage's
CHECK (`blockRecCheckOn = true`).  With it, the `.indDecl` dispatch of
the cached driver (`checkModeledOrNativeSF_run`, moved here from
`BridgeCSDecl.lean`) takes the k-ary route whenever the gate is lifted,
and reads the route's gate only on the one-member arm that goes at the
flip.

The file follows `BridgeCSDecl.lean`'s layout:

1. the index mirrors at `mkFEnv` ARE the pure stages (`*_eqC`);
2. the scoping facts every cached operation's simulation needs
   (`SimC`, `ConLeche/Verify/Cached/SimC.lean`, is stated at well-scoped
   inputs) — the rule stage's residue is the one that needs work: it is
   built by the primitive-recursion abstraction, which is fvar-free by
   construction (`abstractIh_hasFvar`, `blockIhPis_hasFvar`);
3. the single-environment stages as `SimC`s;
4. the rule stage, whose one rule alternates between the rule-less
   recursors' environment and the constructors' (`sharedOpsRuleR`'s
   flushes are what make that a chain of `SimC`s);
5. the assembly, and the dispatch.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. The index mirrors at `mkFEnv` are the pure stages -/

section Mirrors

variable (ops : CheckerOps CheckCM)

theorem checkBlockTeleF_eqC (env : Env) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleF ops (mkFEnv env) nP ms = checkBlockTele ops env nP ms := by
  unfold checkBlockTeleF checkBlockTele
  simp only [checkConstantValF_eq, checkSumTeleF_pushC]

theorem checkBlockTelesF_eqC (env : Env) (nP : Nat) :
    ∀ mss : List MemberShape,
      checkBlockTelesF ops (mkFEnv env) nP mss = checkBlockTeles ops env nP mss
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockTelesF, checkBlockTeles, checkBlockTeleF_eqC,
      checkBlockTelesF_eqC env nP rest]

theorem checkBlockDomsAtF_eqC (env : Env) (off : Nat) (fvs doms : List Expr) :
    ∀ j : Nat, checkBlockDomsAtF ops (mkFEnv env) off fvs doms j
      = checkBlockDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkBlockDomsAtF, checkBlockDomsAt, mkFEnv_env,
      checkBlockDomsAtF_eqC env off fvs doms j]

theorem checkBlockAgreeF_eqC (env : Env) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs : List (ConstantVal × Level),
      checkBlockAgreeF ops (mkFEnv env) nP cvTa0 s0 cvs
        = checkBlockAgree ops env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    simp only [checkBlockAgreeF, checkBlockAgree, checkBlockDomsAtF_eqC,
      checkBlockAgreeF_eqC env nP cvTa0 s0 rest]

theorem consBlockIndsF_mkFEnv (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvTas : List ConstantVal) (i : Nat) (env : Env),
      consBlockIndsF p₁ isRec cvTas i (mkFEnv env) = mkFEnv (consBlockInds p₁ isRec cvTas i env)
  | [], _, _ => rfl
  | cvTa :: rest, i, env => by
    simp only [consBlockIndsF, consBlockInds, push_mkFEnv]
    exact consBlockIndsF_mkFEnv p₁ isRec rest (i + 1) _

theorem checkBlockIndsF_eqC (env : Env) (p : BlockParts) (isRec : Bool) :
    checkBlockIndsF ops (mkFEnv env) p isRec
      = checkBlockInds ops env p isRec >>= fun r => pure (mkFEnv r.1, r.2) := by
  unfold checkBlockIndsF checkBlockInds
  rcases hm : p.members with _ | ⟨ms0, rest⟩
  · rfl
  · simp only [checkBlockTeleF_eqC, checkBlockTelesF_eqC, checkBlockAgreeF_eqC, bind_assoc,
      pure_bind, consBlockIndsF_mkFEnv]

theorem checkBlockCtorsF_eqC (env₀ env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockCtorsF ops (mkFEnv env₀) (mkFEnv env) p l = checkBlockCtors ops env₀ env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockCtorsF, checkBlockCtors, checkSumCtorsF_eq,
      checkBlockCtorsF_eqC env₀ env p rest]

theorem checkBlockIdxSortsF_eqC (env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockIdxSortsF ops (mkFEnv env) p l = checkBlockIdxSorts ops env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockIdxSortsF, checkBlockIdxSorts, checkStructFieldSortsIF_eq,
      checkBlockIdxSortsF_eqC env p rest]

theorem checkBlockRecTysF_eqC (env : Env) (p : BlockShape) (nested : Bool)
    (cvTas : List ConstantVal) :
    ∀ (l : List RecShape) (ri : Nat),
      checkBlockRecTysF ops (mkFEnv env) p nested cvTas l ri
        = checkBlockRecTys ops env p nested cvTas l ri
  | [], _ => rfl
  | rc :: rest, ri => by
    simp only [checkBlockRecTysF, checkBlockRecTys, checkConstantValF_eq, mkFEnv_env,
      checkBlockRecTysF_eqC env p nested cvTas rest (ri + 1)]

theorem checkBlockRuleF_eqC (opsR opsT : CheckerOps CheckCM) (envR envT : Env)
    (p : BlockShape) (recNames : List Name) (rlvls : List Level) (recTys : List Expr)
    (mIs rPs recTgts : List Nat) (ri : Nat) (cvR : ConstantVal) (cA : ConstantVal × Nat)
    (ks : List BlockFieldKind) (rhs : Expr) :
    checkBlockRuleF opsR .plain (mkFEnv envR) opsT (mkFEnv envT) p recNames rlvls recTys
        mIs rPs recTgts ri cvR cA ks rhs
      = checkBlockRule opsR envR opsT envT p recNames rlvls recTys mIs rPs recTgts ri cvR
          cA ks rhs := by
  simp only [checkBlockRuleF, checkBlockRule, mkFEnv_env, StructWalkers.plain,
    constsResolveF_eq]

theorem checkBlockRulesF_eqC (opsR opsT : CheckerOps CheckCM) (envR envT : Env)
    (p : BlockShape) (recNames : List Name) (rlvls : List Level) (recTys : List Expr)
    (mIs rPs recTgts : List Nat) (ri : Nat) (cvR : ConstantVal) :
    ∀ (cs : List ((ConstantVal × Nat) × List BlockFieldKind)) (rhss : List Expr),
      checkBlockRulesF opsR .plain (mkFEnv envR) opsT (mkFEnv envT) p recNames rlvls recTys
          mIs rPs recTgts ri cvR cs rhss
        = checkBlockRules opsR envR opsT envT p recNames rlvls recTys mIs rPs recTgts ri cvR
            cs rhss
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (cA, ks) :: cs, rhs :: rhss => by
    simp only [checkBlockRulesF, checkBlockRules, checkBlockRuleF_eqC,
      checkBlockRulesF_eqC opsR opsT envR envT p recNames rlvls recTys mIs rPs recTgts ri
        cvR cs rhss]

theorem checkBlockRecsRulesF_eqC (opsR opsT : CheckerOps CheckCM) (envR envT : Env)
    (p : BlockParts) (recNames : List Name) (rlvls : List Level)
    (cvRas : List (ConstantVal × Nat)) (ctorsAs : List (List (ConstantVal × Nat))) :
    ∀ (l : List RecShape) (ri : Nat),
      checkBlockRecsRulesF opsR .plain (mkFEnv envR) opsT (mkFEnv envT) p recNames rlvls
          cvRas ctorsAs l ri
        = checkBlockRecsRules opsR envR opsT envT p recNames rlvls cvRas ctorsAs l ri
  | [], _ => rfl
  | rc :: rest, ri => by
    simp only [checkBlockRecsRulesF, checkBlockRecsRules, checkBlockRulesF_eqC,
      checkBlockRecsRulesF_eqC opsR opsT envR envT p recNames rlvls cvRas ctorsAs rest
        (ri + 1)]

end Mirrors

theorem consBlockCtorsF_mkFEnv (nP : Nat) :
    ∀ (ctorsAs : List (List (ConstantVal × Nat))) (env : Env),
      consBlockCtorsF nP ctorsAs (mkFEnv env) = mkFEnv (consBlockCtors nP ctorsAs env)
  | [], _ => rfl
  | ctorsA :: rest, env => by
    simp only [consBlockCtorsF, consBlockCtors, consSumCtorsF_mkFEnv]
    exact consBlockCtorsF_mkFEnv nP rest _

theorem consBlockRecsBareF_mkFEnv (p : BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBareF p m cvRas (mkFEnv env) = mkFEnv (consBlockRecsBare p m cvRas env)
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, env => by
    simp only [consBlockRecsBareF, consBlockRecsBare, push_mkFEnv]
    exact consBlockRecsBareF_mkFEnv p (m + 1) rest _

theorem consBlockRecsF_mkFEnv (find? : Name → Option ConstantInfo) (p : BlockShape)
    (nP : Nat) :
    ∀ (m : Nat) (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
      (env : Env),
      consBlockRecsF find? p nP m rs (mkFEnv env) = mkFEnv (consBlockRecs find? p nP m rs env)
  | _, [], _ => rfl
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, env => by
    simp only [consBlockRecsF, consBlockRecs, push_mkFEnv]
    exact consBlockRecsF_mkFEnv find? p nP (m + 1) rest _

theorem blockOpenedOkF_eqC (env₀ : Env) (names lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (cty : Expr) (nF : Nat) (ks : List BlockFieldKind) :
    blockOpenedOkF .plain (mkFEnv env₀) names lps nP nIdxs cty nF ks
      = blockOpenedOk env₀ names lps nP nIdxs cty nF ks := by
  simp only [blockOpenedOkF, blockOpenedOk, StructWalkers.plain, constsResolveF_eq] <;> rfl

theorem blockFieldsOkF_eqC (env₀ : Env) (names lps : List Name) (nP : Nat) (nIdxs : List Nat)
    (ctorsAs : List (List (ConstantVal × Nat))) (kinds : List (List (List BlockFieldKind))) :
    blockFieldsOkF .plain (mkFEnv env₀) names lps nP nIdxs ctorsAs kinds
      = blockFieldsOk env₀ names lps nP nIdxs ctorsAs kinds := by
  simp only [blockFieldsOkF, blockFieldsOk, blockMemberFieldsOkF, blockMemberFieldsOk,
    blockOpenedOkF_eqC] <;> rfl

theorem checkBlockTablesF_eqC (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env),
      checkBlockTablesF (m := CheckCM) .plain p l (mkFEnv env)
        = checkBlockTables (m := CheckCM) p l env >>= fun e => pure (mkFEnv e)
  | [], _ => by simp only [checkBlockTablesF, checkBlockTables, pure_bind]
  | (ms, ctorsA, sortss) :: rest, env => by
    unfold checkBlockTablesF checkBlockTables
    split
    · split
      · simp only [checkStructProjTableF_pushC, bind_assoc, pure_bind,
          checkBlockTablesF_eqC p rest]
      · simp only [pure_bind, checkBlockTablesF_eqC p rest]
    · simp only [pure_bind, checkBlockTablesF_eqC p rest]

/-! ## 2. Scoping

Every cached operation's simulation is stated at a well-scoped input
(`WScoped`).  Most of the rule stage's inputs are OPENED telescopes of
checked (fvar-free) constants, and the Verify tier's opening lemmas
cover them; the residue is the exception — it is the primitive-
recursion abstraction of the rule body, wrapped in a GENERATED `ih`
telescope — and the two facts it needs are here: the abstraction never
produces a free variable (`abstractIh_hasFvar`), and neither does the
generated telescope over fvar-free pieces (`blockIhPis_ws0`).
"fvar-free" is stated as `WScoped 0`, which is the same thing
(`ws0_iff`) and composes with the opening lemmas. -/

theorem ws0_hasFvar {e : Expr} (h : WScoped 0 e) : e.hasFvar = false :=
  not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow h)

theorem ws_of_ws0 {d : Nat} {e : Expr} (h : WScoped 0 e) : WScoped d e :=
  WScoped.of_not_hasFvar (ws0_hasFvar h)

theorem WScoped.liftLooseBVars' {d n : Nat} :
    ∀ {e : Expr} {c : Nat}, WScoped d e → WScoped d (e.liftLooseBVars n c) := by
  intro e
  induction e with
  | bvar i => intro c _; simp only [Expr.liftLooseBVars]; split <;> simp [WScoped]
  | fvar idx ty _ => intro c hw; simpa [Expr.liftLooseBVars] using hw
  | app f a ihf iha =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ih1 ih2 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | forallE ty b bi ih1 ih2 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | letE ty v b ih1 ih2 ih3 =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2.1, ih3 hw.2.2⟩
  | proj s i e ih =>
    intro c hw
    simp only [WScoped] at hw
    simp only [Expr.liftLooseBVars, WScoped]
    exact ih hw
  | _ => intro c _; simp [Expr.liftLooseBVars, WScoped]

theorem WScoped.instantiate1Lift' {d : Nat} {v : Expr} (hv : WScoped d v) :
    ∀ {e : Expr} {k : Nat}, WScoped d e → WScoped d (e.instantiate1Lift v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1Lift]
    split
    · exact WScoped.liftLooseBVars' hv
    · split <;> simp [WScoped]
  | fvar idx ty _ => intro k hw; simpa [Expr.instantiate1Lift] using hw
  | app f a ihf iha =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ih1 ih2 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | forallE ty b bi ih1 ih2 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2⟩
  | letE ty v' b ih1 ih2 ih3 =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ⟨ih1 hw.1, ih2 hw.2.1, ih3 hw.2.2⟩
  | proj s i e ih =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1Lift, WScoped]
    exact ih hw
  | _ => intro k _; simp [Expr.instantiate1Lift, WScoped]

theorem instPisAtLift_WScoped {d : Nat} :
    ∀ {as : List Expr} {t r : Expr}, Expr.instPisAtLift as t = some r → WScoped d t →
      (∀ a ∈ as, WScoped d a) → WScoped d r
  | [], t, r, h, ht, _ => by
    simp only [Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    cases t with
    | forallE dom body bi =>
      simp only [Expr.instPisAtLift] at h
      simp only [WScoped] at ht
      exact instPisAtLift_WScoped h (WScoped.instantiate1Lift' (ha a List.mem_cons_self) ht.2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ => simp [Expr.instPisAtLift] at h

theorem mkPisOf_WScoped {d : Nat} :
    ∀ {bs : List (Expr × BinderMeta)} {body : Expr}, (∀ b ∈ bs, WScoped d b.1) →
      WScoped d body → WScoped d (Expr.mkPisOf bs body)
  | [], _, _, hb => hb
  | (ty, mt) :: bs, body, hbs, hb => by
    simp only [Expr.mkPisOf, WScoped]
    exact ⟨hbs _ List.mem_cons_self,
      mkPisOf_WScoped (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb⟩

theorem structIdxAt_WScoped {d nF o i l m : Nat} {e : Expr} (h : WScoped d e) :
    WScoped d (structIdxAt nF o i l m e) :=
  WScoped.liftLooseBVars' (WScoped.liftLooseBVars' h)

theorem structTeleAt_WScoped {d nF o i l : Nat} {pw : PropWhen}
    {tele : List (Expr × BinderMeta)} (h : ∀ b ∈ tele, WScoped d b.1) :
    ∀ b ∈ structTeleAt nF o i l pw tele, WScoped d b.1 := by
  intro b hb
  simp only [structTeleAt, List.mem_map, List.mem_range] at hb
  obtain ⟨k, hk, rfl⟩ := hb
  refine structIdxAt_WScoped ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact h _ (List.getElem_mem hk)

theorem structTeleVars_WScoped {d m : Nat} : ∀ x ∈ structTeleVars m, WScoped d x := by
  intro x hx
  simp only [structTeleVars, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  simp [WScoped]

theorem blockRulePrefixVars_WScoped {d rP nF l : Nat} :
    ∀ x ∈ blockRulePrefixVars rP nF l, WScoped d x := by
  intro x hx
  simp only [blockRulePrefixVars, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  simp [WScoped]

/-- **The generated `ih` telescope is fvar-free over fvar-free pieces.** -/
theorem blockIhPis_ws0 {nP rP nF : Nat} {pw : PropWhen} {recTyOf : Nat → Expr}
    {teleOf : Nat → List (Expr × BinderMeta)} {idxOf : Nat → List Expr}
    (hrec : ∀ c, WScoped 0 (recTyOf c)) (htele : ∀ i, ∀ b ∈ teleOf i, WScoped 0 b.1)
    (hidx : ∀ i, ∀ x ∈ idxOf i, WScoped 0 x) :
    ∀ (ks : List (Nat × Nat)) (l : Nat) {body r : Expr}, WScoped 0 body →
      blockIhPis nP rP nF pw recTyOf teleOf idxOf ks l body = some r → WScoped 0 r
  | [], _, body, r, hb, h => by
    simp only [blockIhPis, Option.some.injEq] at h
    exact h ▸ hb
  | (i, c) :: ks, l, body, r, hb, h => by
    simp only [blockIhPis] at h
    split at h
    · exact nomatch h
    · next concl hconcl =>
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
      have hc : WScoped 0 concl := by
        refine instPisAtLift_WScoped hconcl (hrec c) ?_
        intro a ha
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
        rcases ha with (ha | ⟨x, hx, rfl⟩) | rfl
        · exact blockRulePrefixVars_WScoped a ha
        · exact structIdxAt_WScoped (hidx i x hx)
        · exact Expr.WScoped.mkAppN (by simp [WScoped]) structTeleVars_WScoped
      simp only [WScoped]
      exact ⟨mkPisOf_WScoped (structTeleAt_WScoped (htele i)) hc,
        blockIhPis_ws0 hrec htele hidx ks (l + 1) hb hrest⟩

/-- **The primitive-recursion abstraction never produces a free
variable**: a free variable of the body is refused outright, and a
guarded call is replaced by an `ih` variable applied to the field
telescope's own bound variables. -/
theorem abstractIh_ws0 {fr : BlockRuleFrame} :
    ∀ {e : Expr} {d : Nat} {e' : Expr}, abstractIh fr d e = some e' → WScoped 0 e' := by
  intro e
  induction e with
  | bvar j =>
    intro d e' h
    simp only [abstractIh_bvar, Option.some.injEq] at h
    subst h; split <;> simp [WScoped]
  | fvar => intro d e' h; simp at h
  | sort u => intro d e' h; simp only [abstractIh_sort, Option.some.injEq] at h; subst h; simp [WScoped]
  | lit l => intro d e' h; simp only [abstractIh_lit, Option.some.injEq] at h; subst h; simp [WScoped]
  | const n us =>
    intro d e' h
    simp only [abstractIh_const] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq] at h; subst h; simp [WScoped]
  | app f a ihf iha =>
    intro d e' h
    rw [abstractIh_app] at h
    split at h
    · next rpos as hcall =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨_nm, _c, _i, _ex, -, -, -, -, -, -, -, -, hvars, -, -⟩ := blockIhCall?_spine hcall
      refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hvars] at hy
      exact WScoped.liftLooseBVars' (structTeleVars_WScoped y hy)
    · obtain ⟨f', hf', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [WScoped]
      exact ⟨ihf hf', iha ha'⟩
  | lam ty b bi ih1 ih2 =>
    intro d e' h
    simp only [abstractIh] at h
    obtain ⟨ty', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', h2, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [WScoped]
    exact ⟨ih1 h1, ih2 h2⟩
  | forallE ty b bi ih1 ih2 =>
    intro d e' h
    simp only [abstractIh] at h
    obtain ⟨ty', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', h2, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [WScoped]
    exact ⟨ih1 h1, ih2 h2⟩
  | letE ty v b ih1 ih2 ih3 =>
    intro d e' h
    simp only [abstractIh] at h
    obtain ⟨ty', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v', h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', h3, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [WScoped]
    exact ⟨ih1 h1, ih2 h2, ih3 h3⟩
  | proj s i e ih =>
    intro d e' h
    simp only [abstractIh] at h
    split at h
    · exact nomatch h
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [WScoped]
      exact ih hx

theorem piBinders_ws0 : ∀ {e : Expr}, WScoped 0 e →
    (∀ b ∈ e.piBinders.1, WScoped 0 b.1) ∧ WScoped 0 e.piBinders.2
  | .forallE ty b m, h => by
    simp only [WScoped] at h
    obtain ⟨h1, h2⟩ := piBinders_ws0 h.2
    simp only [Expr.piBinders]
    refine ⟨?_, h2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h1 x hx
  | .bvar _, h | .fvar .., h | .sort _, h | .const .., h | .app .., h | .lam .., h
  | .letE .., h | .lit _, h | .proj .., h => by
    constructor
    · intro b hb; simp [Expr.piBinders] at hb
    · simpa [Expr.piBinders] using h

theorem structFieldTeleOf_ws0 {cty : Expr} (h : WScoped 0 cty) (nP nF i : Nat) :
    ∀ b ∈ structFieldTeleOf cty nP nF i, WScoped 0 b.1 := by
  unfold structFieldTeleOf
  split
  · next cbs body hs =>
    have hcbs := (stripPis_not_hasFvar _ hs (ws0_hasFvar h)).1
    have hb : WScoped 0 (cbs.getD (nP + i) default).1 := by
      rw [List.getD_eq_getElem?_getD]
      cases hx : cbs[nP + i]? with
      | none => exact WScoped.of_not_hasFvar (by rfl)
      | some x => exact WScoped.of_not_hasFvar (hcbs x (List.mem_of_getElem? hx))
    exact (piBinders_ws0 hb).1
  · intro b hb; exact nomatch hb

theorem structFieldIdxOf_ws0 {cty : Expr} (h : WScoped 0 cty) (nP nF i : Nat) :
    ∀ x ∈ structFieldIdxOf cty nP nF i, WScoped 0 x := by
  unfold structFieldIdxOf
  split
  · next cbs body hs =>
    have hcbs := (stripPis_not_hasFvar _ hs (ws0_hasFvar h)).1
    have hb : WScoped 0 (cbs.getD (nP + i) default).1 := by
      rw [List.getD_eq_getElem?_getD]
      cases hx : cbs[nP + i]? with
      | none => exact WScoped.of_not_hasFvar (by rfl)
      | some x => exact WScoped.of_not_hasFvar (hcbs x (List.mem_of_getElem? hx))
    intro x hx
    exact Expr.WScoped.getAppArgs (piBinders_ws0 hb).2 x (List.mem_of_mem_drop hx)
  · intro x hx; exact nomatch hx

/-- `instantiateList` at well-scoped values keeps a scoped term scoped. -/
theorem instantiateList_WScoped {d : Nat} {vs : List Expr} {e : Expr}
    (hvs : ∀ v ∈ vs, WScoped d v) (he : WScoped d e) : WScoped d (e.instantiateList vs 0) := by
  by_cases hne : vs = []
  · subst hne; rw [Expr.instantiateList_nil]; exact he
  · rw [instantiateList_eq_instSeq hne]
    exact Expr.instSeq_WScoped _ _ (fun a ha => hvs a (List.mem_reverse.mp ha)) he

/-- An opened telescope's variables carry types scoped at their own
frame. -/
theorem openers_typeD_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) x.fvarTypeD := by
  intro i x hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e off h i x hx
  have hw := (openPisAtFvars_WScoped n e off h he).1 _ (List.mem_of_getElem? hx)
  simp only [WScoped] at hw
  exact hw.2

/-- The same, read at a common frame. -/
theorem openers_typeD_WScoped' {n off d : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) (hd : off + n ≤ d) :
    ∀ x ∈ fvs, WScoped d x.fvarTypeD := by
  intro x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  have hil : i < fvs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : fvs.length = n := ConLeche.Verify.openPisAtFvars_length n h
  exact (openers_typeD_WScoped h he i x hi).mono (by omega)

/-! ## 3. The single-environment stages, simulated -/

section Sims

variable {env : Env}

theorem checkBlockTeleS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {ms : MemberShape} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.fst v).type)
      (checkBlockTele (sharedOpsC mode (mkFEnv env)) env nP ms)
      (checkBlockTele (fueledOpsM mode) env nP ms) := by
  unfold checkBlockTele
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ c c' hs₁ hP => ?_)
  obtain ⟨rfl, hw⟩ := hP
  refine SimC.bind (checkSumTeleS_sim hμ henv hs₁ hw) (fun s₂ r r' hs₂ hR => ?_)
  obtain ⟨rfl, hw'⟩ := hR
  obtain ⟨cvTa, sx⟩ := r
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ q q' hs₃ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort sx) = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  exact SimC.pure hs₃ ⟨rfl, hw'⟩

theorem checkBlockTelesS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat} :
    ∀ {mss : List MemberShape} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ r ∈ v, WScoped 0 (Prod.fst r).type)
        (checkBlockTeles (sharedOpsC mode (mkFEnv env)) env nP mss)
        (checkBlockTeles (fueledOpsM mode) env nP mss)
  | [], s₀, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest, s₀, hs => by
    unfold checkBlockTeles
    refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw⟩ := hP
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ rs rs' hs₂ hR => ?_)
    obtain ⟨rfl, hws⟩ := hR
    refine SimC.pure hs₂ ⟨rfl, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact hws x hx

theorem checkBlockDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j)
        (checkBlockDomsAt (fueledOpsM mode) env off fvs doms j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkBlockDomsAt
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ a a' hs₁ hP => ?_)
    obtain ⟨rfl, hae⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ b b' hs₂ hQ => ?_)
    obtain ⟨rfl, hbe⟩ := hQ
    refine SimC.bind (opB_sim hμ henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkBlockDomsAtS_sim hμ henv hc ht hs₃

theorem checkBlockAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {cvTa0 : ConstantVal} {s0 : Level} (h0 : WScoped 0 cvTa0.type) :
    ∀ {cvs : List (ConstantVal × Level)} {s₀ : CState},
      (∀ r ∈ cvs, WScoped 0 r.1.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockAgree (sharedOpsC mode (mkFEnv env)) env nP cvTa0 s0 cvs)
        (checkBlockAgree (fueledOpsM mode) env nP cvTa0 s0 cvs)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (cvTa, s) :: rest, s₀, hcvs, hs => by
    unfold checkBlockAgree
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq0 tq0' hs₁ hP => ?_)
    obtain ⟨rfl, htq0⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ tq tq' hs₂ hQ => ?_)
    obtain ⟨rfl, htq⟩ := hQ
    have hw : WScoped 0 cvTa.type := hcvs _ List.mem_cons_self
    by_cases hl : (tq.1.length == tq0.1.length) = true
    case neg => simp only [hl]; exact SimC.throw_bind
    simp only [hl, if_true]
    refine SimC.bind (checkBlockDomsAtS_sim hμ henv ?_ ?_ hs₂) (fun s₄ _ _ hs₄ _ => ?_)
    · intro i x hx
      exact openers_typeD_WScoped htq hw i x hx
    · intro i x hx
      rw [List.getElem?_map] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact openers_typeD_WScoped htq0 h0 i y hy
    by_cases he : (Level.isEquiv s s0 == some true) = true
    case neg => simp only [he]; exact SimC.throw_bind
    simp only [he, if_true]
    exact checkBlockAgreeS_sim hμ henv h0 (fun r hr => hcvs r (List.mem_cons_of_mem _ hr)) hs₄

theorem checkBlockIndsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockParts}
    {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ cv ∈ v.2.1, WScoped 0 cv.type)
      (checkBlockInds (sharedOpsC mode (mkFEnv env)) env p isRec)
      (checkBlockInds (fueledOpsM mode) env p isRec) := by
  unfold checkBlockInds
  split
  · exact SimC.throw
  · refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw0⟩ := hP
    obtain ⟨cvTa0, s0⟩ := r
    dsimp only
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ cvs cvs' hs₂ hQ => ?_)
    obtain ⟨rfl, hws⟩ := hQ
    refine SimC.bind (checkBlockAgreeS_sim hμ henv hw0 hws hs₂) (fun s₃ _ _ hs₃ _ => ?_)
    refine SimC.pure hs₃ ⟨rfl, ?_⟩
    intro cv hcv
    rcases List.mem_cons.mp hcv with rfl | hcv
    · exact hw0
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcv
      exact hws r hr

theorem checkBlockCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, x.2.type.hasFvar = false) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockCtors (sharedOpsC mode (mkFEnv env)) env₀ env p l)
        (checkBlockCtors (fueledOpsM mode) env₀ env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockCtors
    refine SimC.bind (checkSumCtorsS_sim hμ henv (hl _ List.mem_cons_self) hs)
      (fun s₁ q q' hs₁ hP => ?_)
    obtain rfl : q = q' := hP
    obtain ⟨ctorsA, sortss⟩ := q
    dsimp only
    refine SimC.bind (checkBlockCtorsS_sim hμ henv (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      hs₁) (fun s₂ r r' hs₂ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₂ rfl

theorem checkBlockIdxSortsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, WScoped 0 x.2.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockIdxSorts (sharedOpsC mode (mkFEnv env)) env p l)
        (checkBlockIdxSorts (fueledOpsM mode) env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockIdxSorts
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq tq' hs₁ hP => ?_)
    obtain ⟨rfl, htq⟩ := hP
    have hw : WScoped 0 cvTa.type := hl _ List.mem_cons_self
    have hxPos : ∀ (i : Nat) (x : Expr), (tq.1.drop p.nP)[i]? = some x →
        WScoped (p.nP + i) (Expr.fvarTypeD x) := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      have := openers_typeD_WScoped htq hw (p.nP + i) x hx
      simpa using this
    refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hxPos hs₁) (fun s₂ is is' hs₂ hI => ?_)
    obtain rfl : is = is' := hI
    refine SimC.bind (checkBlockIdxSortsS_sim hμ henv (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      hs₂) (fun s₃ r r' hs₃ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₃ rfl

/-- `checkBlockDefEqList`, at pairwise-scoped inputs: only the pairs
the walk actually compares need to be scoped. -/
theorem checkBlockDefEqListS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {depth : Nat} {what : String} :
    ∀ {as bs : List Expr},
      (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        WScoped depth a ∧ WScoped depth b) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockDefEqList (sharedOpsC mode (mkFEnv env)) env depth what as bs)
        (checkBlockDefEqList (fueledOpsM mode) env depth what as bs)
  | [], [], _, s₀, hs => SimC.pure hs rfl
  | [], _ :: _, _, s₀, hs => SimC.throw
  | _ :: _, [], _, s₀, hs => SimC.throw
  | a :: as, b :: bs, hab, s₀, hs => by
    unfold checkBlockDefEqList
    dsimp only [sharedOpsC]
    obtain ⟨ha, hb⟩ := hab 0 a b rfl rfl
    refine SimC.bind (opB_sim hμ henv hs ha hb) (fun s₁ c c' hs₁ hP => ?_)
    obtain rfl : c = c' := hP
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkBlockDefEqListS_sim hμ henv (fun i a b ha hb => hab (i + 1) a b ha hb) hs₁

end Sims

section Sims2

variable {env : Env}

theorem checkBlockRecTysS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {nested : Bool} {cvTas : List ConstantVal}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) :
    ∀ {l : List RecShape} {ri : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ q ∈ v, WScoped 0 (Prod.fst q).type)
        (checkBlockRecTys (sharedOpsC mode (mkFEnv env)) env p nested cvTas l ri)
        (checkBlockRecTys (fueledOpsM mode) env p nested cvTas l ri)
  | [], _, s₀, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | rc :: rest, ri, s₀, hs => by
    unfold checkBlockRecTys
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ ms ms' hs₁ hP => ?_)
    obtain ⟨rfl, hms⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ cvTa cvTa' hs₂ hQ => ?_)
    obtain ⟨rfl, hcvTa⟩ := hQ
    have hwT : WScoped 0 cvTa.type := hT cvTa (List.mem_of_getElem? hcvTa)
    refine SimC.bind (checkConstantValS_sim hμ henv hs₂) (fun s₃ cvRi cvRi' hs₃ hR => ?_)
    obtain ⟨rfl, hwR⟩ := hR
    dsimp only
    by_cases h1 : p.nP ≤ p.rulePrefixAt ri
    case neg => simp only [h1, if_false]; exact SimC.throw_bind
    simp only [h1, if_true]
    by_cases h2 : (p.majorIdxAt ri == p.rulePrefixAt ri + ms.nIdx) = true
    case neg => simp only [h2]; exact SimC.throw_bind
    simp only [h2, if_true]
    refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ x x' hs₄ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    refine SimC.bind (SimC.unwrapOr' hs₄) (fun s₅ y y' hs₅ hY => ?_)
    obtain ⟨rfl, hy⟩ := hY
    have hxl : x.1.length = p.majorIdxAt ri + 1 := ConLeche.Verify.openPisAtFvars_length _ hx
    have hyl : y.1.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hy
    refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₅) (fun s₆ _ _ hs₆ _ => ?_)
    · intro i a b ha hb
      rw [List.getElem?_map] at ha hb
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      have hil : i < p.nP := by
        have := (List.getElem?_eq_some_iff.mp ha').1; omega
      rw [List.getElem?_take, if_pos hil] at hb'
      refine ⟨(openers_typeD_WScoped hy hwT i a' ha').mono (by omega),
        (openers_typeD_WScoped hx hwR i b' hb').mono (by omega)⟩
    refine SimC.bind (SimC.unwrapOr' hs₆) (fun s₇ maj maj' hs₇ hM => ?_)
    obtain ⟨rfl, -⟩ := hM
    split
    case isFalse => exact SimC.throw_bind
    case isTrue h3 =>
    try simp only [h3, if_true]
    dsimp only [sharedOpsC]
    have hwc : WScoped (p.majorIdxAt ri + 1) x.2 := by
      have := (openPisAtFvars_WScoped _ _ 0 hx hwR).2
      simpa using this
    refine SimC.bind (opE_infer_sim hμ henv hs₇ hwc) (fun s₈ sty sty' hs₈ hS => ?_)
    obtain ⟨rfl, hwsty⟩ := hS
    refine SimC.bind (opS_sim hμ henv hs₈ hwsty) (fun s₉ u u' hs₉ hU => ?_)
    obtain rfl : u = u' := hU
    have tail : ∀ s₁₀, CSOK mode env s₁₀ →
        SimC mode env s₁₀ (fun v w => v = w ∧ ∀ q ∈ v, WScoped 0 (Prod.fst q).type)
          (do
            let rs ← checkBlockRecTys (sharedOpsC mode (mkFEnv env)) env p nested cvTas rest
              (ri + 1)
            pure ((cvRi, ms.nIdx, u) :: rs))
          (do
            let rs ← checkBlockRecTys (fueledOpsM mode) env p nested cvTas rest (ri + 1)
            pure ((cvRi, ms.nIdx, u) :: rs)) := by
      intro s₁₀ hs₁₀
      refine SimC.bind (checkBlockRecTysS_sim hμ henv hT hs₁₀) (fun s₁₁ rs rs' hs₁₁ hRs => ?_)
      obtain ⟨rfl, hws⟩ := hRs
      refine SimC.pure hs₁₁ ⟨rfl, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hwR
      · exact hws q hq
    by_cases h4 : blockLargeElimAllowed p nested = true
    · simp only [h4, if_true]
      exact tail s₉ hs₉
    · simp only [h4]
      refine SimC.bind (opB_sim hμ henv hs₉ hwsty (by simp [WScoped]))
        (fun s₁₀ b b' hs₁₀ hB => ?_)
      obtain rfl : b = b' := hB
      cases b with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimC.throw_bind
      | true => simp only [↓reduceIte]; exact tail s₁₀ hs₁₀

end Sims2

section Sims3

variable {env : Env}

/-- The member's parameter-and-index telescope at the recursor's own
numbering: the index openers carry types scoped at their own frame,
provided the parameters come first. -/
theorem openPisParamsIdx_typeD_WScoped {nP nIdx rP : Nat} {ty : Expr} {tfvs : List Expr}
    {rest : Expr} (h : openPisParamsIdx nP nIdx rP ty = some (tfvs, rest))
    (hw : WScoped 0 ty) (hle : nP ≤ rP) :
    ∀ (i : Nat) (x : Expr), (tfvs.drop nP)[i]? = some x →
      i < nIdx ∧ WScoped (rP + i) x.fvarTypeD := by
  unfold openPisParamsIdx at h
  split at h
  · exact nomatch h
  · next pfvs body hp =>
    split at h
    · exact nomatch h
    · next ifvs rest' hi =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hpl : pfvs.length = nP := ConLeche.Verify.openPisAtFvars_length _ hp
      have hil : ifvs.length = nIdx := ConLeche.Verify.openPisAtFvars_length _ hi
      have hbody : WScoped rP body :=
        ((openPisAtFvars_WScoped _ _ 0 hp hw).2).mono (by omega)
      intro i x hx
      rw [List.drop_left' hpl] at hx
      exact ⟨by have := (List.getElem?_eq_some_iff.mp hx).1; omega,
        openers_typeD_WScoped hi hbody i x hx⟩

theorem checkBlockRecIdxDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {cvTas : List ConstantVal} (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) :
    ∀ {l : List (ConstantVal × Nat × Level)} {ri : Nat} {s₀ : CState},
      (∀ q ∈ l, WScoped 0 q.1.type) →
      (∀ (j : Nat) (q : ConstantVal × Nat × Level), l[j]? = some q →
        p.nP ≤ p.rulePrefixAt (ri + j) ∧
        p.majorIdxAt (ri + j) = p.rulePrefixAt (ri + j) + q.2.1) →
      CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockRecIdxDomsAt (sharedOpsC mode (mkFEnv env)) env p cvTas l ri)
        (checkBlockRecIdxDomsAt (fueledOpsM mode) env p cvTas l ri)
  | [], _, s₀, _, _, hs => SimC.pure hs rfl
  | (cvR, nIdx, u) :: rest, ri, s₀, hR, hsum, hs => by
    unfold checkBlockRecIdxDomsAt
    obtain ⟨hle, hmI⟩ := hsum 0 _ rfl
    simp only [Nat.add_zero] at hle hmI
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvTa cvTa' hs₁ hP => ?_)
    obtain ⟨rfl, hcvTa⟩ := hP
    have hwT : WScoped 0 cvTa.type := hT cvTa (List.mem_of_getElem? hcvTa)
    have hwR : WScoped 0 cvR.type := hR _ List.mem_cons_self
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ x x' hs₂ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    obtain ⟨fvs, concl⟩ := x
    dsimp only
    refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ y y' hs₃ hY => ?_)
    obtain ⟨rfl, hy⟩ := hY
    obtain ⟨tfvs, trest⟩ := y
    dsimp only
    have hxl : fvs.length = p.majorIdxAt ri + 1 := ConLeche.Verify.openPisAtFvars_length _ hx
    refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₃) (fun s₄ _ _ hs₄ _ => ?_)
    · intro i a b ha hb
      rw [List.getElem?_map] at ha hb
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨hin, hwa⟩ := openPisParamsIdx_typeD_WScoped hy hwT hle i a' ha'
      rw [List.getElem?_take, if_pos hin, List.getElem?_drop] at hb'
      have hrl : p.rulePrefixAt ri + i < p.majorIdxAt ri + 1 := by
        have := (List.getElem?_eq_some_iff.mp hb').1; omega
      refine ⟨hwa.mono (by omega), ?_⟩
      have := openers_typeD_WScoped hx hwR (p.rulePrefixAt ri + i) b' hb'
      exact this.mono (by omega)
    refine checkBlockRecIdxDomsAtS_sim hμ henv hT (fun q hq => hR q (List.mem_cons_of_mem _ hq))
      ?_ hs₄
    intro j q hq
    have := hsum (j + 1) q hq
    rwa [show ri + (j + 1) = ri + 1 + j by omega] at this

theorem checkBlockRecPrefixAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {rP0 : Nat} {doms0 : List Expr} (hd : ∀ x ∈ doms0, WScoped rP0 x) :
    ∀ {l : List ConstantVal} {ri : Nat} {s₀ : CState},
      (∀ cv ∈ l, WScoped 0 cv.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockRecPrefixAt (sharedOpsC mode (mkFEnv env)) env p rP0 doms0 l ri)
        (checkBlockRecPrefixAt (fueledOpsM mode) env p rP0 doms0 l ri)
  | [], _, s₀, _, hs => SimC.pure hs rfl
  | cv :: rest, ri, s₀, hl, hs => by
    unfold checkBlockRecPrefixAt
    by_cases h1 : (p.rulePrefixAt ri == rP0) = true
    case neg => simp only [h1]; exact SimC.throw_bind
    simp only [h1, if_true]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    obtain ⟨fvs, body⟩ := x
    dsimp only
    refine SimC.bind (checkBlockDefEqListS_sim hμ henv ?_ hs₁) (fun s₂ _ _ hs₂ _ => ?_)
    · intro i a b ha hb
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨hd a (List.mem_of_getElem? ha),
        openers_typeD_WScoped' hx (hl cv List.mem_cons_self) (by omega) b'
          (List.mem_of_getElem? hb')⟩
    exact checkBlockRecPrefixAtS_sim hμ henv hd (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hs₂

theorem checkBlockRecPrefixAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {cvRs : List ConstantVal} {s₀ : CState}
    (hl : ∀ cv ∈ cvRs, WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkBlockRecPrefixAgree (sharedOpsC mode (mkFEnv env)) env p cvRs)
      (checkBlockRecPrefixAgree (fueledOpsM mode) env p cvRs) := by
  unfold checkBlockRecPrefixAgree
  split
  · exact SimC.pure hs rfl
  · next cv0 rest =>
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, hx⟩ := hX
    obtain ⟨fvs0, body0⟩ := x
    dsimp only
    refine checkBlockRecPrefixAtS_sim hμ henv ?_ (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hs₁
    intro y hy
    obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
    exact openers_typeD_WScoped' hx (hl cv0 List.mem_cons_self) (by omega) x hx'

theorem checkBlockRecElimAgreeS_sim {us : List Level} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecElimAgree (m := CheckCM) us)
      (checkBlockRecElimAgree (m := FueledM) us) := by
  unfold checkBlockRecElimAgree
  split
  · exact SimC.pure hs rfl
  · split
    · exact SimC.pure hs rfl
    · exact SimC.throw

theorem checkBlockRecSmallElimS_sim {p : BlockShape} {nested : Bool} {us : List Level}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecSmallElim (m := CheckCM) p nested us)
      (checkBlockRecSmallElim (m := FueledM) p nested us) := by
  unfold checkBlockRecSmallElim
  by_cases h1 : 0 < p.k
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  split
  · exact SimC.pure hs rfl
  · exact SimC.throw

theorem checkBlockRecElimPinS_sim {p : BlockShape} {us : List Level} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecElimPin (m := CheckCM) p us)
      (checkBlockRecElimPin (m := FueledM) p us) := by
  unfold checkBlockRecElimPin
  split
  · exact SimC.pure hs rfl
  · exact SimC.throw

theorem checkBlockRecFamilyAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {nested : Bool} {cvTas : List ConstantVal}
    {cvRus : List (ConstantVal × Nat × Level)} {s₀ : CState}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) (hR : ∀ q ∈ cvRus, WScoped 0 q.1.type)
    (hsum : ∀ (j : Nat) (q : ConstantVal × Nat × Level), cvRus[j]? = some q →
      p.nP ≤ p.rulePrefixAt j ∧ p.majorIdxAt j = p.rulePrefixAt j + q.2.1)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkBlockRecFamilyAgree (sharedOpsC mode (mkFEnv env)) env p nested cvTas cvRus)
      (checkBlockRecFamilyAgree (fueledOpsM mode) env p nested cvTas cvRus) := by
  unfold checkBlockRecFamilyAgree
  refine SimC.bind (checkBlockRecElimAgreeS_sim hs) (fun s₁ _ _ hs₁ _ => ?_)
  refine SimC.bind (checkBlockRecSmallElimS_sim hs₁) (fun s₂ _ _ hs₂ _ => ?_)
  refine SimC.bind (checkBlockRecElimPinS_sim hs₂) (fun s₃ _ _ hs₃ _ => ?_)
  refine SimC.bind (checkBlockRecIdxDomsAtS_sim hμ henv hT hR
    (fun j q hq => by simpa using hsum j q hq) hs₃) (fun s₄ _ _ hs₄ _ => ?_)
  refine checkBlockRecPrefixAgreeS_sim hμ henv ?_ hs₄
  intro cv hcv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv
  exact hR q hq

theorem checkBlockRecPinsS_sim {p : BlockParts} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (checkBlockRecPins (m := CheckCM) p)
      (checkBlockRecPins (m := FueledM) p) := by
  unfold checkBlockRecPins
  by_cases h1 : blockRecLpsOk p.toBlockShape = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  by_cases h2 : blockRecNamesUnreserved p.toBlockShape = true
  case neg => simp only [h2]; exact SimC.throw_bind
  simp only [h2, if_true]
  by_cases h3 : blockRecNameSetOk p.toBlockShape = true
  case neg => simp only [h3]; exact SimC.throw_bind
  simp only [h3, if_true]
  by_cases h4 : p.recPinned = true
  case neg => simp only [h4]; exact SimC.throw
  simp only [h4, if_true]
  exact SimC.pure hs rfl

end Sims3

/-- The kinds' classification is operation-free: in the cached monad
it leaves the state alone and computes what the pure one does. -/
theorem classifyMemberKindsC_ok {names lps : List Name} {nP : Nat} {nIdxs : List Nat}
    {ctorsA : List (ConstantVal × Nat)} {s₀ s' : CState} {kinds : List (List BlockFieldKind)}
    (h : classifyMemberKinds (m := CheckCM) names lps nP nIdxs ctorsA s₀ = .ok (kinds, s')) :
    s' = s₀ ∧ classifyMemberKinds (m := CheckM) names lps nP nIdxs ctorsA = .ok kinds := by
  unfold classifyMemberKinds at h ⊢
  obtain ⟨ks, s₁, hu, h⟩ := bindC_ok h
  cases hk : ctorsA.mapM (blockCtorKinds names lps nP nIdxs) with
  | none => rw [hk] at hu; exact nomatch hu
  | some ks' =>
  rw [hk] at hu
  simp only [unwrapOr] at hu
  obtain ⟨rfl, rfl⟩ := pureC_ok hu
  simp only [unwrapOr, hk]
  try dsimp only at h
  split at h
  · exact absurd h throwC_bind_ok
  · try dsimp only at h
    split at h
    · exact absurd h throwC_bind_ok
    · obtain ⟨rfl, rfl⟩ := pureC_ok h
      simp only [*, bind, Except.bind, ↓reduceIte, pure, Except.pure]
      exact ⟨trivial, rfl⟩

theorem classifyBlockKindsC_ok {names lps : List Name} {nP : Nat} {nIdxs : List Nat} :
    ∀ {l : List (List (ConstantVal × Nat))} {s₀ s' : CState}
      {kinds : List (List (List BlockFieldKind))},
      classifyBlockKinds (m := CheckCM) names lps nP nIdxs l s₀ = .ok (kinds, s') →
      s' = s₀ ∧ classifyBlockKinds (m := CheckM) names lps nP nIdxs l = .ok kinds
  | [], s₀, s', kinds, h => by
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨rfl, rfl⟩
  | ctorsA :: rest, s₀, s', kinds, h => by
    unfold classifyBlockKinds at h
    obtain ⟨kss, s₁, h1, h⟩ := bindC_ok h
    obtain ⟨e1, hk1⟩ := classifyMemberKindsC_ok h1
    obtain ⟨rest', s₂, h2, h⟩ := bindC_ok h
    obtain ⟨e2, hk2⟩ := classifyBlockKindsC_ok h2
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    refine ⟨by rw [e2, e1], ?_⟩
    simp only [classifyBlockKinds, hk1, hk2, bind, Except.bind, pure, Except.pure]

/-! ## 4. The rule stage: two environments, one state

One rule runs its first two operations at the rule-less recursors'
environment and the rest at the constructors'; `sharedOpsRuleR`
flushes entering the first and leaving the second.  `SimG` is `SimC`
with the state invariant at entry and at exit left free, so that a
chain of operations can change environment where a flush lets it. -/

/-- `SimC` across environment transitions: `Pre` of the entry state,
`Post` of the exit state. -/
def SimG (Pre Post : CState → Prop) {β α : Type} (P : β → α → Prop) (c : CheckCM β)
    (p : FueledM α) : Prop :=
  ∀ s₀, Pre s₀ → ∀ v' s', c s₀ = .ok (v', s') → Post s' ∧ ∃ v, P v' v ∧ ∃ F, p.val F = .ok v

namespace SimG

variable {A B C : CState → Prop}

theorem ofC {env : Env} {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    (h : ∀ s₀, CSOK mode env s₀ → SimC mode env s₀ P c p) :
    SimG (CSOK mode env) (CSOK mode env) P c p :=
  fun s₀ hs v' s' hr => h s₀ hs v' s' hr

theorem pure {β α : Type} {P : β → α → Prop} {b : β} {a : α} (hAB : ∀ s, A s → B s)
    (h : P b a) : SimG A B P (Pure.pure b) (Pure.pure a) := by
  intro s₀ hs v' s' hr
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hAB _ hs, a, h, 0, rfl⟩

theorem throw_bind {β β' α : Type} {P : β' → α → Prop} {er : CheckError}
    {k : β → CheckCM β'} {p : FueledM α} :
    SimG A B P ((throw er : CheckCM β) >>= k) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem throw {β α : Type} {P : β → α → Prop} {er : CheckError} {p : FueledM α} :
    SimG A B P (throw er : CheckCM β) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem bind {β β' α α' : Type} {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α} {q : α → FueledM α'}
    (hx : SimG A B P c p) (hf : ∀ b a, P b a → SimG B C Q (k b) (q a)) :
    SimG A C Q (c >>= k) (p >>= q) := by
  intro s₀ hs v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx s₀ hs b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf b a hP s₁ hs₁ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

theorem unwrapOr {α : Type} {o : Option α} {err : CheckError} (hAB : ∀ s, A s → B s) :
    SimG A B (fun v w => v = w ∧ o = some v)
      (ConLeche.unwrapOr o err : CheckCM α) (ConLeche.unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimG.throw
  | some a => exact SimG.pure hAB ⟨rfl, rfl⟩

theorem mono {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    {A' B' : CState → Prop} (h : SimG A B P c p) (hA : ∀ s, A' s → A s)
    (hB : ∀ s, B s → B' s) : SimG A' B' P c p :=
  fun s₀ hs v' s' hr =>
    let ⟨h1, h2⟩ := h s₀ (hA s₀ hs) v' s' hr
    ⟨hB s' h1, h2⟩

end SimG

/-- The rule stage's `annotate` at the rule-less recursors'
environment: it flushes first, so it simulates from any residue. -/
theorem ruleR_annotate_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG CSOKF (CSOK mode envR) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).annotate envR d e)
      ((fueledOpsM mode).annotate envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨u, s₁, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hfl
  exact opE_annotate_sim hμ henvR (flushC_csok hs) hw v' s' hr

/-- The rule stage's `inferType` at the rule-less recursors'
environment: it flushes last, so it hands on a state that is an
invariant state of ANY environment. -/
theorem ruleR_infer_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG (CSOK mode envR) (CSOK mode envT) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).inferType envR d e)
      ((fueledOpsM mode).inferType envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨t, s₁, hinf, hr⟩ := bindC_ok hr
  obtain ⟨hs₁, w, hrel, F, hF⟩ := opE_infer_sim hμ henvR hs hw t s₁ hinf
  obtain ⟨u, s₂, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = s₂ := congrArg Prod.snd hfl
  obtain ⟨rfl, rfl⟩ := pureC_ok hr
  exact ⟨flushC_csok hs₁.residue, w, hrel, F, hF⟩

/-- **One rule, simulated.**  From any residue: the right-hand side
annotated and typed at the rule-less recursors' environment `envR`
(`sharedOpsRuleR`'s flushes on either side), then the domains' defeq,
the residue's inference and the conclusion's defeq at the
constructors' `envT`, every input scoped at the frame it is run at. -/
theorem checkBlockRuleS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind} {rhs : Expr}
    (hrec : ∀ t ∈ recTys, WScoped 0 t) (hcA : WScoped 0 cA.1.type) :
    SimG CSOKF (CSOK mode envT) RelVC
      (checkBlockRule (sharedOpsRuleR mode (mkFEnv envR)) envR (sharedOpsC mode (mkFEnv envT))
        envT p recNames rlvls recTys mIs rPs recTgts ri cvR cA ks rhs)
      (checkBlockRule (fueledOpsM mode) envR (fueledOpsM mode) envT p recNames rlvls recTys
        mIs rPs recTgts ri cvR cA ks rhs) := by
  unfold checkBlockRule
  dsimp only
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun recTy recTy' hR => ?_)
  obtain ⟨rfl, hrecTy⟩ := hR
  have hwRec : WScoped 0 recTy := hrec recTy (List.mem_of_getElem? hrecTy)
  by_cases h1 : looseBVarsBounded 0 rhs = true
  case neg => simp only [h1]; exact SimG.throw_bind
  simp only [h1, if_true]
  by_cases h2 : rhs.hasFvar = true
  case pos => simp only [h2, if_true]; exact SimG.throw_bind
  simp only [h2]
  have hwrhs : WScoped 0 rhs := WScoped.of_not_hasFvar (by simpa using h2)
  refine SimG.bind (ruleR_annotate_simG hμ henvR hwrhs) (fun rhsA rhsA' hA => ?_)
  obtain ⟨rfl, hwA⟩ := hA
  by_cases h3 : allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => simp only [h3]; exact SimG.throw_bind
  simp only [h3, if_true]
  by_cases h4 : constsResolve envR rhsA = true
  case neg => simp only [h4]; exact SimG.throw_bind
  simp only [h4, if_true]
  refine SimG.bind (ruleR_infer_simG hμ henvR envT hwA) (fun _ _ _ => ?_)
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun x x' hX => ?_)
  obtain ⟨rfl, hx⟩ := hX
  by_cases h5 : (x.1.all fun b => b.2.pw == (structElimLevel p.elim p.large).zeronessOf) = true
  case neg => simp only [h5]; exact SimG.throw_bind
  simp only [h5, if_true]
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun y y' hY => ?_)
  obtain ⟨rfl, hy⟩ := hY
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun z z' hZ => ?_)
  obtain ⟨rfl, hz⟩ := hZ
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun w w' hW => ?_)
  obtain ⟨rfl, hw⟩ := hW
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun ld ld' hL => ?_)
  obtain ⟨rfl, hld⟩ := hL
  -- the frame's scoping
  have hwy : ∀ a ∈ y.1, WScoped (p.rulePrefixAt ri) a := by
    have := (openPisAtFvars_WScoped _ _ 0 hy hwRec).1
    simpa using this
  have hwz : WScoped (p.rulePrefixAt ri) z.2 :=
    (instPisAt_WScoped _ _ hz (ws_of_ws0 hcA)
      (fun a ha => hwy a (List.mem_of_mem_take ha))).2
  have hww := openPisAtFvars_WScoped _ _ _ hw hwz
  have hD : ∀ a ∈ y.1 ++ w.1, WScoped (p.rulePrefixAt ri + cA.2) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hwy a ha).mono (by omega)
    · exact hww.1 a ha
  have hwld := instLamsAt_WScoped (d := p.rulePrefixAt ri + cA.2) _ _ hld (ws_of_ws0 hwA) hD
  by_cases h6 : (ld.1.all fun t => constsResolve envT t) = true
  case neg => simp only [h6]; exact SimG.throw_bind
  simp only [h6, if_true]
  refine SimG.bind (SimG.ofC (fun s hs => checkBlockDefEqListS_sim hμ henvT ?_ hs))
    (fun _ _ _ => ?_)
  · intro i a b ha hb
    rw [List.getElem?_map] at ha
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨fvarTypeD_WScoped (hD a' (List.mem_of_getElem? ha')),
      hwld.1 b (List.mem_of_getElem? hb)⟩
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun bb bb' hB => ?_)
  obtain ⟨rfl, hbb⟩ := hB
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun ih ih' hI => ?_)
  obtain ⟨rfl, hih⟩ := hI
  have hwih : WScoped 0 ih := by
    refine blockIhPis_ws0 ?_ (fun i => structFieldTeleOf_ws0 hcA _ _ i)
      (fun i => structFieldIdxOf_ws0 hcA _ _ i) _ 0 (abstractIh_ws0 hbb) hih
    intro c
    rw [List.getD_eq_getElem?_getD]
    cases hc : recTys[c]? with
    | none => simp [WScoped]
    | some t => exact hrec t (List.mem_of_getElem? hc)
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun o o' hO => ?_)
  obtain ⟨rfl, ho⟩ := hO
  have hwinst : WScoped (p.rulePrefixAt ri + cA.2)
      (ih.instantiateList (y.1 ++ w.1).reverse 0) :=
    instantiateList_WScoped (fun v hv => hD v (List.mem_reverse.mp hv)) (ws_of_ws0 hwih)
  have hwo := (openPisAtFvars_WScoped _ _ _ ho hwinst).2
  dsimp only [sharedOpsC]
  refine SimG.bind (SimG.ofC (fun s hs => opE_infer_sim hμ henvT hs hwo))
    (fun tyB tyB' hT => ?_)
  obtain ⟨rfl, hwT⟩ := hT
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun cc cc' hC => ?_)
  obtain ⟨rfl, hcc⟩ := hC
  have hwcc : WScoped (p.rulePrefixAt ri + cA.2 +
      (blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length) cc := by
    refine instPisAtLift_WScoped hcc (ws_of_ws0 hwRec) ?_
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact (hwy a ha).mono (by omega)
    · exact (Expr.WScoped.getAppArgs hww.2 a (List.mem_of_mem_drop ha)).mono (by omega)
    · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hwy x (List.mem_of_mem_take hx)).mono (by omega)
      · exact (hww.1 x hx).mono (by omega)
  refine SimG.bind (SimG.ofC (fun s hs => opB_sim hμ henvT hs hwT hwcc))
    (fun r r' hr => ?_)
  obtain rfl : r = r' := hr
  cases r with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact SimG.throw_bind
  | true => simp only [↓reduceIte]; exact SimG.pure (fun _ h => h) rfl

theorem checkBlockRulesS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} (hrec : ∀ t ∈ recTys, WScoped 0 t) :
    ∀ {cs : List ((ConstantVal × Nat) × List BlockFieldKind)} {rhss : List Expr},
      (∀ c ∈ cs, WScoped 0 c.1.1.type) →
      SimG CSOKF CSOKF RelVC
        (checkBlockRules (sharedOpsRuleR mode (mkFEnv envR)) envR
          (sharedOpsC mode (mkFEnv envT)) envT p recNames rlvls recTys mIs rPs recTgts ri cvR
          cs rhss)
        (checkBlockRules (fueledOpsM mode) envR (fueledOpsM mode) envT p recNames rlvls recTys
          mIs rPs recTgts ri cvR cs rhss)
  | [], [], _ => SimG.pure (fun _ h => h) rfl
  | [], _ :: _, _ => SimG.throw
  | _ :: _, [], _ => SimG.throw
  | (cA, ks) :: cs, rhs :: rhss, hc => by
    unfold checkBlockRules
    refine SimG.bind ((checkBlockRuleS_simG hμ henvR henvT hrec
      (hc _ List.mem_cons_self)).mono (fun _ h => h) (fun _ h => h.residue))
      (fun r r' hr => ?_)
    obtain rfl : r = r' := hr
    refine SimG.bind (checkBlockRulesS_simG hμ henvR henvT hrec
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))) (fun rest rest' hrest => ?_)
    obtain rfl : rest = rest' := hrest
    exact SimG.pure (fun _ h => h) rfl

theorem checkBlockRecsRulesS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) (henvT : EnvWF envT) {p : BlockParts} {recNames : List Name}
    {rlvls : List Level} {cvRas : List (ConstantVal × Nat)}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hrec : ∀ q ∈ cvRas, WScoped 0 q.1.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) :
    ∀ {l : List RecShape} {ri : Nat},
      SimG CSOKF CSOKF RelVC
        (checkBlockRecsRules (sharedOpsRuleR mode (mkFEnv envR)) envR
          (sharedOpsC mode (mkFEnv envT)) envT p recNames rlvls cvRas ctorsAs l ri)
        (checkBlockRecsRules (fueledOpsM mode) envR (fueledOpsM mode) envT p recNames rlvls
          cvRas ctorsAs l ri)
  | [], _ => SimG.pure (fun _ h => h) rfl
  | rc :: rest, ri => by
    unfold checkBlockRecsRules
    dsimp only
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun ms ms' hM => ?_)
    obtain ⟨rfl, -⟩ := hM
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun ctorsA ctorsA' hC => ?_)
    obtain ⟨rfl, hctorsA⟩ := hC
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun kss kss' hK => ?_)
    obtain ⟨rfl, -⟩ := hK
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun q q' hQ => ?_)
    obtain ⟨rfl, -⟩ := hQ
    by_cases h1 : (ctorsA.length == ms.ctors.length) = true
    case neg => simp only [h1]; exact SimG.throw_bind
    simp only [h1, if_true]
    have hrec' : ∀ t ∈ cvRas.map (·.1.type), WScoped 0 t := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      exact hrec x hx
    refine SimG.bind (checkBlockRulesS_simG hμ henvR henvT hrec' ?_) (fun rhss rhss' hR => ?_)
    · intro c hc
      exact hct ctorsA (List.mem_of_getElem? hctorsA) c.1 (List.of_mem_zip hc).1
    obtain rfl : rhss = rhss' := hR
    refine SimG.bind (checkBlockRecsRulesS_simG hμ henvR henvT hrec hct)
      (fun rest' rest'' hR' => ?_)
    obtain rfl : rest' = rest'' := hR'
    exact SimG.pure (fun _ h => h) rfl

/-! ## 5. The assembly -/

/-- The rule-less recursors' cons is a `consBlockRecs` with no rules. -/
theorem consBlockRecsBare_eq_consBlockRecs (find? : Name → Option ConstantInfo) (q : BlockShape)
    (nP : Nat) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBare q m cvRas env
        = consBlockRecs find? q nP m
            (cvRas.map fun c => (c.1, ([] : List Expr), c.2, ([] : List (ConstantVal × Nat))))
            env
  | _, [], _ => rfl
  | m, (cv, n) :: rest, env => by
    simp only [consBlockRecsBare, consBlockRecs, List.map_cons, sumRules]
    exact consBlockRecsBare_eq_consBlockRecs find? q nP (m + 1) rest _

/-- **The rule-less recursors' environment is well-formed** when their
checked types are. -/
theorem envWF_consBlockRecsBare {q : BlockShape} {cvRas : List (ConstantVal × Nat)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ c ∈ cvRas, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecsBare q 0 cvRas env) := by
  rw [consBlockRecsBare_eq_consBlockRecs env.find? q 0]
  refine envWF_consBlockRecs henv ?_
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain ⟨h1, h2, h3, h4⟩ := hall c hc
  exact ⟨h1, h2, h3, h4, fun _ h => nomatch h⟩

/-- **The recursor stage at its CHECK, at the cached driver**, is
reproduced by the pure fueled `checkBlockRecK`. -/
theorem checkBlockRecKS_run (hμ : mode.verifiedChecks = true) {env₂ : Env} (henv₂ : EnvWF env₂)
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK mode env₂ s₀)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {s' : CState}
    (h : checkBlockRecKS mode (mkFEnv env₂) p cvTas ctorsAs s₀ = .ok (rs, s')) :
    CSOKF s' ∧ ∃ F, (checkBlockRecK (fueledOpsM mode) env₂ p cvTas ctorsAs).val F = .ok rs := by
  unfold checkBlockRecKS at h
  -- (a) the pins
  obtain ⟨u₁, s₁, hpins, h⟩ := bindC_ok h
  obtain ⟨hs₁, u₁', hu₁, F₁, hF₁⟩ := checkBlockRecPinsS_sim hs u₁ s₁ hpins
  obtain rfl : u₁ = u₁' := hu₁
  -- (b) the types
  rw [checkBlockRecTysF_eqC] at h
  obtain ⟨cvRus, s₂, htys, h⟩ := bindC_ok h
  obtain ⟨hs₂, cvRus', ⟨rfl, hwR⟩, F₂, hF₂⟩ :=
    checkBlockRecTysS_sim hμ henv₂ hT hs₁ cvRus s₂ htys
  have hF₂p : checkBlockRecTys (fueledOps mode F₂) env₂ p.toBlockShape (blockNested p.kinds)
      cvTas p.recs 0 = .ok cvRus := by
    rw [← checkBlockRecTys_datF]; exact hF₂
  obtain ⟨hlenT, hallT⟩ := checkBlockRecTys_inv hF₂p
  have hsum : ∀ (j : Nat) (q : ConstantVal × Nat × Level), cvRus[j]? = some q →
      p.nP ≤ p.toBlockShape.rulePrefixAt j ∧
      p.toBlockShape.majorIdxAt j = p.toBlockShape.rulePrefixAt j + q.2.1 := by
    intro j q hq
    have hj : j < p.recs.length := by
      rw [← hlenT]; exact (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨rc, cvRi, nIdx, u, -, hcu, -, hle, hmI⟩ := hallT j hj
    rw [hq] at hcu
    obtain rfl := Option.some.inj hcu
    simp only [Nat.zero_add] at hle hmI
    exact ⟨hle, hmI⟩
  -- (b') the family's agreements
  obtain ⟨u₃, s₃, hfam, h⟩ := bindC_ok h
  rw [mkFEnv_env] at hfam
  obtain ⟨hs₃, u₃', hu₃, F₃, hF₃⟩ :=
    checkBlockRecFamilyAgreeS_sim hμ henv₂ hT hwR hsum hs₂ u₃ s₃ hfam
  obtain rfl : u₃ = u₃' := hu₃
  -- (c) the rules, at the rule-less recursors' environment and the constructors'
  have hwfR : ∀ c ∈ cvRus.map (fun q => (q.1, q.2.1)), c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env₂ = true ∧ c.1.type.looseBVarsBounded 0 = true := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
    have hjl : j < p.recs.length := by
      rw [← hlenT]; exact (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨rc, cvRi, nIdx, u, -, hcu, hcv, -, -⟩ := hallT j hjl
    rw [hj] at hcu
    obtain rfl := Option.some.inj hcu
    exact checkConstantVal_typeWF hcv
  have henvR := envWF_consBlockRecsBare (q := p.toBlockShape) henv₂ hwfR
  simp only [consBlockRecsBareF_mkFEnv, structWalkersC_eq_plain, checkBlockRecsRulesF_eqC] at h
  have hrecW : ∀ q ∈ cvRus.map (fun q => (q.1, q.2.1)), WScoped 0 q.1.type := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact hwR q' hq'
  obtain ⟨hs', rs', hrs, F₄, hF₄⟩ :=
    checkBlockRecsRulesS_simG hμ henvR henv₂ hrecW hct s₃ hs₃.residue rs s' h
  obtain rfl : rs = rs' := hrs
  obtain ⟨G, hle₁, hle₂, hle₃, hle₄⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G ∧ F₄ ≤ G :=
    ⟨max F₁ (max F₂ (max F₃ F₄)), by omega, by omega, by omega, by omega⟩
  refine ⟨hs', G, ?_⟩
  have g₁ : checkBlockRecPins (m := CheckM) p = .ok () := by
    rw [← checkBlockRecPins_datF (F := G)]; exact FueledM.up hle₁ hF₁
  have g₂ : checkBlockRecTys (fueledOps mode G) env₂ p.toBlockShape (blockNested p.kinds)
      cvTas p.recs 0 = .ok cvRus := by
    rw [← checkBlockRecTys_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkBlockRecFamilyAgree (fueledOps mode G) env₂ p.toBlockShape
      (blockNested p.kinds) cvTas cvRus = .ok () := by
    rw [← checkBlockRecFamilyAgree_datF]; exact FueledM.up hle₃ hF₃
  have g₄ : checkBlockRecsRules (fueledOps mode G)
      (consBlockRecsBare p.toBlockShape 0 (cvRus.map fun q => (q.1, q.2.1)) env₂)
      (fueledOps mode G) env₂ p (blockRecCallData p).1 (blockRecCallData p).2
      (cvRus.map fun q => (q.1, q.2.1)) ctorsAs p.recs 0 = .ok rs := by
    rw [← checkBlockRecsRules_datF]; exact FueledM.up hle₄ hF₄
  rw [checkBlockRecK_datF]
  unfold checkBlockRecK
  simp only [Bind.bind, Except.bind]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  exact g₄

/-- The projection tables at the cached driver: operation-free, the
state unchanged, the environment the pure stage's. -/
theorem checkBlockTablesS_run (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env)
      {s₀ : CState} {fe' : FEnv} {s' : CState}, EnvWF env → CSOKF s₀ →
      checkBlockTablesF (m := CheckCM) .plain p l (mkFEnv env) s₀ = .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
        checkBlockTables (m := CheckM) p l env = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    simp only [checkBlockTablesF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, rfl⟩
  | (ms, ctorsA, sortss) :: rest, env, s₀, fe', s', henv, hwf, h => by
    match ctorsA, sortss with
    | [cA], [sorts] =>
      simp only [checkBlockTablesF] at h
      by_cases hi : (ms.nIdx == 0) = true
      · rw [if_pos hi] at h
        obtain ⟨fe₁, s₁, h1, h⟩ := bindC_ok h
        obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ := checkStructProjTableS_run env henv hwf h1
        rw [hfe₁] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest fe₁.env henv₁ hwf₁ h
        refine ⟨hwf', hfe', henv', ?_⟩
        rw [checkStructProjTable_datF] at hF₁
        simp only [checkBlockTables, if_pos hi, Bind.bind, Except.bind]
        rw [hF₁]
        exact hrest
      · rw [if_neg hi] at h
        simp only [pure_bind] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
        refine ⟨hwf', hfe', henv', ?_⟩
        simp only [checkBlockTables, if_neg hi, pure_bind]
        exact hrest
    | [], _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | _ :: _ :: _, _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], [] =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], _ :: _ :: _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩

/-- The constructors' stage stores fvar-free constructor types. -/
theorem checkBlockCtors_types {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss)) :
    ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨hlenC, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < l[i].1.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, sorts, -, hrun⟩ := hallc j (l[i].1.ctors[j]) c (List.getElem?_eq_getElem hjl) hj
  exact WScoped.of_not_hasFvar (direct_sum_ctor_typeWF hrun).1

/-- **One pass at k members, at the cached driver**, is reproduced by
the pure fueled `checkBlockPass`: the formers' environment is the index
over the pure one, the memo state is an invariant state of it, and the
formers' and the constructors' types are fvar-free. -/
theorem checkBlockPassS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : BlockParts} {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀)
    {q : BlockPass FEnv} {b : Bool} {s' : CState}
    (h : checkBlockPassS mode (mkFEnv env) p₀ isRec s₀ = .ok ((q, b), s')) :
    ∃ env₁ : Env, q.env₁ = mkFEnv env₁ ∧ CSOK mode env₁ s' ∧ EnvWF env₁ ∧
      (∀ cv ∈ q.cvTas, WScoped 0 cv.type) ∧
      (∀ ctorsA ∈ q.ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type) ∧
      EnvWF (consBlockCtors q.p.nP q.ctorsAs env₁) ∧
      ∃ F, (checkBlockPass (fueledOpsM mode) env p₀ isRec).val F
        = .ok (⟨env₁, q.cvTas, q.p, q.ctorsAs, q.sortsss⟩, b) := by
  unfold checkBlockPassS at h
  rw [checkBlockIndsF_eqC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨r₁, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, r₁', hP1, F₁, hF₁⟩ := checkBlockIndsS_sim hμ henv hs r₁ s₁ hind
  obtain ⟨rfl, hwT⟩ := hP1
  obtain ⟨env₁, cvTas, p₁⟩ := r₁
  have hF₁p : checkBlockInds (fueledOps mode F₁) env p₀ isRec = .ok (env₁, cvTas, p₁) := by
    rw [← checkBlockInds_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_block_inds_wf henv hF₁p
  try simp only at h
  obtain ⟨uB, sB, hflB, h⟩ := bindC_ok h
  rw [flushC_run] at hflB
  injection hflB with hflB
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hflB
  rw [checkBlockCtorsF_eqC] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ (p₀.complete p₁).members.zip cvTas, x.2.type.hasFvar = false :=
    fun x hx => hTf x.2 (List.of_mem_zip hx).2
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    checkBlockCtorsS_sim hμ henv₁ hzT (flushC_csok hs₁.residue) q2 s₂ hct
  obtain rfl : q2 = q2' := hP2
  obtain ⟨ctorsAs, sortsss⟩ := q2
  have hF₂p : checkBlockCtors (fueledOps mode F₂) env₁ env₁ (p₀.complete p₁).toBlockShape
      ((p₀.complete p₁).members.zip cvTas) = .ok (ctorsAs, sortsss) := by
    rw [← checkBlockCtors_datF]; exact hF₂
  try simp only at h
  obtain ⟨kinds, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := classifyBlockKindsC_ok hK
  obtain ⟨hq, rfl⟩ := pureC_ok h
  subst hsK
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  refine ⟨env₁, rfl, hs₂, henv₁, hwT, checkBlockCtors_types hF₂p,
    direct_block_ctors_wf henv₁ hF₂p, max F₁ F₂, ?_⟩
  have g₁ : checkBlockInds (fueledOps mode (max F₁ F₂)) env p₀ isRec = .ok (env₁, cvTas, p₁) := by
    rw [← checkBlockInds_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkBlockCtors (fueledOps mode (max F₁ F₂)) env₁ env₁ (p₀.complete p₁).toBlockShape
      ((p₀.complete p₁).members.zip cvTas) = .ok (ctorsAs, sortsss) := by
    rw [← checkBlockCtors_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  rw [checkBlockPass_datF]
  unfold checkBlockPass
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [hKp]

/-- **The install after the pass, at k members and at the recursor
stage's CHECK, at the cached driver**, is reproduced by the pure fueled
`checkBlockTail`. -/
theorem checkBlockTailS_run (hμ : mode.verifiedChecks = true) (hK : blockRecCheckOn = true)
    {env env₁ : Env} (henv₁ : EnvWF env₁) {cvTas : List ConstantVal} {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    (henv₂ : EnvWF (consBlockCtors p.nP ctorsAs env₁))
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockTailS mode (mkFEnv env) ⟨mkFEnv env₁, cvTas, p, ctorsAs, sortsss⟩ s₀
      = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkBlockTail (fueledOpsM mode) env ⟨env₁, cvTas, p, ctorsAs, sortsss⟩).val F
      = .ok feOut.env := by
  unfold checkBlockTailS at h
  dsimp only at h
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  rw [checkBlockIdxSortsF_eqC] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ p.members.zip cvTas, WScoped 0 x.2.type :=
    fun x hx => hT x.2 (List.of_mem_zip hx).2
  obtain ⟨hsS, isorts', hPs, F₀, hF₀⟩ :=
    checkBlockIdxSortsS_sim hμ henv₁ hzT hs isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  rw [structWalkersC_eq_plain, blockFieldsOkF_eqC] at h
  by_cases hk : blockFieldsOk env p.memberNames p.lps p.nP p.nIdxs ctorsAs p.kinds = true
  case neg => rw [if_neg hk] at h; exact absurd h throwC_bind_ok
  rw [if_pos hk] at h
  rw [consBlockCtorsF_mkFEnv] at h
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  obtain ⟨rs, s₃, hrec, h⟩ := bindC_ok h
  unfold checkBlockRecS at hrec
  rw [if_pos hK] at hrec
  obtain ⟨hs₃, F₃, hF₃⟩ := checkBlockRecKS_run hμ henv₂ hT hct (flushC_csok hsS.residue) hrec
  have hF₃p : checkBlockRecK (fueledOps mode F₃) (consBlockCtors p.nP ctorsAs env₁) p cvTas ctorsAs
      = .ok rs := by
    rw [← checkBlockRecK_datF]; exact hF₃
  have henv₃ := envWF_consBlockRecs (find? := (consBlockCtors p.nP ctorsAs env₁).find?)
    (q := p.toBlockShape) (nP := p.nP) henv₂ (checkBlockRecK_facts hF₃p)
  rw [show FEnv.find? (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
    = (consBlockCtors p.nP ctorsAs env₁).find? from mkFEnv_find?_fun _,
    consBlockRecsF_mkFEnv] at h
  obtain ⟨hwfO, hfeO, -, hT₆⟩ := checkBlockTablesS_run _ _ _ henv₃ hs₃ h
  refine ⟨hwfO, hfeO, max F₀ F₃, ?_⟩
  have g₀ : checkBlockIdxSorts (fueledOps mode (max F₀ F₃)) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts := by
    rw [← checkBlockIdxSorts_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₀
  have g₃ : checkBlockRec (fueledOps mode (max F₀ F₃)) (consBlockCtors p.nP ctorsAs env₁) p
      cvTas ctorsAs = .ok rs := by
    unfold checkBlockRec
    rw [if_pos hK, ← checkBlockRecK_datF]
    exact FueledM.up (Nat.le_max_right _ _) hF₃
  rw [checkBlockTail_datF]
  unfold checkBlockTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₀]
  simp only [Except.bind]
  rw [if_pos hk]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₃]
  simp only [Except.bind]
  exact hT₆

/-- **The uniform install at k members, at the recursor stage's CHECK,
at the cached driver**, is reproduced by the pure fueled `checkBlock`:
the pass at the syntactic reading, again at the classified verdict
where it overshot, and the install after the settled one — the k-ary
twin of `checkNativeS_run`. -/
theorem checkBlockKS_run (hμ : mode.verifiedChecks = true) (hK : blockRecCheckOn = true)
    {env : Env} (henv : EnvWF env) {p₀ : BlockParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkBlockKS mode (mkFEnv env) p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkBlock (fueledOps mode F) env p₀ = .ok feOut.env := by
  unfold checkBlockKS at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  obtain ⟨r, s₁, hP, h⟩ := bindC_ok h
  obtain ⟨⟨fe₁, cvTas, p, ctorsAs, sortsss⟩, settled⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hT, hct, henv₂, F₁, hF₁⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hT hct henv₂ hF₁
  subst hq₁
  try simp only at h
  cases settled with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkBlockTailS_run hμ hK henv₁ hT hct henv₂ hs₁ h
    refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
    have g₁ : checkBlockPass (fueledOps mode (max F₁ F₂)) env p₀ (blockRawRec p₀)
        = .ok (⟨env₁, cvTas, p, ctorsAs, sortsss⟩, true) := by
      rw [← checkBlockPass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : checkBlockTail (fueledOps mode (max F₁ F₂)) env ⟨env₁, cvTas, p, ctorsAs, sortsss⟩
        = .ok feOut.env := by
      rw [← checkBlockTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
    unfold checkBlock
    rw [if_pos hnd]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [g₁]
    simp only [Except.bind, ↓reduceIte]
    exact g₂
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  obtain ⟨r', s₂, hP', h⟩ := bindC_ok h
  obtain ⟨⟨fe₁', cvTas', p', ctorsAs', sortsss'⟩, settled'⟩ := r'
  obtain ⟨env₁', hq₁', hs₁', henv₁', hT', hct', henv₂', F₂, hF₂⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hs₁.residue) hP'
  simp only at hq₁' hs₁' henv₁' hT' hct' henv₂' hF₂
  subst hq₁'
  try simp only at h
  cases settled' with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h throwC_bind_ok
  | true =>
  simp only [↓reduceIte] at h
  obtain ⟨hwfO, hfeO, F₃, hF₃⟩ := checkBlockTailS_run hμ hK henv₁' hT' hct' henv₂' hs₁' h
  obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
    ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : checkBlockPass (fueledOps mode G) env p₀ (blockRawRec p₀)
      = .ok (⟨env₁, cvTas, p, ctorsAs, sortsss⟩, false) := by
    rw [← checkBlockPass_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkBlockPass (fueledOps mode G) env p₀ (blockIsRec p.kinds)
      = .ok (⟨env₁', cvTas', p', ctorsAs', sortsss'⟩, true) := by
    rw [← checkBlockPass_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkBlockTail (fueledOps mode G) env ⟨env₁', cvTas', p', ctorsAs', sortsss'⟩
      = .ok feOut.env := by
    rw [← checkBlockTail_datF]; exact FueledM.up hle₃ hF₃
  unfold checkBlock
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind, Bool.false_eq_true, ↓reduceIte]
  rw [g₂]
  simp only [Except.bind, ↓reduceIte]
  exact g₃

variable {pins : List NatOpPinSet}

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkBlockS`, everything else to `checkIndDeclSF`,
and either way the pure fueled `checkDecl` reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match blockParts? nP block with
          | some p => checkBlockS mode (mkFEnv env) p
          | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match basisPinHit block with
      | some kind => checkBasisDecl (m := CheckM) env kind
      | none =>
        if indParamsOk nP block = true then
          (match blockParts? nP block with
            | some p => checkBlock (fueledOps mode F) env p
            | none => checkModeled mode (fueledOps mode F) env block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : blockParts? nP block with
  | some p =>
    rw [hfp] at h
    simp only at h
    -- the k-ary route at the recursor stage's CHECK; the one-member arm
    -- below it reads the route's gate and goes with both gates at the flip
    by_cases hK : blockRecCheckOn = true
    · rw [checkBlockS_K mode hK] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkBlockKS_run hμ hK henv hwf h
      exact ⟨hres, hfe, F, hF⟩
    · have hK' : blockRecCheckOn = false := by simpa using hK
      obtain ⟨⟨ms, hms⟩, rc, hrc⟩ := blockParts?_k1 (blockRouteK1Only_of_recOff hK') hfp
      rw [checkBlockS_one mode hK' hms] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkNativeS_run hμ henv hwf h
      refine ⟨hres, hfe, F, ?_⟩
      simp only []
      rw [← checkBlock_one (m := CheckM) (fueledOps mode F) env hms hrc]
      exact hF
  | none =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩

end ConLeche.Cached
