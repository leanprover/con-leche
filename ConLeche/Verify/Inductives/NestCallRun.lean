module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# The calls' run facts at a nested stage

The run facts the calls' landing reads off the install, beside
`RecCheckRun.lean` and `PositivityInv.lean`:

* every call's typing ran (`targetCallsOk_each`);
* the members' own walked constructors went through the hook
  (`checkBlockPositivity_memberHook`);
* a walked constructor the hook accepted had the rule of every class
  that matches it typed there (`targetHook_rule`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Every call's typing ran -/

/-- **Every call's typing ran**, one by one. -/
theorem targetCallsOk_each {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fws : List Expr} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF fnorm teles absM base k
        pw fws ihs = .ok () →
      ∀ ih ∈ ihs, targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF fnorm teles
        absM base k pw fws ih = .ok ()
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · cases u; exact hu
    · exact targetCallsOk_each h ih hih

/-! ## The members' walked constructors -/

/-- **A member constructor's walked form went through the hook** (node
`0`, `nestMemberNf`): at the positivity run, member `m`'s constructor
`j` at the block's own levels and parameters, its normal form (the run's
`nfs`) read back. -/
theorem checkBlockPositivity_memberHook {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {hook : NestHook CheckM}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {keys : List NestKey}
    {done : List (Nat × Nat × Expr)}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs hook
      = .ok (kinds, nfs, keys, done)) :
    ∃ cvTa0 fvsP rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[m]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
          HookOk hook (nestMemberNf (p.nestCtx fvsP find? consts) cA.1
            ((nfs.getD m []).getD j default)) := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, -, hthr⟩ := checkBlockPositivity_inv_I h
  obtain ⟨-, -, -, -, -, -, -, -, hall⟩ := hthr (fun _ => True) (fun _ _ => True) trivial
    (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
  refine ⟨cvTa0, fvsP, rest, h1, h2, fun m cs hcs j cA hj => ?_⟩
  obtain ⟨-, -, -, tyN, -, xs, -, -, -, hx, htyN, -, -⟩ := hall m cs hcs j cA hj
  rw [htyN]
  exact ⟨xs, hx⟩

/-! ## A walked constructor's rules -/

/-- **The hook's rules at a walked constructor it accepted**: every class
`c` of the family that has the constructor `e.ctor` (at `j`) and matches
the node's instantiation (`targetClassMatch`) had its rule for it typed
there (`targetRule`, K.53′ against `e`). -/
theorem targetEntryRules_rule {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {e : NestCtorNf} {F : Nat} :
    ∀ {c : Nat} {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
      {xs : List (Nat × Nat × Expr)},
      targetEntryRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam e c
        recs tys = .ok xs →
      ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
        recs[i]? = some rc → tys[i]? = some t →
        ∀ j, t.2.1.ctors.findIdx? (·.1.name == e.ctor) = some j →
        targetClassMatch (fueledOps mode F) feT.env p formerTys t.2.1.pfvs t.2.1.lvls t.2.1.ds
          e.lvls e.ds = .ok true →
        ∃ cA rhs o, t.2.1.ctors[j]? = some cA ∧ rc.rhss[j]? = some rhs ∧
          targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam t.1 rc.rP
            t.1.type t.2.1 cA rhs e.ty = .ok o
  | _, [], _, _, _, i, rc, t, hi, _, _, _, _ => nomatch hi
  | _, _ :: _, [], _, _, i, rc, t, _, ht, _, _, _ => nomatch ht
  | c, rc0 :: rcs, (cvRi, M, u) :: ts, xs, h, i, rc, t, hi, ht, j, hj, hm => by
    unfold targetEntryRules at h
    obtain ⟨here, hh, h⟩ := exceptBind_ok h
    obtain ⟨rest, hr, -⟩ := exceptBind_ok h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      obtain rfl := Option.some.inj ht
      unfold targetEntryRule at hh
      simp only at hj hm
      rw [hj] at hh
      obtain ⟨b, hb, hh⟩ := exceptBind_ok hh
      rw [hm] at hb
      obtain rfl := Except.ok.inj hb
      rw [if_pos rfl] at hh
      obtain ⟨cA, hcA, hh⟩ := exceptBind_ok hh
      obtain ⟨rhs, hrhs, hh⟩ := exceptBind_ok hh
      obtain ⟨o, ho, -⟩ := exceptBind_ok hh
      exact ⟨cA, rhs, o, unwrapOr_ok hcA, unwrapOr_ok hrhs, ho⟩
    | succ i => exact targetEntryRules_rule hr i rc t (by simpa using hi) (by simpa using ht) j hj hm

/-- **The hook's rules at a walked constructor it accepted** (`HookOk`),
at the fused traversal's hook. -/
theorem targetHook_rule {fe feR : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
    {F : Nat} {e : NestCtorNf}
    (h : HookOk (targetHook (ShadowOps.fueled mode F) fe feR p formerTys fam recs tys) e) :
    ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
      recs[i]? = some rc → tys[i]? = some t →
      ∀ j, t.2.1.ctors.findIdx? (·.1.name == e.ctor) = some j →
      targetClassMatch (fueledOps mode F) fe.env p formerTys t.2.1.pfvs t.2.1.lvls t.2.1.ds
        e.lvls e.ds = .ok true →
      ∃ cA rhs o, t.2.1.ctors[j]? = some cA ∧ rc.rhss[j]? = some rhs ∧
        targetRule (fueledOps mode F) .plain feR (fueledOps mode F) fe p formerTys fam t.1 rc.rP
          t.1.type t.2.1 cA rhs e.ty = .ok o := by
  obtain ⟨xs, he⟩ := h
  simp only [targetHook, ShadowOps.fueled, ShadowOps.ofOps] at he
  obtain ⟨u1, -, he⟩ := exceptBind_ok he
  obtain ⟨xs', hxs', -⟩ := exceptBind_ok he
  exact targetEntryRules_rule hxs'

end ConLeche
