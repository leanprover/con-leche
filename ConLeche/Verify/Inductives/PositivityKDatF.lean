module

public import ConLeche.Verify.BridgeDecl
public import ConLeche.Kernel.Inductives.BlockPositivityK

public section

/-!
# The key-named positivity check at a fuel (PRIMREC / NESTKN-S0, S0.2)

The `atF` battery for `PositivityK.lean` (and `checkBlockPositivityK`): every
function run at the fueled families (`fueledOpsM`) is, at fuel `F`, the same
function run at `fueledOps mode F` — what `checkBlockPositivity_datF`
(`BridgeDecl.lean`) reads at the switch.

The key-named check runs TRIALS (`CheckerOps.attempt`: the flexibility trial and
the gates of the hook checks, `hookK`), and the fueled trial is the plain one only
on a body whose verdict is settled for good (`fueledOpsM_attempt_atF`).  So each
trial's body gets a stability lemma (`FueledM.Stable`: the core's entry points are
stable by `Mono.lean`, and stability is closed under the monad) next to its `datF`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open FueledM

/-! ## Stability kit -/

theorem fueledOpsM_inferType_stable (env : Env) (d : Nat) (e : Expr) :
    Stable ((fueledOpsM mode).inferType env d e) :=
  ⟨fun hle => inferTypeCore_refines hle d e⟩

theorem fueledOpsM_ensureSort_stable (env : Env) (d : Nat) (e : Expr) :
    Stable ((fueledOpsM mode).ensureSort env d e) :=
  ⟨fun hle => ensureSortCore_refines hle d e⟩

theorem fueledOpsM_isDefEq_stable (env : Env) (d : Nat) (a b : Expr) :
    Stable ((fueledOpsM mode).isDefEq env d a b) :=
  ⟨fun hle => isDefEqCore_refines hle d a b⟩

theorem fueledOpsM_whnf_stable (env : Env) (d : Nat) (e : Expr) :
    Stable ((fueledOpsM mode).whnf env d e) :=
  ⟨fun hle => whnf_refines hle d e⟩

/-- A family that is one computation at every fuel is stable. -/
theorem Stable.of_atF {α : Type} {x : FueledM α} (c : CheckM α) (h : ∀ F, x.val F = c) :
    Stable x := ⟨fun {f f'} _ => by rw [h f, h f']; exact MRefines.rfl⟩

theorem Stable.unwrapOr {α : Type} (o : Option α) (e : CheckError) :
    Stable (unwrapOr o e : FueledM α) :=
  Stable.of_atF _ (unwrapOr_atF o e)

theorem nestInstType_stable (ctx : NestCtx) (hi : Nat) (key : NestKey) :
    Stable (nestInstType (m := FueledM) ctx hi key) :=
  Stable.of_atF _ (nestInstType_datF ctx hi key)

/-- The stability steps: the monad, the catch, the core's entry points. -/
macro "stable_tac" : tactic =>
  `(tactic| repeat' (first
    | exact Stable.pure _
    | exact Stable.throw _
    | exact Stable.unwrapOr _ _
    | exact nestInstType_stable _ _ _
    | exact fueledOpsM_inferType_stable _ _ _
    | exact fueledOpsM_ensureSort_stable _ _ _
    | exact fueledOpsM_isDefEq_stable _ _ _ _
    | exact fueledOpsM_whnf_stable _ _ _
    | apply Stable.bind
    | apply Stable.ite
    | intro _
    | split
    | (dsimp only)
    | assumption))

/-- A trial at a fuel: the plain one, on a stable body. -/
theorem attempt_atF_of_stable {x : FueledM Unit} (hx : Stable x) (F : Nat) :
    ((fueledOpsM mode).attempt x).val F = (fueledOps mode F).attempt (x.val F) :=
  fueledOpsM_attempt_atF x fun _ hle => hx.refines hle

/-- The hook check at a fuel: the plain one, on a stable body. -/
theorem hookK_atF {α : Type} {what : String} {x : FueledM α} {gate : Bool} (hx : Stable x)
    (F : Nat) :
    (hookK (fueledOpsM mode) what x gate).val F = hookK (fueledOps mode F) what (x.val F) gate := by
  unfold hookK
  cases gate with
  | false => rfl
  | true =>
    simp only [if_true, atF_bind,
      attempt_atF_of_stable (Stable.bind hx fun _ => Stable.pure _)]
    congr 1
    funext a
    cases a <;> rfl

/-! ## Keys, merging, the layout's typing -/

theorem dsDefEqK_datF (env : Env) (d F : Nat) :
    ∀ (as bs : List Expr),
      (dsDefEqK (fueledOpsM mode) env d as bs).val F = dsDefEqK (fueledOps mode F) env d as bs
  | a :: as, b :: bs => by
    unfold dsDefEqK
    rw [atF_bind]
    congr 1
    funext r
    cases r
    · rfl
    · exact dsDefEqK_datF env d F as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem findRepK_datF (env : Env) (ctx : NestCtx) (k : NestKey) (F : Nat) :
    ∀ (rs : List NestKey) (j : Nat),
      (findRepK (fueledOpsM mode) env ctx k rs j).val F = findRepK (fueledOps mode F) env ctx k rs j
  | [], _ => rfl
  | r :: rs, j => by
    unfold findRepK
    split
    · rw [atF_bind, dsDefEqK_datF]
      congr 1
      funext b
      cases b
      · exact findRepK_datF env ctx k F rs (j + 1)
      · rfl
    · exact findRepK_datF env ctx k F rs (j + 1)

theorem mergeK_datF (env : Env) (ctx : NestCtx) (F : Nat) :
    ∀ (ks reps : List NestKey) (als : List (NestKey × Nat)),
      (mergeK (fueledOpsM mode) env ctx ks reps als).val F = mergeK (fueledOps mode F) env ctx ks reps als
  | [], _, _ => rfl
  | k :: ks, reps, als => by
    unfold mergeK
    rw [atF_bind, findRepK_datF]
    congr 1
    funext r
    cases r
    · exact mergeK_datF env ctx F ks _ _
    · exact mergeK_datF env ctx F ks _ _

theorem typeAtK_stable (env : Env) (d : Nat) (e : Expr) (sort : Bool) :
    Stable (typeAtK (fueledOpsM mode) env d e sort) := by
  unfold typeAtK
  stable_tac

theorem typeAtK_datF (env : Env) (d : Nat) (e : Expr) (sort : Bool) (F : Nat) :
    (typeAtK (fueledOpsM mode) env d e sort).val F = typeAtK (fueledOps mode F) env d e sort := by
  unfold typeAtK
  rw [atF_bind]
  congr 1
  funext ty
  cases sort
  · rfl
  · rw [atF_ite]
    simp only [atF_bind, atF_pure]
    rfl

theorem typeCrestsK_stable (env : Env) (hi : Nat) :
    ∀ cs : List Expr, Stable (typeCrestsK (fueledOpsM mode) env hi cs)
  | [] => Stable.pure _
  | c :: cs => by
    unfold typeCrestsK
    exact Stable.bind (typeAtK_stable env hi c true) fun _ => typeCrestsK_stable env hi cs

theorem typeCrestsK_datF (env : Env) (hi F : Nat) :
    ∀ cs : List Expr,
      (typeCrestsK (fueledOpsM mode) env hi cs).val F = typeCrestsK (fueledOps mode F) env hi cs
  | [] => rfl
  | c :: cs => by
    unfold typeCrestsK
    rw [atF_bind, typeAtK_datF]
    congr 1
    funext _
    exact typeCrestsK_datF env hi F cs

theorem groupInfoK_datF (ctx : NestCtx) (us : List Level) (dsF : List Expr) (hiK F : Nat) :
    ∀ gs : List Name,
      (groupInfoK (m := FueledM) ctx us dsF hiK gs).val F = groupInfoK (m := CheckM) ctx us dsF hiK gs
  | [] => rfl
  | g :: gs => by
    unfold groupInfoK
    rw [atF_bind, nestInstType_datF]
    congr 1
    funext r
    rw [atF_bind, groupInfoK_datF ctx us dsF hiK F gs]
    rfl

theorem groupInfoK_stable (ctx : NestCtx) (us : List Level) (dsF : List Expr) (hiK : Nat)
    (gs : List Name) : Stable (groupInfoK (m := FueledM) ctx us dsF hiK gs) :=
  Stable.of_atF _ (groupInfoK_datF ctx us dsF hiK · gs)

theorem layoutTypeK_stable (env : Env) (ctx : NestCtx) (kc : NestKey) (gnames : List Name)
    (ctors : List (ConstantVal × Nat)) (S : List (NestKey × Expr)) (nF : Nat) :
    Stable (layoutTypeK (fueledOpsM mode) env ctx kc gnames ctors S nF) := by
  unfold layoutTypeK
  refine Stable.bind (groupInfoK_stable _ _ _ _ _) fun ginfo => ?_
  refine Stable.bind (Stable.unwrapOr _ _) fun crests => ?_
  refine Stable.bind (typeAtK_stable _ _ _ _) fun _ => ?_
  refine Stable.bind (typeCrestsK_stable _ _ _) fun _ => ?_
  exact Stable.pure _

theorem layoutTypeK_datF (env : Env) (ctx : NestCtx) (kc : NestKey) (gnames : List Name)
    (ctors : List (ConstantVal × Nat)) (S : List (NestKey × Expr)) (nF F : Nat) :
    (layoutTypeK (fueledOpsM mode) env ctx kc gnames ctors S nF).val F
      = layoutTypeK (fueledOps mode F) env ctx kc gnames ctors S nF := by
  unfold layoutTypeK
  simp only [atF_bind, atF_pure, groupInfoK_datF, unwrapOr_atF, typeAtK_datF, typeCrestsK_datF]

theorem flexK_datF (env : Env) (ctx : NestCtx) (kc : NestKey) (gnames : List Name)
    (ctors : List (ConstantVal × Nat)) (reps : List NestKey) (als : List (NestKey × Nat))
    (F : Nat) :
    ∀ (rs : List Nat) (fl : List (Nat × Expr × Nat)),
      (flexK (fueledOpsM mode) env ctx kc gnames ctors reps als rs fl).val F
        = flexK (fueledOps mode F) env ctx kc gnames ctors reps als rs fl
  | [], _ => rfl
  | r :: rs, fl => by
    unfold flexK
    split
    · rw [atF_bind, attempt_atF_of_stable
        (Stable.bind (layoutTypeK_stable _ _ _ _ _ _ _) fun _ => Stable.pure _)]
      rw [atF_bind, layoutTypeK_datF]
      congr 1
      funext ok
      exact flexK_datF env ctx kc gnames ctors reps als F rs _
    · exact flexK_datF env ctx kc gnames ctors reps als F rs fl

theorem groupCtorsK_datF (look : Name → Option (Nat × List (ConstantVal × Nat))) (nPc F : Nat) :
    ∀ cs : List Name,
      (groupCtorsK (m := FueledM) look nPc cs).val F = groupCtorsK (m := CheckM) look nPc cs
  | [] => rfl
  | c :: cs => by
    unfold groupCtorsK
    simp only [atF_bind, atF_pure, atF_throw, atF_ite, unwrapOr_atF,
      groupCtorsK_datF look nPc F cs]

theorem famTysSortK_stable (env : Env) :
    ∀ (d : Nat) (ts : List Expr), Stable (famTysSortK (fueledOpsM mode) env d ts)
  | _, [] => Stable.pure _
  | d, t :: ts => by
    unfold famTysSortK
    exact Stable.bind (fueledOpsM_inferType_stable _ _ _) fun _ =>
      Stable.bind (fueledOpsM_ensureSort_stable _ _ _) fun _ => famTysSortK_stable env (d + 1) ts

theorem famTysSortK_datF (env : Env) (F : Nat) :
    ∀ (d : Nat) (ts : List Expr),
      (famTysSortK (fueledOpsM mode) env d ts).val F = famTysSortK (fueledOps mode F) env d ts
  | _, [] => rfl
  | d, t :: ts => by
    unfold famTysSortK
    simp only [atF_bind, famTysSortK_datF env F (d + 1) ts]
    rfl

theorem keysTypedK_stable (env : Env) (d : Nat) :
    ∀ ks : List NestKey, Stable (keysTypedK (fueledOpsM mode) env d ks)
  | [] => Stable.pure _
  | k :: ks => by
    unfold keysTypedK
    exact Stable.bind (fueledOpsM_inferType_stable _ _ _) fun _ => keysTypedK_stable env d ks

theorem keysTypedK_datF (env : Env) (d F : Nat) :
    ∀ ks : List NestKey,
      (keysTypedK (fueledOpsM mode) env d ks).val F = keysTypedK (fueledOps mode F) env d ks
  | [] => rfl
  | k :: ks => by
    unfold keysTypedK
    simp only [atF_bind, keysTypedK_datF env d F ks]
    rfl

/-- One `atF` step: peel a bind (both sides the same program), split a branch, or
rewrite a callee by its own `atF` lemma (the extra ones passed as `simp` arguments). -/
syntax "kdatF_tac" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| kdatF_tac [$ls,*]) =>
    `(tactic| repeat' (first
      | with_reducible rfl
      | (simp only [atF_bind, unwrapOr_atF, atF_pure, atF_throw, atF_ite, fueledOpsM_isDefEq_atF,
        fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF, fueledOpsM_whnf_atF, $ls,*]; done)
      | (rw [hookK_atF]; case hx => stable_tac)
      | (rw [atF_bind]; congr 1 <;> (try rfl) <;> (try funext _))
      | split
      | (dsimp only)
      | (simp only [unwrapOr_atF, atF_pure, atF_throw, atF_ite, fueledOpsM_isDefEq_atF,
        fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF, fueledOpsM_whnf_atF, $ls,*])
      | (congr 1 <;> (try rfl) <;> (try funext _))))

theorem nestLayoutK_datF (env : Env) (ctx : NestCtx)
    (look : Name → Option (Nat × List (ConstantVal × Nat))) (kc0 : NestKey) (F : Nat) :
    (nestLayoutK (fueledOpsM mode) env ctx look kc0).val F
      = nestLayoutK (fueledOps mode F) env ctx look kc0 := by
  unfold nestLayoutK
  kdatF_tac [groupCtorsK_datF, mergeK_datF, flexK_datF,
    hookK_atF (layoutTypeK_stable _ _ _ _ _ _ _), layoutTypeK_datF,
    hookK_atF (famTysSortK_stable _ _ _), famTysSortK_datF,
    hookK_atF (keysTypedK_stable _ _ _), keysTypedK_datF]

/-! ## The match and the hook checks -/

theorem checkParamsK_datF (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK)
    (θ : Nat → Option Expr) (F : Nat) :
    ∀ ps : List (Expr × Expr),
      (checkParamsK (fueledOpsM mode) env ctx L nd θ ps).val F
        = checkParamsK (fueledOps mode F) env ctx L nd θ ps
  | [] => rfl
  | (p, t) :: rest => by
    unfold checkParamsK
    kdatF_tac [typeAtK_datF, checkParamsK_datF env ctx L nd θ F rest]

theorem bindArityK_datF (ctx : NestCtx) (L : LayoutK) (b : Expr) (nI F : Nat) :
    (bindArityK (m := FueledM) ctx L b nI).val F = bindArityK (m := CheckM) ctx L b nI := by
  unfold bindArityK
  kdatF_tac []

theorem bindsOkK_datF (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK)
    (θ : Nat → Option Expr) (F : Nat) :
    ∀ js : List Nat,
      (bindsOkK (fueledOpsM mode) env ctx L nd θ js).val F
        = bindsOkK (fueledOps mode F) env ctx L nd θ js
  | [] => rfl
  | j :: js => by
    unfold bindsOkK
    kdatF_tac [bindArityK_datF, bindsOkK_datF env ctx L nd θ F js]

theorem matchK_datF (env : Env) (ctx : NestCtx) (L : LayoutK) (nd : NodeK) (ps : List Expr)
    (F : Nat) :
    (matchK (fueledOpsM mode) env ctx L nd ps).val F = matchK (fueledOps mode F) env ctx L nd ps := by
  unfold matchK
  kdatF_tac [checkParamsK_datF, bindsOkK_datF]

/-! ## The walk's pieces, with their recursive calls as parameters -/

section Pieces

variable {use : LayoutK → NestKey → List Expr → NestStK → FueledM (Nat × NestStK)}
  {use' : LayoutK → NestKey → List Expr → NestStK → CheckM (Nat × NestStK)}
  {rec : LayoutK → Nat → Nat → Expr → NestStK → FueledM (NestFieldKind × Expr × NestStK)}
  {rec' : LayoutK → Nat → Nat → Expr → NestStK → CheckM (NestFieldKind × Expr × NestStK)}
  {syn : LayoutK → Option NestKey → Expr → NestStK → FueledM NestStK}
  {syn' : LayoutK → Option NestKey → Expr → NestStK → CheckM NestStK}

theorem metK_datF {F : Nat} (huse : ∀ a b c d, (use a b c d).val F = use' a b c d)
    (ctx : NestCtx) (L : LayoutK) (met : List Nat) :
    ∀ (bs : List (Nat × Expr)) (st : NestStK),
      (metK ctx L use met bs st).val F = metK ctx L use' met bs st := by
  intro bs
  induction bs with
  | nil => intro st; rfl
  | cons jb bs ih =>
    intro st
    obtain ⟨j, b⟩ := jb
    unfold metK
    kdatF_tac [huse, ih]

theorem contK_datF {F : Nat} (huse : ∀ a b c d, (use a b c d).val F = use' a b c d)
    (ctx : NestCtx) (L : LayoutK) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestStK) :
    (contK ctx use L kb n us args st).val F = contK ctx use' L kb n us args st := by
  unfold contK
  kdatF_tac [huse, nestInstType_datF]

theorem synKeysK_datF {F : Nat} (huse : ∀ a b c d, (use a b c d).val F = use' a b c d)
    (ctx : NestCtx) (L : LayoutK) (skip : Option NestKey) :
    ∀ (ks : List NestKey) (st : NestStK),
      (synKeysK ctx L use skip ks st).val F = synKeysK ctx L use' skip ks st
  | [], _ => rfl
  | key :: ks, st => by
    unfold synKeysK
    kdatF_tac [huse, synKeysK_datF huse ctx L skip ks]

theorem fieldsK_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (hsyn : ∀ a b c d, (syn a b c d).val F = syn' a b c d) (L : LayoutK) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestStK),
      (fieldsK rec syn L err nF j cur st).val F = fieldsK rec' syn' L err nF j cur st
  | 0, _, _, _ => rfl
  | nF + 1, j, cur, st => by
    unfold fieldsK
    kdatF_tac [hrec, hsyn, fieldsK_datF hrec hsyn L err nF (j + 1)]

theorem ctorsK_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (hsyn : ∀ a b c d, (syn a b c d).val F = syn' a b c d) (ctx : NestCtx) (L : LayoutK) :
    ∀ (cs : List ((ConstantVal × Nat) × Expr)) (st : NestStK),
      (ctorsK ctx rec syn L cs st).val F = ctorsK ctx rec' syn' L cs st
  | [], _ => rfl
  | ((_, nF), crest) :: cs, st => by
    unfold ctorsK
    kdatF_tac [fieldsK_datF hrec hsyn, ctorsK_datF hrec hsyn ctx L cs]

end Pieces

theorem frameNfsK_datF (env : Env) (ctx : NestCtx) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) (F : Nat) :
    ∀ cs : List (ConstantVal × Nat),
      (frameNfsK (fueledOpsM mode) env ctx us ds grp cs).val F
        = frameNfsK (fueledOps mode F) env ctx us ds grp cs
  | [] => rfl
  | (cv, nF) :: cs => by
    unfold frameNfsK
    kdatF_tac [nestFrameCtorNf_datF, frameNfsK_datF env ctx us ds grp F cs]

/-! ## The walk -/

theorem posK_datF (env : Env) (ctx : NestCtx) (F : Nat) :
    ∀ fuel : Nat,
      (∀ L dep kb e st, (posK (fueledOpsM mode) env ctx fuel L dep kb e st).val F
        = posK (fueledOps mode F) env ctx fuel L dep kb e st) ∧
      (∀ L skip e st, (synK (fueledOpsM mode) env ctx fuel L skip e st).val F
        = synK (fueledOps mode F) env ctx fuel L skip e st) ∧
      (∀ L kc ps st, (useK (fueledOpsM mode) env ctx fuel L kc ps st).val F
        = useK (fueledOps mode F) env ctx fuel L kc ps st) ∧
      (∀ kc st, (nodeK (fueledOpsM mode) env ctx fuel kc st).val F
        = nodeK (fueledOps mode F) env ctx fuel kc st)
  | 0 => ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | fuel + 1 => by
    obtain ⟨ih, ihs, ihu, ihn⟩ := posK_datF env ctx F fuel
    refine ⟨fun L dep kb e st => ?_, fun L skip e st => ?_, fun L kc ps st => ?_,
      fun kc st => ?_⟩
    · unfold posK
      kdatF_tac [ih, contK_datF ihu]
    · unfold synK
      exact synKeysK_datF ihu ctx L skip _ st
    · unfold useK
      kdatF_tac [nestInstType_datF, ihn, matchK_datF, metK_datF ihu]
    · unfold nodeK
      kdatF_tac [nestGroupCtors_datF, nestLayoutK_datF, ctorsK_datF ih ihs, nestClassGroup_datF,
        frameNfsK_datF]

/-! ## The root -/

theorem nestMemberCtorK_datF (env : Env) (ctx : NestCtx) (nF : Nat) (crest : Expr)
    (st : NestStK) (F : Nat) :
    (nestMemberCtorK (fueledOpsM mode) env ctx nF crest st).val F
      = nestMemberCtorK (fueledOps mode F) env ctx nF crest st := by
  unfold nestMemberCtorK
  kdatF_tac [fieldsK_datF (posK_datF env ctx F (whnfWalkFuel crest)).1
    (posK_datF env ctx F (whnfWalkFuel crest)).2.1]

theorem nestMemberCtorsK_datF (env : Env) (ctx : NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestStK),
      (nestMemberCtorsK (fueledOpsM mode) env ctx holes cs st).val F
        = nestMemberCtorsK (fueledOps mode F) env ctx holes cs st
  | [], _ => rfl
  | c :: cs, st => by
    unfold nestMemberCtorsK
    kdatF_tac [nestMemberCtorK_datF, nestNoMemberConst_datF,
      nestMemberCtorsK_datF env ctx holes F cs]

theorem nestBlockCtorsGoK_datF (env : Env) (ctx : NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestStK),
      (nestBlockCtorsGoK (fueledOpsM mode) env ctx holes css st).val F
        = nestBlockCtorsGoK (fueledOps mode F) env ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    unfold nestBlockCtorsGoK
    kdatF_tac [nestMemberCtorsK_datF, nestBlockCtorsGoK_datF env ctx holes F css]

/-- **The key-named walk at a fuel.** -/
theorem nestBlockCtorsK_datF (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorss : List (List (ConstantVal × Nat))) (F : Nat) :
    (nestBlockCtorsK (fueledOpsM mode) env ctx holes ctorss).val F
      = nestBlockCtorsK (fueledOps mode F) env ctx holes ctorss := by
  unfold nestBlockCtorsK
  kdatF_tac [nestBlockCtorsGoK_datF]

theorem nestedBlockPositivityK_datF (env : Env) (ctx : NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) (F : Nat) :
    (nestedBlockPositivityK (fueledOpsM mode) env ctx ctorss).val F
      = nestedBlockPositivityK (fueledOps mode F) env ctx ctorss := by
  unfold nestedBlockPositivityK
  kdatF_tac [nestBlockCtorsK_datF]

/-- **The block's key-named positivity stage at a fuel** (S0.2): what
`checkBlockPositivity_datF` becomes at the switch. -/
theorem checkBlockPositivityK_datF (env₁ : Env) (find? : Name → Option ConstantInfo)
    (consts : List ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (checkBlockPositivityK (fueledOpsM mode) env₁ find? consts p cvTas ctorsAs).val F
      = checkBlockPositivityK (fueledOps mode F) env₁ find? consts p cvTas ctorsAs := by
  unfold checkBlockPositivityK
  simp only [atF_bind, atF_pure, atF_throw, atF_ite, unwrapOr_atF, nestBlockCtorsK_datF,
    checkAbsCtorTysAll_datF]

end ConLeche
