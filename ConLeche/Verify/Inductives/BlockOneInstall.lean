module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.Inductives.BlockOne

public section

/-!
# The uniform install at ONE member is the one-member install
(milestone M1)

The bridge the route's gate buys on the install side: at `k = 1` every
stage of `checkBlock` (`ConLeche/Kernel/Inductives/BlockInstall.lean`)
IS the corresponding stage of `checkNative`, at the one-member reading
of the record (`BlockParts.toNative`).  The equations are proved once,
in any monad whose `throw` short-circuits a `bind` (`ThrowBind`), and
instantiated at the monads the drivers run in.
-/

namespace ConLeche

/-! ## The positivity walk at one name -/

theorem memberIdxAt?_single (T : Name) (lvls : List Level) :
    ∀ f : Expr, memberIdxAt? [T] lvls f = if f == Expr.const T lvls then some 0 else none := by
  intro f
  cases f with
  | const n us =>
    simp only [memberIdxAt?, beq_iff_eq, Expr.const.injEq]
    by_cases hu : us = lvls
    · subst hu
      by_cases hn : n = T
      · subst hn; simp [List.findIdx?, List.findIdx?.go]
      · simp [List.findIdx?, List.findIdx?.go, hn, Ne.symm hn]
    · simp [hu]
  | _ => simp [memberIdxAt?]

private theorem toRec_ite {c : Bool} {a b : BlockFieldKind} :
    (if c = true then a else b).toRec = if c = true then a.toRec else b.toRec := by
  cases c <;> rfl

/-- At ONE name the target is always member 0. -/
theorem memberTgt_single (T : Name) (lps : List Name) (e : Expr) :
    memberTgt [T] lps e = 0 := by
  simp only [memberTgt, memberIdxAt?_single]
  split <;> rfl

/-- The block's family test at ONE name is the one-name test. -/
theorem blockFamOk_single (T : Name) (lps : List Name) (nP nIdx o : Nat) (e : Expr) :
    blockFamOk [T] lps nP [nIdx] o e = recFamOk T lps nP nIdx o e := by
  simp only [blockFamOk, recFamOk, memberTgt_single, Expr.mentionsAnyConst_single]
  rfl

/-- The walk's tail (every head but a `∀`), at ONE name: the two
bodies are the same if-chain, so the kinds' targets are the only
difference. -/
private theorem blockPositivity_tail (T : Name) (lps : List Name) (nP nIdx o k : Nat)
    (e : Expr) :
    (if !e.mentionsAnyConst [T] then BlockFieldKind.ordinary
     else if e.getAppFn ==
         Expr.const ([T].getD (memberTgt [T] lps e) default) (lps.map .param) then
       (if e.getAppArgs.length == nP + [nIdx].getD (memberTgt [T] lps e) 0 &&
           e.getAppArgs.take nP == structPsAt (o + k) nP then
         (if blockFamOk [T] lps nP [nIdx] (o + k) e then
           (if k == 0 then .recursive (memberTgt [T] lps e)
            else .reflexive (memberTgt [T] lps e))
          else .negative)
        else .negative)
     else
       match e.getAppFn with
       | .const T' _ => if ([T] : List Name).contains T' then .negative else .unsupported
       | _ => .unsupported).toRec
    = (if !e.mentionsConst T then RecFieldKind.ordinary
       else if e.getAppFn == Expr.const T (lps.map .param) then
         (if e.getAppArgs.length == nP + nIdx &&
             e.getAppArgs.take nP == structPsAt (o + k) nP then
           (if recFamOk T lps nP nIdx (o + k) e then
             (if k == 0 then .recursive else .reflexive)
            else .negative)
          else .negative)
       else
         match e.getAppFn with
         | .const T' _ => if T' == T then .negative else .unsupported
         | _ => .unsupported) := by
  simp only [Expr.mentionsAnyConst_single, memberTgt_single, blockFamOk_single,
    List.getD_cons_zero, List.contains_singleton]
  by_cases h1 : (!e.mentionsConst T) = true
  · simp only [h1, if_pos]; rfl
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : (e.getAppFn == Expr.const T (lps.map .param)) = true
    · simp only [h2, if_pos]
      by_cases h3 : (e.getAppArgs.length == nP + nIdx &&
          e.getAppArgs.take nP == structPsAt (o + k) nP) = true
      · simp only [h3, if_pos]
        by_cases h4 : recFamOk T lps nP nIdx (o + k) e = true
        · simp only [h4, if_pos]
          by_cases h5 : (k == 0) = true
          · simp only [h5, if_pos]; rfl
          · simp only [h5, Bool.false_eq_true, if_false]; rfl
        · simp only [h4, Bool.false_eq_true, if_false]; rfl
      · simp only [h3, Bool.false_eq_true, if_false]; rfl
    · simp only [h2, Bool.false_eq_true, if_false]
      split
      · rename_i T' us hc
        by_cases h6 : (T' == T) = true
        · simp only [h6, if_pos]; rfl
        · simp only [h6, Bool.false_eq_true, if_false]; rfl
      · rfl

/-- The block's positivity walk at ONE name is the one-name walk. -/
theorem blockPositivity_single (T : Name) (lps : List Name) (nP nIdx o : Nat) :
    ∀ (e : Expr) (k : Nat),
      (blockPositivity [T] lps nP [nIdx] o e k).toRec = recPositivity T lps nP nIdx o e k := by
  intro e
  induction e with
  | forallE ty body bi iht ihb =>
    intro k
    simp only [blockPositivity, recPositivity, Expr.mentionsAnyConst_single]
    split
    · rfl
    · exact ihb (k + 1)
  | bvar i | sort u | const n us | fvar i ty _ | lit l | app f a _ _
  | lam ty b bi _ _ | letE t v b _ _ _ | proj s i sub _ =>
    intro k
    exact blockPositivity_tail T lps nP nIdx o k _

/-- The kind of one field, at ONE name. -/
theorem blockFieldKind_single (T : Name) (lps : List Name) (nP nIdx o : Nat) (dom : Expr) :
    (blockFieldKind [T] lps nP [nIdx] o dom).toRec = recFieldKind T lps nP nIdx o dom := by
  simp only [blockFieldKind, recFieldKind, Expr.mentionsAnyConst_single]
  split
  · exact blockPositivity_single T lps nP nIdx o dom 0
  · rfl

/-- The `structUsedLater` guard commutes with forgetting the target. -/
private theorem kind_guard (T : Name) (lps : List Name) (nP nIdx i : Nat)
    (cty dom : Expr) :
    (match blockFieldKind [T] lps nP [nIdx] i dom with
     | .recursive t =>
       if structUsedLater cty nP i then BlockFieldKind.unsupported else BlockFieldKind.recursive t
     | .reflexive t =>
       if structUsedLater cty nP i then BlockFieldKind.unsupported else BlockFieldKind.reflexive t
     | k => k).toRec
      = (match recFieldKind T lps nP nIdx i dom with
         | .recursive =>
           if structUsedLater cty nP i then RecFieldKind.unsupported else RecFieldKind.recursive
         | .reflexive =>
           if structUsedLater cty nP i then RecFieldKind.unsupported else RecFieldKind.reflexive
         | k => k) := by
  have h := blockFieldKind_single T lps nP nIdx i dom
  cases hb : blockFieldKind [T] lps nP [nIdx] i dom with
  | ordinary =>
    rw [hb] at h; simp only [BlockFieldKind.toRec] at h; rw [← h]; rfl
  | negative =>
    rw [hb] at h; simp only [BlockFieldKind.toRec] at h; rw [← h]; rfl
  | unsupported =>
    rw [hb] at h; simp only [BlockFieldKind.toRec] at h; rw [← h]; rfl
  | recursive t =>
    rw [hb] at h; simp only [BlockFieldKind.toRec] at h; rw [← h]
    by_cases hu : structUsedLater cty nP i = true
    · simp only [hu, if_pos]; rfl
    · simp only [hu, Bool.false_eq_true, if_false]; rfl
  | reflexive t =>
    rw [hb] at h; simp only [BlockFieldKind.toRec] at h; rw [← h]
    by_cases hu : structUsedLater cty nP i = true
    · simp only [hu, if_pos]; rfl
    · simp only [hu, Bool.false_eq_true, if_false]; rfl

/-- The kinds of one constructor's fields, at ONE name, are the
one-name kinds. -/
theorem blockCtorKinds_single (T : Name) (lps : List Name) (nP nIdx : Nat)
    (c : ConstantVal × Nat) :
    (blockCtorKinds [T] lps nP [nIdx] c).map (List.map BlockFieldKind.toRec)
      = recCtorKinds T lps nP nIdx c := by
  simp only [blockCtorKinds, recCtorKinds]
  cases hs : Expr.stripPis (nP + c.2) c.1.type with
  | none => rfl
  | some z =>
  obtain ⟨cbs, cbody⟩ := z
  simp only [Expr.mentionsAnyConst_single]
  by_cases hall : ((cbody.getAppArgs.drop nP).all fun a => !a.mentionsConst T) = true
  · simp only [hall, if_pos, Option.map_some, List.map_map, Option.some.injEq]
    refine List.map_congr_left ?_
    intro i _
    exact kind_guard T lps nP nIdx i c.1.type (cbs.getD (nP + i) default).1
  · simp only [hall, Bool.false_eq_true, if_false, Option.map_some, List.map_map,
      Option.some.injEq]
    refine List.map_congr_left ?_
    intro i _
    rfl

/-! ## The install stages

The equations are proved once, in any monad whose `throw`
short-circuits a `bind`, and instantiated at the monads the drivers
run in. -/

/-- A monad in which a `throw` short-circuits a `bind` — every monad
the checker runs in (the pure `Except`, the fueled family, the cached
state monad). -/
class ThrowBindM (m : Type → Type) [Monad m] [MonadExceptOf CheckError m] : Prop where
  /-- a thrown error swallows the continuation -/
  throw_bind {α β : Type} (e : CheckError) (f : α → m β) : (throw e : m α) >>= f = throw e

instance : ThrowBindM CheckM where
  throw_bind _ _ := rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf CheckError m] [ThrowBindM m]

/-- The one-member former stage, as the k-ary member stage plus the
cons: `checkSumInd` IS `checkBlockTele` followed by the environment
extension. -/
theorem checkSumInd_tele (ops : CheckerOps m) (env : Env) (sh : InductiveShape)
    (capsOf : InductiveShape → IndCaps) (ms : MemberShape)
    (h1 : ms.cvT = sh.cvT) (h2 : ms.nIdx = sh.nIdx) :
    checkSumInd ops env sh capsOf
      = checkBlockTele ops env sh.nP ms >>= fun r =>
          pure (⟨.indInfo r.1 (capsOf (sh.withSort r.2)) :: env.consts⟩, r.1, sh.withSort r.2) := by
  simp only [checkSumInd, checkBlockTele, h1, h2, bind_assoc]
  refine bind_congr fun cvTa₀ => ?_
  refine bind_congr fun r => ?_
  refine bind_congr fun q => ?_
  split
  · simp only [pure_bind]
  · simp only [ThrowBindM.throw_bind]

/-! ### The record's readings at one member -/

theorem blockCapsAt_one {q : BlockShape} {ms : MemberShape} (hm : q.members = [ms])
    (isRec : Bool) : blockCapsAt q 0 isRec = nativeCapsAt q.toInductive isRec := by
  simp only [blockCapsAt, nativeCapsAt, BlockShape.toInductive, hm, List.getD_cons_zero,
    List.headD_cons, BlockShape.k, List.length_cons, List.length_nil]
  cases hc : ms.ctors with
  | nil => rfl
  | cons c cs => cases cs with
    | cons d ds => rfl
    | nil => simp

theorem blockIsRec_one (kss : List (List BlockFieldKind)) :
    blockIsRec [kss] = nativeIsRec (kss.map (List.map BlockFieldKind.toRec)) := by
  simp only [blockIsRec, nativeIsRec, List.any_cons, List.any_nil, Bool.or_false,
    List.any_map, Function.comp_def]
  refine congrArg _ ?_
  funext ks
  refine congrArg _ ?_
  funext k
  cases k <;> rfl

theorem blockRawRec_one {p : BlockParts} {ms : MemberShape} (hm : p.members = [ms]) :
    blockRawRec p = nativeRawRec p.toNative := by
  simp only [blockRawRec, nativeRawRec, BlockParts.toNative, BlockShape.toInductive,
    BlockShape.memberNames, hm, List.headD_cons, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, Bool.or_false]
  cases hc : ms.ctors with
  | nil => rfl
  | cons c cs => cases cs with
    | cons d ds => rfl
    | nil =>
      simp only [Expr.mentionsAnyConst_single]
      rfl

/-! ### The pass -/

theorem checkBlockInds_one (ops : CheckerOps m) (env : Env) {p : BlockParts}
    {ms : MemberShape} (hm : p.members = [ms]) (isRec : Bool) {β : Type}
    (k : Env × List ConstantVal × BlockShape → m β) :
    checkBlockInds ops env p isRec >>= k
      = checkSumInd ops env p.toNative.toInductiveShape (fun p₁ => nativeCapsAt p₁ isRec) >>=
          fun r => k (r.1, [r.2.1], p.toBlockShape.withSort r.2.2.resSort) := by
  symm
  rw [checkSumInd_tele ops env _ _ ms (by simp [BlockParts.toNative, BlockShape.toInductive, hm])
    (by simp [BlockParts.toNative, BlockShape.toInductive, hm])]
  simp only [checkBlockInds, hm, checkBlockTeles, checkBlockAgree, consBlockInds,
    bind_assoc, pure_bind, List.map_nil]
  refine bind_congr fun r => ?_
  rw [blockCapsAt_one (q := p.toBlockShape.withSort r.2) (by simpa using hm) isRec]
  rfl

omit [ThrowBindM m] in
theorem checkBlockCtors_one (ops : CheckerOps m) (env₀ env : Env) {q : BlockShape}
    {ms : MemberShape} (hm : q.members = [ms]) (cvTa : ConstantVal) {β : Type}
    (k : List (List (ConstantVal × Nat)) × List (List (List Level)) → m β) :
    checkBlockCtors ops env₀ env q [(ms, cvTa)] >>= k
      = checkSumCtors ops env₀ env ms.cvT.name q.toInductive.cvT.levelParams q.nP ms.nIdx
          q.resSort q.isProp q.large cvTa ms.ctors >>= fun r => k ([r.1], [r.2]) := by
  simp only [checkBlockCtors, bind_assoc, pure_bind, List.headD_cons,
    BlockShape.toInductive, hm, List.headD_cons, BlockShape.lps, List.head?_cons,
    Option.map_some, Option.getD_some]

theorem mapM_blockCtorKinds (T : Name) (lps : List Name) (nP nIdx : Nat) :
    ∀ cs : List (ConstantVal × Nat),
      cs.mapM (recCtorKinds T lps nP nIdx)
        = (cs.mapM (blockCtorKinds [T] lps nP [nIdx])).map
            (List.map (List.map BlockFieldKind.toRec))
  | [] => rfl
  | c :: cs => by
    simp only [List.mapM_cons, bind, Option.bind]
    rw [← blockCtorKinds_single T lps nP nIdx c]
    cases hb : blockCtorKinds [T] lps nP [nIdx] c with
    | none => simp
    | some ks =>
      simp only [Option.map_some]
      rw [mapM_blockCtorKinds T lps nP nIdx cs]
      cases hcs : cs.mapM (blockCtorKinds [T] lps nP [nIdx]) with
      | none => simp
      | some kss => simp [pure, Option.map]

private theorem any_toRec_eq' (kss : List (List BlockFieldKind))
    (f : BlockFieldKind → Bool) (g : RecFieldKind → Bool)
    (h : ∀ k, g k.toRec = f k) :
    (kss.map (List.map BlockFieldKind.toRec)).any (fun ks => ks.any g)
      = kss.any (fun ks => ks.any f) := by
  simp only [List.any_map, Function.comp_def, h]

theorem classifyMemberKinds_one (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) {β : Type} (k : List (List RecFieldKind) → m β) :
    classifyFixKinds (m := m) T lps nP nIdx ctorsA >>= k
      = classifyMemberKinds (m := m) [T] lps nP [nIdx] ctorsA >>=
          fun kss => k (kss.map (List.map BlockFieldKind.toRec)) := by
  simp only [classifyFixKinds, classifyMemberKinds,
    mapM_blockCtorKinds T lps nP nIdx ctorsA, bind_assoc]
  cases hb : ctorsA.mapM (blockCtorKinds [T] lps nP [nIdx]) with
  | none => simp only [Option.map_none, unwrapOr, ThrowBindM.throw_bind, bind, Option.bind]
  | some kss =>
    simp only [Option.map_some, unwrapOr, pure_bind, bind, Option.bind, pure]
    rw [any_toRec_eq' kss (· == .negative) (· == .negative) (by intro k; cases k <;> rfl),
      any_toRec_eq' kss (· == .unsupported) (· == .unsupported) (by intro k; cases k <;> rfl)]
    split
    · simp only [ThrowBindM.throw_bind]
    · split
      · simp only [ThrowBindM.throw_bind]
      · simp only [pure_bind]

/-- **The pass at ONE member is the one-member pass.** -/
theorem checkNativePass_one (ops : CheckerOps m) (env : Env) {p₀ : BlockParts}
    {ms : MemberShape} (hm : p₀.members = [ms]) (isRec : Bool) {β : Type}
    (k : NativePass Env × Bool → m β) :
    checkNativePass ops env p₀.toNative isRec >>= k
      = checkBlockPass ops env p₀ isRec >>= fun r =>
          k (⟨r.1.env₁, r.1.cvTas.headD default, r.1.p.toNative, r.1.ctorsAs.headD [],
            r.1.sortsss.headD []⟩, r.2) := by
  have h1 : ms.cvT = p₀.toNative.toInductiveShape.cvT := by
    simp [BlockParts.toNative, BlockShape.toInductive, hm]
  have h2 : ms.nIdx = p₀.toNative.toInductiveShape.nIdx := by
    simp [BlockParts.toNative, BlockShape.toInductive, hm]
  simp only [checkNativePass, checkBlockPass, checkBlockInds, hm, checkBlockTeles,
    checkBlockAgree, consBlockInds, bind_assoc, pure_bind, List.map_nil,
    checkSumInd_tele ops env _ _ ms h1 h2]
  refine bind_congr fun r => ?_
  obtain ⟨cvTa, s⟩ := r
  simp only [BlockParts.complete_members, BlockShape.withSort_members, hm,
    List.zip_cons_cons, List.zip_nil_right, bind_assoc, pure_bind,
    blockCapsAt_one (q := p₀.toBlockShape.withSort s) (by simpa using hm) isRec]
  rw [checkBlockCtors_one ops _ _ (q := (p₀.complete (p₀.toBlockShape.withSort s)).toBlockShape)
    (by simpa using hm) cvTa]
  simp only [classifyBlockKinds, bind_assoc, pure_bind,
    BlockParts.toNative, BlockShape.toInductive_withSort, InductiveShape.withSort,
    BlockShape.withSort_elim, BlockParts.withKinds_members, BlockParts.withKinds_nP,
    BlockParts.withKinds_elim, BlockParts.withKinds_resSort, BlockParts.withKinds_large,
    BlockParts.withKinds_isProp, BlockParts.withKinds_kinds, BlockParts.withKinds_recPinned,
    BlockParts.complete_kinds, BlockParts.complete_recPinned, BlockParts.complete_members,
    BlockParts.complete_nP, BlockParts.complete_elim, BlockParts.complete_resSort,
    BlockParts.complete_large, BlockParts.complete_isProp,
    NativeParts.complete_cvT, NativeParts.complete_nP, NativeParts.complete_nIdx,
    NativeParts.complete_resSort, NativeParts.complete_isProp, NativeParts.complete_large,
    NativeParts.complete_ctors, InductiveShape.withSort_cvT, InductiveShape.withSort_nP,
    InductiveShape.withSort_nIdx, InductiveShape.withSort_resSort,
    InductiveShape.withSort_isProp, InductiveShape.withSort_large,
    InductiveShape.withSort_ctors, BlockParts.complete_toBlockShape,
    BlockShape.toInductive, BlockShape.memberNames, BlockShape.nIdxs, BlockShape.lps,
    BlockShape.withSort_members, BlockShape.withSort_nP, BlockShape.withSort_resSort,
    BlockShape.withSort_isProp, BlockShape.withSort_large, hm, List.headD_cons,
    List.map_cons, List.map_nil, List.head?_cons, Option.map_some, Option.getD_some]
  refine bind_congr fun r => ?_
  rw [classifyMemberKinds_one (m := m) ms.cvT.name ms.cvT.levelParams p₀.nP ms.nIdx]
  refine bind_congr fun kss => ?_
  refine congrArg k ?_
  congr 1
  simp only [BlockShape.k, BlockParts.withKinds_members, BlockParts.complete_members,
    BlockShape.withSort_members, hm, List.length_cons, List.length_nil, Nat.zero_add,
    List.range_one,
    List.all_cons, List.all_nil, Bool.and_true, blockCaps,
    BlockParts.withKinds_kinds, blockIsRec_one,
    blockCapsAt_one (q := ((p₀.complete (p₀.withSort s)).withKinds [kss]).toBlockShape)
      (by simpa using hm),
    blockCapsAt_one (q := p₀.toBlockShape.withSort s) (by simpa using hm),
    nativeCaps, NativeParts.withKinds, NativeParts.complete, BlockParts.withKinds,
    BlockParts.complete, BlockShape.toInductive, List.headD_cons,
    BlockShape.withSort_nP, BlockShape.withSort_elim, BlockShape.withSort_resSort,
    BlockShape.withSort_large, BlockShape.withSort_isProp]

/-! ### The tail -/

private theorem getD_map_toRec (ks : List BlockFieldKind) (i : Nat) :
    (ks.map BlockFieldKind.toRec).getD i .ordinary = (ks.getD i .ordinary).toRec := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

private theorem nameAt_single (T : Name) (t : Nat) : nameAt [T] t = T := by
  cases t <;> simp [nameAt]

private theorem nIdxAt_single (n : Nat) (t : Nat) : nIdxAt [n] t = n := by
  cases t <;> simp [nIdxAt]

omit [LawfulMonad m] [ThrowBindM m] in
theorem blockOpenedOk_one (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List BlockFieldKind) :
    blockOpenedOk env₀ [T] lps nP [nIdx] cty nF ks
      = nativeOpenedOk env₀ T lps nP nIdx cty nF (ks.map BlockFieldKind.toRec) := by
  unfold blockOpenedOk nativeOpenedOk
  cases h1 : openPisAtFvars nP cty 0 with
  | none => rfl
  | some z =>
  obtain ⟨fvsP, crest⟩ := z
  dsimp only
  cases h2 : openPisAtFvars nF crest nP with
  | none => rfl
  | some w =>
  obtain ⟨xFvs, xrest⟩ := w
  dsimp only
  simp only [getD_map_toRec]
  refine congrArg (fun b => ((xrest.getAppArgs.drop nP).all
    (fun e => e.constsResolve env₀)) && b) ?_
  refine congrArg (List.all (List.range nF)) (funext fun i => ?_)
  cases hx : xFvs[i]? with
  | none => cases (ks.getD i BlockFieldKind.ordinary) <;> rfl
  | some x =>
    cases (ks.getD i BlockFieldKind.ordinary) with
    | ordinary => rfl
    | negative => rfl
    | unsupported => rfl
    | recursive t => simp only [BlockFieldKind.toRec, nameAt_single, nIdxAt_single]
    | reflexive t =>
      simp only [BlockFieldKind.toRec, nameAt_single, nIdxAt_single]
      cases openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) <;> rfl

omit [LawfulMonad m] [ThrowBindM m] in
theorem blockMemberFieldsOk_one (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kss : List (List BlockFieldKind)) :
    blockMemberFieldsOk env₀ [T] lps nP [nIdx] ctorsA kss
      = nativeFieldsOk env₀ T lps nP nIdx ctorsA (kss.map (List.map BlockFieldKind.toRec)) := by
  simp only [blockMemberFieldsOk, nativeFieldsOk, List.length_map, blockOpenedOk_one,
    List.getElem?_map]
  refine congrArg (fun b => (ctorsA.length == kss.length) && b) ?_
  refine congrArg (List.all (List.range ctorsA.length)) (funext fun j => ?_)
  cases ctorsA[j]? with
  | none => cases kss[j]? <;> rfl
  | some cA =>
    cases kss[j]? with
    | none => rfl
    | some ks => simp only [Option.map_some, List.length_map]

omit [LawfulMonad m] [ThrowBindM m] in
theorem blockFieldsOk_one (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kss : List (List BlockFieldKind)) :
    blockFieldsOk env₀ [T] lps nP [nIdx] [ctorsA] [kss]
      = nativeFieldsOk env₀ T lps nP nIdx ctorsA (kss.map (List.map BlockFieldKind.toRec)) := by
  simp only [blockFieldsOk, List.length_cons, List.length_nil, Nat.zero_add,
    List.range_one, List.all_cons, List.all_nil, Bool.and_true, List.getElem?_cons_zero,
    beq_self_eq_true, Bool.true_and, blockMemberFieldsOk_one]

end ConLeche
