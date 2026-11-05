module

public import ConLeche.Verify.Cached.GenRecC

public section

/-!
# A block's install, at its checks

`blockConstants` and `blockTables` read a block's install off the group alone.  Once the block's
checks pass, that reading is what the checks were about: the formers and the constructors are the
ones in the environment the checks ran at, and each recursor is the generated one with the stream's
type and right-hand sides, its rules firing as the generated ones do (`blockInstall_of_checks`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Moving a major's parameters to the rule prefix -/

/-- Instantiating the lowest variable above a lift's cutoff undoes one step of the lift. -/
theorem Expr.liftLooseBVars_succ_instantiate1 {v : Expr} :
    ∀ {e : Expr} {k c : Nat}, (e.liftLooseBVars (k + 1) c).instantiate1 v c = e.liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c
    simp only [Expr.liftLooseBVars]
    split
    · next h =>
      simp only [Expr.instantiate1]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 1
    · next h =>
      simp only [Expr.instantiate1]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | _ => intro k c; simp_all [Expr.liftLooseBVars, Expr.instantiate1]

theorem Expr.liftLooseBVars_amount_zero : ∀ (e : Expr) (c : Nat), e.liftLooseBVars 0 c = e := by
  intro e
  induction e with
  | bvar i =>
    intro c
    simp only [Expr.liftLooseBVars]
    split <;> simp
  | _ => intro c; simp_all [Expr.liftLooseBVars]

theorem Expr.dropVars_lift (e : Expr) : ∀ n, Expr.dropVars n (e.liftLooseBVars n 0) = e
  | 0 => Expr.liftLooseBVars_amount_zero e 0
  | n + 1 => by
    show Expr.dropVars n ((e.liftLooseBVars (n + 1) 0).instantiate1 (.sort .zero)) = e
    rw [show (e.liftLooseBVars (n + 1) 0).instantiate1 (.sort .zero)
        = e.liftLooseBVars n 0 from Expr.liftLooseBVars_succ_instantiate1]
    exact Expr.dropVars_lift e n

/-- **An outside major's firing data, read off the record**: what `streamNestedOk` found in the
major's domain is what `recFire` reads there. -/
theorem recFire_nested {p : BlockShape} {rc : RecShape} {lvls : List Level} {pins : List Expr}
    (ht : ¬ rc.tgt < p.k) (h : streamNestedOk rc.cvR.type rc.mI rc.rP (.nested lvls pins) = true) :
    recFire p rc = .nested lvls pins := by
  obtain ⟨pre, dom, body, D, hs, hfn, hargs⟩ := streamNestedOk_read h
  unfold recFire
  rw [ite_eq_right ht, hs]
  simp only [hfn, hargs]
  congr 1
  have hlen : (pins.map (Expr.liftLooseBVars (rc.mI - rc.rP) 0) ++
      (List.range (rc.mI - rc.rP)).map (fun i => Expr.bvar (rc.mI - rc.rP - 1 - i))).length
        - (rc.mI - rc.rP) = (pins.map (Expr.liftLooseBVars (rc.mI - rc.rP) 0)).length := by
    simp
  rw [hlen, List.take_left, List.map_map]
  conv => rhs; rw [← List.map_id pins]
  exact List.map_congr_left fun e _ => Expr.dropVars_lift e _

/-! ## One recursor -/

/-- The rules' shape checked: the generated rules at the stream's right-hand sides are the stream's
rules, firing `.plain`. -/
theorem sumRules_of_shape {rec : Name} :
    ∀ {rs : List RecRule} {cs : List (ConstantVal × Nat)},
      streamRulesShape (m := CheckM) rec rs cs = .ok () →
      sumRules cs (rs.map (·.rhs)) = rs.map ({ · with fire := .plain })
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [streamRulesShape, throw, throwThe, MonadExceptOf.throw] at h
  | _ :: _, [], h => by simp [streamRulesShape, throw, throwThe, MonadExceptOf.throw] at h
  | r :: rs, c :: cs, h => by
    unfold streamRulesShape at h
    dsimp only at h
    by_cases hc : (r.ctor == c.1.name && r.nfields == c.2) = true
    · rw [ite_eq_left hc] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [List.map_cons, sumRules, sumRules_of_shape h, ← hc.1, ← hc.2]
    · rw [ite_eq_right hc] at h
      exact nomatch h

/-- **What the checks say of one recursor**: the stream's record, firing as `recFire` reads, is the
generated recursor with the stream's type and right-hand sides. -/
structure RecAgrees (p : BlockShape) (rc : RecShape) (o : ConstantVal × TargetMajor × List Expr) :
    Prop where
  cv : o.1 = { rc.cvR with type := o.1.type }
  tgt : rc.tgt = o.2.1.member.getD p.k
  lt : ∀ m, o.2.1.member = some m → m < p.k
  isK : rc.isK = recKExpected p o.2.1
  shape : streamRulesShape (m := CheckM) rc.cvR.name rc.rules o.2.1.ctors = .ok ()
  nested : streamNestedOk rc.cvR.type rc.mI rc.rP (generatedFire o.2.1 rc.rP) = true

theorem RecAgrees.rules {p : BlockShape} {rc : RecShape} {o : ConstantVal × TargetMajor × List Expr}
    (h : RecAgrees p rc o) :
    rc.rules.map ({ · with fire := recFire p rc })
      = generatedRules rc.rP o.2.1 (rc.rules.map (·.rhs)) := by
  unfold generatedRules
  rw [sumRules_of_shape h.shape]
  have hn := h.nested
  have ht := h.tgt
  have hl := h.lt
  cases hm : o.2.1.member with
  | none =>
    rw [hm] at ht
    simp only [generatedFire, hm] at hn
    have hf : recFire p rc = auxRuleFire o.2.1 rc.rP :=
      recFire_nested (by simp [ht]) hn
    simp only [List.map_map, Function.comp_def, hf]
  | some m =>
    rw [hm] at ht
    have hf : recFire p rc = .plain := by
      unfold recFire
      rw [ite_eq_left (by rw [ht]; exact hl m hm)]
    rw [hf]

/-- Each recursor of a list, as the checks say. -/
theorem blockRecs_eq_infos (p : BlockShape) :
    ∀ (rs : List RecShape) (os : List (ConstantVal × TargetMajor × List Expr)) (m : Nat),
      rs.length = os.length →
      (∀ i rc o, rs[i]? = some rc → os[i]? = some o →
        p.recs[m + i]? = some rc ∧ RecAgrees p rc o) →
      blockRecs p rs = blockRecInfosTF p m (streamRecs rs os)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | rc :: rs, o :: os, m, hlen, hall => by
    obtain ⟨hrc, hA⟩ := hall 0 rc o rfl rfl
    have hrest := blockRecs_eq_infos p rs os (m + 1) (by simpa using hlen) fun i rc' o' h₁ h₂ => by
      have := hall (i + 1) rc' o' (by simpa using h₁) (by simpa using h₂)
      rwa [show m + (i + 1) = m + 1 + i by omega] at this
    have hgd : p.recs.getD m default = rc := by
      rw [List.getD_eq_getElem?_getD, show p.recs[m]? = some rc from hrc, Option.getD_some]
    have hcv : { o.1 with type := rc.cvR.type } = rc.cvR := by
      rw [hA.cv]
    show ConstantInfo.recInfo _ _ _ _ _ :: blockRecs p rs =
      ConstantInfo.recInfo { o.1 with type := rc.cvR.type } (p.majorIdxAt m) (p.rulePrefixAt m)
        (recKExpected p o.2.1) (generatedRules (p.rulePrefixAt m) o.2.1 (rc.rules.map (·.rhs))) ::
        blockRecInfosTF p (m + 1) (streamRecs rs os)
    rw [hrest, hcv, BlockShape.majorIdxAt, BlockShape.rulePrefixAt, hgd, ← hA.isK, ← hA.rules]

/-! ## The stage's runs -/

theorem streamKCheck_inv {p : BlockShape} :
    ∀ {recs : List RecShape} {out : List (ConstantVal × TargetMajor × List Expr)},
      streamKCheck (m := CheckM) p recs out = .ok () →
      ∀ (i : Nat) (rc : RecShape) (o : ConstantVal × TargetMajor × List Expr),
        recs[i]? = some rc → out[i]? = some o → rc.isK = recKExpected p o.2.1
  | [], _, _, i, rc, o, h, _ => by simp at h
  | _ :: _, [], _, i, rc, o, _, h => by simp at h
  | rc :: rcs, g :: gs, h, i, rc', o, h₁, h₂ => by
    unfold streamKCheck at h
    dsimp only at h
    by_cases hc : (rc.isK == recKExpected p g.2.1) = true
    · rw [ite_eq_left hc] at h
      cases i with
      | zero =>
        obtain rfl : rc = rc' := by simpa using h₁
        obtain rfl : g = o := by simpa using h₂
        exact beq_iff_eq.mp hc
      | succ i => exact streamKCheck_inv h i rc' o (by simpa using h₁) (by simpa using h₂)
    · rw [ite_eq_right hc] at h
      exact nomatch h

/-- The generated stage ties each output to its record: the record's target is the class's member,
and a class's member is a member of the block. -/
theorem genRecCheck_outMajor {fe₁ fe : FEnv} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (hcls : checkBlockClasses (fueledOps mode F) fe₁ p params ctorsAs = .ok (rd, Ms₀))
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms₀ cvTas block
      = .ok out)
    {i : Nat} {rc : RecShape} {o : ConstantVal × TargetMajor × List Expr}
    (hrc : p.recs[i]? = some rc) (ho : out[i]? = some o) :
    rc.tgt = o.2.1.member.getD p.k ∧ ∀ m, o.2.1.member = some m → m < p.k := by
  obtain ⟨R⟩ := genRecCheck_run h
  obtain ⟨C⟩ := checkBlockClasses_run hcls
  obtain ⟨-, hallG⟩ := classRecTysOk_run R.hcvGs
  obtain ⟨-, hallO⟩ := classRecsRulesOk_run R.hrules
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i rc hrc
  obtain ⟨rhss, hoi, -⟩ := hallO i cvG c hG hc
  rw [ho] at hoi
  obtain rfl := Option.some.inj hoi
  refine ⟨T.htgt, fun m hm => ?_⟩
  simp only at hm
  show m < p.members.length
  -- the class is a checked major: a member at its index
  have hMs : (genRecGen p params R.Ms R.formerTysC rd R.ctors R.pre).cls = R.Ms := rfl
  rw [hMs] at hm
  obtain ⟨hlenN, hallN⟩ := classesNfs_run R.hMs
  obtain ⟨hlenK, hallK⟩ := classMajors_run C.hMs
  have hclt : c < R.Ms.length := by
    refine Nat.lt_of_not_le fun hge => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hm
    exact nomatch hm
  have hc₀ : c < Ms₀.length := by omega
  obtain ⟨nfs, hN, -⟩ := hallN c Ms₀[c] (List.getElem?_eq_getElem hc₀)
  rw [List.getD_eq_getElem?_getD, hN, Option.getD_some] at hm
  have hk : c < C.keys.length := by omega
  obtain ⟨M, hM, ⟨major⟩⟩ := hallK c C.keys[c] (List.getElem?_eq_getElem hk)
  obtain rfl : M = Ms₀[c] := Option.some.inj (hM.symm.trans (List.getElem?_eq_getElem hc₀))
  obtain ⟨major, -⟩ := major
  have hm' : (Ms₀[c]).member = some m := hm
  revert hm'
  generalize Ms₀[c] = M at major
  intro hm'
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar nfs =>
    obtain rfl : t = m := Option.some.inj hm'
    exact (List.getElem?_eq_some_iff.mp hms).1
  | outside => exact nomatch hm'

/-! ## The block -/

theorem checkSumCtors_declared {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat}
    {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (h : checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvTa cs = .ok (ctorsA, sortss)) : ctorsA = cs := by
  obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv h
  refine List.ext_getElem hlen fun j h₁ h₂ => ?_
  obtain ⟨hn, sorts, -, hrun⟩ := hall j cs[j] ctorsA[j] (List.getElem?_eq_getElem h₂)
    (List.getElem?_eq_getElem h₁)
  exact Prod.ext (checkSumCtor_shape hrun).1.1 hn

/-- The checked constructors are the declared ones. -/
theorem checkBlockCtors_declared {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss)) :
    ctorsAs = l.map (·.1.ctors) := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  refine List.ext_getElem (by simpa using hlen) fun i h₁ h₂ => ?_
  have hil : i < l.length := by simpa using h₂
  obtain ⟨ctorsA, sortss, hA, -, hrun⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl : ctorsA = ctorsAs[i] := Option.some.inj (hA.symm.trans (List.getElem?_eq_getElem h₁))
  simpa using checkSumCtors_declared hrun

theorem consBlockInds_consts' (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvs : List ConstantVal) (i : Nat) (env : Env),
      consBlockInds p₁ isRec cvs i env =
        ⟨((cvs.zipIdx i).map fun x => ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)).reverse
          ++ env.consts, env.tables⟩
  | [], _, _ => rfl
  | cv :: cvs, i, env => by
    show consBlockInds p₁ isRec cvs (i + 1) ⟨_ :: env.consts, env.tables⟩ = _
    rw [consBlockInds_consts' p₁ isRec cvs (i + 1)]
    simp [List.zipIdx_cons]

theorem consSumCtors_eq (nP : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (env : Env),
      consSumCtors nP cs env =
        ⟨(cs.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ env.consts, env.tables⟩
  | [], _ => rfl
  | c :: cs, env => by
    show consSumCtors nP cs ⟨_ :: env.consts, env.tables⟩ = _
    rw [consSumCtors_eq nP cs]
    simp

theorem consBlockCtors_eq (nP : Nat) :
    ∀ (L : List (List (ConstantVal × Nat))) (env : Env),
      consBlockCtors nP L env =
        ⟨(L.flatten.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse ++ env.consts, env.tables⟩
  | [], _ => rfl
  | l :: L, env => by
    show consBlockCtors nP L (consSumCtors nP l env) = _
    rw [consBlockCtors_eq nP L, consSumCtors_eq]
    simp

theorem consBlockRecsT_eq_infos (q : BlockShape) :
    ∀ (out : List (ConstantVal × TargetMajor × List Expr)) (m : Nat) (env : Env),
      consBlockRecsT q m out env =
        ⟨(blockRecInfosTF q m out).reverse ++ env.consts, env.tables⟩
  | [], _, _ => rfl
  | (cv, M, rhss) :: rest, m, env => by
    show consBlockRecsT q (m + 1) rest ⟨_ :: env.consts, env.tables⟩ = _
    rw [consBlockRecsT_eq_infos q rest (m + 1)]
    simp [blockRecInfosTF]

/-- **A block's install, at its checks.**  The environment with what the block reads as pushed is the
one holding the formers and constructors the checks ran at and the recursors the checks compared with
the generated ones, with the tables on top. -/
theorem blockInstall_of_checks {F : Nat} {env env₁ : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    {cvTas : List ConstantVal} {p₁ : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    {nestedBit : Bool} {out : List (ConstantVal × TargetMajor × List Expr)} (Q : List ProjTable)
    (hInd : checkBlockInds (fueledOps .verified F) env p₀ (blockRawRec p₀) = .ok (env₁, cvTas, p₁))
    (hCtors : checkBlockCtors (fueledOps .verified F) env₁ env₁ p₁ (p₀.members.zip cvTas)
      = .ok (ctorsAs, sortsss))
    (hcls : checkBlockClasses (fueledOps .verified F) (mkFEnv env₁) p₁ params ctorsAs = .ok (rd, Ms₀))
    (hRec : genRecCheck (ShadowOps.fueled .verified F) (mkFEnv (consBlockCtors p₁.nP ctorsAs env₁))
      p₁ nestedBit params tbl rd Ms₀ cvTas block = .ok out)
    (hK : streamKCheck (m := CheckM) p₁ p₁.recs out = .ok ())
    {w : StructWalkers} {fe : FEnv}
    (hS : streamRecsCheck (m := CheckM) (fueledOps .verified F) w fe p₁.recs out = .ok ()) :
    env.pushDelta (blockConstants p₀) Q =
      (consBlockRecsT p₁ 0 (streamRecs p₁.recs out) (consBlockCtors p₁.nP ctorsAs env₁)).pushDelta [] Q := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, -, hq, hcons, -⟩ := checkBlockInds_shape hInd
  obtain ⟨hcvT, hmem⟩ := checkBlockInds_members hInd
  subst hq
  have hlenZ : (p₀.members.zip cvTas).map (·.1) = p₀.members := by
    rw [hcvT]
    exact List.map_fst_zip (by simp)
  have hctors : ctorsAs = p₀.members.map (·.ctors) := by
    rw [checkBlockCtors_declared hCtors]
    conv => rhs; rw [← hlenZ]
    simp [List.map_map, Function.comp_def]
  obtain ⟨hlenR, hallS⟩ := streamRecsCheck_inv hS
  have hrecsP : (p₀.toBlockShape.withSort s0).recs = p₀.recs := rfl
  have hAg : ∀ i rc o, p₀.recs[i]? = some rc → out[i]? = some o →
      p₀.recs[0 + i]? = some rc ∧ RecAgrees (p₀.toBlockShape.withSort s0) rc o := by
    intro i rc o hrc ho
    refine ⟨by simpa using hrc, ?_⟩
    obtain ⟨hshape, hnested, -⟩ := streamRecCheck_inv (hallS i rc o hrc ho)
    obtain ⟨ht, hl⟩ := genRecCheck_outMajor hcls hRec hrc ho
    exact { cv := (Cached.genRecCheck_outCv hRec).2 i rc o hrc ho, tgt := ht, lt := hl,
            isK := streamKCheck_inv hK i rc o hrc ho, shape := hshape, nested := hnested }
  have hrecs : blockRecs p₀.toBlockShape p₀.recs =
      blockRecInfosTF (p₀.toBlockShape.withSort s0) 0 (streamRecs p₀.recs out) := by
    rw [blockRecs_congr (p := p₀.toBlockShape) (q := p₀.toBlockShape.withSort s0) rfl]
    exact blockRecs_eq_infos _ _ _ 0 hlenR hAg
  have hcaps : ∀ i, blockCapsAt (p₀.toBlockShape.withSort s0) i (blockRawRec p₀)
      = blockCapsAt p₀.toBlockShape i (blockRawRec p₀) := fun _ => rfl
  rw [hrecsP, consBlockRecsT_eq_infos, consBlockCtors_eq, hcons, consBlockInds_consts']
  unfold Env.pushDelta blockConstants blockFormers blockCtors
  rw [hrecs, hctors]
  simp [BlockShape.allCtors, hcaps]

end ConLeche
