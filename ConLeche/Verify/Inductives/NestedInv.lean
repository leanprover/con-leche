module

public import ConLeche.Verify.Inductives.MutualInv
public import ConLeche.Kernel.Inductives.NestedInstall

public section

/-!
# The nested install: inversion (task #279)

The shape of a successful run of `checkNested`
(`ConLeche/Kernel/Inductives/NestedInstall.lean`), read off the monad
exactly as `MutualInv.lean` reads the mutual install's: the two
syntactic front guards, the pure elimination and its mimic count, the
auxiliary block, the mutual install in the scratch environment, the
read-back, the restored constructors, recursor types and rules, the
projection tables, and the two post-checks — closing with the chain of
`∃`s that `ConLeche/Semantics/Inductives/DeclNested.lean` records as a
run and the model tier consumes.

Shape walks only: `exceptBind_ok` per bind, `rw [if_pos …]` per guard,
`close_throw` on the failing branches.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem nestThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact nestThrow_ne_ok (by assumption))
        | (exfalso; exact nestThrow_ne_ok h)
        | (simp at h))

/-- `nestedLift` succeeds only on an `.ok`. -/
theorem nestedLift_ok {α : Type} {r : Except CheckError α} {a : α}
    (h : (nestedLift (m := CheckM) r) = .ok a) : r = .ok a := by
  unfold nestedLift at h
  cases r with
  | ok b => cases h; rfl
  | error e => exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- **The whole nested chain**, as the install ran it. -/
theorem checkNested_inv {env envOut : Env} {p : NestedParts} {F : Nat}
    (h : checkNested (m := CheckM) (fueledOps mode F) env p = .ok envOut) :
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all
        (fun t => !t.mentionsNestedAux)) = true ∧
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true ∧
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
      (ctorsR : List (List (ConstantVal × Nat × Nat)))
      (cvRms cvRns : List ConstantVal)
      (rulesM rulesN : List (List RecRule))
      (a₀ : AuxStored) (fvsA : List Expr × Expr),
      -- the elimination, and the mimic count against the stream's records
      elimNested env p.nP p.lps
        (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
          (⟨cv.name, cv.type,
            (p.ctors.filter (fun c => c.member == mIdx)).map
              fun c => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st ∧
      st.pins.length = p.numNested ∧
      -- every MINTED name is free in the pre-block environment
      copiesFresh env p.k st = true ∧
      -- the auxiliary mutual block, checked in a SCRATCH environment
      auxBlock p st = some b ∧
      checkMutualCore (m := CheckM) (fueledOps mode F) env b none = .ok envAux ∧
      auxStoredAll envAux b b.k = some stored ∧
      -- `pinsOkAux`: the pins typed at the SCRATCH environment
      (stored.take p.k).head? = some a₀ ∧
      openPisAtFvars p.nP a₀.cvTa.type 0 = some fvsA ∧
      nestedPinsOk (m := CheckM) (fueledOps mode F) envAux p.nP fvsA.1 st.pins = .ok () ∧
      -- the restored constructors, at the environment holding the formers
      (stored.take p.k).mapM (fun a =>
          restoreCtors (m := CheckM) (fueledOps mode F)
            (consNestedFormers (stored.take p.k) env) (restoreTbl p st) p.lps a.ctors)
        = .ok ctorsR ∧
      -- the restored recursor types
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
          (stored.take p.k) = .ok cvRms ∧
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.numNested).map p.mimicRecName)
          (stored.drop p.k) = .ok cvRns ∧
      -- the restored rules, at the rule-less provision
      (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
        = .ok rulesM ∧
      (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
        = .ok rulesN ∧
      -- the projection tables, on the stored recursors
      nestedTables (m := CheckM)
          (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
            ((p.formers.getD mIdx default).1.name, a.tbl, cs))
          (storeNestedRecs
            ((cvRms.zip ((stored.take p.k).zip rulesM)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
              ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))) = .ok envOut ∧
      -- POST-CHECK (a): the same pins at the RESTORED environment
      nestedPinsOk (m := CheckM) (fueledOps mode F) envOut p.nP fvsA.1 st.pins = .ok () ∧
      -- POST-CHECK (c): the stream's records against the generated ones
      (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true ∧
      nestedRecsOk (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          p.nP b.k b.n
          ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
              (fun (((sr, cv), rs), mIdx) =>
                (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
            ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
              (fun (((sr, cv), rs), j) =>
                (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
        = .ok () := by
  unfold checkNested at h
  simp only at h
  by_cases hg₀ : (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true
  case neg => rw [if_neg hg₀] at h; close_throw
  rw [if_pos hg₀] at h
  try simp only [bind, Except.bind] at h
  by_cases hg₁ : uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true
  case neg => rw [if_neg hg₁] at h; close_throw
  rw [if_pos hg₁] at h
  refine ⟨hg₀, hg₁, ?_⟩
  try simp only [bind, Except.bind] at h
  obtain ⟨st, helim, h⟩ := exceptBind_ok h
  have helim' := nestedLift_ok helim
  try simp only at h
  by_cases hcnt : (st.pins.length == p.numNested) = true
  case neg => rw [if_neg hcnt] at h; close_throw
  rw [if_pos hcnt] at h
  try simp only [bind, Except.bind] at h
  by_cases hfresh : copiesFresh env p.k st = true
  case neg => rw [if_neg hfresh] at h; close_throw
  rw [if_pos hfresh] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  try simp only at h
  obtain ⟨envAux, haux, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨stored, hst, h⟩ := exceptBind_ok h
  have hst' := unwrapOr_ok hst
  try simp only at h
  obtain ⟨a₀, ha₀, h⟩ := exceptBind_ok h
  have ha₀' := unwrapOr_ok ha₀
  try simp only at h
  obtain ⟨fvsA, hfv, h⟩ := exceptBind_ok h
  have hfv' := unwrapOr_ok hfv
  try simp only at h
  obtain ⟨uA, hpinsAux, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨ctorsR, hctors, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRms, hrm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRns, hrn, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨rulesM, hrlm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨rulesN, hrln, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨env₄, htbl, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u₀, hpins, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hlen : (p.memberRecs.length == cvRms.length &&
      p.mimicRecs.length == cvRns.length) = true
  case neg => rw [if_neg hlen] at h; close_throw
  rw [if_pos hlen] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨u₁, hrecs, h⟩ := exceptBind_ok h
  have henv : env₄ = envOut := by
    simpa [pure, Except.pure] using h
  subst henv
  exact ⟨st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, a₀, fvsA,
    helim', beq_iff_eq.mp hcnt, hfresh, hb', haux, hst', ha₀', hfv',
    (by cases uA; exact hpinsAux), hctors, hrm, hrn, hrlm, hrln, htbl,
    (by cases u₀; exact hpins), hlen, by cases u₁; exact hrecs⟩

end ConLeche
