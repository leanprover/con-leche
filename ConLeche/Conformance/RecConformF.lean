module

public import ConLeche.Kernel.Inductives.SumInstallF

@[expose] public section

/-!
# CONFORMANCE: the recursor conformance check, through the index

**Not needed for soundness** (see `ConLeche/Conformance/RecGen.lean`).
`checkBlockRecConform`'s stages (`ConLeche/Conformance/RecConform.lean`)
over an `FEnv`: the mirror the cached driver runs
(`checkBlockRecS`, `ConLeche/Cached/CheckerC.lean`).  That the mirror
computes what the plain check computes is proved in
`ConLeche/Verify/CheckerF.lean`, and the cached simulation of it in
`ConLeche/Verify/Cached/BlockRunC.lean`.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkNativeRules` through the index. -/
def checkNativeRulesF (w : StructWalkers) (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && w.resolve feR rhs &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRulesF w feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- `fe.push (.recInfo cv mI rP [])` — or, when `hint` carries exactly
that record, the environment `hint` already holds for it (lane LIN1).

The hint's contract is `feH = fe.push (.recInfo cv' mI' rP' [])`
(`FEnv.pushRecBare_eq`): it is how the conformance check reuses the
rule-less recursor environment the recursor stage built at the same
`fe`, instead of pushing the same record a second time — a push onto
an `fe` the caller still holds, i.e. a copy of the whole index. -/
def FEnv.pushRecBare (hint : Option (ConstantVal × Nat × Nat × FEnv)) (fe : FEnv)
    (cv : ConstantVal) (mI rP : Nat) : FEnv :=
  match hint with
  | some (cv', mI', rP', feH) =>
    if cv'.name == cv.name && cv'.levelParams == cv.levelParams && cv'.type == cv.type &&
        mI' == mI && rP' == rP then feH
    else fe.push (.recInfo cv mI rP [])
  | none => fe.push (.recInfo cv mI rP [])

theorem FEnv.pushRecBare_eq {hint : Option (ConstantVal × Nat × Nat × FEnv)} {fe : FEnv}
    (h : ∀ cv' mI' rP' feH, hint = some (cv', mI', rP', feH) →
      feH = fe.push (.recInfo cv' mI' rP' []))
    (cv : ConstantVal) (mI rP : Nat) :
    FEnv.pushRecBare hint fe cv mI rP = fe.push (.recInfo cv mI rP []) := by
  unfold FEnv.pushRecBare
  match hint, h with
  | none, _ => rfl
  | some (cv', mI', rP', feH), h =>
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨hn, hl⟩, ht⟩, hm⟩, hr⟩ := hc
      rw [h cv' mI' rP' feH rfl]
      obtain ⟨n, l, t⟩ := cv
      obtain ⟨n', l', t'⟩ := cv'
      dsimp only at hn hl ht
      subst hn hl ht hm hr
      rfl
    · rfl

/-- `checkNativeRec` through the index.  `hint` (`FEnv.pushRecBare`)
may carry a prebuilt rule-less recursor environment at `fe`; `none`
pushes. -/
def checkNativeRecF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    (hint : Option (ConstantVal × Nat × Nat × FEnv)) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- the recursor pin (task #220), as in `checkNativeRec`
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && w.resolve fe recTy &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := FEnv.pushRecBare hint fe cvRa p.majorIdx p.rulePrefix
  let rhss ← checkNativeRulesF w feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- A hint that honours its contract changes nothing. -/
theorem checkNativeRecF_hint (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    {hint : Option (ConstantVal × Nat × Nat × FEnv)}
    (hv : ∀ cv' mI' rP' feH, hint = some (cv', mI', rP', feH) →
      feH = fe.push (.recInfo cv' mI' rP' []))
    (p : NativeParts) (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    checkNativeRecF ops w fe hint p cvTa ctorsA = checkNativeRecF ops w fe none p cvTa ctorsA := by
  have e : ∀ cv mI rP, FEnv.pushRecBare hint fe cv mI rP = FEnv.pushRecBare none fe cv mI rP :=
    fun cv mI rP => (FEnv.pushRecBare_eq hv cv mI rP).trans rfl
  unfold checkNativeRecF
  simp only [e]

/-- `checkBlockRecConform` through the index: the unverified,
reject-only recursor CONFORMANCE check (the one-member
generate-and-compare, `checkNativeRecF`), at ONE member with ONE
recursor; SKIPPED at `k ≥ 2`, where the kernel has no generator.  The
cached driver runs it after the recursor stage's check
(`targetRecCheck` at `shadowOpsC`), through `thenConform`.  It lives here, beside the
generator it runs, rather than with the block mirrors
(`BlockInstallF.lean`): those do not import the one-member mirror. -/
def checkBlockRecConformF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    (hint : Option (ConstantVal × Nat × Nat × FEnv))
    (p : BlockParts) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) :
    m Unit :=
  match p.members, p.recs, cvTas, ctorsAs with
  | [ms], [_], [cvTa], [ctorsA] => do
    let kinds ← confKinds ms.cvT.name p.lps p.nP ms.nIdx ctorsA
    let pn := p.toNative kinds
    unless nativeRulesOk pn.cvR.name (pn.cvR.levelParams.map .param) .never pn.nP
        pn.ctors.length ctorsA pn.kinds pn.rhss pn.cvR.type do
      throw (.invalid "direct rec: recursor rules are not the generated ones")
    discard <| checkNativeRecF ops w fe hint pn cvTa ctorsA
  | _, _, _, _ => pure ()

end Mirrors

end ConLeche
