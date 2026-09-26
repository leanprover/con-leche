module

public import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `ConLeche/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`ConLeche/Verify/Cached/BridgeCS4.lean`: the per-declaration bridge
(`checkDeclSharedF_bridge`).  The `.indDecl` dispatch
(`checkModeledOrNativeSF_run`) is in `ConLeche/Verify/Cached/TargetRecC.lean`,
beside the uniform route's k-ary run it dispatches to.

As in the interned original the *direct simple-structure* run has no
bridge here: `structsEnabled = false` makes the arm that would
call it unreachable and `structParts?_none` collapses it at one `rw`.

Against `BridgeSDecl` the systematic deletions of the tier carry
through: no arena, hence no `Ext` conjunct anywhere and no
`tierOffE`/tier-flag side condition; `ISOKF` becomes `CSOKF`, whose
`residue` needs no flag witness; the fresh state is `CSOK.empty` rather
than `ISOK.fresh`.  Every pure comparand is byte-identical to the
interned original's.

One piece the interned tier keeps in a *shared* file has to be
replicated here: `checkDeclSF_nonind` (`ConLeche/Verify/CheckerF.lean`)
is stated for `CheckIM`, because the `throw`/`ite` peels it uses are
monad-specific (`rfl` at a concrete `StateT`).  Its `CheckCM` twin —
`checkDeclSFC_nonind`, with the `_push` lemmas it consumes — is proved
below; the pure comparand (`checkDecl` at `sharedOpsC`) is the same
program.  These are the only additions: everything else in the file is
the transposition.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

theorem throwC_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckCM β) : ((throw e : CheckCM α) >>= f) = throw e := rfl


open ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## `CheckCM` peels (the `CheckIM` helpers of
`ConLeche/Verify/CheckerF.lean` at the cached monad) -/

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem installBasisDeclF_pushC (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckCM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindC,
    throwC_bind_eq] <;> rfl

theorem installBasisFoldF_pushC :
    ∀ (l : List ConstantInfo) (env : Env),
      (l.foldlM installBasisDeclF (mkFEnv env) : CheckCM FEnv)
        = l.foldlM installBasisDecl env >>= fun e => pure (mkFEnv e)
  | [], env => by
    simp only [List.foldlM_nil, pure_bind]
  | ci :: l, env => by
    rw [List.foldlM_cons, List.foldlM_cons, installBasisDeclF_pushC,
      bind_assoc, bind_assoc]
    refine bindC_congr fun e => ?_
    rw [pure_bind, installBasisFoldF_pushC l e]

/-! ### The direct simple-structure path's extending stages (task #175
W4c: the cached run bridge restored) -/

/-- The former's telescope stage through the index (task #195): the
whnf loop reads the index's environment, the re-check is the indexed
`checkConstantValF`. -/
theorem checkSumTeleF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkSumTeleF ops (mkFEnv env) cv n cvTa₀
      = checkSumTele ops env cv n cvTa₀ := by
  unfold checkSumTeleF checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none => simp only [checkConstantValF_eq, mkFEnv_env]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [checkConstantValF_eq, mkFEnv_env]

/-- The projection table through the index (task #175 S1). -/
theorem checkStructProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) :
    checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa (mkFEnv env)
      = checkStructProjTable (m := CheckCM) T C lps nP nF rs guards off cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkStructProjTableF checkStructProjTable
  simp only [StructWalkers.plain, constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkStructProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkStructProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok e₁ := by
    unfold checkStructProjTable at hstep ⊢
    cases hb : structProjBodies T nP nF cvCa.type with
    | none =>
      try rw [hb] at hstep
      exact absurd hstep throwC_bind_ok
    | some bodies =>
      try rw [hb] at hstep
      simp only [unwrapOr, pure_bind] at hstep ⊢
      split at hstep
      · next hg =>
        rw [if_pos hg]
        split at hstep
        · next hfam =>
          rw [if_pos hfam]
          split at hstep
          · next hn =>
            rw [if_pos hn]
            obtain ⟨hfe, rfl⟩ := pureC_ok hstep
            subst hfe
            exact ⟨rfl, rfl⟩
          · exact absurd hstep throwC_bind_ok
        · exact absurd hstep throwC_bind_ok
      · exact absurd hstep throwC_bind_ok
  obtain ⟨rfl, hpure⟩ := hrun
  refine ⟨hwf, rfl, direct_table_wf henv hpure, 0, ?_⟩
  rw [checkStructProjTable_datF]
  exact hpure

end ConLeche.Cached
