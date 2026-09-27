module

public import ConLeche.Verify.Inductives.PosDerivK

public section

/-!
# The shape of a derived key-named telescope (PRIMREC / NESTKN-M4)

`posDK_tele_shape`: a derived telescope of the key-named positivity derivation
(`PosDKH`) has one walked output per field and opens at its fields' variables
to its result — what the accessibility proof reads of a node's crest
(`posD_tele_open`'s shape part, for the key-named derivation).
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hk : UseHookK}

/-- **A derived telescope's shape**: one output per field, and the telescope
opens at its fields' variables to the derivation's result. -/
theorem posDK_tele_shape : ∀ {J : PosJK}, PosDKH ops env ctx hk J → match J with
    | .tele L _ nF j cur _ nds res =>
      nds.length = nF ∧ ∃ xs, openPisAtFvars nF cur (L.hi + j) = some (xs, res)
    | _ => True := by
  intro J h
  induction h with
  | teleNil => exact ⟨rfl, [], by simp [openPisAtFvars]⟩
  | @teleCons L met nF j a b bm k nd ks nds res _ _ _ _ _ ihb =>
    obtain ⟨hnl, xs, hop⟩ := ihb
    refine ⟨by simp [hnl], .fvar (L.hi + j) a :: xs, ?_⟩
    simp only [openPisAtFvars]
    rw [show L.hi + j + 1 = L.hi + (j + 1) by omega, hop]
  | _ => trivial

end ConLeche
