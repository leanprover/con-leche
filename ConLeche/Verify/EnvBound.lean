module

public import ConLeche.Kernel.DeclCheck

public section

/-!
# The index answers as the environment

`FEnv` (`ConLeche/Kernel/FEnv.lean`) keeps a name index and a table map beside the environment; for
`mkFEnv` they answer as `Env.find?` and `Env.findTable?` do (`mkFEnv_find?`, `mkFEnv_findTable?`), and
the guard twins that read through them as the `Env` guards do.

Spec-side only: nothing here is called by the checker.
-/

namespace ConLeche

/-- Name uniqueness of an environment's constants: what the fold keeps
(`ConLeche/Verify/Cached/PushChain.lean`), so that a stream's first entry of a name is its only one. -/
@[expose] def NodupNames (env : Env) : Prop := (env.consts.map (·.name)).Nodup

/-- The empty base layer answers nothing. -/
@[simp] theorem FBase.find?_empty (n : Name) : ({} : FBase).find? n = none := by
  simp [FBase.find?]

/-- `mkFEnv` has the empty base layer. -/
@[simp] theorem mkFEnv_base (env : Env) : (mkFEnv env).base = {} := rfl

/-- The index's specification: `List.find?` (the build inserts from the back, so the newest constant
of a name wins). -/
theorem mkIdxGo_getElem? (n : Name) : ∀ l : List ConstantInfo,
    (mkIdxGo l)[n]? = l.find? (·.name == n)
  | [] => by simp [mkIdxGo]
  | ci :: cs => by
    show ((mkIdxGo cs).insert ci.name ci)[n]? = _
    rw [Std.HashMap.getElem?_insert, List.find?_cons, mkIdxGo_getElem? n cs]
    by_cases hn : ci.name == n <;> simp [hn]

/-- The per-entry-call name index computes `Env.find?`. -/
theorem mkFEnv_find? (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n := by
  show (match (mkIdxGo env.consts)[n]? with
        | some ci => some ci
        | none => ({} : FBase).find? n) = _
  rw [mkIdxGo_getElem?, FBase.find?_empty, Env.find?]
  cases env.consts.find? (·.name == n) <;> rfl

/-! ## The table map agrees with `Env.findTable?` -/

/-- The table map's specification: `List.find?` (the build inserts from
the back, so the newest table of a name wins). -/
theorem mkTblsGo_getElem? (T : Name) : ∀ ts : List ProjTable,
    (mkTblsGo ts)[T]? = ts.find? (·.structName == T)
  | [] => by simp [mkTblsGo]
  | t :: ts => by
    show ((mkTblsGo ts).insert t.structName t)[T]? = _
    rw [Std.HashMap.getElem?_insert, List.find?_cons, mkTblsGo_getElem? T ts]
    by_cases hT : t.structName == T <;> simp [hT]

/-- The empty base layer has no tables. -/
@[simp] theorem FBase.findTable?_empty (T : Name) : ({} : FBase).findTable? T = none := by
  simp [FBase.findTable?]

/-- The raw table lookup of `mkFEnv` is the table component's. -/
theorem mkFEnv_rawTable? (env : Env) (T : Name) :
    (mkFEnv env).rawTable? T = env.tables.find? (·.structName == T) := by
  show (match (mkTblsGo env.tables)[T]? with
    | some t => some t
    | none => ({} : FBase).findTable? T) = _
  rw [mkTblsGo_getElem?, FBase.findTable?_empty]
  cases env.tables.find? (·.structName == T) <;> rfl

/-- **The index's table lookup is the environment's** (both gate on the
structure's constant). -/
theorem mkFEnv_findTable? (env : Env) (T : Name) :
    (mkFEnv env).findTable? T = env.findTable? T := by
  unfold FEnv.findTable? Env.findTable?
  rw [mkFEnv_find?, mkFEnv_rawTable?]

/-- The indexed projection lookup computes `Env.findProj?`. -/
theorem mkFEnv_findProj? (env : Env) (T : Name) (i : Nat) :
    (mkFEnv env).findProj? T i = env.findProj? T i := by
  rw [FEnv.findProj?, Env.findProj?, mkFEnv_findTable?]
  cases env.findTable? T <;> rfl

/-! ## Guard twins agree with the `Env` versions -/

theorem natLitSupportedF_eq (env : Env) :
    natLitSupportedF (mkFEnv env) = natLitSupported env := by
  simp only [natLitSupportedF, natLitSupported, mkFEnv_find?]

theorem natLitStoredF_eq (env : Env) :
    natLitStoredF (mkFEnv env) = natLitStored env := by
  simp only [natLitStoredF, natLitStored, mkFEnv_find?]

theorem strLitStoredF_eq (env : Env) :
    strLitStoredF (mkFEnv env) = strLitStored env := by
  simp only [strLitStoredF, strLitStored, mkFEnv_find?, natLitStoredF_eq]

theorem natOpGuardF_eq (env : Env) (c : Name) :
    natOpGuardF (mkFEnv env) c = natOpGuard env c := by
  simp only [natOpGuardF, natOpGuard, mkFEnv_find?, natLitSupportedF_eq]
  rfl

end ConLeche
