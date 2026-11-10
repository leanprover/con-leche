module

public import ConLeche.Modular
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# A record's constants, tables and names, as the driver computes them

The specification reads a record's constants and tables (`declConstants`, `declTables`, and
`Modular.declNames` and `streamEnv` over them) through the plain `blockIsRec`, `recFire` and
`blockTables`.  The worker's reach (`ConLeche/Driver/Reach.lean`, `Worker.lean`) asks for them at
every context record, so the compiled code runs the cached twins (`declConstantsC`,
`declTablesC`, `declNamesC`, `streamEnvC`; `declConstantsC_eq`, `declTablesC_eq`) in their
place.
-/

namespace ConLeche.Cached

open ConLeche

/-- **A record's constants are the cached twin's.** -/
@[csimp] theorem declConstants_eq_declConstantsC : @declConstants = @declConstantsC := by
  funext d
  exact (declConstantsC_eq d).symm

/-- **A record's tables are the cached twin's.** -/
@[csimp] theorem declTables_eq_declTablesC : @declTables = @declTablesC := by
  funext d
  exact (declTablesC_eq d).symm

/-- **The names a record installs are the cached twin's.** -/
@[csimp] theorem declNames_eq_declNamesC : @Modular.declNames = @declNamesC := by
  funext d
  simp only [Modular.declNames, declNamesC, declConstantsC_eq]

/-- **The environment of a list of records is the cached twin's.** -/
@[csimp] theorem streamEnv_eq_streamEnvC : @streamEnv = @streamEnvC := by
  funext ds env
  simp only [streamEnv, streamEnvC, declConstantsC_eq, declTablesC_eq]

end ConLeche.Cached
