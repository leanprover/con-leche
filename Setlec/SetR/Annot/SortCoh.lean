import Setlec.SetR.Annot.SortCoh.Claims
import Setlec.SetR.Annot.SortCoh.Mono
import Setlec.SetR.Annot.SortCoh.Discharge
import Setlec.SetR.Annot.SortCoh.CoreLock
import Setlec.SetR.Annot.SortCoh.LoopLock
import Setlec.SetR.Annot.SortCoh.Theta
import Setlec.SetR.Annot.SortCoh.SubstSim

/-!
# Run-level sort coherence — the umbrella (task #151 tier C)

The claim family, mono apparatus, discharge tiers, coreLock/loopLock
lockstep machinery, the Θ walk and the substitution simulation live
in the `SortCoh/` part-files (split 2026-08-30, pure motion; import
order is dependency order).  This module re-exports the family under
the historical name.
-/
