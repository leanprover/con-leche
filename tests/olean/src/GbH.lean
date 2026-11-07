module
-- Guards task #501: H reads GbG's S (its group, S.rec among its names), then GbG2's w, whose
-- value reads GbG2's S.rec.
import GbG
import GbG2
theorem hz : w = w → ∀ _ : S, True := fun _ _ => trivial
