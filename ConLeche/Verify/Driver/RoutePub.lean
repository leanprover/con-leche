module

public import ConLeche.Verify.Driver.ComposeReads
public import ConLeche.Verify.Driver.RouteWorker
import ConLeche.Verify.Driver.Reach

/-!
# The routes: the public-import route

At a module `M` of a run (task #501), a read of `y` by a record of home `h` that passed by the
public-import route (`PubRoute`): the context's copy is of a module `M1` of `h`'s public-import
closure that exports `y`.  Then `M1` is a module of the run of smaller rank than `h`, loaded at
`h`, and `h`'s name index holds a copy of `y` at it (`pub_loaded`).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

namespace Run

variable {sp : SearchPath} {fs : FS} (R : Run sp fs)

/-- **The public-import route's module is loaded at the reader**, of smaller rank, with a copy of
the name in the reader's name index. -/
theorem pub_loaded {M : Name} (hM : M ∈ R.names) {h y : Name} (hh : h ∈ R.names) {s₁ : Spot}
    (hpub : PubRoute sp fs (R.envOf M) h y s₁) (hne : s₁.part.mod ≠ h) :
    s₁.part.mod ∈ R.names ∧ R.rk s₁.part.mod < R.rk h ∧
      ∃ cp q, (R.w h).reads.index.at cp = some q ∧ q.name = y ∧
        (R.w h).reads.loads.nameAt cp.mod = s₁.part.mod := by
  sorry

end Run

end ConLeche.Driver.Compose
