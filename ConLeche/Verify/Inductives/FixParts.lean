module

public import ConLeche.Kernel.Inductives.NativeParts

public section

/-!
# The direct recursive recogniser, inverted (task #188)

`nativeShape?` is the sum route's core recogniser without the
one-constructor exclusion; `nativeParts?` adds the field kinds
(`nativeKinds?`, one list per constructor).  The inversions give
the pins the P tier consumes: the `isProp` datum, the recursor's level
parameters, the constructors' level parameters and the kinds'
placeholder.  What the recogniser pinned before task #220 and no longer
does — the recursor's NAME, its rule count and rule metadata, the
constructors' result shape — is checked at the install, where a
mismatch REJECTS (`checkNativeRec`, `checkSumCtor`); the facts
the P tier still needs come from those stages' own inversions
(`checkNativeRec_name`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A successful `mapM` in `Option` yields as many results. -/
theorem List.mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [List.mapM_option_length hbs]

end ConLeche
