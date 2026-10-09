--#export demo2
/- Task #333: the comparison the official kernel cannot make.  `Ω` is
the proof with no weak-head normal form from `omega_kloop.lean`
(impredicative `Prop`, `propext`, K-like `Eq.rec`).  Checking `demo2`
compares the declared type `Ω = ι` with the inferred `Ω = Ω`, hence
`Ω ≟ ι`, two proofs of `P`.  The official kernel head-normalizes both
sides before trying proof irrelevance (`is_def_eq_core`) and reports
"(kernel) deep recursion detected", so the declaration is exported with
the kernel check skipped (the elaborator accepts it).  con-leche runs
proof irrelevance on the unreduced pair first (task #333) and accepts:
a deliberate accept-superset of the official kernel. -/
def P : Prop := ∀ A : Prop, A → A

local notation "δ" => (fun z : P => z (P → P) (fun x => x) z)
local notation "Ω" =>
  (δ (fun (A : Prop) (a : A) =>
    @Eq.rec Prop (P → P)
      (fun (B : Prop) (_ : (P → P) = B) => B)
      δ A (propext (Iff.intro (fun _ => a) (fun _ x => x)))))
local notation "ι" => (fun (A : Prop) (a : A) => a)

set_option debug.skipKernelTC true in
theorem demo2 (h : Ω = Ω) : Ω = ι := h
