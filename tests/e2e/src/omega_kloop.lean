--#export demo
/- A proof term with no normal form: impredicative `Prop`, `propext` and
K-like `Eq.rec` reduction make `Ω` loop under weak-head reduction (the
K-like `Eq.rec` reduces to `δ`, which re-applies itself).  `demo` never
needs `Ω` reduced: the official kernel reduces `E` by β to `True.intro`
without touching the argument `f Ω ι`, and accepts.

The verified checker's β-redex argument certificate (`whnfAppI` in
`ConLeche/Cached/CoreC.lean`) compares the argument's type `Ω = Ω`
with the binder domain `Ω = ι`, hence `Ω ≟ ι`.  Before task #333 the
defeq body head-normalized `Ω` (cheap `whnfCore`, before proof
irrelevance, in the official `is_def_eq_core` order) and never
returned; it now runs proof irrelevance on the unreduced pair first and
accepts.  The official kernel loops too when it must compare `Ω` with
`ι` (`omega_demo2.lean`: "(kernel) deep recursion detected"); it just
never has to here.
-/
def P : Prop := ∀ A : Prop, A → A

local notation "δ" => (fun z : P => z (P → P) (fun x => x) z)
local notation "Ω" =>
  (δ (fun (A : Prop) (a : A) =>
    @Eq.rec Prop (P → P)
      (fun (B : Prop) (_ : (P → P) = B) => B)
      δ A (propext (Iff.intro (fun _ => a) (fun _ x => x)))))
local notation "ι" => (fun (A : Prop) (a : A) => a)
local notation "E" =>
  ((fun f : ∀ p q : P, p = q =>
    (fun _ : Ω = ι => True.intro) (f Ω ι))
    (fun p q : P => Eq.refl p))

theorem demo : E = True.intro := Eq.refl E
