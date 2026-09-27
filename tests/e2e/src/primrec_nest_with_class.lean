--#export T.rec T.rec_1 T.rec_2 Forge.rec0 Forge.rec1 Forge.rhs0 Forge.rhs1a Forge.rhs1c
/- PRIMREC/WFMEASURE: WALKFREE's (S) example, the good twin of
   `primrec_nest_missing_class` (which `scripts/mk_wfmeasure_fixtures.py`
   forges from this stream).  `W α | a : α → W α | c : List α → W α`,
   `T | mk : W T → T`: official's family {T, W T, List T} (its auxiliary
   closure contains the `List T` occurrence of `W.c` at `α := T`).
   Official 0, today 0, walk-free target 0 ((S) passes: `W.c`'s field
   `List z_T` is a CHILD call to the class `List T`).

   The `Forge.*` definitions are the forged family's recursor types
   (`rec0`, `rec1`: {T, W T} WITHOUT the `List T` class — `W.c`'s minor
   takes no ih) and its rules (`rhs*`, over `rec0`/`rec1`, which the
   forge renames to `T.rec`/`T.rec_1`); they are ordinary definitions
   (through official's recursors at a unit motive for `List T`), so this
   stream is accepted as it stands. -/
set_option genSizeOf false
set_option genInjectivity false
universe u
inductive W (α : Type) : Type where
  | a : α → W α
  | c : List α → W α
inductive T : Type where
  | mk : W T → T
noncomputable section
namespace Forge
def rec0 {motive_1 : T → Sort u} {motive_2 : W T → Sort u}
    (mk : (a : W T) → motive_2 a → motive_1 (T.mk a))
    (a : (a : T) → motive_1 a → motive_2 (W.a a))
    (c : (a : List T) → motive_2 (W.c a)) (t : T) : motive_1 t :=
  @T.rec motive_1 motive_2 (fun _ => PUnit) mk a (fun l _ => c l) PUnit.unit
    (fun _ _ _ _ => PUnit.unit) t
def rec1 {motive_1 : T → Sort u} {motive_2 : W T → Sort u}
    (mk : (a : W T) → motive_2 a → motive_1 (T.mk a))
    (a : (a : T) → motive_1 a → motive_2 (W.a a))
    (c : (a : List T) → motive_2 (W.c a)) (t : W T) : motive_2 t :=
  @T.rec_1 motive_1 motive_2 (fun _ => PUnit) mk a (fun l _ => c l) PUnit.unit
    (fun _ _ _ _ => PUnit.unit) t
def rhs0 := fun (motive_1 : T → Sort u) (motive_2 : W T → Sort u)
    (mk : (a : W T) → motive_2 a → motive_1 (T.mk a))
    (a : (a : T) → motive_1 a → motive_2 (W.a a))
    (c : (a : List T) → motive_2 (W.c a)) (x : W T) =>
  mk x (@rec1 motive_1 motive_2 mk a c x)
def rhs1a := fun (motive_1 : T → Sort u) (motive_2 : W T → Sort u)
    (mk : (a : W T) → motive_2 a → motive_1 (T.mk a))
    (a : (a : T) → motive_1 a → motive_2 (W.a a))
    (c : (a : List T) → motive_2 (W.c a)) (x : T) =>
  a x (@rec0 motive_1 motive_2 mk a c x)
def rhs1c := fun (motive_1 : T → Sort u) (motive_2 : W T → Sort u)
    (_mk : (a : W T) → motive_2 a → motive_1 (T.mk a))
    (_a : (a : T) → motive_1 a → motive_2 (W.a a))
    (c : (a : List T) → motive_2 (W.c a)) (x : List T) =>
  c x
end Forge
end
