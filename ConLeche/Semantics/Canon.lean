module

public import ConLeche.Semantics.Tower.TowerLeaf
public import ConLeche.Verify.Denote

@[expose] public section

/-!
# The annotated literal spines

The annotated `Nat`-literal and character-list spines (`natLitAV`,
`charListAV`) and their erasure laws: each erases pointwise onto its
`Term` spine (`natLitT`, `charListT`), as `projAV` does onto `projNV`.
(The canonical annotation pass `denoteAnnot` that first used them is
retired — lane DMASTER; `denoteMeta` is the reading in force.)
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level inferTypeCore whnf
  natLitSupported strLitSupported)

/-- The annotated `Nat`-literal spine (the `natLitT` mirror over the
annotated valuation). -/
def natLitAV (za sa : AnnotTerm) : Nat → AnnotTerm
  | 0 => za
  | n + 1 => .app sa (natLitAV za sa n)

/-- The annotated character-list spine (the `charListT` mirror). -/
def charListAV (nilA consA ofNatA za sa : AnnotTerm) :
    List Char → AnnotTerm
  | [] => nilA
  | c :: cs =>
    .app (.app consA (.app ofNatA (natLitAV za sa c.toNat)))
      (charListAV nilA consA ofNatA za sa cs)

/-- The uniform projection spellings erase onto each other:
`projAV`'s image is `projNV` (task #175 wiring W3). -/
theorem erase_projAV : ∀ (i : Nat) (ea : AnnotTerm),
    (projAV i ea).erase = ConLeche.Verify.projNV i ea.erase
  | 0, _ => rfl
  | i + 1, ea => erase_projAV i (.snd ea)

/-! ## The erasure laws -/

/-- The literal spines erase pointwise. -/
theorem natLitAV_erase {za sa : AnnotTerm} {zv sv : Term}
    (hz : za.erase = zv) (hs : sa.erase = sv) :
    ∀ n : Nat, (natLitAV za sa n).erase = natLitT zv sv n := by
  intro n
  induction n with
  | zero => exact hz
  | succ m ih => simp [natLitAV, natLitT, hs, ih]

theorem charListAV_erase {nilA consA ofNatA za sa : AnnotTerm}
    {nilV consV ofNatV zv sv : Term}
    (h1 : nilA.erase = nilV) (h2 : consA.erase = consV)
    (h3 : ofNatA.erase = ofNatV) (hz : za.erase = zv)
    (hs : sa.erase = sv) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).erase
        = charListT nilV consV ofNatV zv sv cs := by
  intro cs
  induction cs with
  | nil => exact h1
  | cons c cs ih =>
    simp [charListAV, charListT, h2, h3, ih, natLitAV_erase hz hs]

end ConLeche.Semantics
