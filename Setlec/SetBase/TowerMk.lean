import Setlec.SetBase.TowerLeaf

/-!
# The constructor tupler (task #175, stage 3b)

`mkTowerGo w Fs` spells the tier's `mkTower` — the right-nested
`.psigmaMk [w, w]` application tower with the `.punitUnit` terminator
— **at the constructor λ-frame**: the field values are the frame's own
bound variables (`.bvar m`, `m` = the count of later fields), and the
pair type arguments are the field domains lifted to that frame
(`liftN (m + 1)`, cutoff `0` for the first-component type, cutoff `1`
under the fibre λ).

The de Bruijn accounting, once: the input list is scoped as peeled —
domain `j` under the parameters plus `j` earlier fields — while every
application node sits under ALL `nF` field binders.  A suffix head
with `m` later fields therefore lifts by `m + 1` (its own binder plus
the `m` later ones); the recursive call's input is scoped one binder
deeper, and its lift amount is one smaller — the arithmetic is
self-consistent with no length parameter threaded.

`mkTowerGo_interp` is the one interpretation equation, two regimes in
one statement: at a fitting spine the tupler reads back as
`if w = 0 then pt else mkTower bs` — exactly `psigmaMkV2_app`'s own
collapse, and exactly what the tier expects (`mkTower_mem` at the
graph regime, `pt_mem_tower` at squash).  The premises are
`FieldsBound` + `SpineFit`, nothing else.
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The environment kit for the λ-frame -/

omit [SetTheory V] in
theorem shiftE_consList_add :
    ∀ (bs : List V) (j : Nat) (ρ : Nat → V),
      shiftE (bs.length + j) 0 (consList bs ρ) = shiftE j 0 ρ
  | [], j, ρ => by simp
  | b :: bs, j, ρ => by
    rw [consList_cons,
      show (b :: bs).length + j = bs.length + (j + 1) by
        simp [List.length_cons]; omega,
      shiftE_consList_add bs (j + 1) (cons b ρ), shiftE_succ_cons]

omit [SetTheory V] in
/-- Dropping a spine's worth of bindings lands back at the base
environment. -/
theorem shiftE_consList (bs : List V) (ρ : Nat → V) :
    shiftE bs.length 0 (consList bs ρ) = ρ := by
  have h := shiftE_consList_add bs 0 ρ
  rwa [shiftE_zero_zero] at h

omit [SetTheory V] in
theorem consList_apply_add :
    ∀ (bs : List V) (ρ : Nat → V) (i : Nat),
      consList bs ρ (i + bs.length) = ρ i
  | [], _, _ => rfl
  | b :: bs, ρ, i => by
    rw [consList_cons,
      show i + (b :: bs).length = (i + 1) + bs.length by
        simp [List.length_cons]; omega,
      consList_apply_add bs (cons b ρ) (i + 1), cons_succ]

/-! ## The tupler -/

/-- The constructor tupler at the λ-frame (see the module docstring
for the de Bruijn accounting). -/
def mkTowerGo (w : Nat) : List AVExpr → AVExpr
  | [] => .const .punitUnit []
  | F :: Fs =>
    .app (.app (.app (.app (.const .psigmaMk [w, w])
        (F.liftN (Fs.length + 1)))
        (.lam (w + 1) (F.liftN (Fs.length + 1))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (.bvar Fs.length))
      (mkTowerGo w Fs)

/-- **The tupler reads back as the tier's tupler**, two regimes in one
statement: at a fitting spine, `mkTower bs` in the graph regime and
`pt` at squash — `psigmaMkV2_app`'s own collapse, matching the tier's
`mkTower_mem`/`pt_mem_tower` intro pair. -/
theorem mkTowerGo_interp {w : Nat} :
    ∀ {Fs : List AVExpr} {ρp : Nat → V} {bs : List V},
      FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      interp2 V (consList bs ρp) (mkTowerGo w Fs)
        = if w = 0 then pt else mkTower bs
  | [], _, [], _, _ => by split <;> rfl
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    -- the frame environment and its retraction to the base
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    -- the pair-type argument's interpretation
    have hA : interp2 V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp2 V ρp F := by
      rw [interp2_liftN, hshift]
    -- the fibre λ's interpretation
    have hBfun : ∀ x : V,
        interp2 V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)
        = interp2 V (cons x ρp) (towerBodyAV w Fs) := fun x => by
      rw [interp2_liftN, ← cons_shiftE, hshift]
    -- the field value's read-back
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    -- the recursive read-back
    have hrec : interp2 V (consList bs (cons b ρp)) (mkTowerGo w Fs)
        = if w = 0 then pt else mkTower bs :=
      mkTowerGo_interp (hb.2 b hsp.1) hsp.2
    -- the psigmaMk application premises
    have hAm : interp2 V ρp F ∈ˢ (univ w : V) := hb.1
    have hBm : (lamR (w + 1) (interp2 V ρp F)
          fun x => interp2 V (cons x ρp) (towerBodyAV w Fs))
        ∈ˢ psigmaFibreSpace V w (interp2 V ρp F) :=
      lamR_mem fun x hx => by
        rw [towerBodyAV_interp (hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hfib : SetTheory.app (lamR (w + 1) (interp2 V ρp F)
          fun x => interp2 V (cons x ρp) (towerBodyAV w Fs)) b
        = towerSet w (teleOfFields (cons b ρp) Fs) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (hb.2 b hsp.1)]
    have hbm : (if w = 0 then pt else mkTower bs)
        ∈ˢ SetTheory.app (lamR (w + 1) (interp2 V ρp F)
          fun x => interp2 V (cons x ρp) (towerBodyAV w Fs)) b := by
      rw [hfib]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp.2
      · next hnz => exact mkTower_mem_teleOfFields hnz hsp.2
    -- assemble
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (bval2 V .psigmaMk [w, w])
        (interp2 V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))))
        (lamR (w + 1)
          (interp2 V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1)))
          fun x => interp2 V (cons x (consList bs (cons b ρp)))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (consList bs (cons b ρp) Fs.length))
        (interp2 V (consList bs (cons b ρp)) (mkTowerGo w Fs))
      = if w = 0 then pt else mkTower (b :: bs)
    have hbv : bval2 V .psigmaMk [w, w] = psigmaMkV2 V w w := rfl
    rw [hA, hval, hrec]
    have hBeq : (fun x => interp2 V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))
        = fun x => interp2 V (cons x ρp) (towerBodyAV w Fs) :=
      funext hBfun
    rw [hBeq, hbv, psigmaMkV2_app V hAm hBm hsp.1 hbm,
      show Nat.max w w = w from Nat.max_self w]
    split <;> rfl

end Setlec.SetR.Interp2
