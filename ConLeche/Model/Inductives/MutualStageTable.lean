module

public import ConLeche.Model.Inductives.FixStageTable
public import ConLeche.Semantics.Tower.MutualLeafI
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The mutual block's projection-table stage (task #278, M2.5e)

`stageMutualTable`: the P step at ONE structure-like member's table
cons — `stageFixTable` read against the MUTUAL carrier.  The two
differences are packaged by `FixEntryLaw.lean`'s tag-generic cores
(`fixEntryTypingCoreT`, `fixEntryIotaCoreT`, `fixEntryIotaCoreZeroT`,
`fixEntryEtaCoreT`, over `FibreAt`):

* the constructor sits at its GLOBAL block position `J`, so a
  constructor application folds to `inj J ⟨f⃗, pt⟩` and the table reads
  its fields at offset `1` past that tag, exactly as on the fixpoint
  route;
* the member's carrier is the block's restricted tagged union at the
  member's tag (`mutualCarrierAt`) — the fibre at `J` is the own
  constructor's field tower, every other constructor's fibre is
  uninhabited because its index equation compares a tagged tuple of a
  DIFFERENT member with the member's own tag (`mutualFibreAt`, from
  `inj_inj`).

`stageMutualTables` folds it over `mutualTables` (`mutualTables_inv`,
`mutualMemberTable_inv`: a member either conses nothing or conses its
table).  The block-wide `NoProjEnv` invariant travels across a cons
because a table's bodies mention only their OWN structure's
projections (`noProjAt_structProjBodies`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BinderMeta ProjEntry
  ProjTable RecRule MutualBlock MutualFormerA projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## A table's bodies mention only its own structure's projections

The bodies are the constructor telescope's domains with the parameters
replaced by `bvar`s and the earlier fields by `T.proj j (bvar 0)`
(`structProjBodies`), so an expression free of `T'.proj i` stays free
of it for every `T' ≠ T`.  This is what carries the block's
`NoProjEnv` invariant across another member's table cons. -/

omit [SetTheory V] in
/-- The default expression is a `bvar`. -/
theorem noProjAt_default {T : Name} {i : Nat} : Expr.NoProjAt T i (default : Expr) :=
  Expr.noProjAt_bvar

theorem noProjAt_liftLooseBVars {T : Name} {i : Nat} (n : Nat) :
    ∀ (c : Nat) (e : Expr), Expr.NoProjAt T i e →
      Expr.NoProjAt T i (Expr.liftLooseBVars n c e) := by
  intro c e
  induction e generalizing c with
  | bvar j => intro _; rw [Expr.liftLooseBVars]; split <;> simp
  | sort u => intro _; rw [Expr.liftLooseBVars]; simp
  | const n us => intro h; rw [Expr.liftLooseBVars]; exact h
  | fvar idx ty => intro h; rw [Expr.liftLooseBVars]; exact h
  | lit l => intro _; rw [Expr.liftLooseBVars]; simp
  | app f a ihf iha =>
    intro h
    rw [Expr.noProjAt_app] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_app]
    exact ⟨ihf c h.1, iha c h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [Expr.noProjAt_lam] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_lam]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [Expr.noProjAt_forallE] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_forallE]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro h
    rw [Expr.noProjAt_letE] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_letE]
    exact ⟨iht c h.1, ihval c h.2.1, ihb (c + 1) h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [Expr.noProjAt_proj] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_proj]
    exact ⟨h.1, ihe c h.2⟩

theorem noProjAt_instantiate1Lift {T : Name} {i : Nat} {v : Expr}
    (hv : Expr.NoProjAt T i v) :
    ∀ (e : Expr) (d : Nat), Expr.NoProjAt T i e →
      Expr.NoProjAt T i (e.instantiate1Lift v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [ConLeche.Expr.instantiate1Lift]
    split
    · exact noProjAt_liftLooseBVars _ _ _ hv
    · split <;> simp
  | sort u => intro d _; rw [ConLeche.Expr.instantiate1Lift]; simp
  | const n us => intro d h; rw [ConLeche.Expr.instantiate1Lift]; exact h
  | fvar idx ty => intro d h; rw [ConLeche.Expr.instantiate1Lift]; exact h
  | lit l => intro d _; rw [ConLeche.Expr.instantiate1Lift]; simp
  | app f a ihf iha =>
    intro d h
    rw [Expr.noProjAt_app] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [Expr.noProjAt_lam] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [Expr.noProjAt_forallE] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [Expr.noProjAt_letE] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [Expr.noProjAt_proj] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_proj]
    exact ⟨h.1, ihe d h.2⟩

theorem noProjAt_instPisAtLift {T : Name} {i : Nat} :
    ∀ (args : List Expr) (e r : Expr),
      (∀ a ∈ args, Expr.NoProjAt T i a) →
      ConLeche.Expr.instPisAtLift args e = some r →
      Expr.NoProjAt T i e → Expr.NoProjAt T i r
  | [], e, r, _, h, he => by
    simp only [ConLeche.Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ he
  | a :: as, e, r, hall, h, he => by
    match e with
    | .forallE ty body mb =>
      rw [Expr.noProjAt_forallE] at he
      refine noProjAt_instPisAtLift as _ r (fun a' ha' => hall a' (List.mem_cons_of_mem _ ha'))
        h ?_
      exact noProjAt_instantiate1Lift (hall a List.mem_cons_self) body 0 he.2
    | .bvar _ | .sort _ | .const _ _ | .fvar _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact nomatch h

theorem noProjAt_structProjBodiesGo {T T' : Name} {i : Nat} (hne : T' ≠ T) :
    ∀ (k i0 : Nat) (e : Expr) (l : List Expr),
      ConLeche.structProjBodiesGo T' k i0 e = some l →
      Expr.NoProjAt T i e → ∀ bd ∈ l, Expr.NoProjAt T i bd := by
  intro k
  induction k with
  | zero =>
    intro i0 e l h _
    simp only [ConLeche.structProjBodiesGo, Option.some.injEq] at h
    subst h
    intro bd hbd
    exact absurd hbd List.not_mem_nil
  | succ k ih =>
    intro i0 e l h he
    match e with
    | .forallE fdom body mb =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      rw [Expr.noProjAt_forallE] at he
      intro bd hbd
      rcases List.mem_cons.mp hbd with rfl | hbd
      · exact he.1
      · refine ih (i0 + 1) _ l' hl' ?_ bd hbd
        refine noProjAt_instantiate1Lift ?_ body 0 he.2
        rw [ConLeche.structProjArgP, Expr.noProjAt_proj]
        exact ⟨fun hh => hne hh.1, by simp⟩
    | .bvar _ | .sort _ | .const _ _ | .fvar _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact nomatch h

/-- **A table's bodies are free of any other structure's projections.** -/
theorem noProjAt_structProjBodies {T T' : Name} {i nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (hne : T' ≠ T)
    (h : ConLeche.structProjBodies T' nP nF cty = some bodies)
    (hcty : Expr.NoProjAt T i cty) :
    ∀ k, Expr.NoProjAt T i (bodies.toList.getD k default) := by
  intro k
  unfold ConLeche.structProjBodies at h
  split at h
  · next r hr =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    have hall : ∀ bd ∈ l, Expr.NoProjAt T i bd :=
      noProjAt_structProjBodiesGo hne nF 0 r l hl
        (noProjAt_instPisAtLift (ConLeche.structProjPs nP) cty r
          (fun a ha => by
            obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
            simp) hr hcty)
    have htl : (List.toArray l).toList = l := rfl
    rw [htl]
    rcases Nat.lt_or_ge k l.length with hk | hk
    · refine hall _ ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]
      exact noProjAt_default
  · exact nomatch h

/-! ## The member's carrier and its fibre -/

/-- **A mutual member's carrier** at a fitting parameter frame: the
block's restricted tagged union at the member's own tag
(`mutualTyAVI_fold` then `fixFamI_app_eq_sum` at the one-element index
spine `[inj mIdx ⟨pt⟩]`). -/
@[expose] noncomputable def mutualCarrierAt (w mIdx : Nat) (FssR Ess' : List (List AnnotTerm))
    (ρ' : Nat → V) : V :=
  sumSet w (sumFibre w (cons (inj mIdx (mkTower [pt])) ρ') (rChains 1 1 FssR Ess'))

/-- **The member's fibre**: at a structure-like member the restricted
tagged union has exactly ONE inhabited fibre — the member's own
constructor's, at its global block position `J`.  Every other
constructor's fibre is empty: its index equation compares its own
tagged tuple with the member's tag, and `inj` is injective, so a
constructor of a different member cannot fit. -/
theorem mutualFibreAt {w J mIdx : Nat} {ρp : Nat → V}
    {FssR Ess' : List (List AnnotTerm)} {Fs : List AnnotTerm}
    (hFsJ : FssR[J]? = some Fs)
    (hother : ∀ j, j ≠ J → ∀ Fs' Es' : List AnnotTerm,
      FssR[j]? = some Fs' → Ess'[j]? = some Es' →
      ∀ fs : List V, SpineFit ρp Fs' fs →
        ∃ (m' : Nat) (a : V), m' ≠ mIdx ∧
          interp V (consList fs ρp) (Es'.getD 0 default) = inj m' a) :
    FibreAt w J Fs ρp (mutualCarrierAt w mIdx FssR Ess' ρp) := by
  have hsh : shiftE 1 0 (cons (inj mIdx (mkTower [pt])) ρp) = ρp := by
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have key : ∀ (j : Nat) (x' : V),
      x' ∈ˢ sumFibre w (cons (inj mIdx (mkTower [pt])) ρp) (rChains 1 1 FssR Ess') j →
      j = J ∧ ∃ fs : List V, SpineFit ρp Fs fs ∧ (w ≠ 0 → x' = mkTower (fs ++ [pt])) := by
    intro j x' hx
    rcases hc : (rChains 1 1 FssR Ess')[j]? with _ | Ch
    · rw [sumFibre_of_ge (List.getElem?_eq_none_iff.mp hc)] at hx
      exact absurd hx (not_mem_empty _)
    · rw [sumFibre_of_getElem? hc] at hx
      have hch := rChains_getElem? 1 1 FssR Ess' j
      rw [hc] at hch
      cases hF : FssR[j]? with
      | none => rw [hF] at hch; exact nomatch hch
      | some Fs' =>
        cases hE : Ess'[j]? with
        | none => rw [hF, hE] at hch; exact nomatch hch
        | some Es' =>
          rw [hF, hE] at hch
          obtain rfl : Ch = rChain 1 1 Fs' Es' := Option.some.inj hch
          -- a member of the fibre is a fitting spine of the restricted chain
          have hspE : ∃ as : List V,
              SpineFit (cons (inj mIdx (mkTower [pt])) ρp) (rChain 1 1 Fs' Es') as ∧
                (w ≠ 0 → x' = mkTower as) := by
            by_cases hw : w = 0
            · subst hw
              obtain ⟨-, as, hfits⟩ := towerSet_zero_elim _ hx
              exact ⟨as, fitsS_teleOfFields.mp hfits, fun h => absurd rfl h⟩
            · obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw hx
              exact ⟨_, hfit, fun _ => heta⟩
          obtain ⟨as, hspA, hxeq⟩ := hspE
          rw [rChain] at hspA
          obtain ⟨fs, rfl, hspL, hall⟩ := spineFit_append_idxEq.mp hspA
          have hspF : SpineFit ρp Fs' fs := by
            have h := (spineFit_liftFields (V := V) 1).mp hspL
            rwa [hsh] at h
          have hlenfs : fs.length = Fs'.length := hspF.length_eq
          -- the index equation: the constructor's tagged tuple is the member's tag
          have hmemEq : ((Es'.getD 0 default).liftN 1 Fs'.length,
              (AnnotTerm.bvar (Fs'.length + 1 - 1 - 0) : AnnotTerm))
              ∈ idxEqsAt 1 1 Fs'.length Es' := by
            unfold idxEqsAt
            exact List.mem_map.mpr ⟨0, by simp, rfl⟩
          have h0 := hall _ hmemEq
          have hrhs : interp V (consList fs (cons (inj mIdx (mkTower [pt])) ρp))
              (AnnotTerm.bvar (Fs'.length + 1 - 1 - 0)) = inj mIdx (mkTower [pt]) := by
            rw [interp_bvar, show Fs'.length + 1 - 1 - 0 = 0 + fs.length from by omega,
              consList_apply_add]
            rfl
          have hlhs : interp V (consList fs (cons (inj mIdx (mkTower [pt])) ρp))
              ((Es'.getD 0 default).liftN 1 Fs'.length)
              = interp V (consList fs ρp) (Es'.getD 0 default) := by
            rw [interp_liftN, ← hlenfs, shiftE_consList_len, hsh]
          have h0' : interp V (consList fs ρp) (Es'.getD 0 default)
              = inj mIdx (mkTower [pt]) := by
            rw [← hlhs]
            exact h0.trans hrhs
          by_cases hj : j = J
          · subst hj
            obtain rfl : Fs' = Fs := Option.some.inj (hF.symm.trans hFsJ)
            exact ⟨rfl, fs, hspF, hxeq⟩
          · exfalso
            obtain ⟨m', a, hm', hval⟩ := hother j hj Fs' Es' hF hE fs hspF
            rw [hval] at h0'
            exact hm' (inj_inj h0').1
  refine ⟨?_, ?_⟩
  · intro hw x hx
    unfold mutualCarrierAt at hx
    obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
    obtain ⟨rfl, fs, hspF, hxeq⟩ := key j a ha
    exact ⟨fs, by rw [hxeq hw], hspF⟩
  · intro hw x hx
    subst hw
    unfold mutualCarrierAt at hx
    obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
    obtain ⟨-, fs, hspF, -⟩ := key j a ha
    exact ⟨rfl, fs, hspF⟩

end ConLeche.Model
