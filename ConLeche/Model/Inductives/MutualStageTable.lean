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
    ∀ k, Expr.NoProjAt T i (bodies.getD k default) := by
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
    have hsz : (List.toArray l).size = l.length := rfl
    rw [Array.getD]
    split
    · next hk =>
      rw [hsz] at hk
      refine hall _ ?_
      show l[k]'hk ∈ l
      exact List.getElem_mem hk
    · exact noProjAt_default
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

/-! ## The P step at a structure-like member's table -/

set_option maxHeartbeats 3200000 in
/-- **The P step at a mutual block's projection table** (task #278
M2.5e): `stageFixTable` against the member's carrier — the block's
restricted tagged union at the member's tag, whose only inhabited
fibre is the member's own constructor's, at its GLOBAL block position
`J`.  The three laws are the tag-generic entry cores
(`FixEntryLaw.lean`); the bodies' frames are `bodyFrames` at that
carrier. -/
theorem stageMutualTable (mp : EnvModelM V μ env)
    {T : Name} {lps : List Name} {nP nF J mIdx : Nat} {resSort : Level} {isProp : Bool}
    {cvTa cvCa : ConstantVal} {caps : IndCaps} {sorts : List Level} {envOut : Env}
    (hTbl : ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) 1 cvCa env = .ok envOut)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hcaps : caps.eta = true → (Level.isEquiv resSort .zero == some true) = false ∧
      caps.etaCtor = cvCa.name ∧ caps.etaParams = nP ∧ caps.etaFields = nF)
    (hlpsT : cvTa.levelParams = lps)
    (hfC : env.find? cvCa.name = some (.ctorInfo cvCa nP nF))
    (hlpsC : cvCa.levelParams = lps)
    (hstripC : (cvCa.type.stripPis (nP + nF)).isSome = true)
    (hProp : isProp = (Level.isEquiv resSort .zero == some true))
    (hTshape : T.isProjFnShape = false)
    (hCshape : cvCa.name.isProjFnShape = false)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresR : ConLeche.reservedBasisNames.contains (T.str "rec") = false)
    (hresC : ConLeche.reservedBasisNames.contains cvCa.name = false)
    (hnp : ∀ j, NoProjEnv env T j)
    {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {lvls : (Name → Nat) → List Nat}
    (hFD : FormerData mp.base2 cvTa nP resSort pps lvls)
    (hCDread : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))))
    (hCDlen : ∀ ψ, (ds ψ).length = nP + nF)
    (hCDbelow : ∀ ψ, DomsBelow 0 (ds ψ))
    (hleq : ∀ k, k < nF → isProp = false → Level.leq (sorts.getD k .zero) resSort = some true)
    -- the block's leaves: the member's fibre leaf and its own
    -- constructor's, at the GLOBAL tag `J`
    {W : (Name → Nat) → Nat} {Idss FssR Ess' Fss₀ : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    (hleafT : ∀ ψ, mp.base2.acval T ψ
      = mutualTyAVI [] (W ψ) (resSort.eval ψ) (pps ψ) 0 (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
          (Ess' ψ) mIdx)
    (hleafC : ∀ ψ, mp.base2.acval cvCa.name ψ
      = sumMkAV [] 0 (resSort.eval ψ) J (ds ψ) (((ds ψ).drop nP).map (·.2.2)) (uChains (FssR ψ)))
    -- the member's carrier at fitting parameters
    (hfold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ
          (mutualTyAVI [] (W ψ) (resSort.eval ψ) (pps ψ) 0 (Idss ψ) rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
            (Ess' ψ) mIdx))
        = mutualCarrierAt (resSort.eval ψ) mIdx (FssR ψ) (Ess' ψ) (consList ts ρ))
    -- the own constructor's chain sits at `J`, every other
    -- constructor's index equation names a DIFFERENT member
    (hFsJ : ∀ ψ, (FssR ψ)[J]? = some (((ds ψ).drop nP).map (·.2.2)))
    (hother : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp →
      ∀ j, j ≠ J → ∀ Fs' Es'' : List AnnotTerm,
        (FssR ψ)[j]? = some Fs' → (Ess' ψ)[j]? = some Es'' →
        ∀ fs : List V, SpineFit ρp Fs' fs →
          ∃ (m' : Nat) (a : V), m' ≠ mIdx ∧
            interp V (consList fs ρp) (Es''.getD 0 default) = inj m' a)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        SumFieldsOkB (resSort.eval ψ) ρ (FssR ψ))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (hboundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        isProp = false → FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)))
    (hsortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        ∀ j, j < nF → ∀ as : List V,
          SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
          interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
            ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)) :
    ∃ mp' : EnvModelM V μ envOut,
      mp'.base2.acval = acvalWith mp.base2.acval (projTableName T) (fun _ => .sort 0) := by
  have hwf' : ConLeche.EnvWF envOut := ConLeche.direct_table_wf mp.base2.wf hTbl
  obtain ⟨bodies, hbodies, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv hTbl
  let tbl : ProjTable := ⟨T, lps, nP, cvCa.name, nF, resSort,
    bodies, ConLeche.structProjGuards cvCa.type nP nF sorts, 1⟩
  -- the fibre facts and the chains' grading
  have hfibAt : ∀ (ψ : Name → Nat) (ρ' : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ' →
      FibreAt (resSort.eval ψ) J (((ds ψ).drop nP).map (·.2.2)) ρ'
        (mutualCarrierAt (resSort.eval ψ) mIdx (FssR ψ) (Ess' ψ) ρ') :=
    fun ψ ρ' hρ' => mutualFibreAt (hFsJ ψ) (hother ψ ρ' hρ')
  have hokU : ∀ (ψ : Name → Nat) (ρ' : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ' →
      SumFieldsOkB (resSort.eval ψ) ρ' (uChains (FssR ψ)) :=
    fun ψ ρ' hρ' => SumFieldsOkB_uChains (hFssOk ψ ρ' hρ')
  -- the field-chain facts, in the frames' spelling
  have hbound : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ → resSort.eval ψ ≠ 0 →
      FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) := by
    intro ψ ρ hρ hw
    cases hp : isProp
    · exact hboundP ψ ρ hρ hp
    · exfalso
      apply hw
      rw [hp] at hProp
      exact Level.isEquiv_sound (beq_iff_eq.mp hProp.symm) ψ
  have hokB : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
      FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) :=
    fun ψ ρ h => (hfields ψ ρ h).1
  -- the guards' content: the official join over the used earlier slots
  have hguardSem : ∀ k, k < nF → ∀ ψ : Name → Nat,
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 →
      (sorts.getD k .zero).eval ψ = 0 ∧
      ∀ j, j < k → ConLeche.structUsedLater cvCa.type nP j = true →
        (sorts.getD j .zero).eval ψ = 0 := by
    intro k hk ψ h0
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)] at h0
    exact ⟨h0.1, fun j hj hu => h0.2 j (List.mem_range.mpr hj) hu⟩
  have hguardOf : ∀ k, k < nF → ∀ ψ : Name → Nat,
      (∀ j, j ≤ k → (sorts.getD j .zero).eval ψ = 0) →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk ψ hall
    rw [ConLeche.structProjGuards_getD _ _ _ _ hk,
      eval_foldl_max_if_zero_iff ψ (ConLeche.structUsedLater cvCa.type nP)
        (fun j => sorts.getD j .zero)]
    exact ⟨hall k (Nat.le_refl _), fun j hj _ => hall j (Nat.le_of_lt (List.mem_range.mp hj))⟩
  have hO5 : ∀ k, k < nF → (Level.isEquiv resSort .zero == some true) = false →
      ∀ ψ : Name → Nat, resSort.eval ψ = 0 →
      ((ConLeche.structProjGuards cvCa.type nP nF sorts).getD k .zero).eval ψ = 0 := by
    intro k hk hne ψ h0
    refine hguardOf k hk ψ fun j hj => ?_
    have := Level.leq_sound (hleq j (by omega) (by rw [hProp]; exact hne)) ψ
    omega
  -- the constructor type's scoping
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the unused earlier fields are free in the projected field's type
  obtain ⟨fvsA, oA, hopAll⟩ := openPisAtFvars_of_stripPis_isSome (nP + nF) 0 hstripC
  have hlenA : fvsA.length = nP + nF := openPisAtFvars_length _ hopAll
  have hfree : ∀ (ψ : Name → Nat) (k : Nat), k < nF → ∀ (j : Nat), j < k →
      ConLeche.structUsedLater cvCa.type nP j = false →
      ∃ X : AnnotTerm, (((ds ψ).drop nP).map (·.2.2)).getD k default = X.liftN 1 (k - 1 - j) := by
    intro ψ k hk j hj hun
    have hsome : (cvCa.type.stripPis (nP + j + 1)).isSome = true :=
      ConLeche.stripPis_isSome_of_le (by omega) hstripC
    obtain ⟨⟨bs, rest⟩, hst⟩ := Option.isSome_iff_exists.mp hsome
    have hrest : rest.hasLooseBVar 0 = false := by
      unfold ConLeche.structUsedLater at hun
      rw [hst] at hun
      have hun' : rest.hasLooseBVarB 0 = false := hun
      rw [ConLeche.Expr.hasLooseBVarB_eq] at hun'
      exact hun'
    obtain ⟨hleavesK, -⟩ := openPisAtFvars_leaf_free (nP + nF) (nP + j) hopAll (by omega)
      hst hrest (by
        intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hl
        exact absurd hl List.not_mem_nil)
    obtain ⟨pps', b, hstA, -, -, hbind⟩ := denoteMeta_openPis (nP + nF) hopAll (hCDread ψ)
    have hppsEq : pps' = ds ψ := by
      have h2 := stripPisAV_mkPisAV (ds ψ) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ))
      rw [hCDlen ψ] at h2
      exact (Prod.mk.inj (Option.some.inj (hstA.symm.trans h2))).1
    obtain ⟨x, hx⟩ : ∃ x, fvsA[nP + k]? = some x :=
      ⟨fvsA[nP + k]'(by rw [hlenA]; omega), List.getElem?_eq_getElem (by rw [hlenA]; omega)⟩
    obtain ⟨q, hq, -, hqread⟩ := hbind (nP + k) x hx
    rw [hppsEq] at hq
    have hW : Expr.WScoped (0 + (nP + k)) (Expr.fvarTypeD x) :=
      openPisAtFvars_typeWScoped (nP + nF) hopAll (Expr.WScoped.of_not_hasFvar hCf) _ x hx
    have hleaf : ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, l.1 ≠ nP + j := by
      intro l hl
      have hsub : l ∈ x.fvarLeaves := by
        cases x with
        | fvar idx ty =>
          simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
          exact List.mem_cons_of_mem _ hl
        | _ => exact hl
      have := hleavesK (nP + k) (by omega) x hx l hsub
      simpa using this
    obtain ⟨X, hX⟩ := denoteMeta_liftN_of_leaf_free mp.base2 (0 + (nP + k)) (Expr.fvarTypeD x) hW
      (q := nP + j) (by omega) (by intro l hl; exact hleaf l hl) hqread
    refine ⟨X, ?_⟩
    have hFk : (((ds ψ).drop nP).map (·.2.2)).getD k default = q.2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, hq]
      rfl
    rw [hFk, hX, show 0 + (nP + k) - 1 - (nP + j) = k - 1 - j from by omega]
  -- names
  have hneT : T ≠ projTableName T := by
    intro h
    have := projTableName_isProjFnShape T
    rw [← h, hTshape] at this
    exact nomatch this
  have hneC : cvCa.name ≠ projTableName T := by
    intro h
    have := projTableName_isProjFnShape T
    rw [← h, hCshape] at this
    exact nomatch this
  have hnres : ConLeche.reservedBasisNames.contains (projTableName T) = false :=
    ConLeche.reservedBasisNames_not_num _ _
  -- the crossings
  have hcrossT : ConsCrossAt (.projInfo tbl) cvTa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (hnp j).type _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfC)).2.2.1
  -- the lookups at the extension
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? T
      = some (.indInfo cvTa caps) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneT h.symm)]
    exact hfT
  have hfC₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? cvCa.name
      = some (.ctorInfo cvCa nP nF) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun h => hneC h.symm)]
    exact hfC
  have hfTbl₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? (projTableName T)
      = some (.projInfo tbl) := ConLeche.Env.find?_cons_self _ _
  have hprev₂ : ∀ j, j < nF →
      ∃ entry, (⟨.projInfo tbl :: env.consts⟩ : Env).findProj? T j = some entry :=
    fun j hj => ⟨tbl.entry j, ConLeche.Env.findProj?_of_table hfTbl₂ hj⟩
  -- the head data at every field
  have hhead : ∀ i, i < nF → ConLeche.TowerHead ⟨.projInfo tbl :: env.consts⟩ (tbl.entry i) :=
    fun i hi => ⟨hresT, hresR, hresC, hi, ⟨cvTa, caps, hfT₂, hlpsT⟩,
      ⟨cvCa, hfC₂, hlpsC, hstripC⟩⟩
  suffices hlaw : ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) →
      ∀ (φ : Name → Nat) (i : Nat), i < tbl.numFields →
        TowerEntryLaw m₂ φ tbl.structName i (tbl.entry i) by
    obtain ⟨mp', hac'⟩ :=
      declStep_preserves_of_tower_cons mp (tbl := tbl) hfresh hnres hwf' hnp hhead hlaw
    exact ⟨mp', hac'⟩
  -- the fields' laws
  intro m₂ hac φ i hi
  replace hi : i < nF := hi
  have hacT : ∀ ψ, m₂.acval T ψ = mp.base2.acval T ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ T ψ = _
    rw [acvalWith_ne hneT]
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = mp.base2.acval cvCa.name ψ := by
    intro ψ
    rw [hac]
    show acvalWith mp.base2.acval (projTableName T) _ cvCa.name ψ = _
    rw [acvalWith_ne hneC]
  have hFD₂ : FormerData m₂ cvTa nP resSort pps lvls :=
    hFD.cross (c₀ := .projInfo tbl) hfresh hcrossT hcbT m₂ hac
  -- the constructor type's reading at the extension
  have hCDread₂ : ∀ ψ, denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ ψ 0 cvCa.type
      = some (mkPisAV (ds ψ) (ctorBodyAVI m₂ T nP nF ψ (Es ψ))) := by
    intro ψ
    have hbody : ctorBodyAVI m₂ T nP nF ψ (Es ψ)
        = ctorBodyAVI mp.base2 T nP nF ψ (Es ψ) := by
      unfold ctorBodyAVI; rw [hacT]
    rw [hbody, hac]
    exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (hCDread ψ)
  -- the body, opened at the variables
  obtain ⟨cds, bodyB, mbB, hcf⟩ :=
    ConLeche.structProjBody_open hbodies hstripC hCb hi
  refine ⟨rfl, rfl, hi, ⟨cvTa, caps, hfT₂, hlpsT, hcaps⟩,
    hO5 i hi, cvCa, hfC₂, hlpsC, ?_, ?_⟩
  · -- the per-instantiation laws
    intro us _
    obtain ⟨fdomA, hfdA, hokFd, hresFd⟩ := bodyFrames m₂ (off := 1) hcf hCf hCb
      (fun j hj => by
        obtain ⟨entry, hfe⟩ := hprev₂ j (by omega)
        refine ⟨entry, hfe, ?_⟩
        obtain ⟨tbl', hf', -, rfl⟩ := ConLeche.Env.findProj?_some hfe
        obtain rfl : tbl = tbl' := ConstantInfo.projInfo.inj (Option.some.inj (hfTbl₂.symm.trans hf'))
        rfl) hi
      (hCDlen (Level.substFn φ lps us))
      (hCDbelow (Level.substFn φ lps us))
      (hCDread₂ (Level.substFn φ lps us))
      (fun ρ h => hfields _ ρ h) (hsortsF _)
      (used := ConLeche.structUsedLater cvCa.type nP) (hfree _ i hi)
      (fun ρ => ρ 0 ∈ˢ mutualCarrierAt (resSort.eval (Level.substFn φ lps us)) mIdx
        (FssR (Level.substFn φ lps us)) (Ess' (Level.substFn φ lps us)) (fun j => ρ (j + 1)))
      (fun ρ hx hsat hw => (hfibAt _ _ hsat).squash hw _ hx)
      (fun ρ hx hsat hw => by
        obtain ⟨fs, heq, hsp⟩ := (hfibAt _ _ hsat).graph hw _ hx
        have hlenF : fs.length = nF := by
          rw [hsp.length_eq, List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]
        rw [heq, dropS_one_inj, ← hlenF, projList_mkTower_take (Nat.le_refl _), List.take_length]
        exact hsp)
      (fun ρ hx hsat j hj => by
        refine wellDenoted_projAV_succ_of (fun _ => hokB _ _ hsat) (hfibAt _ _ hsat) trivial ?_ ?_
        · rw [interp_bvar]; exact hx
        · rw [List.length_map, List.length_drop, hCDlen, Nat.add_sub_cancel_left]; exact hj)
    have hread : denoteMeta m₂.acval ⟨.projInfo tbl :: env.consts⟩ φ 0
        (ConLeche.projTele ((tbl.entry i).numParams + 1)
          ((tbl.entry i).body.instantiateLevelParams (tbl.entry i).levelParams us))
        = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) fdomA) := by
      show denoteMeta m₂.acval _ φ 0 (ConLeche.projTele (nP + 1)
        ((bodies.getD i default).instantiateLevelParams lps us)) = _
      rw [← ConLeche.projTele_instantiateLevelParams,
        denotePInstLevels m₂ φ lps us 0]
      exact denoteMeta_projTele_zero hfdA
    refine ⟨⟨_, hread, ?_⟩, ?_⟩
    · -- (A)
      intro hguardAt ρ vs x rest hlenVs hokApp hokx hmem hpeel
      have hguard' : resSort.eval (Level.substFn φ lps us) = 0 →
          (sorts.getD i .zero).eval (Level.substFn φ lps us) = 0 ∧
          ∀ j, j < i → ConLeche.structUsedLater cvCa.type nP j = true →
            (sorts.getD j .zero).eval (Level.substFn φ lps us) = 0 :=
        fun h0 => hguardSem i hi _ (hguardAt h0)
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = mutualTyAVI [] (W (Level.substFn φ lps us))
            (resSort.eval (Level.substFn φ lps us))
            (pps (Level.substFn φ lps us)) 0 (Idss (Level.substFn φ lps us)) rss
            (tlss (Level.substFn φ lps us)) (Eiss' (Level.substFn φ lps us))
            (Fss₀ (Level.substFn φ lps us)) (Ess' (Level.substFn φ lps us)) mIdx := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT, hleafT]
      rw [hacT'] at hokApp hmem
      exact fixEntryTypingCoreT (J := J) rfl (hCDlen _) (hFD.len _) (by simp) (hiff _) (hokB _)
        (hsortsF _) (used := ConLeche.structUsedLater cvCa.type nP) hguard' (hfree _ i hi) hi
        (hfold _) (fun ρ' hρ' => hfibAt _ ρ' hρ') hresFd (hokFd (fun h0 => (hguard' h0).2))
        ρ vs x rest hlenVs hokApp hokx hmem hpeel
    · -- (B)
      refine ⟨mkPisAV (ds (Level.substFn φ lps us))
        (ctorBodyAVI m₂ T nP nF (Level.substFn φ lps us)
          (Es (Level.substFn φ lps us))), ?_, ?_⟩
      · rw [denotePInstLevels m₂ φ cvCa.levelParams us 0 cvCa.type, hlpsC]
        exact hCDread₂ _
      · intro hguardAt ρ ys rest hlen hok hfit
        have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
            = sumMkAV [] 0 (resSort.eval (Level.substFn φ lps us)) J
              (ds (Level.substFn φ lps us))
              (((ds (Level.substFn φ lps us)).drop nP).map (·.2.2))
              (uChains (FssR (Level.substFn φ lps us))) := by
          show m₂.acval cvCa.name (Level.substFn φ lps us) = _
          rw [hacC, hleafC]
        rw [hacC'] at hok ⊢
        show interp V ρ (projAV (i + 1) _) = _
        by_cases hw : resSort.eval (Level.substFn φ lps us) = 0
        · have hsp : SpineFit ρ ((ds (Level.substFn φ lps us)).map (·.2.2))
              (ys.map (interp V ρ)) :=
            spineFit_of_teleFit (by simp only [List.length_map, hlen, hCDlen]; rfl) hfit
          rw [hw]
          exact fixEntryIotaCoreZeroT (hCDlen _) hi (hsortsF _)
            (hguardSem i hi _ (hguardAt hw)).1 ys hlen hsp
        · exact fixEntryIotaCoreT hw (hCDlen _) hi (hFsJ _) (hokU _) ys hlen hok
  · -- (C)
    intro cvT capsT hf us _
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₂.symm.trans hf))
    refine ⟨mkPisAV (pps (Level.substFn φ lps us))
      (.sort (resSort.eval (Level.substFn φ lps us))), ?_, hFD.okTy _, ?_⟩
    · rw [denotePInstLevels m₂ φ cvTa.levelParams us 0 cvTa.type, hlpsT]
      exact hFD₂.read _
    · intro ρ ts rest x hlents hfit hmem
      have hsp := spineFit_of_teleFit (by rw [hFD.len]; exact hlents) hfit
      have hacT' : m₂.acval tbl.structName (Level.substFn φ (tbl.entry i).levelParams us)
          = mutualTyAVI [] (W (Level.substFn φ lps us))
            (resSort.eval (Level.substFn φ lps us))
            (pps (Level.substFn φ lps us)) 0 (Idss (Level.substFn φ lps us)) rss
            (tlss (Level.substFn φ lps us)) (Eiss' (Level.substFn φ lps us))
            (Fss₀ (Level.substFn φ lps us)) (Ess' (Level.substFn φ lps us)) mIdx := by
        show m₂.acval T (Level.substFn φ lps us) = _
        rw [hacT, hleafT]
      have hacC' : m₂.acval (tbl.entry i).ctor (Level.substFn φ (tbl.entry i).levelParams us)
          = sumMkAV [] 0 (resSort.eval (Level.substFn φ lps us)) J
            (ds (Level.substFn φ lps us))
            (((ds (Level.substFn φ lps us)).drop nP).map (·.2.2))
            (uChains (FssR (Level.substFn φ lps us))) := by
        show m₂.acval cvCa.name (Level.substFn φ lps us) = _
        rw [hacC, hleafC]
      rw [hacT'] at hmem
      rw [hacC']
      show x = (ts ++ (List.range nF).map fun j => projS (j + 1) x).foldl SetTheory.app _
      exact fixEntryEtaCoreT (hCDlen _) (hFD.len _) (hiff _) (hFsJ _) (hokU _) (hfold _)
        (fun ρ' hρ' => hfibAt _ ρ' hρ') ts x hlents hsp hmem

/-! ## The fold over the members -/

/-- The block-wide data the members' leaves and the block's chains are
spelled from — everything the table stage reads that does not depend on
the member. -/
structure TableBlockData where
  /-- the block's level parameters -/
  lps : List Name
  /-- the parameter count -/
  nP : Nat
  /-- the block's `Prop`-ness bit -/
  isProp : Bool
  /-- the tag's sort -/
  W : (Name → Nat) → Nat
  /-- the members' index telescopes -/
  Idss : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' REAL field chains -/
  FssR : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' tagged index expressions -/
  Ess' : (Name → Nat) → List (List AnnotTerm)
  /-- the constructors' X-chains -/
  Fss₀ : (Name → Nat) → List (List AnnotTerm)
  /-- the recursive-slot bits -/
  rss : List (List Bool)
  /-- the recursive slots' telescopes -/
  tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))
  /-- the recursive slots' tagged index expressions -/
  Eiss' : (Name → Nat) → List (List (List AnnotTerm))

/-- **One member's table data**, at the environment and carrier its
table is consed on: the block's `NoProjEnv` invariant at the member,
the member's own lookup, and — when the member is structure-like, so
that the kernel conses its table — everything `stageMutualTable` asks
of its own constructor.  Every member of the block carries it, because
a later member's table cons happens at an environment the earlier
conses have already grown (`MutualTableOk.cross`). -/
@[expose] def MutualTableOk {env : Env} (m : EnvModel V env) (d : TableBlockData)
    (capsOf : Nat → IndCaps) (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (f : MutualFormerA) (mIdx : Nat) : Prop :=
  (∀ j, NoProjEnv env f.cvTa.name j) ∧
  env.find? f.cvTa.name = some (.indInfo f.cvTa (capsOf mIdx)) ∧
  ∀ (J : Nat) (c : ConLeche.MutualCtor), b.ownCtors mIdx = [(J, c)] → f.nIdx = 0 →
    ∃ (cvCa : ConstantVal) (pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (lvls : (Name → Nat) → List Nat),
      cvCa = (ctorsA.getD J default).1 ∧ cvCa.name = c.cv.name ∧
      ((capsOf mIdx).eta = true → (Level.isEquiv f.s .zero == some true) = false ∧
        (capsOf mIdx).etaCtor = cvCa.name ∧ (capsOf mIdx).etaParams = d.nP ∧
        (capsOf mIdx).etaFields = c.nF) ∧
      f.cvTa.levelParams = d.lps ∧
      env.find? cvCa.name = some (.ctorInfo cvCa d.nP c.nF) ∧
      cvCa.levelParams = d.lps ∧
      (cvCa.type.stripPis (d.nP + c.nF)).isSome = true ∧
      d.isProp = (Level.isEquiv f.s .zero == some true) ∧
      f.cvTa.name.isProjFnShape = false ∧ cvCa.name.isProjFnShape = false ∧
      ConLeche.reservedBasisNames.contains f.cvTa.name = false ∧
      ConLeche.reservedBasisNames.contains (f.cvTa.name.str "rec") = false ∧
      ConLeche.reservedBasisNames.contains cvCa.name = false ∧
      FormerData m f.cvTa d.nP f.s pps lvls ∧
      (∀ ψ, denoteMeta m.acval env ψ 0 cvCa.type
        = some (mkPisAV (ds ψ) (ctorBodyAVI m f.cvTa.name d.nP c.nF ψ (Es ψ)))) ∧
      (∀ ψ, (ds ψ).length = d.nP + c.nF) ∧
      (∀ ψ, DomsBelow 0 (ds ψ)) ∧
      (∀ k, k < c.nF → d.isProp = false →
        Level.leq ((sortss.getD J []).getD k .zero) f.s = some true) ∧
      (∀ ψ, m.acval f.cvTa.name ψ
        = mutualTyAVI [] (d.W ψ) (f.s.eval ψ) (pps ψ) 0 (d.Idss ψ) d.rss (d.tlss ψ) (d.Eiss' ψ)
            (d.Fss₀ ψ) (d.Ess' ψ) mIdx) ∧
      (∀ ψ, m.acval cvCa.name ψ
        = sumMkAV [] 0 (f.s.eval ψ) J (ds ψ) (((ds ψ).drop d.nP).map (·.2.2)) (uChains (d.FssR ψ))) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((pps ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (mutualTyAVI [] (d.W ψ) (f.s.eval ψ) (pps ψ) 0 (d.Idss ψ) d.rss (d.tlss ψ) (d.Eiss' ψ)
              (d.Fss₀ ψ) (d.Ess' ψ) mIdx))
          = mutualCarrierAt (f.s.eval ψ) mIdx (d.FssR ψ) (d.Ess' ψ) (consList ts ρ)) ∧
      (∀ ψ, (d.FssR ψ)[J]? = some (((ds ψ).drop d.nP).map (·.2.2))) ∧
      (∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρp →
        ∀ j, j ≠ J → ∀ Fs' Es'' : List AnnotTerm,
          (d.FssR ψ)[j]? = some Fs' → (d.Ess' ψ)[j]? = some Es'' →
          ∀ fs : List V, SpineFit ρp Fs' fs →
            ∃ (m' : Nat) (a : V), m' ≠ mIdx ∧
              interp V (consList fs ρp) (Es''.getD 0 default) = inj m' a) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρ →
          SumFieldsOkB (f.s.eval ψ) ρ (d.FssR ψ)) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔
          Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (f.s.eval ψ) ρ (((ds ψ).drop d.nP).map (·.2.2)) ∧
          FieldsValid ρ (((ds ψ).drop d.nP).map (·.2.2))) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρ →
          d.isProp = false →
            FieldsBound (f.s.eval ψ) ρ (((ds ψ).drop d.nP).map (·.2.2))) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ds ψ).take d.nP).map (·.2.2)).reverse ρ →
          ∀ j, j < c.nF → ∀ as : List V,
            SpineFit ρ ((((ds ψ).drop d.nP).map (·.2.2)).take j) as →
            interp V (consList as ρ) ((((ds ψ).drop d.nP).map (·.2.2)).getD j default)
              ∈ˢ (univ (((sortss.getD J []).getD j .zero).eval ψ) : V))

/-- **A member's table data crosses another member's table cons.**
The head is a table of a DIFFERENT structure, so nothing it stores
mentions this member's slots: its type is a sort, and its bodies are
that structure's constructor telescope with only its OWN projections
inserted (`noProjAt_structProjBodies`). -/
theorem MutualTableOk.cross {m : EnvModel V env} {d : TableBlockData} {capsOf : Nat → IndCaps}
    {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {f : MutualFormerA} {mIdx : Nat}
    (h : MutualTableOk m d capsOf b ctorsA sortss f mIdx)
    {tbl : ProjTable} {cty : Expr} {nF' : Nat}
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hbodies : ConLeche.structProjBodies tbl.structName d.nP nF' cty = some tbl.bodies)
    (hcty : ∃ ci ∈ env.consts, ci.toConstantVal.type = cty)
    (hnpT : ∀ i, NoProjEnv env tbl.structName i)
    (hne : tbl.structName ≠ f.cvTa.name)
    (m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0)) :
    MutualTableOk m₂ d capsOf b ctorsA sortss f mIdx := by
  obtain ⟨hnp, hfT, hrest⟩ := h
  -- the head's pieces mention no member's slots
  have hheadT : ∀ (T : Name) (i : Nat), (∀ j, NoProjEnv env T j) → T ≠ tbl.structName →
      NoProjHead (.projInfo tbl) T i := by
    intro T i hnpT' hneT
    refine ⟨?_, (fun _ _ _ hh => nomatch hh), (fun _ _ _ _ hh => nomatch hh), ?_⟩
    · show Expr.NoProjAt T i (.sort (.succ .zero))
      exact Expr.noProjAt_sort
    · intro tbl₂ heq k _
      obtain rfl := ConstantInfo.projInfo.inj heq
      obtain ⟨ci, hci, rfl⟩ := hcty
      exact noProjAt_structProjBodies (fun hh => hneT hh.symm) hbodies ((hnpT' i).type ci hci) k
  have hnp₂ : ∀ j, NoProjEnv (⟨.projInfo tbl :: env.consts⟩ : Env) f.cvTa.name j :=
    fun j => (hnp j).cons (hheadT f.cvTa.name j hnp (fun hh => hne hh.symm))
  have hfT₂ : (⟨.projInfo tbl :: env.consts⟩ : Env).find? f.cvTa.name
      = some (.indInfo f.cvTa (capsOf mIdx)) := ConLeche.Env.find?_cons_of_fresh hfresh hfT
  have hneT : f.cvTa.name ≠ (ConstantInfo.projInfo tbl).name := by
    intro hh; rw [hh, hfresh] at hfT; exact nomatch hfT
  have hacT : ∀ ψ, m₂.acval f.cvTa.name ψ = m.acval f.cvTa.name ψ := by
    intro ψ; rw [hac, acvalWith_ne hneT]
  refine ⟨hnp₂, hfT₂, ?_⟩
  intro J c hown hnIdx
  obtain ⟨cvCa, pps, ds, Es, lvls, hCeq, hCname, hcaps, hlpsT, hfC, hlpsC, hstripC, hProp,
    hTshape, hCshape, hresT, hresR, hresC, hFD, hCDread, hCDlen, hCDbelow, hleq, hleafT,
    hleafC, hfold, hFsJ, hother, hFssOk, hiff, hfields, hboundP, hsortsF⟩ := hrest J c hown hnIdx
  have hneC : cvCa.name ≠ (ConstantInfo.projInfo tbl).name := by
    intro hh; rw [hh, hfresh] at hfC; exact nomatch hfC
  have hacC : ∀ ψ, m₂.acval cvCa.name ψ = m.acval cvCa.name ψ := by
    intro ψ; rw [hac, acvalWith_ne hneC]
  have hcrossT : ConsCrossAt (.projInfo tbl) f.cvTa.type := by
    intro t2 he' j
    cases he'
    exact (hnpT j).type _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (hnpT j).type _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hcbT : ConstsBound env f.cvTa.type :=
    constsBound_of_constsResolve _ (m.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (m.wf _ (ConLeche.Semantics.Env.find?_mem hfC)).2.2.1
  refine ⟨cvCa, pps, ds, Es, lvls, hCeq, hCname, hcaps, hlpsT,
    ConLeche.Env.find?_cons_of_fresh hfresh hfC, hlpsC, hstripC, hProp, hTshape, hCshape,
    hresT, hresR, hresC, hFD.cross hfresh hcrossT hcbT m₂ hac, ?_, hCDlen, hCDbelow, hleq,
    fun ψ => by rw [hacT, hleafT], fun ψ => by rw [hacC, hleafC], hfold, hFsJ, hother, hFssOk,
    hiff, hfields, hboundP, hsortsF⟩
  intro ψ
  have hbody : ctorBodyAVI m₂ f.cvTa.name d.nP c.nF ψ (Es ψ)
      = ctorBodyAVI m f.cvTa.name d.nP c.nF ψ (Es ψ) := by
    unfold ctorBodyAVI; rw [hacT]
  rw [hbody, hac]
  exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (hCDread ψ)

set_option maxHeartbeats 1600000 in
/-- **The table stage over the members** (task #278 M2.5e): each member
either conses nothing or conses its projection table
(`mutualMemberTable_inv`).  The carrier survives every cons
(`stageMutualTable`), the leaves off the table names are untouched, and
`EtaFamiliesClosed` travels because a table head is not an inductive. -/
theorem stageMutualTablesGo {d : TableBlockData} {capsOf : Nat → IndCaps}
    {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hlps : b.lps = d.lps) (hnP : b.nP = d.nP)
    -- a caller's invariant preserved by every table cons (task #279
    -- M-B′ step 3c (c): the block's representations cross the tables)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m : EnvModel V env') (tbl : ConLeche.ProjTable),
      env'.find? (ConstantInfo.projInfo tbl).name = none →
      ConsCrossEnv env' (.projInfo tbl) → Inv m →
      ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env'.consts⟩,
        m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) → Inv m₂) :
    ∀ (l : List (MutualFormerA × Nat)) {env : Env} (mp : EnvModelM V μ env) {env' : Env},
      ConLeche.EtaFamiliesClosed env →
      ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss l env = .ok env' →
      (l.map (·.1.cvTa.name)).Nodup →
      (∀ p ∈ l, MutualTableOk mp.base2 d capsOf b ctorsA sortss p.1 p.2) →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V μ env',
        (∀ n : Name, (∀ p ∈ l, n ≠ projTableName p.1.cvTa.name) →
          mp'.base2.acval n = mp.base2.acval n) ∧
        -- … and off every name already stored (task #279 M-D′ D2: a
        -- table is consed only where its name is fresh)
        (∀ n : Name, (env.find? n).isSome = true →
          mp'.base2.acval n = mp.base2.acval n) ∧
        ConLeche.EtaFamiliesClosed env' ∧ Inv mp'.base2 := by
  intro l
  induction l with
  | nil =>
    intro env mp env' hE h _ _ hinv
    obtain rfl := ConLeche.mutualTables_nil_inv h
    exact ⟨mp, fun _ _ => rfl, fun _ _ => rfl, hE, hinv⟩
  | cons p rest ih =>
    intro env mp env' hE h hnd hmem hinv
    obtain ⟨f, mIdx⟩ := p
    obtain ⟨envI, hI, hrestRun⟩ := ConLeche.mutualTables_inv h
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases ConLeche.mutualMemberTable_inv hI with rfl | ⟨J, c, hown, hnIdx, htbl⟩
    · -- the member conses nothing
      obtain ⟨mp', hoff, hoffS, hE', hinv'⟩ :=
        ih mp hE hrestRun hnd.2 (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) hinv
      exact ⟨mp', fun n hn => hoff n (fun q hq => hn q (List.mem_cons_of_mem _ hq)), hoffS, hE',
        hinv'⟩
    · -- the member conses its table
      obtain ⟨hnp, hfT, hrest⟩ := hmem (f, mIdx) List.mem_cons_self
      obtain ⟨cvCa, pps, ds, Es, lvls, hCeq, hCname, hcaps, hlpsT, hfC, hlpsC, hstripC, hProp,
        hTshape, hCshape, hresT, hresR, hresC, hFD, hCDread, hCDlen, hCDbelow, hleq, hleafT,
        hleafC, hfold, hFsJ, hother, hFssOk, hiff, hfields, hboundP, hsortsF⟩ :=
        hrest J c hown hnIdx
      rw [← hCeq, ← hCname, hlps, hnP] at htbl
      obtain ⟨bodies, hbodies, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
      obtain ⟨mpI, hacI⟩ := stageMutualTable mp htbl hfT hcaps hlpsT hfC hlpsC hstripC hProp
        hTshape hCshape hresT hresR hresC hnp hFD hCDread hCDlen hCDbelow hleq hleafT hleafC
        hfold hFsJ hother hFssOk hiff hfields hboundP hsortsF
      have hE' : ConLeche.EtaFamiliesClosed
          (⟨.projInfo ⟨f.cvTa.name, d.lps, d.nP, cvCa.name, c.nF, f.s, bodies,
            ConLeche.structProjGuards cvCa.type d.nP c.nF (sortss.getD J []), 1⟩
            :: env.consts⟩ : Env) :=
        ConLeche.EtaFamiliesClosed.cons_nonind hE hfreshTbl
          (fun _ _ hh => nomatch hh)
      have hmemI : ∀ q ∈ rest, MutualTableOk mpI.base2 d capsOf b ctorsA sortss q.1 q.2 := by
        intro q hq
        refine (hmem q (List.mem_cons_of_mem _ hq)).cross (nF' := c.nF) (cty := cvCa.type)
          (tbl := ⟨f.cvTa.name, d.lps, d.nP, cvCa.name, c.nF, f.s, bodies,
            ConLeche.structProjGuards cvCa.type d.nP c.nF (sortss.getD J []), 1⟩)
          hfreshTbl hbodies ⟨.ctorInfo cvCa d.nP c.nF,
            ConLeche.Semantics.Env.find?_mem hfC, rfl⟩ hnp ?_ mpI.base2 hacI
        intro hh
        refine hnd.1 ?_
        show f.cvTa.name ∈ rest.map (·.1.cvTa.name)
        rw [show f.cvTa.name = q.1.cvTa.name from hh]
        exact List.mem_map_of_mem hq
      have hinvI : Inv mpI.base2 :=
        hInv mp.base2 ⟨f.cvTa.name, d.lps, d.nP, cvCa.name, c.nF, f.s, bodies,
            ConLeche.structProjGuards cvCa.type d.nP c.nF (sortss.getD J []), 1⟩
          hfreshTbl (fun tbl' heq i => by
            obtain rfl := ConstantInfo.projInfo.inj heq
            exact hnp i) hinv mpI.base2 hacI
      obtain ⟨mp', hoff, hoffS, hE'', hinv'⟩ := ih mpI hE' hrestRun hnd.2 hmemI hinvI
      refine ⟨mp', fun n hn => ?_, fun n hn => ?_, hE'', hinv'⟩
      · rw [hoff n (fun q hq => hn q (List.mem_cons_of_mem _ hq)), hacI,
          acvalWith_ne (hn (f, mIdx) List.mem_cons_self)]
      · -- a stored name is not the fresh table's
        have hne : n ≠ projTableName f.cvTa.name := by
          intro hh
          rw [hh] at hn
          have : (env.find? (projTableName f.cvTa.name)).isSome = true := hn
          rw [hfreshTbl] at this
          exact nomatch this
        have hnI : ((⟨.projInfo ⟨f.cvTa.name, d.lps, d.nP, cvCa.name, c.nF, f.s, bodies,
            ConLeche.structProjGuards cvCa.type d.nP c.nF (sortss.getD J []), 1⟩
            :: env.consts⟩ : Env).find? n).isSome = true := by
          rw [ConLeche.Env.find?_cons, if_neg (fun hh => hne hh.symm)]
          exact hn
        rw [hoffS n hnI, hacI, acvalWith_ne hne]

/-- **The table stage** (task #278 M2.5e): the run's final environment
carries an `EnvModelM` whose carrier agrees with the recursor store's
off the block's table names, and `EtaFamiliesClosed` survives. -/
theorem stageMutualTables {d : TableBlockData} {capsOf : Nat → IndCaps}
    {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {fms : List MutualFormerA} {env env' : Env} (mp : EnvModelM V μ env)
    (hlps : b.lps = d.lps) (hnP : b.nP = d.nP)
    (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss fms.zipIdx env = .ok env')
    (hnd : (fms.map (·.cvTa.name)).Nodup)
    (hmem : ∀ p ∈ fms.zipIdx, MutualTableOk mp.base2 d capsOf b ctorsA sortss p.1 p.2)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m : EnvModel V env') (tbl : ConLeche.ProjTable),
      env'.find? (ConstantInfo.projInfo tbl).name = none →
      ConsCrossEnv env' (.projInfo tbl) → Inv m →
      ∀ m₂ : EnvModel V ⟨.projInfo tbl :: env'.consts⟩,
        m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0) → Inv m₂)
    (hinv : Inv mp.base2) :
    ∃ mp' : EnvModelM V μ env',
      (∀ n : Name, (∀ f ∈ fms, n ≠ projTableName f.cvTa.name) →
        mp'.base2.acval n = mp.base2.acval n) ∧
      (∀ n : Name, (env.find? n).isSome = true →
        mp'.base2.acval n = mp.base2.acval n) ∧
      ConLeche.EtaFamiliesClosed env' ∧ Inv mp'.base2 := by
  have hnd' : ((fms.zipIdx).map (·.1.cvTa.name)).Nodup := by
    rw [show fms.zipIdx.map (·.1.cvTa.name) = fms.map (·.cvTa.name) from by
      rw [show (fun x : MutualFormerA × Nat => x.1.cvTa.name)
        = (fun f : MutualFormerA => f.cvTa.name) ∘ Prod.fst from rfl, ← List.map_map,
        List.zipIdx_map_fst]]
    exact hnd
  obtain ⟨mp', hoff, hoffS, hE', hinv'⟩ :=
    stageMutualTablesGo hlps hnP Inv hInv fms.zipIdx mp hE hrun hnd' hmem hinv
  refine ⟨mp', fun n hn => hoff n fun q hq => hn q.1 ?_, hoffS, hE', hinv'⟩
  have hget : fms[q.2]? = some q.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hq)
  exact List.mem_of_getElem? hget

end ConLeche.Model
