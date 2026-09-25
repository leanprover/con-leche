module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Semantics.NoBVar
import ConLeche.Semantics.Inductives.HoleApp
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.NestPosOut
public import ConLeche.Model.Inductives.HoleSubst
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Inductives.StructRead
import ConLeche.Model.Inductives.StructEntryFree
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.IndPointKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.IndSubst
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.StructBody
import ConLeche.Verify.Rules.InferBridge

public section

/-!
# Stored field shape facts (lane HOLE2, stage E2a)

**The interface.**  A block constructor's fields with holes `F` (the
member-abstracted stored field readings, members at the hole slots) and
its concrete stored field readings `S` are related by kind-free facts
(`StoredFieldShapes`):

* `holeApp`: every hole occurs applied to the parameters (M3, at
  every field, container fields included);
* `override`: `F` read with the members' leaf values in the hole slots is
  `S` — "members := their own values" is the stored reading.

**The producer** (`storedFieldShapes_of_walk`, the ONLY place that reads
the walk's syntax for these facts): the positivity walk on the stored
(DECLARED) constructor returns its normal form `tyN`
(`checkBlockPositivity_inv`); M3 is the walk's own check on `tyN`
(`holesApplied_openPis`, `holeApp_of_holesApplied`), and the
override by the substitution lemma iterated (`HoleSubst.lean`).  The
normal form reads like the declared crest along satisfying prefixes
(`FieldsEqOn`, from `red_sound` through `nestMemberCtor_red`,
`NestPosRed.lean`): the facts are about `tyN`'s fields, `D.fields`
reads them, and the declared type is tied to them only semantically
(lane ALPHA1).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  NestFieldKind nestAbstract nestHoles nestMemberCtor instPisWith openPisAtFvars fueledOps
  structUsedLater)

universe w

/-! ## Hole and field slots -/

namespace LfpDatum

/-- The hole positions at local depth `lo`: the variables `lo ..< lo + k`. -/
@[expose] def holeSlots (k lo : Nat) : Nat → Prop := fun i => lo ≤ i ∧ i < lo + k

/-- Field `l`'s variable, seen from depth `l'` (`l < l'`). -/
@[expose] def fieldSlot (l l' : Nat) : Nat → Prop := fun i => i = l' - 1 - l

end LfpDatum

/-! ## The interface -/

/-- **Stored field shape facts**: the fields with holes `F` against the
stored field readings `S` (see the module docstring); `leaf t` is member
`t`'s leaf (its former's reading); `Δp` the parameter context the override
is stated at (the fields with holes are the walk's NORMAL FORM, which
reads like the declared type only at frames satisfying the walk's
context — lane ALPHA1). -/
structure StoredFieldShapes (V : Type w) [SetTheory V] (k nP w : Nat) (nIdxOf : Nat → Nat)
    (leaf : Nat → AnnotTerm) (Δp : List AnnotTerm) (F S : List AnnotTerm) : Prop where
  len : F.length = S.length
  /-- every hole occurs applied to the parameters (M3 at every field;
  lane NESTKERN: a kind-free fact, true at container fields too, where
  the flat shape below is not) -/
  holeApp : ∀ (l : Nat) (F' : AnnotTerm), F[l]? = some F' → HoleApp k nP l F'
  override : ∀ hs : List V, hs.length = k →
    (∀ t, t < k → ∀ σ : Nat → V, interp V σ (leaf t) = hs.getD t pt) →
    ∀ (ρ : Nat → V), Sat V Δp ρ → ∀ l, l < F.length → ∀ (as : List V), as.length = l →
      SpineFit ρ (S.take l) as →
      interp V (consList as (consList hs ρ)) (F.getD l default)
        = interp V (consList as ρ) (S.getD l default)

/-- The facts read the members' leaves below `k` only. -/
theorem StoredFieldShapes.congr_leaf {V : Type w} [SetTheory V] {k nP w : Nat}
    {nIdxOf : Nat → Nat} {leaf leaf' : Nat → AnnotTerm} {Δp F S : List AnnotTerm}
    (h : StoredFieldShapes V k nP w nIdxOf leaf Δp F S) (hl : ∀ t, t < k → leaf t = leaf' t) :
    StoredFieldShapes V k nP w nIdxOf leaf' Δp F S :=
  ⟨h.len, h.holeApp,
    fun hs hhs hv => h.override hs hhs fun t ht σ => by rw [hl t ht]; exact hv t ht σ⟩

/-- A term reading no hole slot applies no hole. -/
theorem holeApp_of_noBVar {k nP lo : Nat} {e : AnnotTerm}
    (h : NoBVar (LfpDatum.holeSlots k lo) e) : HoleApp k nP lo e := by
  have h' : NoBVar (fun i => lo ≤ i ∧ i < lo + (List.replicate k AnnotTerm.prf).length) e := by
    rw [List.length_replicate]; exact h
  have := instAll_liftN_of_noBVar e (List.replicate k .prf) lo h'
  rw [List.length_replicate] at this
  rw [← this]
  exact holeApp_liftN k nP _ lo

/-! ## The walked term looks up no member

The member-abstracted constructor type mentions no member constant
(M2′, `nestNoMemberConst`), and no literal-support constant a reading
consults can be a member: `Nat.zero`/`Nat.succ` are constructors, the
string-support constants' types end in a constant (a member's in a
sort), and `Char` is mentioned by `Char.ofNat`'s stored type, so it is
older than the block.  So two leaf assignments agreeing off the members
read it alike (`denoteMeta_agree_of_readsAt`). -/

/-- A term free of member constants looks up no member, given that no
literal-support constant it may consult is one. -/
theorem Expr.readsAt_of_nestOcc {names : List Name} {lo hi : Nat} {env : Env}
    (hnat : ConLeche.natLitSupported env = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names)
    (hstr : ConLeche.strLitSupported env = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names) :
    ∀ e : Expr, e.nestOcc names lo hi = false → Expr.ReadsAt (· ∉ names) env e := by
  intro e
  induction e with
  | const n us =>
    intro h
    simpa [Expr.ReadsAt, Expr.nestOcc] using h
  | app f a ihf iha =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.nestOcc, Bool.or_eq_false_iff] at h
    exact ⟨iht h.1, ihb h.2⟩
  | proj s i e ihe => intro h; exact ihe h
  | lit l =>
    intro _
    cases l with
    | natVal n => exact hnat
    | strVal s =>
      intro hs
      have hn : ConLeche.natLitSupported env = true := by
        simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hs
        exact hs.1.1.1.1.1.1.1
      obtain ⟨h1, h2, h3, h4, h5⟩ := hstr hs
      exact ⟨h1, h2, h3, h4, h5, (hnat hn).1, (hnat hn).2⟩
  | _ => intro _; trivial

theorem piResult_of_stripPis_sort :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {s : Level},
      e.stripPis n = some (bs, .sort s) → e.piResult = .sort s
  | 0, e, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]; rfl
  | n + 1, e, bs, s, h => by
    match e with
    | .forallE ty b m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', r⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      show b.piResult = _
      exact piResult_of_stripPis_sort n hr
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [Expr.stripPis])

/-- **No literal-support constant a reading consults is a block member**
(see the section docstring): the members are `indInfo`s of the block's
environment whose types end in a sort, fresh before it, and the block's
environment agrees with the pre-block one off the members. -/
theorem blockMembers_notLit {env envI : Env} (hwf : ConLeche.EnvWF env)
    {cvTas : List ConstantVal} {names : List Name}
    (hnames : ∀ n, n ∈ names ↔ ∃ cvTb ∈ cvTas, cvTb.name = n)
    (hfindM : ∀ cvTb ∈ cvTas, (∃ caps, envI.find? cvTb.name = some (.indInfo cvTb caps)) ∧
      ∃ k bs s, cvTb.type.stripPis k = some (bs, .sort s))
    (hfresh : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none)
    (hI : ∀ n, (∀ cvTb ∈ cvTas, cvTb.name ≠ n) → envI.find? n = env.find? n) :
    (ConLeche.natLitSupported envI = true →
      ConLeche.natZeroName ∉ names ∧ ConLeche.natSuccName ∉ names) ∧
    (ConLeche.strLitSupported envI = true →
      ConLeche.stringOfListName ∉ names ∧ ConLeche.listNilName ∉ names ∧
        ConLeche.listConsName ∉ names ∧ ConLeche.charName ∉ names ∧
        ConLeche.charOfNatName ∉ names) := by
  -- a member: an `indInfo` whose type ends in a sort, fresh before the block
  have hmem : ∀ n ∈ names, ∃ cvTb caps s, envI.find? n = some (.indInfo cvTb caps) ∧
      cvTb.type.piResult = .sort s ∧ env.find? n = none := by
    intro n hn
    obtain ⟨cvTb, hcv, rfl⟩ := (hnames n).mp hn
    obtain ⟨⟨caps, hf⟩, k, bs, s, hs⟩ := hfindM cvTb hcv
    exact ⟨cvTb, caps, s, hf, piResult_of_stripPis_sort k hs, hfresh cvTb hcv⟩
  have hnm : ∀ n, n ∉ names → ∀ cvTb ∈ cvTas, cvTb.name ≠ n :=
    fun n hn cvTb hcv h => hn ((hnames n).mpr ⟨cvTb, hcv, h⟩)
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hs
    obtain ⟨⟨-, hZ⟩, hS⟩ := hs
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · obtain ⟨cvTb, caps, s, hf, -, -⟩ := hmem _ hn
      rw [hf] at hZ
      simp [ConLeche.natZeroOk] at hZ
    · obtain ⟨cvTb, caps, s, hf, -, -⟩ := hmem _ hn
      rw [hf] at hS
      simp [ConLeche.natSuccOk] at hS
  · simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hO⟩, -⟩, hNil⟩, hCons⟩, -⟩, hCO⟩ := hs
    have hO' : ConLeche.stringOfListName ∉ names := by
      intro hn
      obtain ⟨cvTb, caps, s, hf, hsort, -⟩ := hmem _ hn
      rw [hf] at hO
      simp only [ConLeche.stringOfListTyOk, Bool.and_eq_true] at hO
      obtain ⟨-, hO⟩ := hO
      change (match cvTb.type with
        | .forallE (.app (.const l1 us1) (.const c1 [])) (.const c2 []) _mb =>
          l1 == ConLeche.listName && us1 == [.zero] && c1 == ConLeche.charName &&
            c2 == ConLeche.stringName
        | _ => false) = true at hO
      split at hO
      · rename_i heq
        rw [heq] at hsort
        simp [ConLeche.Expr.piResult] at hsort
      · exact nomatch hO
    have hNil' : ConLeche.listNilName ∉ names := by
      intro hn
      obtain ⟨cvTb, caps, s, hf, hsort, -⟩ := hmem _ hn
      rw [hf] at hNil
      simp only [ConLeche.listNilTyOk] at hNil
      split at hNil
      · split at hNil
        · rename_i heq
          change cvTb.type = _ at heq
          rw [heq] at hsort
          simp [ConLeche.Expr.piResult] at hsort
        · exact nomatch hNil
      · exact nomatch hNil
    have hCons' : ConLeche.listConsName ∉ names := by
      intro hn
      obtain ⟨cvTb, caps, s, hf, hsort, -⟩ := hmem _ hn
      rw [hf] at hCons
      simp only [ConLeche.listConsTyOk] at hCons
      split at hCons
      · split at hCons
        · rename_i heq
          change cvTb.type = _ at heq
          rw [heq] at hsort
          simp [ConLeche.Expr.piResult] at hsort
        · exact nomatch hCons
      · exact nomatch hCons
    -- `Char.ofNat : Nat → Char` is stored with a non-sort result …
    obtain ⟨ci, hci⟩ : ∃ ci, envI.find? ConLeche.charOfNatName = some ci := by
      cases h : envI.find? ConLeche.charOfNatName with
      | none => rw [h] at hCO; exact nomatch hCO
      | some ci => exact ⟨ci, rfl⟩
    rw [hci] at hCO
    simp only [ConLeche.charOfNatTyOk, Bool.and_eq_true] at hCO
    obtain ⟨-, hCO⟩ := hCO
    obtain ⟨dom, m, hty, hc2⟩ : ∃ dom m, ci.toConstantVal.type
        = .forallE dom (.const ConLeche.charName []) m ∧ True := by
      split at hCO
      · rename_i c1 c2 mb heq
        simp only [Bool.and_eq_true, beq_iff_eq] at hCO
        exact ⟨_, mb, by rw [heq, hCO.2], trivial⟩
      · exact nomatch hCO
    have hCO' : ConLeche.charOfNatName ∉ names := by
      intro hn
      obtain ⟨cvTb, caps, s, hf, hsort, -⟩ := hmem _ hn
      rw [hf] at hci
      obtain rfl := Option.some.inj hci
      change cvTb.type = _ at hty
      rw [hty] at hsort
      simp [ConLeche.Expr.piResult] at hsort
    -- … so it is older than the block, and so is the `Char` it mentions
    have hciE : env.find? ConLeche.charOfNatName = some ci := by
      rw [← hI _ (hnm _ hCO')]; exact hci
    have hres := (hwf ci (List.mem_of_find?_eq_some hciE)).2.2.1
    rw [hty] at hres
    simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true] at hres
    have hChar' : ConLeche.charName ∉ names := by
      intro hn
      obtain ⟨-, -, -, -, -, hfr⟩ := hmem _ hn
      rw [hfr] at hres
      exact nomatch hres.2
    exact ⟨hO', hNil', hCons', hChar', hCO'⟩

/-! ## Reading the walked shapes -/

section Read

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {ψ : Name → Nat}

/-- The readings of a spine come from its terms. -/
theorem DenoteMetaSpine.mem_vals {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env ψ d as vs →
      ∀ v ∈ vs, ∃ a ∈ as, denoteMeta acval env ψ d a = some v
  | _, _, .nil, _, hv => nomatch hv
  | a :: _, _ :: _, .cons ha h, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨b, hb, hr⟩ := DenoteMetaSpine.mem_vals h v hv
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- The hole positions of the walk read, at depth `hiAt 0 + l`, as the
hole slots `l ..< l + k`. -/
theorem noBVar_holeSlots_of_holeP {ctx : NestCtx} {l : Nat} {e : AnnotTerm}
    (h : NoBVar (holeP (ctx.hiAt 0 + l) ctx.nP (ctx.hiAt 0)) e) :
    NoBVar (LfpDatum.holeSlots ctx.names.length l) e := by
  refine NoBVar.mono (fun i hi => ?_) h
  simp only [LfpDatum.holeSlots] at hi
  simp only [holeP, ConLeche.NestCtx.hiAt] at ⊢
  omega

/-- A hole-free term reads without the hole slots. -/
theorem noBVar_holeSlots_of_nestOcc {ctx : NestCtx} {l : Nat} {e : Expr} {ea : AnnotTerm}
    (hw : Expr.WScoped (ctx.hiAt 0 + l) e)
    (hocc : e.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false)
    (h : denoteMeta m.acval env ψ (ctx.hiAt 0 + l) e = some ea) :
    NoBVar (LfpDatum.holeSlots ctx.names.length l) ea :=
  noBVar_holeSlots_of_holeP (denoteMeta_noBVar_of_nestOcc _ e hw (by omega) hocc h)

/-- **A member hole applied to the parameter variables and hole-free
arguments** reads as the hole's slot applied to `holeParams` and
hole-free readings. -/
theorem denoteMeta_holeHead {ctx : NestCtx} {t l : Nat} {e : Expr} {ea : AnnotTerm}
    (hfn : ∃ ty, e.getAppFn = .fvar (ctx.nP + t) ty) (ht : t < ctx.names.length)
    (hps : ∀ p, p < ctx.nP → ∃ ty, e.getAppArgs[p]? = some (.fvar p ty))
    (hlen : ctx.nP ≤ e.getAppArgs.length)
    (hfree : ∀ x ∈ e.getAppArgs.drop ctx.nP, x.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false)
    (hw : Expr.WScoped (ctx.hiAt 0 + l) e)
    (hea : denoteMeta m.acval env ψ (ctx.hiAt 0 + l) e = some ea) :
    ∃ es, ea = AnnotTerm.mkAppN (.bvar (l + (ctx.names.length - 1 - t)))
        (holeParams ctx.names.length ctx.nP l ++ es) ∧
      (∀ x ∈ es, NoBVar (LfpDatum.holeSlots ctx.names.length l) x) ∧
      es.length = e.getAppArgs.length - ctx.nP ∧
      DenoteMetaSpine m.acval env ψ (ctx.hiAt 0 + l) (e.getAppArgs.drop ctx.nP) es := by
  obtain ⟨ty, hfn⟩ := hfn
  have hsp := Expr.mkAppN_getApp e
  rw [hfn] at hsp
  have hwArgs : ∀ a ∈ e.getAppArgs, Expr.WScoped (ctx.hiAt 0 + l) a := by
    have h0 := hw
    rw [← hsp] at h0
    exact (wScoped_mkAppN _ h0).2
  rw [← hsp] at hea
  obtain ⟨fa, vs, hfa, hspine, rfl⟩ := denoteMeta_mkAppN_inv hea
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  rw [← List.take_append_drop ctx.nP e.getAppArgs] at hspine
  obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := DenoteMetaSpine.append_inv hspine
  have hv₁ : vs₁ = paramBvarsAt ctx.nP (ctx.hiAt 0 + l) := by
    refine DenoteMetaSpine.unique h₁ (denoteMetaSpine_params _ (by simp; omega) ?_)
    intro p x hx
    have hp : p < ctx.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp at this; omega
    rw [List.getElem?_take_of_lt hp] at hx
    obtain ⟨ty', hty'⟩ := hps p hp
    rw [hty'] at hx
    exact ⟨ty', (Option.some.inj hx).symm⟩
  have hk : ctx.hiAt 0 + l = ctx.nP + ctx.names.length + l := by
    simp [ConLeche.NestCtx.hiAt]
  refine ⟨vs₂, ?_, fun x hx => ?_, ?_, h₂⟩
  · rw [hv₁, hk]
    unfold paramBvarsAt holeParams
    congr 1
    · congr 1; omega
    · congr 1
      refine List.map_congr_left fun p _ => ?_
      congr 1; omega
  · obtain ⟨a, ha, hr⟩ := DenoteMetaSpine.mem_vals h₂ x hx
    exact noBVar_holeSlots_of_nestOcc (hwArgs a (List.mem_of_mem_drop ha)) (hfree a ha) hr
  · rw [← DenoteMetaSpine.length_eq h₂, List.length_drop]

/-- An application spine grows at the right. -/
theorem AnnotTerm.mkAppN_snoc' :
    ∀ (as : List AnnotTerm) (f a : AnnotTerm),
      AnnotTerm.mkAppN f (as ++ [a]) = .app (AnnotTerm.mkAppN f as) a := by
  intro as
  induction as with
  | nil => intro f a; rfl
  | cons x xs ih => intro f a; exact ih (.app f x) a

/-! ## M3 and M2′ on the walk's normal form (lane NESTKERN, session 2)

`Expr.holesApplied` (the check `nestMemberCtor` runs on its normal form)
read at a model: the reading is `HoleApp` (every hole slot heads a spine
whose first `nP` arguments are the parameter slots) and the term names
no member constant — at every kind, containers included. -/

theorem holeParamsApp_nestOcc_zero {names : List Name} {lo hi : Nat} :
    ∀ (n : Nat) (e : Expr), e.holeParamsApp lo hi n = true → e.nestOcc names 0 0 = false
  | 0, .fvar i _, _ => by simp [ConLeche.Expr.nestOcc]
  | n + 1, .app f (.fvar j _), h => by
    simp only [ConLeche.Expr.holeParamsApp, Bool.and_eq_true] at h
    simp [ConLeche.Expr.nestOcc, holeParamsApp_nestOcc_zero n f h.2]
  | 0, .bvar _, h | 0, .sort _, h | 0, .const .., h | 0, .app .., h | 0, .lam .., h
  | 0, .forallE .., h | 0, .letE .., h | 0, .lit _, h | 0, .proj .., h => by
    simp [ConLeche.Expr.holeParamsApp] at h
  | _ + 1, .bvar _, h | _ + 1, .fvar .., h | _ + 1, .sort _, h | _ + 1, .const .., h
  | _ + 1, .lam .., h | _ + 1, .forallE .., h | _ + 1, .letE .., h | _ + 1, .lit _, h
  | _ + 1, .proj .., h => by simp [ConLeche.Expr.holeParamsApp] at h
  | _ + 1, .app _ (.bvar _), h | _ + 1, .app _ (.sort _), h | _ + 1, .app _ (.const ..), h
  | _ + 1, .app _ (.app ..), h | _ + 1, .app _ (.lam ..), h | _ + 1, .app _ (.forallE ..), h
  | _ + 1, .app _ (.letE ..), h | _ + 1, .app _ (.lit _), h | _ + 1, .app _ (.proj ..), h => by
    simp [ConLeche.Expr.holeParamsApp] at h

/-- **M2′ on the normal form**: a term the check passed names no member. -/
theorem holesApplied_nestOcc_zero {names : List Name} {nP hi : Nat} :
    ∀ (e : Expr), e.holesApplied names nP hi = true → e.nestOcc names 0 0 = false := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar i ty _ => intro _; simp [ConLeche.Expr.nestOcc]
  | sort u => intro _; rfl
  | const n us =>
    intro h
    simpa [ConLeche.Expr.holesApplied, ConLeche.Expr.nestOcc] using h
  | app f a ihf iha =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact holeParamsApp_nestOcc_zero _ _ h
    · simp [ConLeche.Expr.nestOcc, ihf h1, iha h2]
  | lam t b mm iht ihb =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp [ConLeche.Expr.nestOcc, iht h.1, ihb h.2]
  | forallE t b mm iht ihb =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp [ConLeche.Expr.nestOcc, iht h.1, ihb h.2]
  | letE t v b _ _ _ =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact nestOcc_zero_of _ h
  | lit l => intro _; rfl
  | proj s i e _ =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact nestOcc_zero_of _ h

/-- Instantiating a bound variable by a non-hole variable above the
parameters keeps a hole applied to exactly the parameters (and a term
that is not one, not one). -/
theorem holeParamsApp_instantiate1 {lo hi D : Nat} (hD : ¬ (lo ≤ D ∧ D < hi)) (ty : Expr) :
    ∀ (n : Nat) (e : Expr) (k : Nat), n ≤ D →
      (e.instantiate1 (.fvar D ty) k).holeParamsApp lo hi n = e.holeParamsApp lo hi n
  | 0, .bvar i, k, _ => by
    simp only [ConLeche.Expr.instantiate1]
    split
    · simp [ConLeche.Expr.holeParamsApp, hD]
    · split <;> simp [ConLeche.Expr.holeParamsApp]
  | n + 1, .bvar i, k, _ => by
    simp only [ConLeche.Expr.instantiate1]
    split
    · simp [ConLeche.Expr.holeParamsApp]
    · split <;> simp [ConLeche.Expr.holeParamsApp]
  | n + 1, .app f a, k, hn => by
    have ih := holeParamsApp_instantiate1 hD ty n f k (by omega)
    cases a with
    | bvar i =>
      simp only [ConLeche.Expr.instantiate1]
      split
      · simp only [ConLeche.Expr.holeParamsApp]
        have : (D == n) = false := by simp; omega
        simp [this]
      · split <;> simp [ConLeche.Expr.holeParamsApp]
    | fvar j t => simp [ConLeche.Expr.instantiate1, ConLeche.Expr.holeParamsApp, ih]
    | _ => simp [ConLeche.Expr.instantiate1, ConLeche.Expr.holeParamsApp]
  | 0, .fvar .., _, _ | 0, .sort _, _, _ | 0, .const .., _, _ | 0, .app .., _, _
  | 0, .lam .., _, _ | 0, .forallE .., _, _ | 0, .letE .., _, _ | 0, .lit _, _, _
  | 0, .proj .., _, _ => by simp [ConLeche.Expr.instantiate1, ConLeche.Expr.holeParamsApp]
  | _ + 1, .fvar .., _, _ | _ + 1, .sort _, _, _ | _ + 1, .const .., _, _
  | _ + 1, .lam .., _, _ | _ + 1, .forallE .., _, _ | _ + 1, .letE .., _, _
  | _ + 1, .lit _, _, _ | _ + 1, .proj .., _, _ => by
    simp [ConLeche.Expr.instantiate1, ConLeche.Expr.holeParamsApp]

/-- The check survives instantiating a bound variable by a variable above
the holes. -/
theorem holesApplied_instantiate1 {names : List Name} {nP hi D : Nat} (hD : hi ≤ D)
    (hP : nP ≤ D) (ty : Expr) :
    ∀ (e : Expr) (k : Nat), e.holesApplied names nP hi = true →
      (e.instantiate1 (.fvar D ty) k).holesApplied names nP hi = true := by
  have hD' : ¬ (nP ≤ D ∧ D < hi) := by omega
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [ConLeche.Expr.instantiate1]
    split
    · simp [ConLeche.Expr.holesApplied, hD']
    · split <;> rfl
  | fvar i t _ => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [ConLeche.Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at h
    have hpa := holeParamsApp_instantiate1 hD' ty nP (.app f a) k hP
    simp only [ConLeche.Expr.instantiate1] at hpa ⊢
    simp only [ConLeche.Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true, hpa]
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨ihf k h1, iha k h2⟩
  | lam t b mm iht ihb =>
    intro k h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b mm iht ihb =>
    intro k h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.holesApplied, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v b _ _ _ =>
    intro k h
    have := nestOcc_instantiate1_fvar (names := names) hD' ty (.letE t v b) k
    simp only [ConLeche.Expr.instantiate1] at this ⊢
    simp only [ConLeche.Expr.holesApplied] at h ⊢
    rw [this]; exact h
  | proj s i e _ =>
    intro k h
    have := nestOcc_instantiate1_fvar (names := names) hD' ty (.proj s i e) k
    simp only [ConLeche.Expr.instantiate1] at this ⊢
    simp only [ConLeche.Expr.holesApplied] at h ⊢
    rw [this]; exact h

/-- A hole applied to exactly the parameter variables reads as its slot
applied to the parameter slots. -/
theorem denoteMeta_holeParamsApp {lo hi d : Nat} :
    ∀ (n : Nat) (e : Expr) {ea : AnnotTerm}, e.holeParamsApp lo hi n = true →
      denoteMeta m.acval env ψ d e = some ea →
      ∃ i, lo ≤ i ∧ i < hi ∧
        ea = AnnotTerm.mkAppN (.bvar (d - 1 - i)) ((List.range n).map fun p => .bvar (d - 1 - p))
  | 0, .fvar i _, ea, h, hr => by
    simp only [ConLeche.Expr.holeParamsApp, decide_eq_true_eq] at h
    rw [denoteMeta] at hr
    cases hr
    exact ⟨i, h.1, h.2, rfl⟩
  | n + 1, .app f (.fvar j _), ea, h, hr => by
    simp only [ConLeche.Expr.holeParamsApp, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hf⟩ := h
    rw [denoteMeta] at hr
    rcases hfa : denoteMeta m.acval env ψ d f with _ | fa
    · rw [hfa] at hr; exact nomatch hr
    rw [hfa] at hr
    simp only [denoteMeta, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hr
    obtain ⟨i, h1, h2, rfl⟩ := denoteMeta_holeParamsApp j f hf hfa
    refine ⟨i, h1, h2, ?_⟩
    rw [← hr, List.range_succ, List.map_append, List.map_cons, List.map_nil, AnnotTerm.mkAppN_snoc']
  | 0, .bvar _, _, h, _ | 0, .sort _, _, h, _ | 0, .const .., _, h, _ | 0, .app .., _, h, _
  | 0, .lam .., _, h, _ | 0, .forallE .., _, h, _ | 0, .letE .., _, h, _ | 0, .lit _, _, h, _
  | 0, .proj .., _, h, _ => by simp [ConLeche.Expr.holeParamsApp] at h
  | _ + 1, .bvar _, _, h, _ | _ + 1, .fvar .., _, h, _ | _ + 1, .sort _, _, h, _
  | _ + 1, .const .., _, h, _ | _ + 1, .lam .., _, h, _ | _ + 1, .forallE .., _, h, _
  | _ + 1, .letE .., _, h, _ | _ + 1, .lit _, _, h, _ | _ + 1, .proj .., _, h, _ => by
    simp [ConLeche.Expr.holeParamsApp] at h
  | _ + 1, .app _ (.bvar _), _, h, _ | _ + 1, .app _ (.sort _), _, h, _
  | _ + 1, .app _ (.const ..), _, h, _ | _ + 1, .app _ (.app ..), _, h, _
  | _ + 1, .app _ (.lam ..), _, h, _ | _ + 1, .app _ (.forallE ..), _, h, _
  | _ + 1, .app _ (.letE ..), _, h, _ | _ + 1, .app _ (.lit _), _, h, _
  | _ + 1, .app _ (.proj ..), _, h, _ => by simp [ConLeche.Expr.holeParamsApp] at h

/-- A term free of members and holes reads as `HoleApp` at the hole
slots of its depth. -/
theorem holeApp_of_nestOcc {ctx : NestCtx} {d : Nat} {e : Expr} {ea : AnnotTerm}
    (hw : Expr.WScoped d e) (hd : ctx.hiAt 0 ≤ d)
    (hocc : e.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false)
    (h : denoteMeta m.acval env ψ d e = some ea) :
    HoleApp ctx.names.length ctx.nP (d - ctx.hiAt 0) ea := by
  obtain ⟨l, rfl⟩ : ∃ l, d = ctx.hiAt 0 + l := ⟨d - ctx.hiAt 0, by omega⟩
  rw [show ctx.hiAt 0 + l - ctx.hiAt 0 = l by omega]
  exact holeApp_of_noBVar (noBVar_holeSlots_of_nestOcc hw hocc h)

/-- **M3 on the normal form, read**: a term the check passed reads, at
any depth above the holes, as `HoleApp` at that depth's hole slots. -/
theorem holeApp_of_holesApplied {ctx : NestCtx} :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm}, Expr.WScoped d e → ctx.hiAt 0 ≤ d →
      e.holesApplied ctx.names ctx.nP (ctx.hiAt 0) = true →
      denoteMeta m.acval env ψ d e = some ea →
      HoleApp ctx.names.length ctx.nP (d - ctx.hiAt 0) ea := by
  have hhi : ctx.hiAt 0 = ctx.nP + ctx.names.length := by simp [ConLeche.NestCtx.hiAt]
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    cases h; exact .sort
  | case2 d idx ty =>
    intro ea hws hd hha h
    rw [denoteMeta] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.holesApplied, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hha
    rcases hha with hpa | hnot
    · -- `nP = 0`: the bare hole is the hole applied to no parameter
      cases hnP : ctx.nP with
      | succ n => rw [hnP] at hpa; simp [ConLeche.Expr.holeParamsApp] at hpa
      | zero =>
        rw [hnP] at hpa
        simp only [ConLeche.Expr.holeParamsApp, decide_eq_true_eq] at hpa
        have := HoleApp.hole (k := ctx.names.length) (nP := 0) (lo := d - ctx.hiAt 0)
          (h := d - 1 - idx) (rest := []) (by omega) (by omega) (fun r hr => nomatch hr)
        simpa [holeParams, hnP] using this
    · refine .bvar fun ⟨h1, h2⟩ => hnot ⟨?_, ?_⟩ <;> omega
  | case3 d n us ci hf hlen =>
    intro ea hws hd hha h
    refine holeApp_of_nestOcc hws hd ?_ h
    simpa [ConLeche.Expr.holesApplied, ConLeche.Expr.nestOcc] using hha
  | case4 d n us ci hf hlen =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea _ _ _ h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ea hws hd hha h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at hha
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hha' := holesApplied_instantiate1 hd (by omega) ty body 0 hha.2
    have hb := ihbody hws' (by omega) hha' hba
    rw [show d + 1 - ctx.hiAt 0 = d - ctx.hiAt 0 + 1 by omega] at hb
    exact .pi (ihty hws.1 hd hha.1 hta) hb
  | case7 d ty body mb ihty ihbody =>
    intro ea hws hd hha h
    rw [denoteMeta] at h
    rcases hta : denoteMeta m.acval env ψ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta m.acval env ψ (d + 1) (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    cases h
    simp only [Expr.WScoped] at hws
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at hha
    have hws' : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      Expr.WScoped.instantiate1 hws.1 0 hws.2
    have hha' := holesApplied_instantiate1 hd (by omega) ty body 0 hha.2
    have hb := ihbody hws' (by omega) hha' hba
    rw [show d + 1 - ctx.hiAt 0 = d - ctx.hiAt 0 + 1 by omega] at hb
    exact .lam (ihty hws.1 hd hha.1 hta) hb
  | case8 d fe a ihf iha =>
    intro ea hws hd hha h
    simp only [ConLeche.Expr.holesApplied, Bool.or_eq_true, Bool.and_eq_true] at hha
    rcases hha with hpa | ⟨h1, h2⟩
    · obtain ⟨i, hi1, hi2, rfl⟩ := denoteMeta_holeParamsApp ctx.nP _ hpa h
      simp only [Expr.WScoped] at hws
      have := HoleApp.hole (k := ctx.names.length) (nP := ctx.nP) (lo := d - ctx.hiAt 0)
        (h := d - 1 - i) (rest := []) (by omega) (by omega) (fun r hr => nomatch hr)
      rw [List.append_nil] at this
      have hp : holeParams ctx.names.length ctx.nP (d - ctx.hiAt 0)
          = (List.range ctx.nP).map fun p => AnnotTerm.bvar (d - 1 - p) := by
        unfold holeParams
        refine List.map_congr_left fun p hp => ?_
        have := List.mem_range.mp hp
        congr 1
        omega
      rw [hp] at this
      exact this
    · rw [denoteMeta] at h
      rcases hfa : denoteMeta m.acval env ψ d fe with _ | fa
      · rw [hfa] at h; exact nomatch h
      rw [hfa] at h
      rcases haa : denoteMeta m.acval env ψ d a with _ | aa
      · rw [haa] at h; exact nomatch h
      rw [haa] at h
      cases h
      simp only [Expr.WScoped] at hws
      exact .app (ihf hws.1 hd h1 hfa) (iha hws.2 hd h2 haa)
  | case9 d ty val body =>
    intro ea _ _ _ h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea hws hd hha h
    refine holeApp_of_nestOcc hws hd ?_ h
    simpa [ConLeche.Expr.holesApplied] using hha
  | case11 | case12 | case13 | case14 =>
    intro ea hws hd hha h
    refine holeApp_of_nestOcc hws hd ?_ h
    simpa [ConLeche.Expr.holesApplied] using hha
  | case15 d x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    intro ea _ _ _ h
    cases x with
    | bvar i => simp [denoteMeta] at h
    | sort u => exact (h1 u rfl).elim
    | fvar i t => exact (h2 i t rfl).elim
    | const n us => exact (h3 n us rfl).elim
    | forallE t b mm => exact (h4 t b mm rfl).elim
    | lam t b mm => exact (h5 t b mm rfl).elim
    | app f a => exact (h6 f a rfl).elim
    | letE t v b => exact (h7 t v b rfl).elim
    | proj sn i e => exact (h8 sn i e rfl).elim
    | lit l => cases l with
      | natVal n => exact (h9 n rfl).elim
      | strVal s => exact (h10 s rfl).elim

/-- An opening at variables above the holes keeps the check, on every
opened domain and on the body. -/
theorem holesApplied_openPis {names : List Name} {nP hi : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {xs : List Expr} {r : Expr},
      openPisAtFvars n e d = some (xs, r) → hi ≤ d → nP ≤ d →
      e.holesApplied names nP hi = true →
      (∀ x ∈ xs, x.fvarTypeD.holesApplied names nP hi = true) ∧
        r.holesApplied names nP hi = true
  | 0, e, d, xs, r, h, _, _, he => by
    simp only [openPisAtFvars] at h
    cases h
    exact ⟨(fun _ hx => nomatch hx), he⟩
  | n + 1, e, d, xs, r, h, hd, hp, he => by
    match e, h with
    | .forallE dom b bm, h =>
      simp only [openPisAtFvars] at h
      split at h
      · rename_i xs' r' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at he
        obtain ⟨h1, h2⟩ := holesApplied_openPis n h' (by omega) (by omega)
          (holesApplied_instantiate1 hd hp dom b 0 he.2)
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact h1 x hx
      · exact nomatch h

end Read

/-! ## The producer's syntactic lemmas -/

/-- Two telescopes erasure-equal open to erasure-equal bodies. -/
theorem openPisAtFvars_erasedEq_body :
    ∀ (n : Nat) {e e' : Expr} {d : Nat} {xs xs' : List Expr} {r r' : Expr},
      Expr.ErasedEq e e' → openPisAtFvars n e d = some (xs, r) →
      openPisAtFvars n e' d = some (xs', r') → Expr.ErasedEq r r'
  | 0, e, e', d, xs, xs', r, r', he, h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨-, rfl⟩ := h
    obtain ⟨-, rfl⟩ := h'
    exact he
  | n + 1, e, e', d, xs, xs', r, r', he, h, h' => by
    cases e with
    | forallE t b bm =>
      cases e' with
      | forallE t' b' bm' =>
        obtain ⟨-, -, hb⟩ := he
        simp only [openPisAtFvars] at h h'
        split at h
        · rename_i fvs o hop
          split at h'
          · rename_i fvs' o' hop'
            simp only [Option.some.injEq, Prod.mk.injEq] at h h'
            obtain ⟨-, rfl⟩ := h
            obtain ⟨-, rfl⟩ := h'
            exact openPisAtFvars_erasedEq_body n
              (Expr.ErasedEq.instantiate1 (v := .fvar d t) (v' := .fvar d t') hb rfl) hop hop'
          · exact nomatch h'
        · exact nomatch h
      | _ => simp [Expr.ErasedEq] at he
    | _ => simp [openPisAtFvars] at h

/-- A telescope opening `n` binders strips every shorter prefix. -/
theorem stripPis_isSome_of_inst_fvar {d : Nat} {ty : Expr} :
    ∀ (k : Nat) (b : Expr) (j : Nat), ((b.instantiate1 (.fvar d ty) j).stripPis k).isSome = true →
      (b.stripPis k).isSome = true
  | 0, b, j, _ => by simp [Expr.stripPis]
  | k + 1, b, j, h => by
    cases b with
    | forallE t body mb =>
      simp only [Expr.instantiate1, Expr.stripPis, Option.isSome_map] at h ⊢
      exact stripPis_isSome_of_inst_fvar k body (j + 1) h
    | bvar i =>
      simp only [Expr.instantiate1] at h
      split at h
      · simp [Expr.stripPis] at h
      · split at h <;> simp [Expr.stripPis] at h
    | _ => simp [Expr.instantiate1, Expr.stripPis] at h

theorem stripPis_of_openPis :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars n e d = some (fvs, body) → ∀ j, j ≤ n → (e.stripPis j).isSome = true
  | _, e, _, _, _, _, 0, _ => by simp [Expr.stripPis]
  | 0, _, _, _, _, _, _ + 1, hj => absurd hj (by omega)
  | n + 1, e, d, fvs, body, h, j + 1, hj => by
    cases e with
    | forallE t b bm =>
      simp only [openPisAtFvars] at h
      split at h
      · rename_i fvs' o hop
        simp only [Expr.stripPis, Option.isSome_map]
        exact stripPis_isSome_of_inst_fvar j b 0 (stripPis_of_openPis n hop j (by omega))
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

/-- A lift by one never reads its cut. -/
theorem noBVar_liftN_one : ∀ (X : AnnotTerm) (c : Nat), NoBVar (fun i => i = c) (X.liftN 1 c) := by
  intro X
  induction X with
  | bvar i =>
    intro c
    show ¬ ((if i < c then i else i + 1) = c)
    split <;> omega
  | sort u => intro c; trivial
  | const k us => intro c; trivial
  | prf => intro c; trivial
  | app f a ihf iha => intro c; exact ⟨ihf c, iha c⟩
  | eqE a b iha ihb => intro c; exact ⟨iha c, ihb c⟩
  | fst e ih => intro c; exact ih c
  | snd e ih => intro c; exact ih c
  | lam u A b ihA ihb =>
    intro c
    refine ⟨ihA c, NoBVar.mono (fun i hi => ?_) (ihb (c + 1))⟩
    cases i with
    | zero => exact absurd hi (by simp [shiftP])
    | succ i => show i + 1 = c + 1; simp only [shiftP] at hi; omega
  | pi u v A B ihA ihB =>
    intro c
    refine ⟨ihA c, NoBVar.mono (fun i hi => ?_) (ihB (c + 1))⟩
    cases i with
    | zero => exact absurd hi (by simp [shiftP])
    | succ i => show i + 1 = c + 1; simp only [shiftP] at hi; omega

/-- Erasure keeps the variable bound. -/
theorem erasedEq_fvarsBelow {d : Nat} :
    ∀ (a b : Expr), Expr.ErasedEq a b → Expr.fvarsBelow d a → Expr.fvarsBelow d b := by
  intro a
  induction a with
  | fvar i ty _ => intro b h ha; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarsBelow]
  | bvar i => intro b h _; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarsBelow]
  | sort u => intro b h _; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarsBelow]
  | const n us => intro b h _; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarsBelow]
  | lit l => intro b h _; cases b <;> simp_all [Expr.ErasedEq, Expr.fvarsBelow]
  | app f a ihf iha =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    exact ⟨ihf _ h.1 ha.1, iha _ h.2 ha.2⟩
  | lam t bd mm iht ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    exact ⟨iht _ h.2.1 ha.1, ihb _ h.2.2 ha.2⟩
  | forallE t bd mm iht ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    exact ⟨iht _ h.2.1 ha.1, ihb _ h.2.2 ha.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    exact ⟨iht _ h.1 ha.1, ihv _ h.2.1 ha.2.1, ihb _ h.2.2 ha.2.2⟩
  | proj s i e ih =>
    intro b h ha
    cases b <;> simp only [Expr.ErasedEq] at h
    rename_i s' i' e'
    exact ih e' h.2.2 ha

/-! ## The members' holes, as leaves -/

/-- **Every leaf at a member hole's index carries that member's stored
type** (the walked term's hole variables are `nestHoles`'). -/
@[expose] def HoleLeafOk (ctx : NestCtx) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, ctx.nP ≤ l.1 → l.1 < ctx.hiAt 0 →
    ∃ cv caps, ctx.find? (ctx.names.getD (l.1 - ctx.nP) .anonymous) = some (.indInfo cv caps) ∧
      l.2 = cv.type

theorem HoleLeafOk.open {ctx : NestCtx} {n : Nat} {e : Expr} {d : Nat} {fvs : List Expr}
    {body : Expr} (h : HoleLeafOk ctx e) (hd : ctx.hiAt 0 ≤ d)
    (hop : openPisAtFvars n e d = some (fvs, body)) :
    HoleLeafOk ctx body ∧ ∀ x ∈ fvs, HoleLeafOk ctx x.fvarTypeD := by
  have hidx := ConLeche.openPisAtFvars_index n e d hop
  have key : ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) → l.1 < ctx.hiAt 0 →
      l ∈ e.fvarLeaves := by
    intro l hl hlt
    rcases ConLeche.Verify.openPisAtFvars_leaves n hop l hl with h1 | h1
    · exact h1
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem h1
      obtain ⟨ty, hty⟩ := hidx j _ hj
      simp only [Expr.fvar.injEq] at hty
      omega
  refine ⟨fun l hl h1 h2 => h l (key l (Or.inl hl) h2) h1 h2,
    fun x hx l hl h1 h2 => h l (key l (Or.inr ⟨x, hx, ?_⟩) h2) h1 h2⟩
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, rfl⟩ := hidx j x hj
  simp only [Expr.fvarTypeD] at hl
  simp [Expr.fvarLeaves, hl]

/-- The walked term's leaves: the parameters' (below `nP`) and the holes'. -/
theorem holeLeafOk_crest {ctx : NestCtx} {holes : List Expr} {cty crest : Expr}
    (hholes : nestHoles ctx = some holes)
    (hcl : ∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.hasFvar = false)
    (hparW : ∀ x ∈ ctx.params, Expr.WScoped ctx.nP x) (hcf : cty.hasFvar = false)
    (hcrest : instPisWith ctx.params (nestAbstract ctx holes cty) = some crest) :
    HoleLeafOk ctx crest := by
  intro l hl h1 h2
  rcases ConLeche.fvarLeaves_instPisWith hcrest l hl with h | ⟨a, ha, h'⟩
  · obtain ⟨c', us, r, hr, hlr⟩ := ConLeche.fvarLeaves_replaceConsts_closed _ hcf l h
    have hrm : r ∈ holes := by
      split at hr
      · split at hr
        · exact List.mem_of_getElem? hr
        · exact nomatch hr
      · exact nomatch hr
    obtain ⟨i, cv, caps, hf, rfl⟩ := ConLeche.nestHoles_mem hholes r hrm
    have hnil : cv.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar (hcl _ _ hf)
    simp only [Expr.fvarLeaves, hnil, List.mem_cons, List.not_mem_nil, or_false] at hlr
    subst hlr
    exact ⟨cv, caps, by simpa using hf, rfl⟩
  · have := Expr.fvarLeaves_lt_of_wscoped (hparW a ha) l h'
    omega

/-! ## The producer's reading lemmas -/

section Producer

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {ψ : Name → Nat}

/-- **U4, read**: a field whose variable no later binder and not the result
uses is read by no later field — at any base depth (lane ACCMODEL session 3:
a container frame's telescope). -/
theorem u4_fieldSlotAt {b nF l l' : Nat} {crest rest : Expr} {xs : List Expr}
    {x : Expr} {ea : AnnotTerm}
    (hop : openPisAtFvars nF crest (b) = some (xs, rest))
    (hW : Expr.WScoped (b) crest) (hU : structUsedLater crest 0 l = false)
    (hl : l < nF) (hll : l < l') (hx : xs[l']? = some x)
    (hr : denoteMeta m.acval env ψ (b + l') x.fvarTypeD = some ea) :
    NoBVar (LfpDatum.fieldSlot l l') ea := by
  obtain ⟨⟨bs, r⟩, hst⟩ := Option.isSome_iff_exists.mp
    (stripPis_of_openPis nF hop (l + 1) (by omega))
  have hfree : r.hasLooseBVar 0 = false := by
    unfold structUsedLater at hU
    rw [Nat.zero_add, hst] at hU
    simpa [Expr.hasLooseBVarB_eq] using hU
  obtain ⟨h1, -⟩ := openPisAtFvars_leaf_free nF l hop hl hst hfree fun z hz => by
    have := Expr.fvarLeaves_lt_of_wscoped hW z hz
    omega
  have hxfree : ∀ z ∈ x.fvarTypeD.fvarLeaves, z.1 ≠ b + l := by
    intro z hz
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF crest (b) hop l' x hx
    exact h1 l' hll _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])
  have hwx := openPisAtFvars_typeWScoped nF hop hW l' x hx
  obtain ⟨X, rfl⟩ := denoteMeta_liftN_of_leaf_free m _ _ hwx (q := b + l) (by omega)
    hxfree hr
  refine NoBVar.mono (fun i hi => ?_) (noBVar_liftN_one X _)
  simp only [LfpDatum.fieldSlot] at hi
  omega

/-- **U4, read**: a field whose variable no later binder and not the result
uses is read by no later field. -/
theorem u4_fieldSlot {ctx : NestCtx} {nF l l' : Nat} {crest rest : Expr} {xs : List Expr}
    {x : Expr} {ea : AnnotTerm}
    (hop : openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) crest) (hU : structUsedLater crest 0 l = false)
    (hl : l < nF) (hll : l < l') (hx : xs[l']? = some x)
    (hr : denoteMeta m.acval env ψ (ctx.hiAt 0 + l') x.fvarTypeD = some ea) :
    NoBVar (LfpDatum.fieldSlot l l') ea :=
  u4_fieldSlotAt hop hW hU hl hll hx hr

end Producer

/-! ## The producer -/

/-- **A stored block constructor's kind-free facts**: its reading (the
Π-tower over `ds ψ` ending in the family at the parameters and `Es ψ`),
its opening at the canonical variables (parameters at `0 ..< nP`, fields
at `nP ..< nP + nF`), and its opened result: the member `T` at the
parameter variables and the index arguments.  `CtorDataI`'s reading
facts and `BlockCtorDataI`'s opening facts, without any field kind
(`BlockCtorDataI.storedCtorFacts`). -/
structure StoredCtorFacts {V : Type w} [SetTheory V] {env : Env} (m : EnvModel V env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF : Nat) (fvsP xFvs : List Expr) (xrest : Expr)
    (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (Es : (Name → Nat) → List AnnotTerm) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvC.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  len : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  lenE : ∀ ψ : Name → Nat, (Es ψ).length = idxArgs.length
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  pLen : fvsP.length = nP
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  resShape : xrest = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)
  hasFvar : cvC.type.hasFvar = false
  bounded : cvC.type.looseBVarsBounded 0 = true

/-- `BlockCtorDataI`, with the stored type's closedness. -/
theorem BlockCtorDataI.storedCtorFacts {V : Type w} [SetTheory V] {env : Env}
    {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat}
    {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {fvsP xFvs : List Expr} {xrest : Expr}
    (h : BlockCtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs fvsP xFvs
      xrest)
    (hf : cvC.type.hasFvar = false) (hb : cvC.type.looseBVarsBounded 0 = true) :
    StoredCtorFacts m T lps cvC nP nF fvsP xFvs xrest idxArgs ds Es :=
  ⟨h.read, h.len, fun ψ => by rw [h.lenE ψ, h.idxLen], h.opens, h.pLen, h.pIdx, h.resShape, hf, hb⟩

/-- **THE PRODUCER of the stored field shape facts** — the only place that
reads a stored constructor's syntax for them.  From the install's
positivity run at a stored (DECLARED) constructor of the block — the walk
takes the member-abstracted crest `crest` to its normal form `tyN` with
flat kinds; U2's sort row on `tyN`'s fields — the constructor's kind-free
facts, the members' formers, and the walk's semantic link (`hlink`, from
`nestMemberCtor_red`: the crest and the normal form read as Π-towers with
the same body whose fields read alike at every frame satisfying the walk's
context `Δh`): the crest reads, at the walk's depth, as a Π-tower over
`abD` and the normal form over `abN`, both ending in the constructor's
member hole at the parameters and the result indices `E` (the stored
result index readings lifted over the holes), and `abN`'s readings are the
fields with holes of `StoredFieldShapes` against the stored field readings:
M3 (the walk's check on its normal form), and the override through the
declared crest (substitution, at every frame) and the link (at frames
satisfying the walk's context, `hsatH`). -/
theorem storedFieldShapes_of_walk {V : Type w} [SetTheory V] {env : Env} (m : EnvModel V env)
    (ψ : Name → Nat) {F : Nat} {ctx : NestCtx} {holes : List Expr}
    (hfind : ctx.find? = env.find?) (hholes : nestHoles ctx = some holes)
    (hnd : ctx.names.Nodup) (hplen : ctx.params.length = ctx.nP)
    (hpar : ∀ (p : Nat) (x : Expr), ctx.params[p]? = some x → ∃ ty, x = .fvar p ty)
    (hparW : ∀ x ∈ ctx.params, Expr.WScoped ctx.nP x) {w : Nat}
    (hformers : ∀ t, t < ctx.names.length → ∃ cv caps bs s,
      env.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) ∧
      cv.levelParams = ctx.lps ∧
      cv.type.stripPis (ctx.nP + ctx.nIdxs.getD t 0) = some (bs, .sort s) ∧ s.eval ψ = w)
    {c nF : Nat} (hc : c < ctx.names.length) {cvC : ConstantVal} {fvsP xFvs : List Expr}
    {xrest : Expr} {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm}
    (hD : StoredCtorFacts m (ctx.names.getD c .anonymous) ctx.lps cvC ctx.nP nF fvsP xFvs xrest
      idxArgs ds Es)
    {crest : Expr} (hcrest : instPisWith ctx.params (nestAbstract ctx holes cvC.type) = some crest)
    {tyN : Expr} {st₀ st₁ : NestState} {ks : List NestFieldKind}
    (hwalk : nestMemberCtor (fueledOps .verified F) env ctx nF crest st₀ = .ok (ks, tyN, st₁))
    (hU2 : ∃ (isProp : Bool) (xq : List Expr × Expr) (sorts : List Level),
      openPisAtFvars nF tyN (ctx.hiAt 0) = some xq ∧
      ConLeche.checkStructFieldSortsI (fueledOps .verified F) env isProp false ctx.sort
        (ctx.hiAt 0) xq.1 [] nF = .ok sorts)
    {Δp Δh : List AnnotTerm}
    (hlink : ∀ ca : AnnotTerm, denoteMeta m.acval env ψ (ctx.hiAt 0) crest = some ca →
      ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ca = mkPisAV abD B ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
      abD.length = nF ∧ abN.length = nF ∧
      FieldsEqOn V Δh (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Rules.Frame (ctx.hiAt 0) tyN ∧ Rules.LeavesSub tyN crest)
    (hsatH : ∀ hs : List V, hs.length = ctx.names.length →
      (∀ t, t < ctx.names.length → ∀ σ : Nat → V,
        interp V σ (m.acval (ctx.names.getD t .anonymous) ψ) = hs.getD t pt) →
      ∀ ρ : Nat → V, Sat V Δp ρ → Sat V Δh (consList hs ρ)) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (E : List AnnotTerm),
      denoteMeta m.acval env ψ (ctx.hiAt 0) crest
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (nF + (ctx.names.length - 1 - c)))
            (paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + nF) ++ E))) ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0) tyN
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (nF + (ctx.names.length - 1 - c)))
            (paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + nF) ++ E))) ∧
      abD.length = nF ∧ abN.length = nF ∧ E = (Es ψ).map (·.liftN ctx.names.length nF) ∧
      StoredFieldShapes V ctx.names.length ctx.nP w (fun t => ctx.nIdxs.getD t 0)
        (fun t => m.acval (ctx.names.getD t .anonymous) ψ) Δp (abN.map (·.2.2))
        (((ds ψ).drop ctx.nP).map (·.2.2)) := by
  classical
  -- ## the context
  have henv : ConLeche.EnvWF env := m.wf
  have hcl : ∀ n ci, ctx.find? n = some ci → ci.toConstantVal.type.hasFvar = false := by
    intro n ci hf
    rw [hfind] at hf
    exact (henv ci (List.mem_of_find?_eq_some hf)).1
  have hhi : ctx.hiAt 0 = ctx.nP + ctx.names.length := by simp [ConLeche.NestCtx.hiAt]
  have hlenH : holes.length = ctx.names.length := ConLeche.nestHoles_length hholes
  have hholeAt : ∀ t, t < ctx.names.length → ∃ cv caps,
      ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) ∧
      holes[t]? = some (.fvar (ctx.nP + t) cv.type) :=
    fun t ht => ConLeche.nestHoles_getElem? hholes ht
  have hholesOk : ∀ x ∈ holes, Expr.WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty := by
    intro x hx
    obtain ⟨t, htx⟩ := List.getElem?_of_mem hx
    have ht : t < ctx.names.length := by
      rw [← hlenH]; exact (List.getElem?_eq_some_iff.mp htx).1
    obtain ⟨cv, caps, hf, hget⟩ := hholeAt t ht
    rw [htx] at hget
    obtain rfl := Option.some.inj hget
    refine ⟨?_, _, _, rfl⟩
    simp only [Expr.WScoped]
    exact ⟨by rw [hhi]; omega, Expr.WScoped.of_not_hasFvar (hcl _ _ hf)⟩
  have hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty := fun h hm => (hholesOk h hm).2
  have hparW' : ∀ x ∈ ctx.params, Expr.WScoped (ctx.hiAt 0) x :=
    fun x hx => Expr.WScoped.mono (by rw [hhi]; omega) (hparW x hx)
  have hW : Expr.WScoped (ctx.hiAt 0) crest :=
    ConLeche.memberCrest_wscoped hholesOk hparW' hD.hasFvar hcrest
  have hB : crest.looseBVarsBounded 0 = true := by
    refine ConLeche.looseBVarsBounded_instPisWith (fun a ha => ?_) ?_ hcrest
    · obtain ⟨p, hp⟩ := List.getElem?_of_mem ha
      obtain ⟨ty, rfl⟩ := hpar p a hp
      rfl
    · unfold nestAbstract
      refine ConLeche.looseBVarsBounded_replaceConsts (fun c us r hr => ?_) _ 0 hD.bounded
      split at hr
      · split at hr
        · obtain ⟨i, ty, rfl⟩ := hh r (List.mem_of_getElem? hr)
          rfl
        · exact nomatch hr
      · exact nomatch hr
  -- ## the walk: the declared crest opened as the walk opened it
  obtain ⟨err, nds, rest, hfw, hrw, -, -, hresFree, hha⟩ := nestMemberCtor_inv hwalk
  obtain ⟨xs, hop, -, -, -⟩ := nestFields_inv nF 0 crest st₀ ks nds rest st₁ hfw hrw
  rw [Nat.add_zero] at hop
  -- ## the concrete reading, peeled past the parameters
  obtain ⟨crestc, hopP, hopX⟩ := hD.opens
  have hlenD := hD.len ψ
  have hreadc : denoteMeta m.acval env ψ ctx.nP crestc = some (mkPisAV ((ds ψ).drop ctx.nP)
      (ctorBodyAVI m (ctx.names.getD c .anonymous) ctx.nP nF ψ (Es ψ))) := by
    have hr := hD.read ψ
    rw [← List.take_append_drop ctx.nP (ds ψ), mkPisAV_append'] at hr
    have := (denoteMeta_peel ctx.nP hopP (by rw [List.length_take]; omega) hr).1
    simpa using this
  -- ## the walked term is the concrete one, abstracted (up to erasure)
  have hwc : Expr.WScoped ctx.nP crestc := by
    have := (ConLeche.openPisAtFvars_WScoped ctx.nP cvC.type 0 hopP
      (Expr.WScoped.of_not_hasFvar hD.hasFvar)).2
    rwa [Nat.zero_add] at this
  have hA₂ := nestAbstract_instPisWith (ctx := ctx) hh (instPisWith_of_openPis ctx.nP hopP)
  have hvars : ∀ x ∈ fvsP, ∃ i ty, x = .fvar i ty := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, h⟩ := hD.pIdx q x hq
    exact ⟨q, ty, h⟩
  have hparE : Expr.ErasedEqL ctx.params (fvsP.map (nestAbstract ctx holes)) :=
    Expr.ErasedEqL.trans
      (erasedEqL_of_fvarIdx ctx.params fvsP 0
        (fun i x hx => by
          obtain ⟨ty, h⟩ := hpar i x hx
          exact ⟨ty, by rw [h, Nat.zero_add]⟩)
        (fun i x hx => by
          obtain ⟨ty, h⟩ := hD.pIdx i x hx
          exact ⟨ty, by rw [h, Nat.zero_add]⟩)
        (by rw [hplen, hD.pLen]))
      (erasedEqL_map_nestAbstract hvars)
  obtain ⟨crest', hc', herased⟩ := instPisWith_erasedEq hparE (Expr.ErasedEq.rfl _) hcrest
  rw [hA₂] at hc'
  obtain rfl := Option.some.inj hc'
  -- ## the members, substituted back
  obtain ⟨Ts, hTs⟩ : ∃ Ts : List Expr, Ts = (List.range ctx.names.length).map
      fun t => Expr.const (ctx.names.getD t .anonymous) (ctx.lps.map .param) := ⟨_, rfl⟩
  obtain ⟨leaves, hleaves⟩ : ∃ leaves : List AnnotTerm, leaves = (List.range ctx.names.length).map
      fun t => m.acval (ctx.names.getD t .anonymous) ψ := ⟨_, rfl⟩
  have hTsL : Ts.length = ctx.names.length := by simp [hTs]
  have hleavesL : leaves.length = ctx.names.length := by simp [hleaves]
  have herase2 : Expr.ErasedEq (substAll ctx.nP Ts (nestAbstract ctx holes crestc)) crestc := by
    refine substAll_replaceConsts_erasedEq (fun a ha => ?_) (fun c' us e he => ?_) crestc
      hwc.fvarsBelow
    · rw [hTs] at ha
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨_, _, rfl⟩
    · split at he
      · rename_i hus
        split at he
        · rename_i mm hmm
          obtain ⟨hmmlt, hmmeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmm
          obtain ⟨cv, caps, -, hget⟩ := hholeAt mm hmmlt
          rw [he] at hget
          obtain rfl := Option.some.inj hget
          refine ⟨mm, cv.type, rfl, ?_⟩
          rw [hTs, List.getElem?_map, List.getElem?_range hmmlt, Option.map_some]
          simp only [beq_iff_eq] at hmmeq hus
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmmlt, Option.getD_some, hmmeq,
            hus]
        · exact nomatch he
      · exact nomatch he
  have hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : AnnotTerm) (k : Nat),
      (m.acval n ψ').inst y k = m.acval n ψ' :=
    fun n ψ' y k => AVExprSubst.inst_eq_self_of_closed (m.acval_closed n ψ') y k
  have hleafRead : ∀ t, t < ctx.names.length → ∀ d, denoteMeta m.acval env ψ d
      (.const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
        = some (m.acval (ctx.names.getD t .anonymous) ψ) := by
    intro t ht d
    obtain ⟨cv, caps, bs, s, hf, hlps, -, -⟩ := hformers t ht
    rw [denoteMeta_const hf (by simp [ConstantInfo.toConstantVal, hlps])]
    simp only [ConstantInfo.toConstantVal, hlps, ConLeche.Level.substFn_param_self]
  have hsubst := denoteMeta_substAll (env := env) (φ := ψ) m.acval_closed hainst Ts leaves
    (by rw [hTsL, hleavesL])
    (fun i a x ha hx => by
      have hi : i < ctx.names.length := by
        have := (List.getElem?_eq_some_iff.mp ha).1
        simpa [hTs] using this
      rw [hTs, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.some.injEq] at ha
      rw [hleaves, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.some.injEq] at hx
      subst ha hx
      exact ⟨by simp [Expr.WScoped], rfl, hleafRead i hi⟩)
    ctx.nP ctx.nP (nestAbstract ctx holes crestc) (Nat.le_refl _)
    (by
      rw [hTsL, ← hhi]
      exact erasedEq_fvarsBelow _ _ herased hW.fvarsBelow)
  have hRc : (denoteMeta m.acval env ψ (ctx.hiAt 0) crest).map (instAll leaves 0)
      = some (mkPisAV ((ds ψ).drop ctx.nP)
          (ctorBodyAVI m (ctx.names.getD c .anonymous) ctx.nP nF ψ (Es ψ))) := by
    rw [← hreadc, ← denoteMeta_erasedEq herase2 ctx.nP, hsubst, denoteMeta_erasedEq herased,
      hTsL, hhi, Nat.sub_self]
  obtain ⟨R, hR, hRi⟩ := Option.map_eq_some_iff.mp hRc
  obtain ⟨pps, Bb, hst, hBb, hppl, hdoms⟩ := denoteMeta_openPis nF hop hR
  obtain ⟨rfl, -⟩ := stripPisAV_eq_mkPis hst
  rw [instAll_mkPisAV] at hRi
  obtain ⟨hTele, hBody⟩ := mkPisAV_inj
    (by rw [instTele_length, hppl, List.length_drop, hlenD]; omega) hRi
  rw [Nat.zero_add, hppl] at hBody
  -- ## the result: the constructor's member hole at the parameters and the indices
  have hnA : nestAbstract ctx holes crestc = holeAbs ctx holes crestc := by
    unfold holeAbs
    rw [Expr.shiftFromN_eq_self_of_fvarsBelow _ hwc.fvarsBelow]
  have hopA := openPisAtFvars_holeAbs (ctx := ctx) hh nF (j := 0) (by rw [Nat.add_zero]; exact hopX)
  have hopA' : openPisAtFvars nF (holeAbs ctx holes crestc) (ctx.hiAt 0)
      = some (xFvs.map (holeAbs ctx holes), holeAbs ctx holes xrest) := by
    rw [hhi]; simpa using hopA
  obtain ⟨cvc, capsc, -, hholeC⟩ := hholeAt c hc
  have hrestE : Expr.ErasedEq rest (Expr.mkAppN (.fvar (ctx.nP + c) cvc.type)
      ((fvsP ++ idxArgs).map (holeAbs ctx holes))) := by
    have h1 := openPisAtFvars_erasedEq_body nF (Expr.ErasedEq.trans herased
      (Expr.ErasedEq.of_eq hnA)) hop hopA'
    rwa [hD.resShape, holeAbs_mkAppN, holeAbs_member hnd hc hholeC] at h1
  obtain ⟨hfnE, hlenE, hargE⟩ := erasedEq_getApp _ _ hrestE
  rw [Expr.getAppFn_mkAppN] at hfnE
  rw [Expr.getAppArgs_mkAppN] at hlenE hargE
  simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append] at hfnE hlenE hargE
  have hfnR : ∃ ty, rest.getAppFn = .fvar (ctx.nP + c) ty := by
    cases hq : rest.getAppFn <;> rw [hq] at hfnE <;> simp only [Expr.ErasedEq] at hfnE
    subst hfnE
    exact ⟨_, rfl⟩
  have hlenR : rest.getAppArgs.length = ctx.nP + idxArgs.length := by
    rw [hlenE, List.length_map, List.length_append, hD.pLen]
  have hparR : ∀ p, p < ctx.nP → ∃ ty, rest.getAppArgs[p]? = some (.fvar p ty) := by
    intro p hp
    have hpl := hD.pLen
    obtain ⟨y, hy⟩ : ∃ y, rest.getAppArgs[p]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨x, hx⟩ : ∃ x, fvsP[p]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ty, rfl⟩ := hD.pIdx p x hx
    obtain ⟨ty', hty'⟩ := holeAbs_fvar_lt ctx holes hp ty
    have hy' := hargE p y _ hy (by
      rw [List.getElem?_map, List.getElem?_append_left (by omega), hx, Option.map_some, hty'])
    cases y <;> simp only [Expr.ErasedEq] at hy'
    subst hy'
    exact ⟨_, hy⟩
  have hwr : Expr.WScoped (ctx.hiAt 0 + nF) rest :=
    (ConLeche.openPisAtFvars_WScoped nF crest (ctx.hiAt 0) hop hW).2
  obtain ⟨E, hBbE, hEfree, hElen, -⟩ := denoteMeta_holeHead (m := m) (ψ := ψ) (l := nF) hfnR hc
    hparR (by omega) hresFree hwr hBb
  have hEl : E.length = idxArgs.length := by rw [hElen, hlenR]; omega
  have hmap : E.map (instAll leaves nF) = Es ψ := by
    have h2 := hBody
    rw [hBbE, instAll_mkAppN, List.map_append] at h2
    have hhead : instAll leaves nF (.bvar (nF + (ctx.names.length - 1 - c)))
        = m.acval (ctx.names.getD c .anonymous) ψ := by
      refine instAll_bvar_mid leaves (fun y hy k => ?_) ?_ (by rw [hleavesL]; omega)
      · rw [hleaves] at hy
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hy
        exact m.acval_closed _ _ k
      · rw [hleavesL, show ctx.names.length - 1 - (ctx.names.length - 1 - c) = c by omega, hleaves,
          List.getElem?_map, List.getElem?_range hc, Option.map_some]
    have hpar2 : (holeParams ctx.names.length ctx.nP nF).map (instAll leaves nF)
        = paramBvars ctx.nP nF := by
      unfold holeParams paramBvars
      rw [List.map_map]
      refine List.map_congr_left fun p hp => ?_
      have hp' := List.mem_range.mp hp
      simp only [Function.comp_apply]
      rw [instAll_bvar_ge leaves (by rw [hleavesL]; omega), hleavesL]
      congr 1
      omega
    rw [hhead, hpar2] at h2
    unfold ctorBodyAVI at h2
    obtain ⟨-, h3⟩ := AnnotTerm.mkAppN_inj h2 (by simp [paramBvars, hEl, hD.lenE ψ])
    exact List.append_cancel_left h3
  have hE : E = (Es ψ).map (·.liftN ctx.names.length nF) := by
    rw [← hmap, List.map_map]
    refine (List.map_id E).symm.trans (List.map_congr_left fun e he => ?_)
    have := instAll_liftN_of_noBVar e leaves nF (by rw [hleavesL]; exact hEfree e he)
    rw [hleavesL] at this
    exact this.symm
  -- ## the normal form: the link, its reading and its fields
  obtain ⟨abD, abN, B₀, hRD, hRN, hlD, hlN, hEqF, hfrN, hsubN⟩ := hlink _ hR
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (hppl.trans hlD.symm) hRD
  obtain ⟨hWN, -, -⟩ := hfrN
  obtain ⟨isProp, ⟨xsN, restN⟩, sorts, hopN, hsorts⟩ := hU2
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  obtain ⟨ppsN, BbN, hstN, -, -, hdomsN⟩ := denoteMeta_openPis nF hopN hRN
  rw [← hlN, stripPisAV_mkPisAV] at hstN
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hstN).symm
  have hformer' : ∀ t, t < ctx.names.length → ∀ cv caps,
      ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) →
      ∃ bs s, cv.type.stripPis (ctx.nP + ctx.nIdxs.getD t 0) = some (bs, .sort s) ∧
        s.eval ψ = w := by
    intro t ht cv caps hf
    obtain ⟨cv', caps', bs, s, hf', -, hst, hs⟩ := hformers t ht
    rw [hfind, hf'] at hf
    simp only [Option.some.injEq, ConstantInfo.indInfo.injEq] at hf
    obtain ⟨rfl, -⟩ := hf
    exact ⟨bs, s, hst, hs⟩
  have hleafCrest : HoleLeafOk ctx crest := holeLeafOk_crest hholes hcl hparW hD.hasFvar hcrest
  have hleafN : HoleLeafOk ctx tyN := fun l hl h1 h2 => hleafCrest l (hsubN l hl) h1 h2
  have hleafX := (hleafN.open (Nat.le_refl _) hopN).2
  have hSget : ∀ l p, pps[l]? = some p →
      (((ds ψ).drop ctx.nP).map (·.2.2)).getD l default = instAll leaves l p.2.2 := by
    intro l p hp
    rw [← hTele, List.getD_eq_getElem?_getD, List.getElem?_map, instTele_getElem?, hp]
    simp
  have hFgetD : ∀ l p, pps[l]? = some p → (pps.map (·.2.2)).getD l default = p.2.2 := by
    intro l p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rfl
  have hFget : ∀ l p, ppsN[l]? = some p → (ppsN.map (·.2.2)).getD l default = p.2.2 := by
    intro l p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rfl
  have hfield : ∀ l, l < nF → ∃ x p, xsN[l]? = some x ∧ ppsN[l]? = some p ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0 + l) x.fvarTypeD = some p.2.2 := by
    intro l hl
    have hxlN : xsN.length = nF := ConLeche.Verify.openPisAtFvars_length nF hopN
    obtain ⟨x, hx⟩ : ∃ x, xsN[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p, hp, -, hr⟩ := hdomsN l x hx
    exact ⟨x, p, hx, hp, hr⟩
  have hHP : holeParams ctx.names.length ctx.nP nF
      = paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + nF) := by
    unfold holeParams paramBvarsAt
    refine List.map_congr_left fun p hp => ?_
    have := List.mem_range.mp hp
    congr 1
    omega
  -- the declared fields at the leaves' values are the stored ones, at every frame
  have hdecl : ∀ (hs : List V), hs.length = ctx.names.length →
      (∀ t, t < ctx.names.length → ∀ σ : Nat → V,
        interp V σ (m.acval (ctx.names.getD t .anonymous) ψ) = hs.getD t pt) →
      ∀ (l : Nat) (as : List V) (ρ : Nat → V), l < nF → as.length = l →
        interp V (consList as (consList hs ρ)) ((pps.map (·.2.2)).getD l default)
          = interp V (consList as ρ) ((((ds ψ).drop ctx.nP).map (·.2.2)).getD l default) := by
    intro hs hsl hv l as ρ hl has
    obtain ⟨p, hp⟩ : ∃ p, pps[l]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hFgetD l p hp, hSget l p hp, ← has]
    refine (interp_instAll leaves hs (by rw [hleavesL, hsl]) (fun i y g hy hg σ => ?_) p.2.2 as
      ρ).symm
    have hi : i < ctx.names.length := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      rwa [hleavesL] at this
    rw [hleaves, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at hy
    subst hy
    rw [hv i hi σ, List.getD_eq_getElem?_getD, hg]
    rfl
  -- M3 at every field, containers included: the walk's check on its normal form
  have hholeApp : ∀ (l : Nat) (F' : AnnotTerm), (ppsN.map (·.2.2))[l]? = some F' →
      HoleApp ctx.names.length ctx.nP l F' := by
    intro l F' hF'
    have hl : l < nF := by
      have := (List.getElem?_eq_some_iff.mp hF').1
      simpa [hlN] using this
    obtain ⟨x, p, hx, hp, hread⟩ := hfield l hl
    rw [List.getElem?_map, hp, Option.map_some, Option.some.injEq] at hF'
    subst hF'
    have hwx : Expr.WScoped (ctx.hiAt 0 + l) x.fvarTypeD :=
      openPisAtFvars_typeWScoped nF hopN hWN l x hx
    have hhx := (holesApplied_openPis nF hopN (Nat.le_refl _) (by rw [hhi]; omega) hha).1 x
      (List.mem_of_getElem? hx)
    have := holeApp_of_holesApplied (m := m) (ψ := ψ) (ctx := ctx) _ _ hwx (by omega) hhx hread
    rwa [show ctx.hiAt 0 + l - ctx.hiAt 0 = l by omega] at this
  refine ⟨pps, ppsN, E, ?_, ?_, hlD, hlN, hE, ⟨by simp [hlN, hlenD], hholeApp, ?_⟩⟩
  · -- the crest's reading
    rw [hR, hBbE, hHP]
  · -- the normal form's reading
    rw [hRN, hBbE, hHP]
  · -- the override: through the declared crest (at every frame) and the link (at frames
    -- satisfying the walk's context)
    intro hs hsl hv ρ hρ l hl as has hfit
    have hl' : l < nF := by simpa [hlN] using hl
    have hfitD : SpineFit (consList hs ρ) ((pps.map (·.2.2)).take l) as := by
      refine (spineFit_congr_all (by simp [hlD, hlenD]) (fun i as' hi has' => ?_) as).mpr hfit
      have hil : i < l := by simp only [List.length_take, List.length_map, hlD] at hi; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hil, ← List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD (l := List.take l _), List.getElem?_take_of_lt hil,
        ← List.getD_eq_getElem?_getD]
      exact hdecl hs hsl hv i as' ρ (by omega) has'
    rw [← hdecl hs hsl hv l as ρ hl' has]
    exact (hEqF.getD_eq (hsatH hs hsl hv ρ hρ) l as (by simp [hlD, hl']) hfitD).symm

end ConLeche.Model
