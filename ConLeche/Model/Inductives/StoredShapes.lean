module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Semantics.NoBVar
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.ErasureKit
public import ConLeche.Model.Inductives.HoleSubst
public import ConLeche.Model.Inductives.HoleKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.IndPointKit
import ConLeche.Model.IndSubst
import ConLeche.Verify.Inductives.ScopeKit
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Denote.TeleOpen

public section

/-!
# Stored field shape facts

**The interface.**  A block constructor's fields with holes `F` (the
member-abstracted stored field readings, members at the hole slots) and
its concrete stored field readings `S` are related by kind-free facts
(`StoredFieldShapes`):

* `holeApp`: every hole occurs applied to the parameters (M3, at
  every field, container fields included);
* `override`: `F` read with the members' leaf values in the hole slots is
  `S` — "members := their own values" is the stored reading.

**The producer** of the old route (`storedFieldShapes_of_walk`, in
`StoredShapesWalk.lean`) reads them off the positivity walk's
derivation; this file holds the interface, its consequences, and a
stored constructor's kind-free facts (`StoredCtorFacts`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal NestCtx nestAbstract nestHoles
  instPisWith openPisAtFvars fueledOps structUsedLater)

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
context). -/
structure StoredFieldShapes (V : Type w) [SetTheory V] (k nP w : Nat) (nIdxOf : Nat → Nat)
    (leaf : Nat → AnnotTerm) (Δp : List AnnotTerm) (F S : List AnnotTerm) : Prop where
  len : F.length = S.length
  /-- every hole occurs applied to the parameters (M3 at every field: a
  kind-free fact, true at container fields too) -/
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
  obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := DenoteMetaSpine.split _ hspine
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

/-! ## M3 and M2′ on the walk's normal form

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
  | letE t v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp [ConLeche.Expr.nestOcc, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit l => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.holesApplied] at h
    simp [ConLeche.Expr.nestOcc, ih h]

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
  | letE t v b iht ihv ihb =>
    intro k h
    simp only [ConLeche.Expr.holesApplied, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.holesApplied, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [ConLeche.Expr.holesApplied] at h
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.holesApplied]
    exact ih k h

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

/-- `HoleApp` is closed under the uniform projection spelling. -/
theorem holeApp_projAV {k nP lo : Nat} :
    ∀ (j : Nat) {e : AnnotTerm}, HoleApp k nP lo e → HoleApp k nP lo (projAV j e)
  | 0, _, h => .fst h
  | j + 1, _, h => holeApp_projAV j (.snd h)

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
    -- a projection reads as `.fst ∘ .snd^j` of its struct's reading: the
    -- holes there are applied, and `HoleApp` is closed under `fst`/`snd`
    intro ea hws hd hha h
    simp only [ConLeche.Expr.holesApplied] at hha
    simp only [Expr.WScoped] at hws
    rw [denoteMeta] at h
    rcases hsub : denoteMeta m.acval env ψ d e with _ | sa
    · rw [hsub] at h; exact nomatch h
    rw [hsub] at h
    have hs := ihe hws hd hha hsub
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h; exact holeApp_projAV _ hs
    · rcases i with _ | _ | i
      · cases h; exact .fst hs
      · cases h; exact .snd hs
      · exact nomatch h
  | case11 | case12 | case13 | case14 =>
    intro ea hws hd hha h
    refine holeApp_of_nestOcc hws hd ?_ h
    simp [ConLeche.Expr.nestOcc]
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
        exact Verify.stripPis_instantiate1_fvar_isSome_rev (e := b) j 0 (stripPis_of_openPis n hop j (by omega))
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

/-! ## A stored constructor's kind-free facts -/

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

end ConLeche.Model
