module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Semantics.NoBVar
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Verify.Inductives.UniformOcc
import ConLeche.Verify.Inductives.HoleBack
import ConLeche.Model.Inductives.HoleOverride
public import ConLeche.Verify.Inductives.PosDeriv
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.IndPointKit
import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.Annot.BitInst
import ConLeche.Model.IndSubst
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Denote.TeleOpen

public section

/-!
# Stored field shape facts

**The interface.**  A block constructor's fields with holes `F` (the
member-abstracted stored field readings, the members' whole applications
at the hole slots) and its concrete stored field readings `S` are related
by a kind-free fact (`StoredFieldShapes`):

* `override`: `F` read with, at each hole slot, the member's value
  APPLIED TO THE PARAMETERS is `S` — "each hole := the application it
  stands for" is the stored reading.

**The producer** (`storedFieldShapes_of_walk`, the ONLY place that reads
the walk's syntax for these facts): the positivity walk on the stored
(DECLARED) constructor returns its normal form `tyN`, read off its
derivation (`MemberCtorD`); the override by ONE parallel substitution
putting the whole applications back (`Expr.substFvars_replaceApps_erasedEq`,
read by `denoteMeta_substFvars`, `substE_holeBack`).  The
normal form reads like the declared crest along satisfying prefixes
(`FieldsEqOn`, from `red_sound` through `memberCtorD_red`,
`NestPosRed.lean`): the facts are about `tyN`'s fields, `D.fields`
reads them, and the declared type is tied to them only semantically.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal NestCtx nestHoles
  instPisWith openPisAtFvars fueledOps structUsedLater)

universe w

open ConLeche.Semantics.AnnotTerm in
/-- A term closed in the lifting sense is fixed by every lift. -/
theorem liftN_closed {x : AnnotTerm} (hx : ∀ k, x.liftN 1 k = x) :
    ∀ (n k : Nat), x.liftN n k = x
  | 0, k => liftN_zero x k
  | n + 1, k => by
    rw [show n + 1 = 1 + n by omega, ← liftN_liftN x 1 n k, liftN_closed hx n k, hx k]

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
  override : ∀ (ρ : Nat → V), Sat V Δp ρ → ∀ hs : List V, hs.length = k →
    (∀ t, t < k → hs.getD t pt = (frameIdx nP ρ).foldl app (interp V ρ (leaf t))) →
    ∀ l, l < F.length → ∀ (as : List V), as.length = l →
      SpineFit ρ (S.take l) as →
      interp V (consList as (consList hs ρ)) (F.getD l default)
        = interp V (consList as ρ) (S.getD l default)

/-- The facts read the members' leaves below `k` only. -/
theorem StoredFieldShapes.congr_leaf {V : Type w} [SetTheory V] {k nP w : Nat}
    {nIdxOf : Nat → Nat} {leaf leaf' : Nat → AnnotTerm} {Δp F S : List AnnotTerm}
    (h : StoredFieldShapes V k nP w nIdxOf leaf Δp F S) (hl : ∀ t, t < k → leaf t = leaf' t) :
    StoredFieldShapes V k nP w nIdxOf leaf' Δp F S :=
  ⟨h.len, fun ρ hρ hs hhs hv => h.override ρ hρ hs hhs fun t ht => by rw [hl t ht]; exact hv t ht⟩

/-! ## The walked term looks up no member

The member-abstracted constructor type mentions no member constant
(official's uniform check, `nestUniform`), and no literal-support constant a reading
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

/-- **A member hole applied to hole-free arguments** reads as the hole's
slot applied to hole-free readings. -/
theorem denoteMeta_holeHead {ctx : NestCtx} {t l : Nat} {e : Expr} {ea : AnnotTerm}
    (hfn : ∃ ty, e.getAppFn = .fvar (ctx.nP + t) ty) (ht : t < ctx.names.length)
    (hfree : ∀ x ∈ e.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false)
    (hw : Expr.WScoped (ctx.hiAt 0 + l) e)
    (hea : denoteMeta m.acval env ψ (ctx.hiAt 0 + l) e = some ea) :
    ∃ es, ea = AnnotTerm.mkAppN (.bvar (l + (ctx.names.length - 1 - t))) es ∧
      (∀ x ∈ es, NoBVar (LfpDatum.holeSlots ctx.names.length l) x) ∧
      es.length = e.getAppArgs.length ∧
      DenoteMetaSpine m.acval env ψ (ctx.hiAt 0 + l) e.getAppArgs es := by
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
  have hk : ctx.hiAt 0 + l = ctx.nP + ctx.names.length + l := by
    simp [ConLeche.NestCtx.hiAt]
  refine ⟨vs, ?_, fun x hx => ?_, (DenoteMetaSpine.length_eq hspine).symm, hspine⟩
  · rw [hk]; congr 2; omega
  · obtain ⟨a, ha, hr⟩ := DenoteMetaSpine.mem_vals hspine x hx
    exact noBVar_holeSlots_of_nestOcc (hwArgs a ha) (hfree a ha) hr

/-- An application spine grows at the right. -/
theorem AnnotTerm.mkAppN_snoc' :
    ∀ (as : List AnnotTerm) (f a : AnnotTerm),
      AnnotTerm.mkAppN f (as ++ [a]) = .app (AnnotTerm.mkAppN f as) a := by
  intro as
  induction as with
  | nil => intro f a; rfl
  | cons x xs ih => intro f a; exact ih (.app f x) a

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

/-! ## The members' holes, as leaves -/

/-- **Every leaf at a member hole's index carries that member's hole
type** — its former at the canonical parameters (the walked term's hole
variables are `nestHoles`'). -/
@[expose] def HoleLeafOk (ctx : NestCtx) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, ctx.nP ≤ l.1 → l.1 < ctx.hiAt 0 →
    ∃ cv caps ty, ctx.find? (ctx.names.getD (l.1 - ctx.nP) .anonymous) = some (.indInfo cv caps) ∧
      instPisWith ctx.params cv.type = some ty ∧ l.2 = ty

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
    (hcrest : ConLeche.nestCrest ctx.names (ctx.lps.map .param) ctx.params holes cty = some crest) :
    HoleLeafOk ctx crest := by
  intro l hl h1 h2
  have hlenH := ConLeche.nestHoles_length hholes
  obtain ⟨a, ha, hla⟩ := ConLeche.fvarLeaves_nestCrest hcf (by omega) hcrest l hl
  rcases List.mem_append.mp ha with ha | ha
  · have := Expr.fvarLeaves_lt_of_wscoped (hparW a ha) l hla
    omega
  · obtain ⟨i, cv, caps, ty, hf, hty, rfl⟩ := ConLeche.nestHoles_mem hholes a ha
    simp only [Expr.fvarLeaves, List.mem_cons] at hla
    rcases hla with rfl | hla
    · exact ⟨cv, caps, ty, by simpa using hf, hty, rfl⟩
    · -- a leaf of the hole's type is a parameter's
      have hwt : Expr.WScoped ctx.nP ty :=
        ConLeche.wscoped_instPisWith hparW (Expr.WScoped.of_not_hasFvar (hcl _ _ hf)) hty
      have := Expr.fvarLeaves_lt_of_wscoped hwt l hla
      omega

/-! ## The producer's reading lemmas -/

section Producer

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {ψ : Name → Nat}

/-- **U4, read**: a field whose variable no later binder and not the result
uses is read by no later field — at any base depth (a container frame's
telescope). -/
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

/-- Spines of erasure-equal heads and arguments are erasure-equal. -/
private theorem erasedEq_mkAppN_congr :
    ∀ {as bs : List Expr} {f g : Expr}, Expr.ErasedEq f g → Expr.ErasedEqL as bs →
      Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN g bs)
  | [], [], _, _, h, _ => h
  | _ :: as, _ :: bs, _, _, h, ⟨hab, hrest⟩ => erasedEq_mkAppN_congr (as := as) (bs := bs)
      (show Expr.ErasedEq (.app _ _) (.app _ _) from ⟨h, hab⟩) hrest

/-- **THE PRODUCER of the stored field shape facts** — the only place that
reads a stored constructor's syntax for them.  From the install's
positivity run at a stored (DECLARED) constructor of the block — the walk
takes the crest `crest` (every whole member application abstracted,
`nestCrest`) to its normal form `tyN` — the constructor's kind-free facts, the members' formers, and the walk's
semantic link (`hlink`, from `memberCtorD_red`: the crest and the normal
form read as Π-towers with the same body whose fields read alike at every
frame satisfying the walk's context `Δh`): the crest reads, at the walk's
depth, as a Π-tower over `abD` and the normal form over `abN`, both ending
in the constructor's member hole applied to the result indices `E` (the
stored result index readings lifted over the holes), and `abN`'s readings
are the fields with holes of `StoredFieldShapes` against the stored field
readings: the override through the declared crest (the whole applications
put back by one parallel substitution, at every parameter frame) and the
link (at frames satisfying the walk's context, `hsatH`). -/
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
    {crest : Expr}
    (hcrest : ConLeche.nestCrest ctx.names (ctx.lps.map .param) ctx.params holes cvC.type
      = some crest)
    {tyN : Expr} {ksD : List ConLeche.NestFieldKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env ctx nF crest ksD tyN ts)
    {Δp Δh : List AnnotTerm}
    (hlink : ∀ ca : AnnotTerm, denoteMeta m.acval env ψ (ctx.hiAt 0) crest = some ca →
      ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ca = mkPisAV abD B ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
      abD.length = nF ∧ abN.length = nF ∧
      FieldsEqOn V Δh (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Rules.Frame (ctx.hiAt 0) tyN ∧ Rules.LeavesSub tyN crest)
    (hsatH : ∀ ρ : Nat → V, Sat V Δp ρ → ∀ hs : List V, hs.length = ctx.names.length →
      (∀ t, t < ctx.names.length →
        hs.getD t pt = (frameIdx ctx.nP ρ).foldl app
          (interp V ρ (m.acval (ctx.names.getD t .anonymous) ψ))) →
      Sat V Δh (consList hs ρ)) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (E : List AnnotTerm),
      denoteMeta m.acval env ψ (ctx.hiAt 0) crest
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (nF + (ctx.names.length - 1 - c))) E)) ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0) tyN
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (nF + (ctx.names.length - 1 - c))) E)) ∧
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
  have hparW' : ∀ x ∈ ctx.params, Expr.WScoped (ctx.hiAt 0) x :=
    fun x hx => Expr.WScoped.mono (by rw [hhi]; omega) (hparW x hx)
  have hholesOk : ∀ x ∈ holes, Expr.WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty :=
    ConLeche.nestHoles_ok (fun n ci hf => hcl n ci hf) hparW hholes
  have hW : Expr.WScoped (ctx.hiAt 0) crest :=
    ConLeche.WScoped_nestCrest hD.hasFvar (by omega)
      (fun x hx => (List.mem_append.mp hx).elim (hparW' x) (fun h => (hholesOk x h).1)) hcrest
  -- ## the walk: the declared crest opened as the walk opened it
  obtain ⟨nds, rest, htele, -, -, -, hresFree'⟩ := hd
  obtain ⟨-, -, xs, hop, -⟩ := posD_tele_open htele
  rw [Nat.add_zero] at hop
  have hresFree : ∀ a ∈ rest.getAppArgs, a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false :=
    fun a ha => by simpa using List.all_eq_true.mp hresFree' a ha
  -- ## the concrete reading, peeled past the parameters
  obtain ⟨crestc, hopP, hopX⟩ := hD.opens
  have hlenD := hD.len ψ
  have hreadc : denoteMeta m.acval env ψ ctx.nP crestc = some (mkPisAV ((ds ψ).drop ctx.nP)
      (ctorBodyAVI m (ctx.names.getD c .anonymous) ctx.nP nF ψ (Es ψ))) := by
    have hr := hD.read ψ
    rw [← List.take_append_drop ctx.nP (ds ψ), mkPisAV_append'] at hr
    have := (denoteMeta_peel ctx.nP hopP (by rw [List.length_take]; omega) hr).1
    simpa using this
  have hwc : Expr.WScoped ctx.nP crestc := by
    have := (ConLeche.openPisAtFvars_WScoped ctx.nP cvC.type 0 hopP
      (Expr.WScoped.of_not_hasFvar hD.hasFvar)).2
    rwa [Nat.zero_add] at this
  -- ## the walked crest is the concrete one, abstracted (up to erasure)
  have hsubC : ∀ c us, Option.Rel Expr.ErasedEq
      (ConLeche.nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP c us)
      (ConLeche.nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP c us) := by
    intro c us
    cases ConLeche.nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP c us with
    | none => exact .none
    | some h => exact .some (Expr.ErasedEq.rfl h)
  have herased : Expr.ErasedEq crest (holeAbs ctx crestc) := by
    unfold ConLeche.nestCrest at hcrest
    rw [hplen] at hcrest
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hcrest
    have h1 : Expr.ErasedEq (A.replaceFVars (ConLeche.nestKeyMap ctx.params holes)) A :=
      replaceFVars_erasedEq_idx (fun i a ha => by
        unfold ConLeche.nestKeyMap at ha
        split at ha
        · obtain ⟨ty, rfl⟩ := hpar i a ha
          exact ⟨ty, rfl⟩
        · obtain ⟨j, cv, caps, ty, -, -, rfl⟩ := ConLeche.nestHoles_mem hholes a
            (List.mem_of_getElem? ha)
          have hj : j = i - ctx.params.length := by
            have := ConLeche.nestHoles_getElem? hholes
              (show i - ctx.params.length < ctx.names.length by
                have := (List.getElem?_eq_some_iff.mp ha).1; omega)
            obtain ⟨cv', caps', ty', -, -, h'⟩ := this
            rw [ha] at h'
            simp only [Option.some.injEq, Expr.fvar.injEq] at h'
            omega
          exact ⟨ty, by rw [hj, hplen]; congr 1; omega⟩) A
    unfold ConLeche.nestCanonCrest at hA
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hA
    have hP : Expr.ErasedEqL (ConLeche.nestPhs ctx.nP) fvsP :=
      erasedEqL_of_fvarIdx _ fvsP 0
        (fun i x hx => by
          have hi : i < ctx.nP := by
            have := (List.getElem?_eq_some_iff.mp hx).1; simpa [ConLeche.nestPhs] using this
          rw [show (ConLeche.nestPhs ctx.nP)[i]? = some (.fvar i (.sort .zero)) by
            simp [ConLeche.nestPhs, List.getElem?_range hi]] at hx
          cases hx
          exact ⟨_, by rw [Nat.zero_add]⟩)
        (fun i x hx => by
          obtain ⟨ty, h⟩ := hD.pIdx i x hx
          exact ⟨ty, by rw [h, Nat.zero_add]⟩)
        (by simp [ConLeche.nestPhs, hD.pLen])
    obtain ⟨r', hr', hre⟩ := instPisWith_erasedEq hP (Expr.ErasedEq.rfl _) ht
    rw [instPisWith_of_openPis ctx.nP hopP] at hr'
    obtain rfl := Option.some.inj hr'
    have hsh : holeAbs ctx crestc = crestc.replaceApps
        (ConLeche.nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0 ctx.nP := by
      unfold holeAbs
      rw [Expr.shiftFromN_eq_self_of_fvarsBelow _ hwc.fvarsBelow]
    rw [hsh]
    exact h1.trans (Expr.replaceApps_erasedEq hsubC _ _ hre)
  -- ## the whole applications, put back
  have hsh : holeAbs ctx crestc = crestc.replaceApps
      (ConLeche.nestCanonSub ctx.names (ctx.lps.map .param) ctx.nP) 0 ctx.nP := by
    unfold holeAbs
    rw [Expr.shiftFromN_eq_self_of_fvarsBelow _ hwc.fvarsBelow]
  have hfvsW : ∀ x ∈ fvsP, Expr.WScoped ctx.nP x := by
    intro x hx
    have := (ConLeche.openPisAtFvars_WScoped ctx.nP cvC.type 0 hopP
      (Expr.WScoped.of_not_hasFvar hD.hasFvar)).1 x hx
    rwa [Nat.zero_add] at this
  have hfvsP : ∀ (p : Nat) (x : Expr), fvsP[p]? = some x → ∃ ty, x = .fvar (0 + p) ty := by
    intro p x hx
    obtain ⟨ty, h⟩ := hD.pIdx p x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  let s : Nat → Expr := fun i => if i < ctx.nP then .fvar i (.sort .zero)
    else Expr.mkAppN (.const (ctx.names.getD (i - ctx.nP) .anonymous) (ctx.lps.map .param)) fvsP
  let x : Nat → AnnotTerm := fun i => if i < ctx.nP then .bvar (ctx.nP - 1 - i)
    else AnnotTerm.mkAppN (m.acval (ctx.names.getD (i - ctx.nP) .anonymous) ψ)
      (paramBvarsAt ctx.nP ctx.nP)
  have herase2 : Expr.ErasedEq
      (Expr.substFvars (ctx.nP + ctx.names.length) ctx.nP s (holeAbs ctx crestc)) crestc := by
    rw [hsh]
    refine Expr.substFvars_replaceApps_erasedEq (Nat.le_refl _)
      (fun i hi => ⟨.sort .zero, by dsimp only [s]; rw [if_pos hi]⟩)
      (fun mm hmm args hlen hvar => ?_) crestc hwc.fvarsBelow
    dsimp only [s]
    rw [if_neg (show ¬ ctx.nP + mm < ctx.nP by omega), show ctx.nP + mm - ctx.nP = mm by omega]
    exact erasedEq_mkAppN_congr (Expr.ErasedEq.rfl _) (erasedEqL_of_fvarIdx fvsP args 0 hfvsP
      (fun p y hy => by obtain ⟨ty, h⟩ := hvar p y hy; exact ⟨ty, by rw [h, Nat.zero_add]⟩)
      (by rw [hD.pLen, hlen]))
  have hleafRead : ∀ t, t < ctx.names.length → ∀ d, denoteMeta m.acval env ψ d
      (.const (ctx.names.getD t .anonymous) (ctx.lps.map .param))
        = some (m.acval (ctx.names.getD t .anonymous) ψ) := by
    intro t ht d
    obtain ⟨cv, caps, bs, s', hf, hlps, -, -⟩ := hformers t ht
    rw [denoteMeta_const hf (by simp [ConstantInfo.toConstantVal, hlps])]
    simp only [ConstantInfo.toConstantVal, hlps, ConLeche.Level.substFn_param_self]
  have hs : ∀ i, i < ctx.nP + ctx.names.length → Expr.WScoped ctx.nP (s i) ∧
      (s i).looseBVarsBounded 0 = true ∧ denoteMeta m.acval env ψ ctx.nP (s i) = some (x i) := by
    intro i hi
    by_cases hin : i < ctx.nP
    · dsimp only [s, x]
      rw [if_pos hin, if_pos hin]
      refine ⟨?_, rfl, by rw [denoteMeta_fvar]⟩
      simp only [Expr.WScoped]
      exact ⟨hin, by simp⟩
    · dsimp only [s, x]
      rw [if_neg hin, if_neg hin]
      have hsp := denoteMetaSpine_params (acval := m.acval) (env := env) (φ := ψ) ctx.nP hD.pLen
        hD.pIdx
      refine ⟨?_, ?_, denoteMeta_mkAppN hsp (hleafRead _ (by omega) _)⟩
      · have : ∀ (as : List Expr) (f : Expr), Expr.WScoped ctx.nP f →
            (∀ a ∈ as, Expr.WScoped ctx.nP a) → Expr.WScoped ctx.nP (Expr.mkAppN f as) := by
          intro as
          induction as with
          | nil => intro f hf _; exact hf
          | cons a as ih =>
            intro f hf ha
            refine ih (.app f a) ?_ (fun b hb => ha b (List.mem_cons_of_mem _ hb))
            simp only [Expr.WScoped]
            exact ⟨hf, ha a List.mem_cons_self⟩
        exact this fvsP _ (by rw [Expr.WScoped]; trivial) hfvsW
      · have : ∀ (as : List Expr) (f : Expr), f.looseBVarsBounded 0 = true →
            (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
              (Expr.mkAppN f as).looseBVarsBounded 0 = true := by
          intro as
          induction as with
          | nil => intro f hf _; exact hf
          | cons a as ih =>
            intro f hf ha
            refine ih (.app f a) ?_ (fun b hb => ha b (List.mem_cons_of_mem _ hb))
            simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
            exact ⟨hf, ha a List.mem_cons_self⟩
        refine this fvsP _ rfl fun a ha => ?_
        obtain ⟨p, hp⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := hD.pIdx p a hp
        rfl
  have hAbsB : Expr.fvarsBelow (ctx.nP + ctx.names.length + 0) (holeAbs ctx crestc) := by
    rw [Nat.add_zero, ← hhi]
    exact erasedEq_fvarsBelow _ _ herased hW.fvarsBelow
  have hsubRead := denoteMeta_substFvars (φ := ψ) m (b := ctx.nP + ctx.names.length)
    (D := ctx.nP) (s := s) (x := x) hs (holeAbs ctx crestc) 0 hAbsB
  rw [Nat.add_zero, Nat.add_zero, denoteMeta_erasedEq herase2, hreadc] at hsubRead
  obtain ⟨R, hR, hRi⟩ := Option.map_eq_some_iff.mp hsubRead.symm
  have hRc : denoteMeta m.acval env ψ (ctx.hiAt 0) crest = some R := by
    rw [denoteMeta_erasedEq herased, hhi]; exact hR
  obtain ⟨pps, Bb, hst, hBb, hppl, -⟩ := denoteMeta_openPis nF hop hRc
  obtain ⟨rfl, -⟩ := stripPisAV_eq_mkPis hst
  rw [AnnotTerm.substAV_mkPisAV] at hRi
  have hsubTeleL : ∀ (c : Nat) (ab : List (Nat × Nat × AnnotTerm)),
      (AnnotTerm.substTele (substTau (ctx.nP + ctx.names.length) ctx.nP x) c ab).length
        = ab.length := by
    intro c ab
    induction ab generalizing c with
    | nil => rfl
    | cons d ab ih => simp [AnnotTerm.substTele, ih]
  obtain ⟨hTele, hBody⟩ := mkPisAV_inj
    (by rw [hsubTeleL, hppl, List.length_drop, hlenD]; omega) hRi
  rw [Nat.zero_add, hppl] at hBody
  -- ## the result: the constructor's member hole applied to the indices
  obtain ⟨xs', rest', hop', hrestE⟩ := openPisAtFvars_holeAbs (ctx := ctx) nF (j := 0)
    (e := crestc) (by rw [Nat.add_zero]; exact hopX) herased
  rw [Nat.add_zero, ← hhi, hop] at hop'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hop')
  have hxr : holeAbs ctx xrest
      = Expr.mkAppN (.fvar (ctx.nP + c) (.sort .zero)) (idxArgs.map (holeAbs ctx)) := by
    rw [hD.resShape]; exact holeAbs_memberApp hnd hc hD.pLen hD.pIdx idxArgs
  rw [hxr] at hrestE
  obtain ⟨hfnE, hlenE, -⟩ := erasedEq_getApp _ _ hrestE
  rw [Expr.getAppFn_mkAppN] at hfnE
  have hfnR : ∃ ty, rest.getAppFn = .fvar (ctx.nP + c) ty := by
    cases hq : rest.getAppFn <;> rw [hq] at hfnE <;>
      simp only [Expr.ErasedEq, Expr.getAppFn] at hfnE
    subst hfnE
    exact ⟨_, rfl⟩
  have hwr : Expr.WScoped (ctx.hiAt 0 + nF) rest :=
    (ConLeche.openPisAtFvars_WScoped nF crest (ctx.hiAt 0) hop hW).2
  obtain ⟨E, hBbE, hEfree, hElen, -⟩ := denoteMeta_holeHead (m := m) (ψ := ψ) (l := nF) hfnR hc
    hresFree hwr hBb
  have hEl : E.length = (Es ψ).length := by
    rw [hElen, hlenE, Expr.getAppArgs_mkAppN, hD.lenE ψ]
    simp [Expr.getAppArgs]
  have happ : ∀ (as bs : List AnnotTerm) (f : AnnotTerm),
      AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs = AnnotTerm.mkAppN f (as ++ bs) := by
    intro as
    induction as with
    | nil => intro bs f; rfl
    | cons a as ih => intro bs f; exact ih bs (.app f a)
  have hliftApp : ∀ (as : List AnnotTerm) (f : AnnotTerm) (n c' : Nat),
      (AnnotTerm.mkAppN f as).liftN n c' = AnnotTerm.mkAppN (f.liftN n c') (as.map (·.liftN n c')) := by
    intro as
    induction as with
    | nil => intro f n c'; rfl
    | cons a as ih => intro f n c'; simp only [AnnotTerm.mkAppN_cons, ih, List.map_cons]; rfl
  have hhead : AnnotTerm.substAV (substTau (ctx.nP + ctx.names.length) ctx.nP x)
      (.bvar (nF + (ctx.names.length - 1 - c))) nF
      = AnnotTerm.mkAppN (m.acval (ctx.names.getD c .anonymous) ψ) (paramBvars ctx.nP nF) := by
    rw [AnnotTerm.substAV_bvar_ge _ (by omega),
      show nF + (ctx.names.length - 1 - c) - nF = ctx.names.length - 1 - c by omega]
    unfold substTau
    rw [if_pos (by omega)]
    dsimp only [x]
    rw [if_neg (by omega),
      show ctx.nP + ctx.names.length - 1 - (ctx.names.length - 1 - c) - ctx.nP = c by omega,
      hliftApp, liftN_closed (m.acval_closed _ _) nF 0]
    congr 1
    unfold paramBvarsAt paramBvars
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have := List.mem_range.mp hp
    simp only [Function.comp_apply, AnnotTerm.liftN_bvar, if_false, Nat.not_lt_zero]
    congr 1; omega
  have hmap : E.map (AnnotTerm.substAV (substTau (ctx.nP + ctx.names.length) ctx.nP x) · nF)
      = Es ψ := by
    have h2 := hBody
    rw [hBbE, AnnotTerm.substAV_mkAppN, hhead, happ] at h2
    unfold ctorBodyAVI at h2
    obtain ⟨-, h3⟩ := AnnotTerm.mkAppN_inj h2 (by simp [hEl])
    exact List.append_cancel_left h3
  have hxP : ∀ i, i < ctx.nP → x i = .bvar (ctx.nP - 1 - i) := fun i hi => by
    dsimp only [x]; rw [if_pos hi]
  have hE : E = (Es ψ).map (·.liftN ctx.names.length nF) := by
    rw [← hmap, List.map_map]
    refine (List.map_id E).symm.trans (List.map_congr_left fun e he => ?_)
    exact (substAV_holeBack_liftN hxP e nF (hEfree e he)).symm
  -- ## the normal form: the link, its reading and its fields
  obtain ⟨abD, abN, B₀, hRD, hRN, hlD, hlN, hEqF, -, -⟩ := hlink _ hRc
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (hppl.trans hlD.symm) hRD
  -- the stored field readings are the crest's, the holes filled back
  have hSget : ∀ l p, pps[l]? = some p →
      (((ds ψ).drop ctx.nP).map (·.2.2)).getD l default
        = AnnotTerm.substAV (substTau (ctx.nP + ctx.names.length) ctx.nP x) p.2.2 l := by
    have hTget : ∀ (c : Nat) (ab : List (Nat × Nat × AnnotTerm)) (l : Nat),
        (AnnotTerm.substTele (substTau (ctx.nP + ctx.names.length) ctx.nP x) c ab)[l]?
          = (ab[l]?).map fun d => (d.1, d.2.1,
              AnnotTerm.substAV (substTau (ctx.nP + ctx.names.length) ctx.nP x) d.2.2 (c + l)) := by
      intro c ab
      induction ab generalizing c with
      | nil => intro l; rfl
      | cons d ab ih =>
        intro l
        cases l with
        | zero => rfl
        | succ l =>
          simp only [AnnotTerm.substTele, List.getElem?_cons_succ, ih (c + 1) l]
          rw [show c + 1 + l = c + (l + 1) by omega]
    intro l p hp
    rw [← hTele, List.getD_eq_getElem?_getD, List.getElem?_map, hTget, hp]
    simp
  have hFgetD : ∀ l p, pps[l]? = some p → (pps.map (·.2.2)).getD l default = p.2.2 := by
    intro l p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rfl
  -- the declared fields at the members' applied values are the stored ones, at every frame
  have hdecl : ∀ (ρ : Nat → V) (hs : List V), hs.length = ctx.names.length →
      (∀ t, t < ctx.names.length →
        hs.getD t pt = (frameIdx ctx.nP ρ).foldl app
          (interp V ρ (m.acval (ctx.names.getD t .anonymous) ψ))) →
      ∀ (l : Nat) (as : List V), l < nF → as.length = l →
        interp V (consList as (consList hs ρ)) ((pps.map (·.2.2)).getD l default)
          = interp V (consList as ρ) ((((ds ψ).drop ctx.nP).map (·.2.2)).getD l default) := by
    intro ρ hs hsl hv l as hl has
    obtain ⟨p, hp⟩ : ∃ p, pps[l]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hFgetD l p hp, hSget l p hp, interp_substAV, ← has]
    have h1 := substE_consList V (substTau (ctx.nP + ctx.names.length) ctx.nP x) as 0 ρ
    rw [Nat.add_zero] at h1
    rw [h1, substE_holeBack hxP ρ]
    suffices hhs : hs = (List.range ctx.names.length).map fun mm => interp V ρ (x (ctx.nP + mm)) by
      rw [hhs]
    apply List.ext_getElem (by simp [hsl])
    intro t h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    have ht : t < ctx.names.length := by rw [← hsl]; exact h₁
    have := hv t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at this
    rw [this]
    dsimp only [x]
    rw [if_neg (by omega), show ctx.nP + t - ctx.nP = t by omega, interp_mkAppN_foldl]
    congr 1
    unfold paramBvarsAt frameIdx
    rw [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp_apply, interp_bvar]
  refine ⟨pps, abN, E, ?_, ?_, hlD, hlN, hE, ⟨by simp [hlN, hlenD], ?_⟩⟩
  · rw [hRc, hBbE]
  · rw [hRN, hBbE]
  · -- the override: through the declared crest (at every parameter frame) and the link (at
    -- frames satisfying the walk's context)
    intro ρ hρ hs hsl hv l hl as has hfit
    have hl' : l < nF := by simpa [hlN] using hl
    have hfitD : SpineFit (consList hs ρ) ((pps.map (·.2.2)).take l) as := by
      refine (spineFit_congr_all (by simp [hlD, hlenD]) (fun i as' hi has' => ?_) as).mpr hfit
      have hil : i < l := by simp only [List.length_take, List.length_map, hlD] at hi; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hil, ← List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD (l := List.take l _), List.getElem?_take_of_lt hil,
        ← List.getD_eq_getElem?_getD]
      exact hdecl ρ hs hsl hv i as' (by omega) has'
    rw [← hdecl ρ hs hsl hv l as hl' has]
    exact (hEqF.getD_eq (hsatH ρ hρ hs hsl hv) l as (by simp [hlD, hl']) hfitD).symm

end ConLeche.Model
