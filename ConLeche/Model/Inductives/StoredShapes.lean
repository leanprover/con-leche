module

public import ConLeche.Model.Annot.LfpHoleWitness
public import ConLeche.Semantics.Inductives.HoleApp
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.NestPosOut
public import ConLeche.Model.Inductives.HoleSubst
public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Verify.Inductives.PositivityInv
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

* `FlatShape`: every field is hole-free, or a Π-tower of hole-free
  domains (codomain bits at the block's regime) over a member hole
  applied to the parameters and hole-free index readings; no later field
  reads a field of the second shape;
* `override`: `F` read with the members' leaf values in the hole slots is
  `S` — "members := their own values" is the stored reading.

**The producer** (`storedFieldShapes_of_walk`, the ONLY place that reads
the stored syntax for these facts): the install's tail run (β′) — the
walk returns every stored constructor as its own normal form
(`checkBlockPositivity_inv`) — inverted syntactically
(`NestPosOut.lean`: every domain hole-free or `HoleIn`, U4), read
(`denoteMeta_holeIn`), with the bits from the U2 sort row, and the
override by the substitution lemma iterated (`HoleSubst.lean`).
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

/-! ## The interface -/

/-- **The flat shape of fields with holes** (hole positions
`LfpDatum.holeSlots k l`, field slots `LfpDatum.fieldSlot`): a field `l`
with `rec l = some (tl, m, es)` is the Π-tower over `tl` (hole-free
domains, codomain bits zero exactly at `w = 0`) of member `m`'s hole
applied to the parameters and the hole-free readings `es` (member `m`'s
index count of them); every other field is hole-free; no later field
reads a field of the first kind. -/
@[expose] def FlatShape (k nP w : Nat) (nIdxOf : Nat → Nat) (F : List AnnotTerm)
    (rec : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) : Prop :=
  (∀ l tl m es, rec l = some (tl, m, es) → l < F.length ∧ m < k ∧
    F.getD l default = mkPisAV tl (AnnotTerm.mkAppN (.bvar (l + tl.length + (k - 1 - m)))
      (holeParams k nP (l + tl.length) ++ es)) ∧
    (∀ q dd, tl[q]? = some dd →
      (dd.2.1 = 0 ↔ w = 0) ∧ NoBVar (LfpDatum.holeSlots k (l + q)) dd.2.2) ∧
    (∀ e ∈ es, NoBVar (LfpDatum.holeSlots k (l + tl.length)) e) ∧ es.length = nIdxOf m) ∧
  (∀ l, l < F.length → rec l = none → NoBVar (LfpDatum.holeSlots k l) (F.getD l default)) ∧
  (∀ l, l < F.length → rec l ≠ none → ∀ l', l < l' → l' < F.length →
     NoBVar (LfpDatum.fieldSlot l l') (F.getD l' default))

/-- **Stored field shape facts**: the fields with holes `F` against the
stored field readings `S` (see the module docstring); `leaf t` is member
`t`'s leaf (its former's reading). -/
structure StoredFieldShapes (V : Type w) [SetTheory V] (k nP w : Nat) (nIdxOf : Nat → Nat)
    (leaf : Nat → AnnotTerm) (F S : List AnnotTerm) : Prop where
  len : F.length = S.length
  flat : ∃ rec, FlatShape k nP w nIdxOf F rec
  override : ∀ hs : List V, hs.length = k →
    (∀ t, t < k → ∀ σ : Nat → V, interp V σ (leaf t) = hs.getD t pt) →
    ∀ l, l < F.length → ∀ (as : List V) (ρ : Nat → V), as.length = l →
      interp V (consList as (consList hs ρ)) (F.getD l default)
        = interp V (consList as ρ) (S.getD l default)

/-- The facts read the members' leaves below `k` only. -/
theorem StoredFieldShapes.congr_leaf {V : Type w} [SetTheory V] {k nP w : Nat}
    {nIdxOf : Nat → Nat} {leaf leaf' : Nat → AnnotTerm} {F S : List AnnotTerm}
    (h : StoredFieldShapes V k nP w nIdxOf leaf F S) (hl : ∀ t, t < k → leaf t = leaf' t) :
    StoredFieldShapes V k nP w nIdxOf leaf' F S :=
  ⟨h.len, h.flat, fun hs hhs hv => h.override hs hhs fun t ht σ => by rw [hl t ht]; exact hv t ht σ⟩

/-- A Π-telescope whose `l`-th domain is `HoleApp` at `lo + l` and whose
body is at `lo + |ab|` is `HoleApp` at `lo`. -/
theorem holeApp_mkPisAV_of {k nP : Nat} :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) {lo : Nat} {b : AnnotTerm},
      (∀ l dd, ab[l]? = some dd → HoleApp k nP (lo + l) dd.2.2) →
      HoleApp k nP (lo + ab.length) b → HoleApp k nP lo (mkPisAV ab b)
  | [], lo, b, _, hb => by simp only [List.length_nil, Nat.add_zero] at hb; exact hb
  | dd :: ab, lo, b, hd, hb => by
    refine .pi (by simpa using hd 0 dd rfl) (holeApp_mkPisAV_of ab (fun l d' hl => ?_) ?_)
    · have := hd (l + 1) d' (by simpa using hl)
      rwa [show lo + (l + 1) = lo + 1 + l by omega] at this
    · rwa [show lo + 1 + ab.length = lo + (dd :: ab).length by simp; omega]

/-- A term reading no hole slot applies no hole. -/
theorem holeApp_of_noBVar {k nP lo : Nat} {e : AnnotTerm}
    (h : NoBVar (LfpDatum.holeSlots k lo) e) : HoleApp k nP lo e := by
  have h' : NoBVar (fun i => lo ≤ i ∧ i < lo + (List.replicate k AnnotTerm.prf).length) e := by
    rw [List.length_replicate]; exact h
  have := instAll_liftN_of_noBVar e (List.replicate k .prf) lo h'
  rw [List.length_replicate] at this
  rw [← this]
  exact holeApp_liftN k nP _ lo

/-- **The flat shape applies each hole to the parameters.** -/
theorem FlatShape.holeApp {k nP w : Nat} {nIdxOf : Nat → Nat} {F : List AnnotTerm}
    {rec : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)}
    (h : FlatShape k nP w nIdxOf F rec) :
    ∀ (l : Nat) (F' : AnnotTerm), F[l]? = some F' → HoleApp k nP l F' := by
  intro l F' hl
  have hlt : l < F.length := (List.getElem?_eq_some_iff.mp hl).1
  have hget : F.getD l default = F' := by rw [List.getD_eq_getElem?_getD, hl]; rfl
  cases hr : rec l with
  | none => rw [← hget]; exact holeApp_of_noBVar (h.2.1 l hlt hr)
  | some x =>
    obtain ⟨tl, m, es⟩ := x
    obtain ⟨-, hm, hF, htl, hes, -⟩ := h.1 l tl m es hr
    rw [← hget, hF]
    refine holeApp_mkPisAV_of tl (fun q dd hq => holeApp_of_noBVar (htl q dd hq).2) ?_
    exact .hole (by omega) (by omega) fun r hr => holeApp_of_noBVar (hes r hr)

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

/-- **A field domain of member-hole shape, read**: the Π-tower over its
hole-free domains of the member's hole applied to the parameters and
hole-free index readings; its opening is the telescope's. -/
theorem denoteMeta_holeIn {ctx : NestCtx} {t : Nat} :
    ∀ {dep : Nat} {e : Expr}, HoleIn ctx t dep e → ctx.hiAt 0 ≤ dep → Expr.WScoped dep e →
      ∀ {ea : AnnotTerm}, denoteMeta m.acval env ψ dep e = some ea →
      ∃ (tl : List (Nat × Nat × AnnotTerm)) (es : List AnnotTerm) (fvs : List Expr) (body : Expr),
        openPisAtFvars tl.length e dep = some (fvs, body) ∧ HoleAppE ctx t body ∧
        ea = mkPisAV tl (AnnotTerm.mkAppN
          (.bvar (dep - ctx.hiAt 0 + tl.length + (ctx.names.length - 1 - t)))
          (holeParams ctx.names.length ctx.nP (dep - ctx.hiAt 0 + tl.length) ++ es)) ∧
        (∀ q dd, tl[q]? = some dd →
          NoBVar (LfpDatum.holeSlots ctx.names.length (dep - ctx.hiAt 0 + q)) dd.2.2) ∧
        (∀ x ∈ es, NoBVar (LfpDatum.holeSlots ctx.names.length (dep - ctx.hiAt 0 + tl.length)) x) ∧
        es.length = ctx.nIdxs.getD t 0 := by
  intro dep e h
  induction h with
  | @app dep e hA =>
    intro hhi hw ea hea
    obtain ⟨hfn, ht, hlen, hps, hfree⟩ := hA
    have hdep : dep = ctx.hiAt 0 + (dep - ctx.hiAt 0) := by omega
    rw [hdep] at hw hea
    obtain ⟨es, rfl, hes, hesl, -⟩ := denoteMeta_holeHead (l := dep - ctx.hiAt 0) hfn ht hps
      (by omega) (fun x hx => hfree x (List.mem_of_mem_drop hx)) hw hea
    refine ⟨[], es, [], e, rfl, ⟨hfn, ht, hlen, hps, hfree⟩, ?_, ?_, ?_, ?_⟩
    · simp [mkPisAV]
    · intro q dd hq; simp at hq
    · simpa using hes
    · rw [hesl, hlen]; omega
  | @pi dep a b bm ha _ ih =>
    intro hhi hw ea hea
    simp only [Expr.WScoped] at hw
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hea
    obtain ⟨tl, es, fvs, body, hop, hA, rfl, htl, hes, hesl⟩ :=
      ih (by omega) (Expr.WScoped.instantiate1 hw.1 0 hw.2) hba
    have hdep : dep = ctx.hiAt 0 + (dep - ctx.hiAt 0) := by omega
    have hta' : NoBVar (LfpDatum.holeSlots ctx.names.length (dep - ctx.hiAt 0)) ta := by
      rw [hdep] at hw hta
      exact noBVar_holeSlots_of_nestOcc hw.1 ha hta
    refine ⟨(0, pwBit ψ bm.pw, ta) :: tl, es, .fvar dep a :: fvs, body, ?_, hA, ?_,
      fun q dd hq => ?_, ?_, hesl⟩
    · simp only [List.length_cons, openPisAtFvars, hop]
    · simp only [mkPisAV, List.length_cons]
      rw [show dep + 1 - ctx.hiAt 0 + tl.length = dep - ctx.hiAt 0 + (tl.length + 1) by omega]
    · cases q with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        simpa using hta'
      | succ q =>
        simp only [List.getElem?_cons_succ] at hq
        have := htl q dd hq
        rwa [show dep + 1 - ctx.hiAt 0 + q = dep - ctx.hiAt 0 + (q + 1) by omega] at this
    · intro x hx
      have := hes x hx
      simp only [List.length_cons]
      rwa [show dep + 1 - ctx.hiAt 0 + tl.length = dep - ctx.hiAt 0 + (tl.length + 1) by omega]
        at this

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

/-- A member-hole shape names a member. -/
theorem HoleIn.lt {ctx : NestCtx} {t : Nat} :
    ∀ {dep : Nat} {e : Expr}, HoleIn ctx t dep e → t < ctx.names.length := by
  intro dep e h
  induction h with
  | app h => exact h.2.1
  | pi _ _ ih => exact ih

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

/-- **The codomain bits of a member-hole field's telescope** are at the
member's sort's regime: the U2 sort row, walked through the binders
(`piBits_of_infer`), ends at the hole applied — typed by the member's
stored type (`HoleLeafOk`), a telescope into `Sort s`. -/
theorem holeIn_bits {ctx : NestCtx} {F : Nat} {t dep : Nat} {a : Expr}
    {tl : List (Nat × Nat × AnnotTerm)} {fvs : List Expr} {body : Expr} {B : AnnotTerm}
    {ty : Expr} {u : Level} {w : Nat}
    (hop : openPisAtFvars tl.length a dep = some (fvs, body)) (hA : HoleAppE ctx t body)
    (hleaf : HoleLeafOk ctx body)
    (hformer : ∀ cv caps, ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) →
      ∃ bs s, cv.type.stripPis (ctx.nP + ctx.nIdxs.getD t 0) = some (bs, .sort s) ∧
        s.eval ψ = w)
    (hinf : ConLeche.inferTypeCore .verified env F dep a = .ok ty)
    (hens : ConLeche.ensureSortCore .verified env F dep ty = .ok u)
    (hread : denoteMeta m.acval env ψ dep a = some (mkPisAV tl B)) :
    ∀ dd ∈ tl, (dd.2.1 = 0 ↔ w = 0) := by
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ := piBits_of_infer rfl tl.length hop hinf hens
  obtain ⟨⟨tyh, hfn⟩, ht, hlen, -, -⟩ := hA
  have hleafh := hleaf _ (Rules.mem_fvarLeaves_of_getAppFn hfn) (by simp)
    (by simp [ConLeche.NestCtx.hiAt]; omega)
  simp only [Nat.add_sub_cancel_left] at hleafh
  obtain ⟨cv, caps, hf, rfl⟩ := hleafh
  obtain ⟨bs, s, hst, hs⟩ := hformer cv caps hf
  rw [← Expr.mkAppN_getApp body, hfn] at hib
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv _ hib
  have htf' : ConLeche.inferTypeCore .verified env F' (dep + tl.length)
      (.fvar (ctx.nP + t) cv.type) = .ok cv.type := by
    cases F' with
    | zero => rw [ConLeche.inferTypeCore_zero] at htf; exact nomatch htf
    | succ F' =>
      obtain ⟨-, rfl⟩ := ConLeche.Rules.inferTypeCore_fvar_inv htf
      exact htf
  obtain rfl := inferTypeCore_mkAppN_sort _ htf' (by rw [hlen]; exact hst) hib
  obtain rfl := ensureSortCore_sort_eq hensb
  intro dd hdd
  rw [← hs]
  exact stripPisAV_bits tl.length (hbits ψ) hread (stripPisAV_mkPisAV tl B) dd hdd

/-- **One field with a member hole, as a flat-shape entry.** -/
@[expose] def FieldHoleShape (k nP w : Nat) (nIdxOf : Nat → Nat) (Fl : AnnotTerm) (l : Nat)
    (x : List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm) : Prop :=
  x.2.1 < k ∧
  Fl = mkPisAV x.1 (AnnotTerm.mkAppN (.bvar (l + x.1.length + (k - 1 - x.2.1)))
    (holeParams k nP (l + x.1.length) ++ x.2.2)) ∧
  (∀ q dd, x.1[q]? = some dd →
    (dd.2.1 = 0 ↔ w = 0) ∧ NoBVar (LfpDatum.holeSlots k (l + q)) dd.2.2) ∧
  (∀ e ∈ x.2.2, NoBVar (LfpDatum.holeSlots k (l + x.1.length)) e) ∧ x.2.2.length = nIdxOf x.2.1

/-- A field domain of member-hole shape, read and typed, is a flat-shape
entry. -/
theorem fieldHoleShape_of_holeIn {ctx : NestCtx} {F : Nat} {t l : Nat} {a : Expr} {Fl : AnnotTerm}
    {w : Nat} {ty : Expr} {u : Level}
    (hHI : HoleIn ctx t (ctx.hiAt 0 + l) a) (hw : Expr.WScoped (ctx.hiAt 0 + l) a)
    (hleaf : HoleLeafOk ctx a)
    (hformer : ∀ cv caps, ctx.find? (ctx.names.getD t .anonymous) = some (.indInfo cv caps) →
      ∃ bs s, cv.type.stripPis (ctx.nP + ctx.nIdxs.getD t 0) = some (bs, .sort s) ∧
        s.eval ψ = w)
    (hinf : ConLeche.inferTypeCore .verified env F (ctx.hiAt 0 + l) a = .ok ty)
    (hens : ConLeche.ensureSortCore .verified env F (ctx.hiAt 0 + l) ty = .ok u)
    (hread : denoteMeta m.acval env ψ (ctx.hiAt 0 + l) a = some Fl) :
    ∃ x, FieldHoleShape ctx.names.length ctx.nP w (fun t => ctx.nIdxs.getD t 0) Fl l x := by
  obtain ⟨tl, es, fvs, body, hop, hA, hFl, htl, hes, hesl⟩ :=
    denoteMeta_holeIn hHI (Nat.le_add_right _ _) hw hread
  simp only [Nat.add_sub_cancel_left] at hFl htl hes
  have hbits := holeIn_bits (m := m) hop hA
    (hleaf.open (Nat.le_add_right _ _) hop).1 hformer hinf hens (by rw [hread, hFl])
  refine ⟨(tl, t, es), hA.2.1, hFl, fun q dd hq => ⟨hbits dd (List.mem_of_getElem? hq),
    htl q dd hq⟩, hes, hesl⟩

/-- **U4, read**: a field whose variable no later binder and not the result
uses is read by no later field. -/
theorem u4_fieldSlot {ctx : NestCtx} {nF l l' : Nat} {crest rest : Expr} {xs : List Expr}
    {x : Expr} {ea : AnnotTerm}
    (hop : openPisAtFvars nF crest (ctx.hiAt 0) = some (xs, rest))
    (hW : Expr.WScoped (ctx.hiAt 0) crest) (hU : structUsedLater crest 0 l = false)
    (hl : l < nF) (hll : l < l') (hx : xs[l']? = some x)
    (hr : denoteMeta m.acval env ψ (ctx.hiAt 0 + l') x.fvarTypeD = some ea) :
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
  have hxfree : ∀ z ∈ x.fvarTypeD.fvarLeaves, z.1 ≠ ctx.hiAt 0 + l := by
    intro z hz
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF crest (ctx.hiAt 0) hop l' x hx
    exact h1 l' hll _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])
  have hwx := openPisAtFvars_typeWScoped nF hop hW l' x hx
  obtain ⟨X, rfl⟩ := denoteMeta_liftN_of_leaf_free m _ _ hwx (q := ctx.hiAt 0 + l) (by omega)
    hxfree hr
  refine NoBVar.mono (fun i hi => ?_) (noBVar_liftN_one X _)
  simp only [LfpDatum.fieldSlot] at hi
  omega

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
reads a stored constructor's syntax for them.  From the install's tail run
at a stored constructor of the block (the walk returns `crest` on `crest`
with flat kinds, (β′); U2's sort row), the constructor's kind-free facts
and the members' formers: the walked term READS, at the walk's depth, as
a Π-tower over the fields with holes `ab` ending in the constructor's
member hole at the parameters and the result indices `E` (the stored
result index readings lifted over the holes), and `ab`'s readings are the
fields with holes of `StoredFieldShapes` against the stored field
readings. -/
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
    {st₀ st₁ : NestState} {ks : List NestFieldKind}
    (hwalk : nestMemberCtor (fueledOps .verified F) env ctx nF crest st₀ = .ok (ks, crest, st₁))
    (hflat : ∀ k ∈ ks, k.flat = true)
    (hU2 : ∃ (isProp : Bool) (xq : List Expr × Expr) (sorts : List Level),
      openPisAtFvars nF crest (ctx.hiAt 0) = some xq ∧
      ConLeche.checkStructFieldSortsI (fueledOps .verified F) env isProp false ctx.sort
        (ctx.hiAt 0) xq.1 [] nF = .ok sorts) :
    ∃ (ab : List (Nat × Nat × AnnotTerm)) (E : List AnnotTerm),
      denoteMeta m.acval env ψ (ctx.hiAt 0) crest
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (nF + (ctx.names.length - 1 - c)))
            (paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + nF) ++ E))) ∧
      ab.length = nF ∧ E = (Es ψ).map (·.liftN ctx.names.length nF) ∧
      StoredFieldShapes V ctx.names.length ctx.nP w (fun t => ctx.nIdxs.getD t 0)
        (fun t => m.acval (ctx.names.getD t .anonymous) ψ) (ab.map (·.2.2))
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
  -- ## the walk, field by field
  obtain ⟨xs, rest, hop, hresFree, hfields⟩ := storedWalk_fields henv hplen hpar hB hwalk hflat
  obtain ⟨isProp, xq, sorts, hxq, hsorts⟩ := hU2
  rw [hop] at hxq
  obtain rfl := Option.some.inj hxq
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
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
  -- ## the fields
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
  have hleafX := (hleafCrest.open (Nat.le_refl _) hop).2
  have hSget : ∀ l p, pps[l]? = some p →
      (((ds ψ).drop ctx.nP).map (·.2.2)).getD l default = instAll leaves l p.2.2 := by
    intro l p hp
    rw [← hTele, List.getD_eq_getElem?_getD, List.getElem?_map, instTele_getElem?, hp]
    simp
  have hFget : ∀ l p, pps[l]? = some p → (pps.map (·.2.2)).getD l default = p.2.2 := by
    intro l p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rfl
  have hfield : ∀ l, l < nF → ∃ x p, xs[l]? = some x ∧ pps[l]? = some p ∧
      denoteMeta m.acval env ψ (ctx.hiAt 0 + l) x.fvarTypeD = some p.2.2 := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p, hp, -, hr⟩ := hdoms l x hx
    exact ⟨x, p, hx, hp, hr⟩
  have hHP : holeParams ctx.names.length ctx.nP nF
      = paramBvarsAt ctx.nP (ctx.nP + ctx.names.length + nF) := by
    unfold holeParams paramBvarsAt
    refine List.map_congr_left fun p hp => ?_
    have := List.mem_range.mp hp
    congr 1
    omega
  refine ⟨pps, E, ?_, hppl, hE, ⟨by simp [hppl, hlenD], ⟨fun l =>
    if h : l < nF ∧ structUsedLater crest 0 l = false ∧ ∃ x, FieldHoleShape ctx.names.length
        ctx.nP w (fun t => ctx.nIdxs.getD t 0) ((pps.map (·.2.2)).getD l default) l x
    then some (Classical.choose h.2.2) else none, ?_, ?_, ?_⟩, ?_⟩⟩
  · -- the reading
    rw [hR, hBbE, hHP]
  · -- a field with a member hole
    intro l tl mm es hr
    try dsimp only at hr
    split at hr
    · rename_i h
      have hs := Classical.choose_spec h.2.2
      rw [Option.some.inj hr] at hs
      obtain ⟨hmm, hF, htl, hes, hesl⟩ := hs
      exact ⟨by simp only [List.length_map, hppl]; exact h.1, hmm, hF, htl, hes, hesl⟩
    · exact nomatch hr
  · -- every other field is hole-free
    intro l hl hr
    have hl' : l < nF := by simpa [hppl] using hl
    obtain ⟨x, p, hx, hp, hread⟩ := hfield l hl'
    have hwx : Expr.WScoped (ctx.hiAt 0 + l) x.fvarTypeD :=
      openPisAtFvars_typeWScoped nF hop hW l x hx
    rcases hfields l x hx with hocc | ⟨t, hHI, hU⟩
    · rw [hFget l p hp]
      exact noBVar_holeSlots_of_nestOcc hwx hocc hread
    · exfalso
      obtain ⟨fv, ty, u, hfv, -, hinf, hens, -⟩ := hrows l hl'
      have hfx : fv = x := by
        simp only at hfv
        rw [hx] at hfv
        exact (Option.some.inj hfv).symm
      subst hfx
      have hsh := fieldHoleShape_of_holeIn (m := m) (F := F) hHI hwx
        (hleafX fv (List.mem_of_getElem? hx)) (hformer' t hHI.lt) hinf hens hread
      try dsimp only at hr
      rw [dif_pos ⟨hl', hU, by rw [hFget l p hp]; exact hsh⟩] at hr
      exact nomatch hr
  · -- U4: no later field reads a field with a member hole
    intro l hl hr l' hll hl'
    have hl'' : l' < nF := by simpa [hppl] using hl'
    by_cases h : l < nF ∧ structUsedLater crest 0 l = false ∧ ∃ x, FieldHoleShape ctx.names.length
        ctx.nP w (fun t => ctx.nIdxs.getD t 0) ((pps.map (·.2.2)).getD l default) l x
    · obtain ⟨x, p, hx, hp, hread⟩ := hfield l' hl''
      rw [hFget l' p hp]
      exact u4_fieldSlot hop hW h.2.1 h.1 hll hx hread
    · exact absurd (dif_neg h) hr
  · -- the override: the leaves' values in the hole slots
    intro hs hsl hv l hl as ρ has
    have hl' : l < nF := by simpa [hppl] using hl
    obtain ⟨x, p, hx, hp, -⟩ := hfield l hl'
    rw [hFget l p hp, hSget l p hp, ← has]
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


/-- **The producer at the install's run** (`checkBlockPositivity`, the
(β′) tail run on the stored constructors, `DeclBlockRun` conjunct 7b): the
walk context's parameters are the head former's opened variables, and
every stored constructor `cA` of member `c` yields its walked term
`crest`, read as the Π-tower over the fields with holes `ab` over the
member hole at the parameters and the lifted result indices `E`, with
the stored field shape facts. -/
theorem storedFieldShapes_of_run {V : Type w} [SetTheory V] {env : Env} (m : EnvModel V env)
    (ψ : Name → Nat) {F : Nat} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs = .ok ())
    (hTas : ∀ cvT ∈ cvTas, cvT.type.hasFvar = false) (hnd : p.memberNames.Nodup) {w : Nat}
    (hformers : ∀ t, t < p.memberNames.length → ∃ cv caps bs s,
      env.find? (p.memberNames.getD t .anonymous) = some (.indInfo cv caps) ∧
      cv.levelParams = p.lps ∧
      cv.type.stripPis (p.nP + p.nIdxs.getD t 0) = some (bs, .sort s) ∧ s.eval ψ = w)
    {c j : Nat} {cs : List (ConstantVal × Nat)} {cA : ConstantVal × Nat}
    (hcs : ctorsAs[c]? = some cs) (hcA : cs[j]? = some cA) (hc : c < p.memberNames.length)
    {fvsPc xFvs : List Expr} {xrest : Expr} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    (hD : StoredCtorFacts m (p.memberNames.getD c .anonymous) p.lps cA.1 p.nP cA.2 fvsPc xFvs
      xrest idxArgs ds Es) :
    ∃ (cvTa0 : ConstantVal) (fvsP : List Expr) (rest : Expr) (holes : List Expr) (crest : Expr)
      (ab : List (Nat × Nat × AnnotTerm)) (E : List AnnotTerm),
      cvTas.head? = some cvTa0 ∧ openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes ∧
      instPisWith fvsP (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type)
        = some crest ∧
      denoteMeta m.acval env ψ (p.nP + p.memberNames.length) crest
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (p.memberNames.length - 1 - c)))
            (paramBvarsAt p.nP (p.nP + p.memberNames.length + cA.2) ++ E))) ∧
      ab.length = cA.2 ∧ E = (Es ψ).map (·.liftN p.memberNames.length cA.2) ∧
      StoredFieldShapes V p.memberNames.length p.nP w (fun t => p.nIdxs.getD t 0)
        (fun t => m.acval (p.memberNames.getD t .anonymous) ψ) (ab.map (·.2.2))
        (((ds ψ).drop p.nP).map (·.2.2)) := by
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv hrun
  obtain ⟨crest, hcrest, ⟨st₀, ks, st₁, hm, hks⟩, -, hU2, -⟩ := hall c cs hcs j cA hcA
  have hT0f : cvTa0.type.hasFvar = false :=
    hTas cvTa0 (List.mem_of_getElem? (by rwa [List.head?_eq_getElem?] at hcv0))
  have hplen : fvsP.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hpar : ∀ (q : Nat) (x : Expr), fvsP[q]? = some x → ∃ ty, x = .fvar q ty := by
    intro q x hx
    obtain ⟨ty, h⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 q x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hparW : ∀ x ∈ fvsP, Expr.WScoped p.nP x := by
    intro x hx
    have := (ConLeche.openPisAtFvars_WScoped p.nP cvTa0.type 0 hop0
      (Expr.WScoped.of_not_hasFvar hT0f)).1 x hx
    rwa [Nat.zero_add] at this
  obtain ⟨xq, sorts, hxq, hsorts⟩ := hU2
  obtain ⟨ab, E, hread, hab, hE, hS⟩ := storedFieldShapes_of_walk (ctx := p.nestCtx fvsP env.find?
    env.consts) m ψ rfl hholes hnd hplen hpar hparW hformers hc hD hcrest hm hks
    ⟨_, xq, sorts, hxq, hsorts⟩
  refine ⟨cvTa0, fvsP, rest, holes, crest, ab, E, hcv0, hop0, hholes, hcrest, ?_, hab, hE, hS⟩
  simpa [ConLeche.NestCtx.hiAt, ConLeche.BlockParts.nestCtx] using hread

end ConLeche.Model
