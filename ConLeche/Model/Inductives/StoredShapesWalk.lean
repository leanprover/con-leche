module

import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Semantics.NoBVar
import ConLeche.Semantics.Inductives.HoleApp
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Inductives.PosNodes
public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Model.Inductives.HoleSubst
import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.IndPointKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.IndSubst
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.DirectGen
public import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Verify.Inductives.ScopeKit

public section

/-!
# Stored field shape facts: the positivity walk's producer

`storedFieldShapes_of_walk` — the old positivity walk's producer of the
kind-free facts of `StoredShapes.lean` (`StoredFieldShapes`): the walk on
the stored (DECLARED) constructor returns its normal form `tyN`, read
off its derivation (`MemberCtorD`); M3 is the walk's own check on `tyN`,
and the override is the substitution lemma iterated (`HoleSubst.lean`).
With its reading lemmas (`HoleLeafOk`, `u4_fieldSlot*`).  Consumed only
by the old route (`BlockHoleGrade.blockRunLink`, `ContAccFrame`,
`BlockAccRunCont`); it goes with the positivity walk at the class
check's flip.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal NestCtx nestAbstract nestHoles
  instPisWith openPisAtFvars fueledOps structUsedLater)

universe w

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

/-- **THE PRODUCER of the stored field shape facts** — the only place that
reads a stored constructor's syntax for them.  From the install's
positivity run at a stored (DECLARED) constructor of the block — the walk
takes the member-abstracted crest `crest` to its normal form `tyN` with
flat kinds; U2's sort row on `tyN`'s fields — the constructor's kind-free
facts, the members' formers, and the walk's semantic link (`hlink`, from
`memberCtorD_red`: the crest and the normal form read as Π-towers with
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
    {tyN : Expr} {ksD : List ConLeche.PosKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env ctx nF crest ksD tyN ts)
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
  obtain ⟨nds, rest, htele, -, -, -, hresFree', hha⟩ := hd
  obtain ⟨-, -, xs, hop, -⟩ := posD_tele_open htele
  rw [Nat.add_zero] at hop
  have hresFree : ∀ a ∈ rest.getAppArgs.drop ctx.nP,
      a.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false := fun a ha => by
    simpa using List.all_eq_true.mp hresFree' a ha
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
