module

import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.FixRecRead
import ConLeche.Model.Inductives.FixCtorReads
public section

/-!
# A block field's readings (task #315 M3)

`FieldReadAt` (`ConLeche/Model/Inductives/FixRecRead.lean`) — the
per-field package the recursor lane's `ihNodeVal_blockRec` consumes —
off a BLOCK constructor's reading record `BlockCtorDataI`
(`BlockData.lean`), the block route's counterpart of the native
route's `CtorReadR`.

The native route builds the package by `fieldReadAt_of`, out of
`CtorReadR`'s `fieldRead`/`recEntry`/`fieldArity`/`teleLen` — but
`CtorReadR` is a SINGLE family's record (one former `T`, one index
count), and a block's field reads at the former of the member it
TARGETS.  `FieldReadAt` itself mentions neither the former nor the
index count, so the algebra `fieldReadAt_of` performs is factored out
here once, `fieldReadAt_of_parts`, with the family's leaf a free
`AnnotTerm` and the index count a free `Nat`; `blockFieldReadAt_of`
is that at the block's per-field target.

**The bound.**  The package exists at a field whose domain is (a
Π-tower over) a member of the block — the RECURSIVE and REFLEXIVE
fields.  At an ordinary field `BlockCtorDataI` supplies no telescope
(`tssNone`) and no readings (`ordNone`), and nothing asks: the
recursor lane's `hfld` is bounded to the fields the frame's `ihKeys`
name (`BlockRecRule.lean`), and `blockIhKeys` ranges over
`blockRecIdxOf` — exactly the recursive and reflexive positions
(`pairIdxOf_blockIhKeys_kind`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind BlockFieldKind IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The algebra, with the family free -/

/-- **A field's readings, off its domain's reading** — `fieldReadAt_of`
with the family's leaf `A` and the index count `nI` free.

`hdom` is the field's domain, at the field's own depth with the
parameters and the earlier fields as variables, read as the Π-tower
over the field's telescope `tl` of `A` at the parameter variables and
the field's index readings `Eis`.  Peeling the tower at the raw
binder's own `∀`-binders gives the telescope binderwise (clauses 1 and
2), and inverting the body's application spine — whose argument count
is `harity` — the index expressions (clause 3). -/
theorem fieldReadAt_of_parts {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF nI i : Nat} {cty : Expr} {fvs : List Expr} {o : Expr}
    {cbs : List (Expr × BinderMeta)} {cbody : Expr} {A : AnnotTerm}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hst : cty.stripPis (nP + nF) = some (cbs, cbody))
    (hop : ConLeche.openPisAtFvars (nP + nF) cty 0 = some (fvs, o))
    (hlen0 : fvs.length = nP + nF)
    (hidx0 : ∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hiF : i < nF)
    (hteleLen : tl.length = (ConLeche.structFieldTeleOf cty nP nF i).length)
    (heisLen : Eis.length = nI)
    (harity : (((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs).length = nP + nI)
    (hdom : ∀ x, fvs[nP + i]? = some x →
      denoteMeta m.acval env ψ (nP + i) x.fvarTypeD
        = some (mkPisAV tl
            (AnnotTerm.mkAppN A (paramBvarsAt nP (nP + i + tl.length) ++ Eis)))) :
    FieldReadAt m ψ nP nF i cty fvs tl Eis := by
  obtain ⟨x, hx⟩ : ∃ x, fvs[nP + i]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen0]; omega)⟩
  obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by rw [ConLeche.Expr.stripPis_length _ hst]; omega)⟩
  have hbd : cbs.getD (nP + i) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  have htele : ConLeche.structFieldTeleOf cty nP nF i = (b.1.piBinders).1 := by
    unfold ConLeche.structFieldTeleOf
    rw [hst]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hidxOf : ConLeche.structFieldIdxOf cty nP nF i
      = (b.1.piBinders).2.getAppArgs.drop nP := by
    unfold ConLeche.structFieldIdxOf
    rw [hst]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hlenTl : tl.length = (b.1.piBinders).1.length := by rw [hteleLen, htele]
  have hS : (fvs.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (y : Expr), (fvs.take (nP + i))[k]? = some y →
      ∃ ty, y = Expr.fvar k ty := by
    intro k y hy
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hy
        exact nomatch hy
    rw [List.getElem?_take, if_pos hk] at hy
    exact hidx0 k y hy
  have hread := hdom x hx
  rw [openPisAtFvars_fvarTypeD (nP + nF) hop hst (nP + i) b x hb hx,
    ← Expr.mkPisOf_piBinders b.1] at hread
  obtain ⟨tl₀, B, heq, hlen₀, hbind, hbody⟩ :=
    denoteMeta_instSeq_mkPisOf_inv (b.1.piBinders).1 (b.1.piBinders).2 (fvs.take (nP + i))
      (nP + i) _ hS hidxS hread
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by rw [hlenTl, hlen₀]) heq
  refine ⟨by rw [htele, hlenTl], ?_, ?_⟩
  · intro k b' p hb' hp
    rw [htele] at hb'
    exact hbind k b' p hb' hp
  · rw [← hlenTl] at hbody
    rw [hbd] at harity
    rw [← Expr.mkAppN_getApp (b.1.piBinders).2, Expr.instSeq_mkAppN] at hbody
    obtain ⟨fa, vs, hfa, hsp, hval⟩ := denoteMeta_mkAppN_inv hbody
    have hlenvs : vs.length = nP + nI := by
      rw [← hsp.length, List.length_map]
      exact harity
    have hlenPE : (paramBvarsAt nP (nP + i + tl.length) ++ Eis).length = nP + nI := by
      rw [List.length_append, paramBvarsAt, List.length_map, List.length_range, heisLen]
    obtain ⟨-, hvs⟩ := mkAppN_inj_args hval (by rw [hlenPE, hlenvs])
    rw [← List.take_append_drop nP ((b.1.piBinders).2.getAppArgs), List.map_append] at hsp
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.append_inv hsp
    have hlen1 : vs₁.length = nP := by
      rw [← hsp₁.length, List.length_map, List.length_take, harity]
      omega
    obtain ⟨-, rfl⟩ := List.append_inj hvs
      (by rw [hlen1, paramBvarsAt, List.length_map, List.length_range])
    rw [hidxOf]
    exact hsp₂

/-! ## The block instance -/

/-- **A block field's readings, off the constructors' stage's own
record.**  `fieldReadAt_of_parts` at the field's TARGET member's
former and index count: the recursive field's entry is
`BlockCtorDataI.recEntry` (an empty telescope, `tssNone`), the
reflexive one's `reflEntry`, and the telescope's length and the
domain's argument count come from the opened-form guard
(`BlockOpened.recF`/`reflF`, through `BlockCtorDataI.reflOpen`).

Bounded to the RECURSIVE and REFLEXIVE fields: at an ordinary field
the record supplies neither telescope nor readings, and no consumer
asks (see the module docstring). -/
theorem blockFieldReadAt_of {m : EnvModel V env} {ψ : Name → Nat} {env₀ : Env}
    {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List RecFieldKind} {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcd : BlockCtorDataI m env₀ T Tof nIdxOf lps cvC nP nF nIdx resSort isProp large
      idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    {fvs : List Expr} {o : Expr} {i : Nat}
    (hop : ConLeche.openPisAtFvars (nP + nF) cvC.type 0 = some (fvs, o))
    (hiF : i < nF)
    (hk : ks.getD i .ordinary = .recursive ∨ ks.getD i .ordinary = .reflexive) :
    FieldReadAt m ψ nP nF i cvC.type fvs ((tss ψ).getD i []) ((Eiss ψ).getD i []) := by
  obtain ⟨cbs, es, hst, -⟩ := hcd.resid
  obtain ⟨crest, hopP, hopX⟩ := hcd.opens
  have hopAll : ConLeche.openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop.symm.trans hopAll))
  have hlen0 : (fvsP ++ xFvs).length = nP + nF := by
    rw [List.length_append, hcd.pLen, hcd.xLen]
  have hidx0 : ∀ (k : Nat) (y : Expr), (fvsP ++ xFvs)[k]? = some y → ∃ ty, y = Expr.fvar k ty :=
    fun k y hy => by
      obtain ⟨ty, h⟩ := (opening_vars_at hopAll).2.1 k y hy
      exact ⟨ty, by rw [h, Nat.zero_add]⟩
  obtain ⟨x, hx⟩ : ∃ x, xFvs[i]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hcd.xLen]; exact hiF)⟩
  have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
    rw [List.getElem?_append_right (by rw [hcd.pLen]; omega), hcd.pLen, Nat.add_sub_cancel_left]
    exact hx
  have hbd : ∃ b, cbs[nP + i]? = some b ∧ cbs.getD (nP + i) default = b := by
    have hlt : nP + i < cbs.length := by rw [ConLeche.Expr.stripPis_length _ hst]; omega
    exact ⟨_, List.getElem?_eq_getElem hlt, by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl⟩
  obtain ⟨b, hb, hbdEq⟩ := hbd
  -- the raw binder's Π-tower and its body's spine, through the opening's frame
  have hfvL : ∀ a ∈ (fvsP ++ xFvs).take (nP + i), ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
    intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
    obtain ⟨ty, rfl⟩ := hidx0 q a hq
    exact ⟨_, ty, rfl⟩
  have hpb : (x.fvarTypeD.piBinders).1.length = (b.1.piBinders).1.length ∧
      (x.fvarTypeD.piBinders).2.getAppArgs.length = (b.1.piBinders).2.getAppArgs.length := by
    have hty := openPisAtFvars_fvarTypeD (nP + nF) hopAll hst (nP + i) b x hb hxA
    have hlenTake : ((fvsP ++ xFvs).take (nP + i)).length = nP + i := by
      rw [List.length_take, hlen0]
      omega
    obtain ⟨h1, h2⟩ := Expr.piBinders_instSeq ((fvsP ++ xFvs).take (nP + i))
      (nP + i - 1) b.1 hfvL (by rw [hlenTake]; omega)
    rw [hty]
    refine ⟨h1, ?_⟩
    rw [h2, Expr.getAppArgs_instSeq_fvars _ _ _ hfvL, List.length_map]
  have hteleEq : ConLeche.structFieldTeleOf cvC.type nP nF i = (b.1.piBinders).1 := by
    unfold ConLeche.structFieldTeleOf
    rw [hst]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  refine fieldReadAt_of_parts (nI := nIdxOf i) (A := m.acval (Tof i) ψ) hst hopAll hlen0 hidx0
    hiF ?_ ?_ ?_ ?_
  · -- the telescope's length
    rw [hteleEq, ← hpb.1]
    rcases hk with hk | hk
    · obtain ⟨hfn, -, -, -, -, -⟩ := hcd.opened.recF i x hx hk
      rw [Expr.piBinders_nil_of_getAppFn_const hfn,
        hcd.tssNone ψ i (fun h => by rw [hk] at h; exact nomatch h)]
      rfl
    · obtain ⟨afvs, body, -, hlenTl, -, -⟩ := hcd.reflOpen ψ i x hx hk
      rw [hlenTl]
  · -- the index readings' count
    rcases hk with hk | hk
    · exact hcd.eisLen ψ i hk hiF
    · exact hcd.eisLenRefl ψ i hk hiF
  · -- the domain's argument count, under the field's own telescope
    rw [hbdEq, ← hpb.2]
    rcases hk with hk | hk
    · obtain ⟨hfn, -, hlenA, -, -, -⟩ := hcd.opened.recF i x hx hk
      rw [Expr.piBinders_nil_body (Expr.piBinders_nil_of_getAppFn_const hfn)]
      exact hlenA
    · obtain ⟨afvs, body, hopA, -, -, -, -, hlenA, -, -, -⟩ := hcd.opened.reflF i x hx hk
      have hbody := openPisAtFvars_instSeq (x.fvarTypeD.piBinders).1.length hopA
        (Expr.stripPis_piBinders x.fvarTypeD)
      have hfvA : ∀ a ∈ afvs, ∃ (k : Nat) (ty : Expr), a = Expr.fvar k ty := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := (opening_vars_at hopA).2.1 q a hq
        exact ⟨_, ty, rfl⟩
      rw [hbody, Expr.getAppArgs_instSeq_fvars _ _ _ hfvA, List.length_map] at hlenA
      exact hlenA
  · -- the domain reads to the field's entry
    intro x' hx'
    rw [Option.some.inj (hx'.symm.trans hxA), hcd.domRead ψ i x hx]
    rcases hk with hk | hk
    · rw [hcd.tssNone ψ i (fun h => by rw [hk] at h; exact nomatch h),
        hcd.recEntry ψ i hk hiF]
      rfl
    · rw [hcd.reflEntry ψ i hk hiF]

/-! ## The bound, from the frame's `ihKeys` -/

/-- A found position names its pair. -/
theorem mem_of_pairIdxOf? {ps : List (Nat × Nat)} {p : Nat × Nat} {r : Nat}
    (h : ConLeche.pairIdxOf? ps p = some r) : p ∈ ps := by
  have hr : r < ps.length := List.mem_range.mp (List.mem_of_find?_eq_some h)
  have hp : ps.getD r (0, 0) = p := by
    have := List.find?_some h
    simpa using this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr] at hp
  exact hp ▸ List.getElem_mem hr

/-- The recursive positions of a block constructor: in range, and with
a kind that carries a target. -/
theorem mem_blockRecIdxOf {ks : List BlockFieldKind} {i : Nat}
    (h : i ∈ ConLeche.blockRecIdxOf ks) :
    i < ks.length ∧
      ((ks.map BlockFieldKind.toRec).getD i .ordinary = .recursive ∨
        (ks.map BlockFieldKind.toRec).getD i .ordinary = .reflexive) := by
  unfold ConLeche.blockRecIdxOf at h
  rw [List.mem_filter, List.mem_range] at h
  refine ⟨h.1, ?_⟩
  rw [getD_map_toRec]
  have h2 := h.2
  cases hq : ks.getD i .ordinary with
  | ordinary => rw [hq] at h2; exact nomatch h2
  | recursive t => exact Or.inl rfl
  | reflexive t => exact Or.inr rfl
  | negative => rw [hq] at h2; exact nomatch h2
  | unsupported => rw [hq] at h2; exact nomatch h2

end ConLeche.Model
