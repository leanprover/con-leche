import Setlec.Verify.Cached.BridgeCP
import Setlec.Verify.ParseP

/-!
# The conversion boundary: parsed declarations become `DeclC`s (task #163)

`Setlec/Verify/Cached/GuardsC.lean` proves the expression-level half of
the conversion (`ofStore_spec_denote`: at a *denoting* index the
conversion succeeds and its result erases to the denotation).  This
file lifts that to declarations and supplies the missing totality leg.

The production driver's fold gets `denoteDeclP s₀.store pd = some d`
from `denoteDeclP_total` applied to the per-step index-range check
(`checkDeclSPStep_inRange`).  The cached driver has **no** range check
— `declsCOfP` runs before the fold and simply fails when an index does
not resolve.  What its *success* gives instead is
`ofStore_denote_of_some` below: a converted index either hit the memo
(whose invariant already carries the denotation) or read a node, and a
stored node read on a canonical store is a `Valid1` index, whose
denotation is total (`denote_total`).  So conversion success replaces
the range check as the totality supplier, and the two halves compose
into `ofStore_rel`: the acceptance-direction statement the capstone's
fold consumes, in the shape `checkDeclSPStepC_run` wants
(`DeclCRel pc d` for the *denoted* declaration `d`).

Nothing here needs the reverse (rejection) direction, and nothing here
is stated at a non-canonical store: the driver's argument is a
`WFStore`.
-/

namespace Setlec.Cached

open Setlec
open Setlec.Cached.ExprC

/-! ## The declaration-level conversion relation -/

/-- A parsed declaration and its conversion, related through the
denotation: `pd` denotes `d` in the parse store and the converted `pc`
is `DeclCRel`-related to `d`.  This is exactly the pair of facts
`foldSP_R` obtains from `denoteDeclP_total` + `checkDeclSPStep_run`'s
premise, packaged for a driver that converts up front. -/
def DeclPCRel (st : EStore) (pd : DeclP) (pc : DeclC) : Prop :=
  ∃ d, denoteDeclP st pd = some d ∧ DeclCRel pc d

/-- The pointwise (`Forall₂`-shaped) lift of `DeclPCRel` to lists.
Spelled out rather than imported: core Lean has no `List.Forall₂`, and
the two consumers (the fold, and the input-level membership argument)
want exactly the two constructors. -/
inductive DeclsPCRel (st : EStore) : List DeclP → List DeclC → Prop where
  | nil : DeclsPCRel st [] []
  | cons {pd : DeclP} {pc : DeclC} {pds : List DeclP} {ds : List DeclC} :
      DeclPCRel st pd pc → DeclsPCRel st pds ds →
      DeclsPCRel st (pd :: pds) (pc :: ds)

/-! ## Totality from conversion success -/

/-- **Conversion success supplies the denotation's totality.**  This is
the cached driver's replacement for the parsed-index driver's
`inRangeB` check: `ofStoreGo` either hits the memo — and the memo
invariant already carries a denotation — or reads a node, and a stored
node read on a canonical store is a valid tier-one index. -/
theorem ofStore_denote_of_some {st : EStore} (hwf : st.WF) {s : OfStoreS}
    {e : EIdx} {c : ExprC} (hs : OfStoreS.Inv st s)
    (h : (ofStore st s e).1 = some c) : ∃ x, st.denote e = some x := by
  rcases hgo : ofStoreGo st s.memo s.lmemo e with ⟨r, memo', lmemo'⟩
  have hr : r = some c := by rw [ofStore, hgo] at h; exact h
  unfold ofStoreGo at hgo
  cases hm : s.memo[e]? with
  | some y =>
    rw [hm] at hgo
    injection hgo with h1
    obtain ⟨-, hdy⟩ := hs.1 e y hm
    rw [hwf.denoteT_eq] at hdy
    exact ⟨_, hdy⟩
  | none =>
    rw [hm] at hgo
    cases hn : st.getNode e with
    | none =>
      rw [hn] at hgo
      injection hgo with h1
      rw [← h1] at hr
      exact nomatch hr
    | some n =>
      have hn1 : st.node1? e = some n := by rw [← hwf.getNode_eq]; exact hn
      exact EStore.denote_total hwf e (EStore.node1?_valid1 hn1)

/-- **The conversion boundary, acceptance direction.**  A successful
`ofStore` on a canonical parse store returns the conversion of the
index's denotation, and re-establishes the threaded invariant. -/
theorem ofStore_rel {st : EStore} (hwf : st.WF) {s : OfStoreS}
    {e : EIdx} {c : ExprC} (hs : OfStoreS.Inv st s)
    (h : (ofStore st s e).1 = some c) :
    (∃ x, st.denote e = some x ∧ RelC c x) ∧
      OfStoreS.Inv st (ofStore st s e).2 := by
  obtain ⟨x, hx⟩ := ofStore_denote_of_some hwf hs h
  obtain ⟨c', hc', hwc, hec, hinv⟩ := ofStore_spec_denote hwf hs hx
  rw [hc'] at h
  obtain rfl : c' = c := Option.some.inj h
  exact ⟨⟨x, hx, hwc, hec⟩, hinv⟩

/-! ## Headers and declarations -/

/-- A successful header conversion denotes, and the converted header is
the denoted one field by field. -/
theorem cvCOfP_rel {st : EStore} (hwf : st.WF) {s : OfStoreS}
    {cv : ConstantValP} {cvc : ConstantValC}
    (hs : OfStoreS.Inv st s) (h : (cvCOfP st s cv).1 = some cvc) :
    (∃ ty, st.denote cv.type = some ty ∧ RelC cvc.type ty ∧
        cvc.name = cv.name ∧ cvc.levelParams = cv.levelParams) ∧
      OfStoreS.Inv st (cvCOfP st s cv).2 := by
  rcases hf : ofStore st s cv.type with ⟨r, s₁⟩
  have hr1 : (ofStore st s cv.type).1 = r := by rw [hf]
  have hr2 : (ofStore st s cv.type).2 = s₁ := by rw [hf]
  cases r with
  | none =>
    rw [cvCOfP, hf] at h
    exact nomatch h
  | some t =>
    obtain ⟨⟨x, hx, hrel⟩, hinv⟩ := ofStore_rel hwf hs hr1
    rw [hr2] at hinv
    rw [cvCOfP, hf] at h
    dsimp only at h
    obtain rfl : (⟨cv.name, cv.levelParams, t⟩ : ConstantValC) = cvc :=
      Option.some.inj h
    refine ⟨⟨x, hx, hrel, rfl, rfl⟩, ?_⟩
    rw [cvCOfP, hf]
    exact hinv

/-- **One declaration converts to a `DeclCRel`-related twin.**  The
per-step premise `checkDeclSPStepC_run` takes, supplied where
`foldSP_R` supplies `denoteDeclP s₀.store pd = some d`. -/
theorem declCOfP_rel {st : EStore} (hwf : st.WF) {s : OfStoreS}
    {pd : DeclP} {pc : DeclC} (hs : OfStoreS.Inv st s)
    (h : (declCOfP st s pd).1 = some pc) :
    DeclPCRel st pd pc ∧ OfStoreS.Inv st (declCOfP st s pd).2 := by
  cases pd with
  | basisDecl kind =>
    rw [declCOfP] at h
    dsimp only at h
    obtain rfl : DeclC.basisDecl kind = pc := Option.some.inj h
    exact ⟨⟨_, rfl, .basisDecl⟩, by rw [declCOfP]; exact hs⟩
  | indDecl block =>
    rw [declCOfP] at h
    dsimp only at h
    obtain rfl : DeclC.indDecl block = pc := Option.some.inj h
    exact ⟨⟨_, rfl, .indDecl⟩, by rw [declCOfP]; exact hs⟩
  | axiomDecl v =>
    rcases hf : cvCOfP st s v with ⟨r, s₁⟩
    have hr1 : (cvCOfP st s v).1 = r := by rw [hf]
    have hr2 : (cvCOfP st s v).2 = s₁ := by rw [hf]
    cases r with
    | none => rw [declCOfP, hf] at h; exact nomatch h
    | some cvc =>
      obtain ⟨⟨ty, hty, hrel, hnm, hlp⟩, hinv⟩ := cvCOfP_rel hwf hs hr1
      rw [hr2] at hinv
      rw [declCOfP, hf] at h
      dsimp only at h
      obtain rfl : DeclC.axiomDecl cvc = pc := Option.some.inj h
      refine ⟨⟨.axiomDecl ⟨cvc.name, cvc.levelParams, ty⟩, ?_,
        .axiomDecl hrel⟩, by rw [declCOfP, hf]; exact hinv⟩
      simp [denoteDeclP, denoteCVP, hty, hnm, hlp]
  | defnDecl v value hint =>
    rcases hf : cvCOfP st s v with ⟨r, s₁⟩
    have hr1 : (cvCOfP st s v).1 = r := by rw [hf]
    have hr2 : (cvCOfP st s v).2 = s₁ := by rw [hf]
    cases r with
    | none => rw [declCOfP, hf] at h; exact nomatch h
    | some cvc =>
      obtain ⟨⟨ty, hty, hrel, hnm, hlp⟩, hinv⟩ := cvCOfP_rel hwf hs hr1
      rw [hr2] at hinv
      rw [declCOfP, hf] at h
      dsimp only at h
      rcases hg : ofStore st s₁ value with ⟨rv, s₂⟩
      have hv1 : (ofStore st s₁ value).1 = rv := by rw [hg]
      have hv2 : (ofStore st s₁ value).2 = s₂ := by rw [hg]
      rw [hg] at h
      cases rv with
      | none => dsimp only at h; exact nomatch h
      | some vc =>
        obtain ⟨⟨ve, hve, hrelv⟩, hinv₂⟩ := ofStore_rel hwf hinv hv1
        rw [hv2] at hinv₂
        dsimp only at h
        obtain rfl : DeclC.defnDecl cvc vc hint = pc := Option.some.inj h
        refine ⟨⟨.defnDecl ⟨cvc.name, cvc.levelParams, ty⟩ ve hint, ?_,
          .defnDecl hrel hrelv⟩, by simp only [declCOfP, hf, hg]; exact hinv₂⟩
        simp [denoteDeclP, denoteCVP, hty, hve, hnm, hlp]
  | thmDecl v value =>
    rcases hf : cvCOfP st s v with ⟨r, s₁⟩
    have hr1 : (cvCOfP st s v).1 = r := by rw [hf]
    have hr2 : (cvCOfP st s v).2 = s₁ := by rw [hf]
    cases r with
    | none => rw [declCOfP, hf] at h; exact nomatch h
    | some cvc =>
      obtain ⟨⟨ty, hty, hrel, hnm, hlp⟩, hinv⟩ := cvCOfP_rel hwf hs hr1
      rw [hr2] at hinv
      rw [declCOfP, hf] at h
      dsimp only at h
      rcases hg : ofStore st s₁ value with ⟨rv, s₂⟩
      have hv1 : (ofStore st s₁ value).1 = rv := by rw [hg]
      have hv2 : (ofStore st s₁ value).2 = s₂ := by rw [hg]
      rw [hg] at h
      cases rv with
      | none => dsimp only at h; exact nomatch h
      | some vc =>
        obtain ⟨⟨ve, hve, hrelv⟩, hinv₂⟩ := ofStore_rel hwf hinv hv1
        rw [hv2] at hinv₂
        dsimp only at h
        obtain rfl : DeclC.thmDecl cvc vc = pc := Option.some.inj h
        refine ⟨⟨.thmDecl ⟨cvc.name, cvc.levelParams, ty⟩ ve, ?_,
          .thmDecl hrel hrelv⟩, by simp only [declCOfP, hf, hg]; exact hinv₂⟩
        simp [denoteDeclP, denoteCVP, hty, hve, hnm, hlp]
  | opaqueDecl v value =>
    rcases hf : cvCOfP st s v with ⟨r, s₁⟩
    have hr1 : (cvCOfP st s v).1 = r := by rw [hf]
    have hr2 : (cvCOfP st s v).2 = s₁ := by rw [hf]
    cases r with
    | none => rw [declCOfP, hf] at h; exact nomatch h
    | some cvc =>
      obtain ⟨⟨ty, hty, hrel, hnm, hlp⟩, hinv⟩ := cvCOfP_rel hwf hs hr1
      rw [hr2] at hinv
      rw [declCOfP, hf] at h
      dsimp only at h
      rcases hg : ofStore st s₁ value with ⟨rv, s₂⟩
      have hv1 : (ofStore st s₁ value).1 = rv := by rw [hg]
      have hv2 : (ofStore st s₁ value).2 = s₂ := by rw [hg]
      rw [hg] at h
      cases rv with
      | none => dsimp only at h; exact nomatch h
      | some vc =>
        obtain ⟨⟨ve, hve, hrelv⟩, hinv₂⟩ := ofStore_rel hwf hinv hv1
        rw [hv2] at hinv₂
        dsimp only at h
        obtain rfl : DeclC.opaqueDecl cvc vc = pc := Option.some.inj h
        refine ⟨⟨.opaqueDecl ⟨cvc.name, cvc.levelParams, ty⟩ ve, ?_,
          .opaqueDecl hrel hrelv⟩, by simp only [declCOfP, hf, hg]; exact hinv₂⟩
        simp [denoteDeclP, denoteCVP, hty, hve, hnm, hlp]

/-! ## The whole list -/

/-- **The driver's conversion pass is pointwise correct.**  A
successful `declsCOfP` returns the conversions of the input's
denotations, one for one. -/
theorem declsCOfP_rel {st : EStore} (hwf : st.WF) :
    ∀ (pds : List DeclP) (s : OfStoreS) {ds : List DeclC},
      OfStoreS.Inv st s → declsCOfP st s pds = .ok ds →
      DeclsPCRel st pds ds
  | [], s, ds, _, h => by
    obtain rfl : ([] : List DeclC) = ds := Except.ok.inj h
    exact .nil
  | pd :: pds, s, ds, hs, h => by
    rcases hf : declCOfP st s pd with ⟨r, s₁⟩
    have hr1 : (declCOfP st s pd).1 = r := by rw [hf]
    have hr2 : (declCOfP st s pd).2 = s₁ := by rw [hf]
    cases r with
    | none => rw [declsCOfP, hf] at h; exact nomatch h
    | some pc =>
      obtain ⟨hrel, hinv⟩ := declCOfP_rel hwf hs hr1
      rw [hr2] at hinv
      rw [declsCOfP, hf] at h
      dsimp only at h
      cases hrest : declsCOfP st s₁ pds with
      | error e => rw [hrest] at h; exact nomatch h
      | ok ds' =>
        rw [hrest] at h
        obtain rfl : pc :: ds' = ds := Except.ok.inj h
        exact .cons hrel (declsCOfP_rel hwf pds s₁ hinv hrest)

/-- The membership form the fold consumes: every converted declaration
relates to *some* spec declaration.  (The fold's step needs only this;
the positional form above is what the input-level statements need.) -/
theorem declsCOfP_relable {st : EStore} (hwf : st.WF)
    {pds : List DeclP} {s : OfStoreS} {ds : List DeclC}
    (hs : OfStoreS.Inv st s) (h : declsCOfP st s pds = .ok ds) :
    ∀ pc ∈ ds, ∃ d, DeclCRel pc d := by
  have hall := declsCOfP_rel hwf pds s hs h
  clear h hs
  induction hall with
  | nil => intro pc hpc; exact nomatch hpc
  | cons hrel _ ih =>
    intro pc hpc
    rcases List.mem_cons.mp hpc with rfl | hmem
    · obtain ⟨d, -, hd⟩ := hrel
      exact ⟨d, hd⟩
    · exact ih pc hmem

end Setlec.Cached
