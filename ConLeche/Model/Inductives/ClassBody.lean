module

public import ConLeche.Model.Inductives.ClassIdent
public import ConLeche.Model.Inductives.ClassComplete
import ConLeche.Model.IndReduct

public section

/-!
# A crest's result, identified (P2d, DESIGN CLASSCHECK / P2D4)

`classCrest_spineFit_recorded` identifies a container class's crest's
FIELDS with its container's recorded fields.  The recorded fit (`HFits`)
also fixes the index tuple the constructor lands at — the recorded result
index readings (`resIdx`).  This file identifies the crest's result with
them.

**The crest's result is its own class applied to its indices.**  The
constructor's conclusion is its inductive applied to parameters and
indices; the class check's walk ends at the class's OWN hole
(`ClassResOk`), so the abstraction recognised the whole conclusion
(`classAbs_head_hole`: an abstraction headed by a hole recognised the
whole spine) and replaced it by the hole applied to its abstracted
indices (`classAbsSpec_occ_spine`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo classOcc?)

universe w

/-! ## The recogniser along a spine -/

section Spine

variable {cls : List ClassInfo} {H : Nat}

/-- **One more index argument**: an occurrence applied to one more
argument is an occurrence with one more index. -/
theorem classOcc_app_succ (hwf : ClassOccWF cls H) {f a h : Expr} {n : Nat}
    (hf : classOcc? cls f = some (h, n)) : classOcc? cls (.app f a) = some (h, n + 1) := by
  obtain ⟨c, hc, hch, us, hfn, hle, hn, -⟩ := classOcc_spec hwf hf
  have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
  have hchs : c.hole.isSome := by rw [hch]; rfl
  have hfilt : cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ (f.getAppArgs ++ [a]).length))
      = cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ f.getAppArgs.length)) := by
    apply List.filter_congr
    intro c' hc'
    by_cases hh : c'.hole.isSome
    · by_cases hI : c'.key.ind = c.key.ind
      · have := hwf.nPc c' hc' c hc hh hchs hI
        simp [hh, hI, this]
        omega
      · have hI' : (c'.key.ind == c.key.ind) = false := by simpa using hI
        simp [hI']
    · simp [hh]
  unfold classOcc? at hf ⊢
  rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl, hfn]
  rw [hfn] at hf
  dsimp only at hf ⊢
  rw [hargs, hfilt]
  have hmem : ∀ c', c' ∈ cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
      decide (c'.nPc ≤ f.getAppArgs.length)) → c'.nPc = c.nPc := by
    intro c' hc'
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
    exact hwf.nPc c' hc'.1 c hc hc'.2.1.1 hchs hc'.2.1.2
  revert hmem hf
  generalize cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
      decide (c'.nPc ≤ f.getAppArgs.length)) = cs
  intro hf hmem
  match cs, hf, hmem with
  | [], hf, _ => exact nomatch hf
  | c0 :: rest, hf, hmem =>
    have h0 := hmem c0 (List.mem_cons_self ..)
    have htake : (f.getAppArgs ++ [a]).take c0.nPc = f.getAppArgs.take c0.nPc :=
      List.take_append_of_le_length (by omega)
    simp only [htake, List.length_append, List.length_singleton]
    simp only at hf
    have hpk : ∀ c', c' ∈ c0 :: rest →
        (c'.hole.map fun h' => (h', f.getAppArgs.length - c'.nPc)) = some (h, n) →
        (c'.hole.map fun h' => (h', f.getAppArgs.length + 1 - c'.nPc)) = some (h, n + 1) := by
      intro c' hc' hp
      have := hmem c' hc'
      cases hh : c'.hole with
      | none => rw [hh] at hp; exact nomatch hp
      | some h' =>
        rw [hh] at hp
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp ⊢
        exact ⟨hp.1, by omega⟩
    split at hf
    · rename_i c1 hf1
      try rw [hf1]
      exact hpk c1 (List.mem_of_find?_eq_some hf1) hf
    · rename_i hf1
      try rw [hf1]
      split at hf
      · rename_i c1 hf2
        try rw [hf2]
        exact hpk c1 (List.mem_of_find?_eq_some hf2) hf
      · exact nomatch hf

/-- The abstraction in `some` mode, along a recognised spine: the hole
applied to the last `n` arguments abstracted. -/
theorem classAbsSpec_some_spine {occ : Expr → Option (Expr × Nat)}
    (hsp : ∀ x h n, occ x = some (h, n + 1) → ∃ f a, x = .app f a ∧ occ f = some (h, n)) :
    ∀ (n : Nat) (x h : Expr), occ x = some (h, n) →
      ∃ as : List Expr, as.length = n ∧ ConLeche.classAbsSpec occ (some (h, n)) x
        = Expr.mkAppN h (as.map (ConLeche.classAbsSpec occ none)) ∧
        ∃ f, x = Expr.mkAppN f as ∧ occ f = some (h, 0)
  | 0, x, h, hx => ⟨[], rfl, by cases x <;> rfl, x, rfl, hx⟩
  | n + 1, x, h, hx => by
    obtain ⟨f, a, rfl, hf⟩ := hsp x h n hx
    obtain ⟨as, hl, he, g, rfl, hg⟩ := classAbsSpec_some_spine hsp n f h hf
    refine ⟨as ++ [a], by simp [hl], ?_, g, by rw [Expr.mkAppN_append']; rfl, hg⟩
    simp only [ConLeche.classAbsSpec, he, List.map_append, List.map_cons, List.map_nil,
      Expr.mkAppN_append']
    rfl

/-- The abstraction at a recognised application (`none` mode). -/
theorem classAbsSpec_occ {occ : Expr → Option (Expr × Nat)} {f a h : Expr} {n : Nat}
    (hx : occ (.app f a) = some (h, n)) :
    ConLeche.classAbsSpec occ none (.app f a) = ConLeche.classAbsSpec occ (some (h, n)) (.app f a) := by
  simp only [ConLeche.classAbsSpec, hx]
  rcases n with _ | n <;> rfl

/-- **An abstraction headed by a hole recognised the whole spine**: at a
constant-headed term, the abstraction's head is a free variable only if
the recogniser took the whole term (the longest prefix it takes, and
one more argument never loses an occurrence). -/
theorem classAbs_head_hole {occ : Expr → Option (Expr × Nat)}
    (hsp : ∀ x h n, occ x = some (h, n + 1) → ∃ f a, x = .app f a ∧ occ f = some (h, n))
    (hsucc : ∀ f a h n, occ f = some (h, n) → occ (.app f a) = some (h, n + 1))
    (hhole : ∀ x h n, occ x = some (h, n) → ∃ j t, h = .fvar j t)
    {i : Nat} {ty : Expr} :
    ∀ (x : Expr) (I : Name) (us : List Level), x.getAppFn = .const I us →
      (ConLeche.classAbsSpec occ none x).getAppFn = .fvar i ty →
      ∃ f a n, x = .app f a ∧ occ x = some (.fvar i ty, n) := by
  intro x
  induction x with
  | app f a ihf _ =>
    intro I us hfn hhd
    have hfn' : f.getAppFn = .const I us := hfn
    cases hx : occ (.app f a) with
    | none =>
      simp only [ConLeche.classAbsSpec, hx] at hhd
      obtain ⟨f', a', n, -, hf⟩ := ihf I us hfn' hhd
      rw [hsucc f a _ n hf] at hx
      exact nomatch hx
    | some p =>
      obtain ⟨h', n⟩ := p
      rw [classAbsSpec_occ hx] at hhd
      obtain ⟨as, -, he, -⟩ := classAbsSpec_some_spine hsp n _ h' hx
      rw [he, Expr.getAppFn_mkAppN'] at hhd
      refine ⟨f, a, n, rfl, ?_⟩
      obtain ⟨j, t, rfl⟩ := hhole _ _ _ hx
      simp only [Expr.getAppFn] at hhd
      cases hhd
      rfl
  | const n us' =>
    intro I us _ hhd
    simp [ConLeche.classAbsSpec, Expr.getAppFn] at hhd
  | _ =>
    intro I us hfn _
    simp [Expr.getAppFn] at hfn

end Spine

/-! ## The body of a Π-telescope, read -/

/-- The `n`-deep body of a Π-telescope. -/
@[expose] def bodyN : Nat → Expr → Expr
  | 0, X => X
  | n + 1, .forallE _ b _ => bodyN n b
  | _ + 1, X => X

section Body

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- **A Π-tower's body is its term's body read below the opened
binders**: for a transform commuting with `Π`. -/
theorem pis_body_read {H : Nat} {F : Expr → Expr}
    (hF : ∀ t b m, F (.forallE t b m) = .forallE (F t) (F b) m) :
    ∀ (n : Nat) (X : Expr), IsPisN n X → ∀ (d : Nat) (as : List Expr), LocList H d as →
      ∀ (ab : List (Nat × Nat × AnnotTerm)) (r : AnnotTerm), ab.length = n →
      denoteMeta acval env φ (H + d) ((F X).instantiateList as 0) = some (mkPisAV ab r) →
      ∃ L, LocList H (d + n) L ∧
        denoteMeta acval env φ (H + d + n) ((F (bodyN n X)).instantiateList L 0) = some r
  | 0, X, _, d, as, has, ab, r, hl, h => by
    cases ab with
    | nil => exact ⟨as, has, by simpa [bodyN, mkPisAV] using h⟩
    | cons _ _ => simp at hl
  | n + 1, X, hX, d, as, has, ab, r, hl, h => by
    obtain ⟨t, b, m, rfl, hb⟩ := hX
    cases ab with
    | nil => simp at hl
    | cons e ab =>
    rw [hF] at h
    simp only [Expr.instantiateList] at h
    rw [denoteMeta_forallE] at h
    obtain ⟨ta, ba, hta, hba, hP⟩ := obind2 h
    rw [← Expr.instantiateList_cons] at hba
    simp only [mkPisAV] at hP
    injection hP with _ _ _ hba'
    subst hba'
    obtain ⟨L, hL, hr⟩ := pis_body_read hF n b hb (d + 1) _
      (has.cons ((F t).instantiateList as 0)) ab r (by simpa using hl)
      (by rw [show H + (d + 1) = H + d + 1 by omega]; exact hba)
    refine ⟨L, by rw [show d + (n + 1) = d + 1 + n by omega]; exact hL, ?_⟩
    rw [show H + d + (n + 1) = H + (d + 1) + n by omega]
    simpa [bodyN] using hr

/-- **A spine headed by a free variable, instantiated and read**: the
variable's position applied to the arguments' readings. -/
theorem fvarSpine_read {D : Nat} {i : Nat} {ty : Expr} {as L : List Expr} {r : AnnotTerm}
    (h : denoteMeta acval env φ D ((Expr.mkAppN (.fvar i ty) as).instantiateList L 0) = some r) :
    ∃ vs, DenoteMetaSpine acval env φ D (as.map (·.instantiateList L 0)) vs ∧
      r = AnnotTerm.mkAppN (.bvar (D - 1 - i)) vs := by
  rw [Expr.instantiateList_mkAppN'] at h
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv h
  simp only [Expr.instantiateList] at hfa
  rw [denoteMeta_fvar] at hfa
  cases hfa
  exact ⟨vs, hsp, rfl⟩

/-- **The commutation equation's bodies**: the two substitution
instances' Π-towers are equal, so are their bodies (below the fields). -/
theorem commute_body (m : EnvModel V env) {H b D : Nat} {L A : Expr}
    {gL gR : Nat → Option Expr} {xL xR : Nat → AnnotTerm}
    (hgL : ∀ i, i < H → Expr.fvarsBelow D ((gL i).getD (.fvar i (.sort .zero))) ∧
      ((gL i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gL i).getD (.fvar i (.sort .zero))) = some (xL i))
    (hgR : ∀ i, i < b → Expr.fvarsBelow D ((gR i).getD (.fvar i (.sort .zero))) ∧
      ((gR i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gR i).getD (.fvar i (.sort .zero))) = some (xR i))
    (hL : Expr.fvarsBelow H L) (hA : Expr.fvarsBelow b A)
    (heq : (L.replaceFVars gL).eraseFVarTys = (A.replaceFVars gR).eraseFVarTys)
    {abL ab : List (Nat × Nat × AnnotTerm)} {rL r : AnnotTerm}
    (haL : denoteMeta m.acval env φ H L = some (mkPisAV abL rL))
    (haA : denoteMeta m.acval env φ b A = some (mkPisAV ab r)) (hlen : abL.length = ab.length) :
    AnnotTerm.substAV (substTau H D xL) rL abL.length
      = AnnotTerm.substAV (substTau b D xR) r ab.length := by
  have h := substRead_eq (φ := φ) m hgL hgR hL hA heq haL haA
  rw [AnnotTerm.substAV_mkPisAV, AnnotTerm.substAV_mkPisAV] at h
  obtain ⟨-, hB⟩ := mkPisAV_injC (by rw [substTele_len, substTele_len, hlen]) h
  simpa using hB

theorem liftN_mkAppN_B (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, liftN_mkAppN_B n k as, AnnotTerm.liftN_app]

theorem mkAppN_mkAppN_AV (f : AnnotTerm) (as bs : List AnnotTerm) :
    AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs = AnnotTerm.mkAppN f (as ++ bs) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [AnnotTerm.mkAppN_cons, List.cons_append, ih]

end Body

/-! ## The result, at a class's frame -/

section Result

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 6400000 in
/-- **The crest's result is the canonical text's, at the frame** (I2 for
the result): in the setting of `classCrest_spineFit_frame`, when the
crest's conclusion is its own class's hole applied to its indices (the
walked and the restricted abstraction alike, `hfB`/`hgB`) and the
canonical text's conclusion is member `c'`'s variable applied to the
parameters and the result index readings `es`: the hole is member `c'`'s
group hole, and under any spine of the fields' length the crest's index
readings at `τ` are the canonical ones at the frame. -/
theorem classCrest_result_frame (m : EnvModel V env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk m.acval env φ cls H) {isF isG : Expr → Bool}
    (hkf : KeysFOk m.acval env φ cls (fun h => isF h || isG h) H)
    (hFc : FClosed cls (fun h => isF h || isG h))
    {al : List ConLeche.ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta m.acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, (isF a.hole || isG a.hole) = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V m.acval env φ cls (fun h => isF h || isG h) H τ)
    (hsem : AliasKeySem V m.acval env φ cls al H Good)
    {names : List Name} {c : ClassInfo} {e0 A : Expr} {n : Nat} (hPis : IsPisN n e0)
    {lps : List Name} {us : List Level}
    (heq : ((classAbsF cls (fun h => isF h || isG h) e0).replaceFVars
        (ConLeche.classGL cls names c H (c.dsA.map (classAbsF cls isF)))).eraseFVarTys
      = ((A.instantiateLevelParams lps us).replaceFVars
        (ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF)))).eraseFVarTys)
    {pF : List AnnotTerm} (hlp : c.dsA.length = c.nPc) (hlpF : pF.length = c.nPc)
    (hpF : ∀ i, i < c.nPc → Expr.fvarsBelow H ((c.dsA.map (classAbsF cls isF)).getD i default) ∧
      ((c.dsA.map (classAbsF cls isF)).getD i default).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ H ((c.dsA.map (classAbsF cls isF)).getD i default)
        = some (pF.getD i default))
    (hL : Expr.fvarsBelow H (classAbsF cls (fun h => isF h || isG h) e0))
    (hA : Expr.fvarsBelow (c.nPc + names.length) (A.instantiateLevelParams lps us))
    {abC abL ab : List (Nat × Nat × AnnotTerm)} {rC rL r : AnnotTerm}
    (hCr : denoteMeta m.acval env φ H (ConLeche.classAliasAbs al (ConLeche.classAbs cls e0))
      = some (mkPisAV abC rC))
    (hLr : denoteMeta m.acval env φ H (classAbsF cls (fun h => isF h || isG h) e0)
      = some (mkPisAV abL rL))
    (hAr : denoteMeta m.acval env φ (c.nPc + names.length) (A.instantiateLevelParams lps us)
      = some (mkPisAV ab r))
    (hlC : abC.length = n) (hlL : abL.length = n) (hlA : ab.length = n)
    {hv : List V} (hk : hv.length = names.length) {τ : Nat → V} (hτ : Good τ)
    (hgrp : ∀ i mm, i < H → ConLeche.classGrpOf cls names c i = some mm →
      τ (H - 1 - i) = (pF.map (interp V τ)).foldl SetTheory.app (hv.getD mm pt))
    {hg : Nat} {hty : Expr} {idx : List Expr}
    (hfB : ConLeche.classAliasAbs al (ConLeche.classAbs cls (bodyN n e0))
      = Expr.mkAppN (.fvar hg hty) (idx.map fun a => ConLeche.classAliasAbs al (ConLeche.classAbs cls a)))
    (hgB : classAbsF cls (fun h => isF h || isG h) (bodyN n e0)
      = Expr.mkAppN (.fvar hg hty) (idx.map (classAbsF cls (fun h => isF h || isG h))))
    (hhg : hg < H) {mm : Nat} (hmm : ConLeche.classGrpOf cls names c hg = some mm)
    {c' : Nat} (hc' : c' < names.length) {es : List AnnotTerm}
    (hr : r = AnnotTerm.mkAppN (.bvar (n + (names.length - 1 - c')))
      ((List.range c.nPc).map (fun i => AnnotTerm.bvar (c.nPc + names.length + n - 1 - i)) ++ es)) :
    mm = c' ∧ ∃ vsC, rC = AnnotTerm.mkAppN (.bvar (H + n - 1 - hg)) vsC ∧
      vsC.length = idx.length ∧ es.length = idx.length ∧
      ∀ fs : List V, fs.length = n → ∀ l, l < idx.length →
        interp V (consList fs τ) (vsC.getD l default) =
          interp V (consList fs (consList hv fun j => if j < c.nPc then
            interp V τ (pF.getD (c.nPc - 1 - j) default) else τ (j - c.nPc + H)))
            (es.getD l default) := by
  have hdl : (c.dsA.map (classAbsF cls isF)).length = c.nPc := by simp [hlp]
  have hdsFw : ∀ x ∈ (c.dsA.map (classAbsF cls isF)),
      Expr.fvarsBelow H x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hpF i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    exact ⟨this.1, this.2.1⟩
  have hspine : DenoteMetaSpine m.acval env φ (H + names.length) (c.dsA.map (classAbsF cls isF))
      (pF.map (AnnotTerm.liftN names.length · 0)) :=
    readSpine_lift m hacl (by rw [hdl, hlpF]) fun i hi => ⟨(hpF i (by omega)).1, (hpF i (by omega)).2.2⟩
  let xL : Nat → AnnotTerm := fun i => match ConLeche.classGrpOf cls names c i with
    | some mm => AnnotTerm.mkAppN (.bvar (names.length - 1 - mm))
        (pF.map (AnnotTerm.liftN names.length · 0))
    | none => .bvar (H + names.length - 1 - i)
  let xR : Nat → AnnotTerm := fun i =>
    if i < c.nPc then (pF.getD i default).liftN names.length 0 else .bvar (names.length - 1 - (i - c.nPc))
  let σ : Nat → V := consList hv fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
    else τ (j - c.nPc + H)
  have hgL : ∀ i, i < H → Expr.fvarsBelow (H + names.length)
      (((ConLeche.classGL cls names c H (c.dsA.map (classAbsF cls isF))) i).getD
        (.fvar i (.sort .zero))) ∧
      (((ConLeche.classGL cls names c H (c.dsA.map (classAbsF cls isF))) i).getD
        (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ (H + names.length)
        (((ConLeche.classGL cls names c H (c.dsA.map (classAbsF cls isF))) i).getD
          (.fvar i (.sort .zero))) = some (xL i) := by
    intro i hi
    cases hg : ConLeche.classGrpOf cls names c i with
    | none =>
      simp only [ConLeche.classGL, hg, Option.map_none, Option.getD_none, xL]
      exact ⟨by simp [Expr.fvarsBelow]; omega, rfl, denoteMeta_fvar _ _ _ _⟩
    | some mm =>
      have hmm := classGrpOf_lt hg
      simp only [ConLeche.classGL, hg, Option.map_some, Option.getD_some, xL]
      refine ⟨fvarsBelow_mkAppN_C (by simp [Expr.fvarsBelow]; omega)
          (fun x hx => Expr.fvarsBelow_mono (by omega) (hdsFw x hx).1),
        looseBVarsBounded_mkAppN_C rfl (fun x hx => (hdsFw x hx).2), ?_⟩
      rw [denoteMeta_mkAppN_of (c.dsA.map (classAbsF cls isF)) (denoteMeta_fvar _ _ _ _) hspine,
        show H + names.length - 1 - (H + mm) = names.length - 1 - mm by omega]
  have hgR : ∀ i, i < c.nPc + names.length → Expr.fvarsBelow (H + names.length)
      (((ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF))) i).getD (.fvar i (.sort .zero))) ∧
      (((ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF))) i).getD
        (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ (H + names.length)
        (((ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF))) i).getD
          (.fvar i (.sort .zero))) = some (xR i) := by
    intro i hi
    by_cases hin : i < c.nPc
    · have hgi : (ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF)) i)
          = some ((c.dsA.map (classAbsF cls isF)).getD i default) := by
        simp [ConLeche.classGR, hin, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : i < (c.dsA.map (classAbsF cls isF)).length)]
      simp only [hgi, Option.getD_some, xR, if_pos hin]
      obtain ⟨h1, h2, h3⟩ := hpF i hin
      refine ⟨Expr.fvarsBelow_mono (by omega) h1, h2, ?_⟩
      rw [denoteMeta_lift_fb hacl h1 (H + names.length) (by omega), h3]
      simp
    · simp only [ConLeche.classGR, if_neg hin, Option.getD_some, xR]
      exact ⟨by simp [Expr.fvarsBelow]; omega, rfl, by rw [denoteMeta_fvar]; congr 2; omega⟩
  -- the two substitutions read at `τ` and at the frame
  have hxL : substE V (substTau H (H + names.length) xL) 0 (consList hv τ) = τ := by
    refine substE_substTau_eq (fun i hi => ?_) (fun j hj => by
      rw [show j - H + (H + names.length) = j + hv.length by omega, consList_apply_add])
    cases hg : ConLeche.classGrpOf cls names c i with
    | none =>
      simp only [xL, hg]
      rw [interp_bvar, show H + names.length - 1 - i = (H - 1 - i) + hv.length by omega,
        consList_apply_add]
    | some mm =>
      have hmm := classGrpOf_lt hg
      simp only [xL, hg]
      rw [interp_mkAppN, interp_bvar, consList_getD_of_lt _ _ _ (by omega), hgrp i mm hi hg,
        show hv.length - 1 - (names.length - 1 - mm) = mm by omega, List.foldl_map, List.foldl_map]
      congr 1
      funext r a
      rw [← hk, interp_liftN_consList]
  have hxR : substE V (substTau (c.nPc + names.length) (H + names.length) xR) 0 (consList hv τ)
      = σ := by
    refine substE_substTau_eq (fun i hi => ?_) (fun j hj => ?_)
    · by_cases hin : i < c.nPc
      · simp only [xR, if_pos hin, σ]
        rw [← hk, interp_liftN_consList,
          show c.nPc + hv.length - 1 - i = (c.nPc - 1 - i) + hv.length by omega,
          consList_apply_add, if_pos (by omega), show c.nPc - 1 - (c.nPc - 1 - i) = i by omega]
      · simp only [xR, if_neg hin, σ]
        rw [interp_bvar, consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega),
          show c.nPc + names.length - 1 - i = names.length - 1 - (i - c.nPc) by omega]
    · simp only [σ]
      rw [show j - (c.nPc + names.length) + (H + names.length)
          = (j - c.nPc - names.length + H) + hv.length by omega, consList_apply_add,
        show j = (j - names.length) + hv.length by omega, consList_apply_add, if_neg (by omega)]
      congr 1
      omega
  -- the walked and the restricted bodies
  obtain ⟨L2, hL2, hrC⟩ := pis_body_read (acval := m.acval) (env := env) (φ := φ)
    (F := fun e => ConLeche.classAliasAbs al (ConLeche.classAbs cls e))
    (fun t b mm => by simp only [classAbs_forallE, classAliasAbs_forallE]) n e0 hPis 0 []
    (LocList.nil H) abC rC hlC (by simpa [Expr.instantiateList_nil] using hCr)
  simp only [hfB, Nat.add_zero, Nat.zero_add] at hrC hL2
  obtain ⟨vsC, hspC, rfl⟩ := fvarSpine_read hrC
  obtain ⟨L1, hL1, hrL⟩ := pis_body_read (acval := m.acval) (env := env) (φ := φ) (F := classAbsF cls (fun h => isF h || isG h))
    (classAbsF_forallE cls _) n e0 hPis 0 [] (LocList.nil H) abL rL hlL
    (by simpa [Expr.instantiateList_nil] using hLr)
  simp only [hgB, Nat.add_zero, Nat.zero_add] at hrL hL1
  obtain ⟨vsL, hspL, rfl⟩ := fvarSpine_read hrL
  have hlC' : vsC.length = idx.length := by
    simp [← DenoteMetaSpine.length_eq hspC]
  have hlL' : vsL.length = idx.length := by
    simp [← DenoteMetaSpine.length_eq hspL]
  -- the restricted body against the canonical one
  have hbody := commute_body m hgL hgR hL hA heq hLr hAr (by rw [hlL, hlA])
  rw [hlL, hlA, hr, AnnotTerm.substAV_mkAppN, AnnotTerm.substAV_mkAppN,
    AnnotTerm.substAV_bvar_ge _ (by omega), AnnotTerm.substAV_bvar_ge _ (by omega)] at hbody
  have e1 : H + n - 1 - hg - n = H - 1 - hg := by omega
  have e2 : n + (names.length - 1 - c') - n = names.length - 1 - c' := by omega
  rw [e1, e2] at hbody
  simp only [substTau, if_pos (show H - 1 - hg < H by omega),
    if_pos (show names.length - 1 - c' < c.nPc + names.length by omega),
    show H - 1 - (H - 1 - hg) = hg by omega,
    show c.nPc + names.length - 1 - (names.length - 1 - c') = c.nPc + c' by omega, xL, xR, hmm,
    if_neg (show ¬ c.nPc + c' < c.nPc by omega), show c.nPc + c' - c.nPc = c' by omega,
    liftN_mkAppN_B, AnnotTerm.liftN_bvar, if_neg (show ¬ names.length - 1 - mm < 0 by omega),
    if_neg (show ¬ names.length - 1 - c' < 0 by omega), mkAppN_mkAppN_AV, List.map_append] at hbody
  obtain ⟨hhead, hargs⟩ := mkAppN_bvar_inj hbody
  have hmmc : mm = c' := by
    have := classGrpOf_lt hmm
    omega
  refine ⟨hmmc, vsC, rfl, hlC', ?_, fun fs hfs l hl => ?_⟩
  · have := congrArg List.length hargs
    simp only [List.length_append, List.length_map, List.length_range, hlpF] at this
    omega
  · -- the restricted readings against the canonical ones
    have hpre : ((pF.map (AnnotTerm.liftN names.length · 0)).map fun a => AnnotTerm.liftN n a 0).length
        = (((List.range c.nPc).map fun i => AnnotTerm.bvar (c.nPc + names.length + n - 1 - i)).map
          (AnnotTerm.substAV (substTau (c.nPc + names.length) (H + names.length) xR) · n)).length := by
      simp [hlpF]
    obtain ⟨-, hes⟩ := List.append_inj hargs hpre
    have hlL : l < vsL.length := by omega
    have hles : l < es.length := by
      have := congrArg List.length hes; simp at this; omega
    have hel : AnnotTerm.substAV (substTau H (H + names.length) xL) (vsL.getD l default) n
        = AnnotTerm.substAV (substTau (c.nPc + names.length) (H + names.length) xR)
          (es.getD l default) n := by
      have := congrArg (fun xs => xs[l]?) hes
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlL,
        List.getElem?_eq_getElem hles, Option.map_some, Option.some.injEq] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlL, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hles, Option.getD_some, Option.getD_some]
      exact this
    have hread := congrArg (interp V (consList fs (consList hv τ))) hel
    rw [interp_substAV, interp_substAV, ← hfs, show fs.length = fs.length + 0 from rfl,
      substE_consList, substE_consList, hxL, hxR] at hread
    rw [← hread]
    -- the walked readings against the restricted ones
    have hag := crestAbs_read_stageF hacl hwf hhk hkf hFc hawf hden hF hG hsem
      (idx.getD l default) (d := n) hL2 hL1
    have hl' : l < idx.length := hl
    have hC := DenoteMetaSpine.getD hspC default l (by simpa using hl')
    have hLd := DenoteMetaSpine.getD hspL default l (by simpa using hl')
    simp only [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hl', Option.map_some, Option.getD_some, Function.comp_apply] at hC hLd
    unfold ConLeche.classAliasAbs at hC
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some] at hag
    rw [hC, hLd] at hag
    simpa [List.getD_eq_getElem?_getD] using hag fs τ hfs hτ

end Result

end ConLeche.Model
