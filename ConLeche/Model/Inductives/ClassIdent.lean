module

public import ConLeche.Model.Inductives.ClassStageF
public import ConLeche.Model.Annot.BitSubstFvars
public import ConLeche.Verify.Inductives.ClassInv
import ConLeche.Model.IndReduct
import ConLeche.Model.Annot.BitLevels
public import ConLeche.Model.Annot.LfpFormer

public section

/-!
# The identification: a class's crest reads as its container's recorded clause (P2d, I2)

The class check's commutation equation (`classCommutes`,
DESIGN CLASSCHECK / P2D3) says two SUBSTITUTION INSTANCES are equal up to
the free variables' annotations: the crest with its stage classes
abstracted, its group holes written back as placeholder members applied
to the key's free-hole form `dsF`; and the container's canonical text
(what the recorded clause reads), its parameters `dsF`, its members the
placeholders.  Read, both sides are substitutions of their readings
(`denoteMeta_replaceFVars`), so the crest reads as the recorded text at
the valuation holding the key's free-hole form and, at each member slot,
the value the group hole holds applied back — no induction over terms.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## 1. A replacement of free variables, read -/

/-- **A replacement of free variables reads as the parallel substitution
of its readings**: `e` scoped below `b`, every replaced variable's term
(an unreplaced one standing for itself) scoped at `D`, closed, and read. -/
theorem denoteMeta_replaceFVars (m : EnvModel V env) {b D : Nat} {g : Nat → Option Expr}
    {x : Nat → AnnotTerm}
    (hg : ∀ i, i < b → Expr.fvarsBelow D ((g i).getD (.fvar i (.sort .zero))) ∧
      ((g i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((g i).getD (.fvar i (.sort .zero))) = some (x i))
    {e : Expr} (he : Expr.fvarsBelow b e) :
    denoteMeta m.acval env φ D (e.replaceFVars g)
      = (denoteMeta m.acval env φ b e).map (AnnotTerm.substAV (substTau b D x) · 0) := by
  let s : Nat → Expr := fun i => ((g i).getD (.fvar i (.sort .zero))).eraseFVarTys
  have hE : Expr.ErasedEq (e.replaceFVars g) (Expr.substFvars b D s e) := by
    refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) e he
    cases hgv : g v with
    | none =>
      simp only [Option.getD_none, s, hgv, Expr.eraseFVarTys, Expr.replaceFVars, Option.getD_some]
      exact rfl
    | some t =>
      simp only [Option.getD_some, s, hgv]
      exact Expr.erasedEq_eraseFVarTys t
  rw [denoteMeta_semEq (Expr.semEq_of_erasedEq hE)]
  have hs : ∀ i, i < b → Expr.WScoped D (s i) ∧ (s i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D (s i) = some (x i) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hg i hi
    have hsem : Expr.SemEq ((g i).getD (.fvar i (.sort .zero))) (s i) :=
      Expr.semEq_of_erasedEq (Expr.erasedEq_eraseFVarTys _)
    refine ⟨Expr.wscoped_eraseFVarTys h1, ?_, ?_⟩
    · rw [← Expr.SemEq.looseBVarsBounded hsem 0]; exact h2
    · rw [← denoteMeta_semEq hsem]; exact h3
  have := denoteMeta_substFvars (φ := φ) m hs e 0 (by simpa using he)
  simpa using this

/-! ## 2. The commutation equation, read -/

/-- **Two substitution instances equal up to annotations read as equal
substitutions of their readings** — the commutation equation's reading:
`L` (the crest, stage classes abstracted) below `H` and `A` (the canonical
text) below `b`, each replaced into depth `D`. -/
theorem substRead_eq (m : EnvModel V env) {H b D : Nat} {L A : Expr} {gL gR : Nat → Option Expr}
    {xL xR : Nat → AnnotTerm}
    (hgL : ∀ i, i < H → Expr.fvarsBelow D ((gL i).getD (.fvar i (.sort .zero))) ∧
      ((gL i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gL i).getD (.fvar i (.sort .zero))) = some (xL i))
    (hgR : ∀ i, i < b → Expr.fvarsBelow D ((gR i).getD (.fvar i (.sort .zero))) ∧
      ((gR i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ D ((gR i).getD (.fvar i (.sort .zero))) = some (xR i))
    (hL : Expr.fvarsBelow H L) (hA : Expr.fvarsBelow b A)
    (heq : (L.replaceFVars gL).eraseFVarTys = (A.replaceFVars gR).eraseFVarTys)
    {aL aA : AnnotTerm} (haL : denoteMeta m.acval env φ H L = some aL)
    (haA : denoteMeta m.acval env φ b A = some aA) :
    AnnotTerm.substAV (substTau H D xL) aL 0 = AnnotTerm.substAV (substTau b D xR) aA 0 := by
  have h1 := denoteMeta_replaceFVars (φ := φ) m hgL hL
  have h2 := denoteMeta_replaceFVars (φ := φ) m hgR hA
  rw [haL, Option.map_some] at h1
  rw [haA, Option.map_some] at h2
  have hsem : Expr.SemEq (L.replaceFVars gL) (A.replaceFVars gR) :=
    Expr.semEq_of_erasedEq ((Expr.erasedEq_of_eraseFVarTys heq))
  rw [denoteMeta_semEq hsem, h2] at h1
  exact (Option.some.inj h1).symm

/-! ## 3. Agreement of Π-towers, field by field -/

section Tele

variable {acval : Name → (Name → Nat) → AnnotTerm}

theorem obind2 {α β γ : Type} {x : Option α} {y : Option β} {f : α → β → γ} {c : γ}
    (h : (do let a ← x; let b ← y; some (f a b)) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ f a b = c := by
  cases x <;> cases y <;> simp_all

/-- `X` opens with (at least) `n` `Π`-binders. -/
@[expose] def IsPisN : Nat → Expr → Prop
  | 0, _ => True
  | n + 1, X => ∃ t b m, X = .forallE t b m ∧ IsPisN n b

set_option maxHeartbeats 1600000 in
/-- **Two transforms of a Π-tower that agree on every opened subterm fit
the same spines**: `f`, `g` commute with `Π`; if every term's `f`- and
`g`-images read alike at every admissible valuation (any number of opened
locals), the readings' first `n` fields fit the same spines there. -/
theorem teleAgree_spineFit {H : Nat} {Good : (Nat → V) → Prop} {f g : Expr → Expr}
    (hf : ∀ t b m, f (.forallE t b m) = .forallE (f t) (f b) m)
    (hg : ∀ t b m, g (.forallE t b m) = .forallE (g t) (g b) m)
    (hag : ∀ (e : Expr) (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d)
        (denoteMeta acval env φ (H + d) ((f e).instantiateList as2 0))
        (denoteMeta acval env φ (H + d) ((g e).instantiateList as1 0))) :
    ∀ (ab1 : List (Nat × Nat × AnnotTerm)) (X : Expr), IsPisN ab1.length X →
      ∀ (d : Nat) (as2 as1 : List Expr),
      LocList H d as2 → LocList H d as1 → ∀ (ab2 : List (Nat × Nat × AnnotTerm)) (r1 r2 : AnnotTerm),
      denoteMeta acval env φ (H + d) ((f X).instantiateList as2 0) = some (mkPisAV ab1 r1) →
      denoteMeta acval env φ (H + d) ((g X).instantiateList as1 0) = some (mkPisAV ab2 r2) →
      ab1.length = ab2.length → ∀ τ, Good τ → ∀ vals : List V, vals.length = d →
      ∀ fs : List V, SpineFit (consList vals τ) (ab1.map (·.2.2)) fs ↔
        SpineFit (consList vals τ) (ab2.map (·.2.2)) fs
  | [], _, _, _, _, _, _, _, ab2, _, _, _, _, hl, _, _, _, _, fs => by
    cases ab2 with
    | nil => exact Iff.rfl
    | cons _ _ => simp at hl
  | e1 :: ab1, X, hX, d, as2, as1, h2, h1, ab2, r1, r2, hX1, hX2, hl, τ, hτ, vals, hvl, fs => by
    cases ab2 with
    | nil => simp at hl
    | cons e2 ab2 =>
    obtain ⟨t, b, m, rfl, hb⟩ := hX
    rw [hf] at hX1
    rw [hg] at hX2
    simp only [Expr.instantiateList] at hX1 hX2
    rw [denoteMeta_forallE] at hX1 hX2
    obtain ⟨ta1, ba1, hta1, hba1, hP1⟩ := obind2 hX1
    obtain ⟨ta2, ba2, hta2, hba2, hP2⟩ := obind2 hX2
    have hT := hag t d as2 as1 h2 h1
    rw [hta1, hta2] at hT
    rw [← Expr.instantiateList_cons] at hba1 hba2
    simp only [mkPisAV] at hP1 hP2
    injection hP1 with _ _ hta1' hba1'
    injection hP2 with _ _ hta2' hba2'
    subst hta1' hta2'
    simp only [List.map_cons]
    cases fs with
    | nil => simp [SpineFit]
    | cons x fs =>
      simp only [SpineFit]
      rw [hT vals τ hvl hτ]
      refine and_congr_right fun _ => ?_
      have hrec := teleAgree_spineFit hf hg hag ab1 b hb (d + 1) _ _
        (h2.cons ((f t).instantiateList as2 0)) (h1.cons ((g t).instantiateList as1 0)) ab2 r1 r2
        (by rw [show H + (d + 1) = H + d + 1 by omega, hba1, hba1'])
        (by rw [show H + (d + 1) = H + d + 1 by omega, hba2, hba2'])
        (by simpa using hl) τ hτ (vals ++ [x]) (by simp [hvl]) fs
      simpa [consList_append] using hrec

end Tele

/-! ## 4. The commutation equation's telescopes -/

theorem substTele_len (τ : Nat → AnnotTerm) :
    ∀ (k : Nat) (ab : List (Nat × Nat × AnnotTerm)), (AnnotTerm.substTele τ k ab).length = ab.length
  | _, [] => rfl
  | k, _ :: ab => by simp [AnnotTerm.substTele, substTele_len τ (k + 1) ab]

theorem mkPisAV_injC :
    ∀ {pps₁ pps₂ : List (Nat × Nat × AnnotTerm)} {b₁ b₂ : AnnotTerm},
      pps₁.length = pps₂.length → mkPisAV pps₁ b₁ = mkPisAV pps₂ b₂ →
      pps₁ = pps₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | d₁ :: pps₁, d₂ :: pps₂, b₁, b₂, hlen, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨hu, hv, hA, hB⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_injC (by simpa using hlen) hB
    refine ⟨?_, rfl⟩
    congr 1
    exact Prod.ext hu (Prod.ext hv hA)

/-- The valuation a substitution at depth `0` reads at. -/
theorem substE_substTau_zero (b D : Nat) (x : Nat → AnnotTerm) (ρ : Nat → V) (j : Nat) :
    substE V (substTau b D x) 0 ρ j
      = if j < b then interp V ρ (x (b - 1 - j)) else ρ (j - b + D) := by
  unfold substE substTau
  simp only [Nat.not_lt_zero, if_false, Nat.sub_zero, shiftE_zero_zero]
  split
  · rfl
  · rw [interp_bvar]

/-- **The commutation equation fits the same spines**: the crest side's
field telescope (below `H`) at the valuation its substitution reads at,
the canonical text's (below `b`) at its own. -/
theorem commute_spineFit (m : EnvModel V env) {H b D : Nat} {L A : Expr}
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
    (haA : denoteMeta m.acval env φ b A = some (mkPisAV ab r)) (hlen : abL.length = ab.length)
    (ρ : Nat → V) (fs : List V) :
    SpineFit (substE V (substTau H D xL) 0 ρ) (abL.map (·.2.2)) fs ↔
      SpineFit (substE V (substTau b D xR) 0 ρ) (ab.map (·.2.2)) fs := by
  have h := substRead_eq (φ := φ) m hgL hgR hL hA heq haL haA
  rw [AnnotTerm.substAV_mkPisAV, AnnotTerm.substAV_mkPisAV] at h
  obtain ⟨hT, -⟩ := mkPisAV_injC (by rw [substTele_len, substTele_len, hlen]) h
  rw [← spineFit_substTele, ← spineFit_substTele, hT]

/-! ## 5. The class check's commutation equation, unfolded -/

/-- **`classCommutes`, unfolded.** -/
theorem classCommutes_spec {cls : List ClassInfo} {mates : Name → List Name} {H : Nat}
    {isF isG : Expr → Bool} {c d : ClassInfo} {cv : ConLeche.ConstantVal}
    (h : ConLeche.classCommutes cls mates H isF isG c d cv = true) :
    ∃ e0 A, ConLeche.instPisWith d.dsA (cv.type.instantiateLevelParams cv.levelParams d.key.lvls)
        = some e0 ∧ ConLeche.classCanonText (mates c.key.ind) c.nPc cv = some A ∧
      ((ConLeche.classAbsIf cls (fun h => isF h || isG h) e0).replaceFVars
          (ConLeche.classGL cls (mates c.key.ind) c H (c.dsA.map (ConLeche.classAbsIf cls isF)))).eraseFVarTys
        = ((A.instantiateLevelParams cv.levelParams c.key.lvls).replaceFVars
          (ConLeche.classGR c.nPc H (c.dsA.map (ConLeche.classAbsIf cls isF)))).eraseFVarTys := by
  unfold ConLeche.classCommutes at h
  dsimp only at h
  cases he0 : ConLeche.instPisWith d.dsA (cv.type.instantiateLevelParams cv.levelParams d.key.lvls)
    with
  | none => rw [he0] at h; exact absurd h (by simp)
  | some e0 =>
    cases hA : ConLeche.classCanonText (mates c.key.ind) c.nPc cv with
    | none => rw [he0, hA] at h; exact absurd h (by simp)
    | some A =>
      rw [he0, hA] at h
      exact ⟨e0, A, rfl, rfl, by simpa using h⟩

/-- The restricted recogniser is `occRestrict`: `classAbsIf` is `classAbsF`. -/
theorem classAbsIf_eq (cls : List ClassInfo) (P : Expr → Bool) (e : Expr) :
    ConLeche.classAbsIf cls P e = classAbsF cls P e := by
  unfold ConLeche.classAbsIf classAbsF
  have : ConLeche.classOccIf cls P = occRestrict (classOcc? cls) P := by
    funext x
    unfold ConLeche.classOccIf occRestrict
    rfl
  rw [this]
  exact (classAbsGo_spec _ e none {} (fun _ _ h => by simp at h)).1

/-! ## 6. The crest reads as the canonical text at the frame -/

/-- The valuation a depth-`0` substitution reads at, when its terms read
as a given valuation's slots and the rest is the given valuation shifted. -/
theorem substE_substTau_eq {b D : Nat} {x : Nat → AnnotTerm} {ρ σ : Nat → V}
    (h1 : ∀ i, i < b → interp V ρ (x i) = σ (b - 1 - i))
    (h2 : ∀ j, b ≤ j → ρ (j - b + D) = σ j) : substE V (substTau b D x) 0 ρ = σ := by
  funext j
  rw [substE_substTau_zero]
  split
  · rename_i hj
    rw [h1 (b - 1 - j) (by omega), show b - 1 - (b - 1 - j) = j by omega]
  · exact h2 j (by omega)

theorem classAbsSpec_forallE (occ : Expr → Option (Expr × Nat)) (t b : Expr) (m : ConLeche.BinderMeta) :
    classAbsSpec occ none (.forallE t b m)
      = .forallE (classAbsSpec occ none t) (classAbsSpec occ none b) m := by
  simp [classAbsSpec]

theorem classAbs_forallE (cls : List ClassInfo) (t b : Expr) (m : ConLeche.BinderMeta) :
    ConLeche.classAbs cls (.forallE t b m)
      = .forallE (ConLeche.classAbs cls t) (ConLeche.classAbs cls b) m := by
  rw [ConLeche.classAbs_eq_spec, ConLeche.classAbs_eq_spec, ConLeche.classAbs_eq_spec,
    classAbsSpec_forallE]

theorem classAliasAbs_forallE (al : List ConLeche.ClassAlias) (t b : Expr)
    (m : ConLeche.BinderMeta) :
    ConLeche.classAliasAbs al (.forallE t b m)
      = .forallE (ConLeche.classAliasAbs al t) (ConLeche.classAliasAbs al b) m := by
  unfold ConLeche.classAliasAbs
  rw [(ConLeche.classAbsGo_spec _ _ none {} (fun _ _ h => by simp at h)).1,
    (ConLeche.classAbsGo_spec _ t none {} (fun _ _ h => by simp at h)).1,
    (ConLeche.classAbsGo_spec _ b none {} (fun _ _ h => by simp at h)).1, classAbsSpec_forallE]

theorem classAbsF_forallE (cls : List ClassInfo) (F : Expr → Bool) (t b : Expr)
    (m : ConLeche.BinderMeta) :
    classAbsF cls F (.forallE t b m) = .forallE (classAbsF cls F t) (classAbsF cls F b) m := by
  unfold classAbsF; exact classAbsSpec_forallE _ t b m

set_option maxHeartbeats 1600000 in
/-- **The identification of a class's crest with its container's
canonical text** (DESIGN CLASSCHECK / P2D3, I2): at every locally
coherent valuation `τ` (the stage holes `F` arbitrary, every other class
its `F`-key) under which the group holes hold what the crest side's
write-back reads (`hxL`), a spine fits the crest's first `n` fields
exactly when it fits the canonical text's at the valuation the canonical
side's substitution reads at (`σ`: the key's free-hole form, the
placeholders' values). -/
theorem crest_spineFit_canon (m : EnvModel V env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk m.acval env φ cls H) {F : Expr → Bool}
    (hkf : KeysFOk m.acval env φ cls F H) (hFc : FClosed cls F)
    {al : List ConLeche.ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta m.acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, F a.hole = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V m.acval env φ cls F H τ)
    (hsem : AliasKeySem V m.acval env φ cls al H Good)
    {e0 : Expr} {n : Nat} (hPis : IsPisN n e0)
    {k nPc : Nat} {A : Expr} {gL gR : Nat → Option Expr} {xL xR : Nat → AnnotTerm}
    (hgL : ∀ i, i < H → Expr.fvarsBelow (H + k) ((gL i).getD (.fvar i (.sort .zero))) ∧
      ((gL i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ (H + k) ((gL i).getD (.fvar i (.sort .zero))) = some (xL i))
    (hgR : ∀ i, i < nPc + k → Expr.fvarsBelow (H + k) ((gR i).getD (.fvar i (.sort .zero))) ∧
      ((gR i).getD (.fvar i (.sort .zero))).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ (H + k) ((gR i).getD (.fvar i (.sort .zero))) = some (xR i))
    (hL : Expr.fvarsBelow H (classAbsF cls F e0)) (hA : Expr.fvarsBelow (nPc + k) A)
    (heq : ((classAbsF cls F e0).replaceFVars gL).eraseFVarTys = (A.replaceFVars gR).eraseFVarTys)
    {abC abL ab : List (Nat × Nat × AnnotTerm)} {rC rL r : AnnotTerm}
    (hCr : denoteMeta m.acval env φ H (ConLeche.classAliasAbs al (ConLeche.classAbs cls e0))
      = some (mkPisAV abC rC))
    (hLr : denoteMeta m.acval env φ H (classAbsF cls F e0) = some (mkPisAV abL rL))
    (hAr : denoteMeta m.acval env φ (nPc + k) A = some (mkPisAV ab r))
    (hlC : abC.length = n) (hlL : abL.length = n) (hlA : ab.length = n)
    {hv : List V} (hk : hv.length = k) {τ : Nat → V} (hτ : Good τ)
    (hxL : ∀ i, i < H → interp V (consList hv τ) (xL i) = τ (H - 1 - i))
    {σ : Nat → V} (hxR : ∀ i, i < nPc + k → interp V (consList hv τ) (xR i) = σ (nPc + k - 1 - i))
    (hσ : ∀ j, nPc + k ≤ j → consList hv τ (j - (nPc + k) + (H + k)) = σ j)
    (fs : List V) :
    SpineFit τ (abC.map (·.2.2)) fs ↔ SpineFit σ (ab.map (·.2.2)) fs := by
  -- the crest against its restriction to the stage holes
  have h1 := teleAgree_spineFit (V := V) (acval := m.acval) (env := env) (φ := φ) (H := H)
    (Good := Good) (f := fun e => ConLeche.classAliasAbs al (ConLeche.classAbs cls e))
    (g := classAbsF cls F)
    (fun t b mm => by simp only [classAbs_forallE, classAliasAbs_forallE])
    (fun t b mm => classAbsF_forallE cls F t b mm)
    (fun e d as2 as1 h2 h1 => crestAbs_read_stageF hacl hwf hhk hkf hFc hawf hden hF hG hsem e h2 h1)
    abC e0 (by rw [hlC]; exact hPis) 0 [] [] (LocList.nil H) (LocList.nil H) abL rC rL
    (by simpa [Expr.instantiateList_nil] using hCr) (by simpa [Expr.instantiateList_nil] using hLr)
    (by rw [hlC, hlL]) τ hτ [] rfl fs
  simp only [consList_nil] at h1
  -- the restriction against the canonical text
  have h2 := commute_spineFit (φ := φ) m hgL hgR hL hA heq hLr hAr (by rw [hlL, hlA])
    (consList hv τ) fs
  rw [substE_substTau_eq (σ := τ) hxL (fun j hj => by
      rw [show j - H + (H + k) = j + hv.length by omega, consList_apply_add]),
    substE_substTau_eq (σ := σ) hxR hσ] at h2
  exact h1.trans h2

/-! ## 7. The identification, in the class check's vocabulary -/

theorem interp_liftN_consList (hv : List V) (τ : Nat → V) (a : AnnotTerm) :
    interp V (consList hv τ) (a.liftN hv.length 0) = interp V τ a := by
  rw [interp_liftN, ConLeche.Semantics.shiftE_consList]

theorem classGrpOf_lt {cls : List ClassInfo} {names : List Name} {c : ClassInfo} {i m : Nat}
    (h : ConLeche.classGrpOf cls names c i = some m) : m < names.length := by
  unfold ConLeche.classGrpOf at h
  exact List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- The key's free-hole form, read: a spine of readings at the frame `H`. -/
theorem readSpine_lift (m : EnvModel V env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {H k : Nat} :
    ∀ {ds : List Expr} {ps : List AnnotTerm}, ds.length = ps.length →
      (∀ i, i < ds.length → Expr.fvarsBelow H (ds.getD i default) ∧
        denoteMeta m.acval env φ H (ds.getD i default) = some (ps.getD i default)) →
      DenoteMetaSpine m.acval env φ (H + k) ds (ps.map (AnnotTerm.liftN k · 0))
  | [], [], _, _ => .nil
  | d :: ds, p :: ps, hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    refine .cons ?_ (readSpine_lift m hacl (by simpa using hl) fun i hi => by
      simpa using h (i + 1) (by simp; omega))
    rw [denoteMeta_lift_fb hacl h0.1 (H + k) (by omega), h0.2]
    simp
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem fvarsBelow_mkAppN_C {d : Nat} : ∀ {xs : List Expr} {f : Expr},
    Expr.fvarsBelow d f → (∀ x ∈ xs, Expr.fvarsBelow d x) → Expr.fvarsBelow d (Expr.mkAppN f xs)
  | [], _, hf, _ => hf
  | x :: xs, f, hf, h => fvarsBelow_mkAppN_C (f := .app f x) ⟨hf, h x (by simp)⟩
      (fun y hy => h y (by simp [hy]))

theorem looseBVarsBounded_mkAppN_C {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    f.looseBVarsBounded k = true → (∀ x ∈ xs, x.looseBVarsBounded k = true) →
    (Expr.mkAppN f xs).looseBVarsBounded k = true
  | [], _, hf, _ => hf
  | x :: xs, f, hf, h => looseBVarsBounded_mkAppN_C (f := .app f x)
      (by simp [Expr.looseBVarsBounded, hf, h x (by simp)]) (fun y hy => h y (by simp [hy]))

set_option maxHeartbeats 3200000 in
/-- **The identification at a class's frame** (I2 in the class check's
vocabulary): the class check's commutation equation at container class
`c` (block `names`, stage holes `isF ∨ isG`) makes a spine fit the
crest's first `n` fields at every locally coherent valuation `τ` whose
group holes hold the placeholder values `hv` applied to the key's
free-hole form, exactly when it fits the canonical text's fields at the
frame `consList hv ρP` — `ρP` the key's free-hole form's values. -/
theorem classCrest_spineFit_frame (m : EnvModel V env)
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
    (fs : List V) :
    SpineFit τ (abC.map (·.2.2)) fs ↔
      SpineFit (consList hv fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
        else τ (j - c.nPc + H)) (ab.map (·.2.2)) fs := by
  have hdl : (c.dsA.map (classAbsF cls isF)).length = c.nPc := by simp [hlp]
  have hdsFw : ∀ x ∈ (c.dsA.map (classAbsF cls isF)), Expr.fvarsBelow H x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hpF i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    exact ⟨this.1, this.2.1⟩
  have hspine : DenoteMetaSpine m.acval env φ (H + names.length) (c.dsA.map (classAbsF cls isF)) (pF.map (AnnotTerm.liftN names.length · 0)) :=
    readSpine_lift m hacl (by rw [hdl, hlpF]) fun i hi => ⟨(hpF i (by omega)).1, (hpF i (by omega)).2.2⟩
  let xL : Nat → AnnotTerm := fun i => match ConLeche.classGrpOf cls names c i with
    | some mm => AnnotTerm.mkAppN (.bvar (names.length - 1 - mm)) (pF.map (AnnotTerm.liftN names.length · 0))
    | none => .bvar (H + names.length - 1 - i)
  let xR : Nat → AnnotTerm := fun i =>
    if i < c.nPc then (pF.getD i default).liftN names.length 0 else .bvar (names.length - 1 - (i - c.nPc))
  let σ : Nat → V := consList hv fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
    else τ (j - c.nPc + H)
  refine crest_spineFit_canon (φ := φ) m hacl hwf hhk hkf hFc hawf hden hF hG hsem hPis
    (k := names.length) (nPc := c.nPc) (gL := ConLeche.classGL cls names c H (c.dsA.map (classAbsF cls isF)))
    (gR := ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF))) (xL := xL) (xR := xR) ?_ ?_ hL hA heq hCr hLr hAr
    hlC hlL hlA hk hτ ?_ (σ := σ) ?_ ?_ fs
  · -- the crest side's write-back, read
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
  · -- the canonical side's substitution, read
    intro i hi
    by_cases hin : i < c.nPc
    · have hgi : (ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF)) i) = some ((c.dsA.map (classAbsF cls isF)).getD i default) := by
        simp [ConLeche.classGR, hin, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < (c.dsA.map (classAbsF cls isF)).length)]
      simp only [hgi, Option.getD_some, xR, if_pos hin]
      obtain ⟨h1, h2, h3⟩ := hpF i hin
      refine ⟨Expr.fvarsBelow_mono (by omega) h1, h2, ?_⟩
      rw [denoteMeta_lift_fb hacl h1 (H + names.length) (by omega), h3]
      simp
    · simp only [ConLeche.classGR, if_neg hin, Option.getD_some, xR]
      exact ⟨by simp [Expr.fvarsBelow]; omega, rfl, by rw [denoteMeta_fvar]; congr 2; omega⟩
  · -- the crest side's valuation is `τ`
    intro i hi
    cases hg : ConLeche.classGrpOf cls names c i with
    | none =>
      simp only [xL, hg]
      rw [interp_bvar, show H + names.length - 1 - i = (H - 1 - i) + hv.length by omega, consList_apply_add]
    | some mm =>
      have hmm := classGrpOf_lt hg
      simp only [xL, hg]
      rw [interp_mkAppN, interp_bvar, consList_getD_of_lt _ _ _ (by omega), hgrp i mm hi hg,
        show hv.length - 1 - (names.length - 1 - mm) = mm by omega, List.foldl_map, List.foldl_map]
      congr 1
      funext r a
      rw [← hk, interp_liftN_consList]
  · -- the canonical side's valuation is the frame, on its variables
    intro i hi
    by_cases hin : i < c.nPc
    · simp only [xR, if_pos hin, σ]
      rw [← hk, interp_liftN_consList, show c.nPc + hv.length - 1 - i = (c.nPc - 1 - i) + hv.length by omega,
        consList_apply_add, if_pos (by omega), show c.nPc - 1 - (c.nPc - 1 - i) = i by omega]
    · simp only [xR, if_neg hin, σ]
      rw [interp_bvar, consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega),
        show c.nPc + names.length - 1 - i = names.length - 1 - (i - c.nPc) by omega]
  · -- and beyond them the frame below
    intro j hj
    simp only [σ]
    rw [show j - (c.nPc + names.length) + (H + names.length) = (j - c.nPc - names.length + H) + hv.length by omega, consList_apply_add,
      show j = (j - names.length) + hv.length by omega, consList_apply_add, if_neg (by omega)]
    congr 1
    omega

/-! ## 8. … and as the RECORDED clause's fields (I3) -/

theorem fvarsBelow_instLevelsC (ks : List Name) (us : List Level) {d : Nat} :
    ∀ {e : Expr}, Expr.fvarsBelow d e → Expr.fvarsBelow d (e.instantiateLevelParams ks us) := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.fvarsBelow, Expr.instantiateLevelParams]

/-- The class check's canonical text is the recorded clause's canonical
crest (`canonAbs` at the canonical parameters). -/
theorem classCanonText_eq (names : List Name) (nPc : Nat) (cv : ConLeche.ConstantVal) :
    ConLeche.classCanonText names nPc cv
      = ConLeche.instPisWith (canonParams nPc) (canonAbs names cv.levelParams nPc names.length cv.type) :=
  rfl

/-- A fitting spine satisfies the entries it fits, pushed onto the
ambient context. -/
theorem sat_of_spineFitC :
    ∀ {Ds : List AnnotTerm} {as : List V} {Δ₀ : List AnnotTerm} {ρ : Nat → V},
      Sat V Δ₀ ρ → SpineFit ρ Ds as →
      Sat V (Ds.reverse ++ Δ₀) (consList as ρ)
  | [], [], _, _, h, _ => by simpa using h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | D :: Ds, a :: as, Δ₀, ρ, h, hsp => by
    rw [consList_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact sat_of_spineFitC (Sat_cons V h hsp.1) hsp.2

/-- **The frame satisfies the recorded reading's hole context**: the
parameters, then each member's hole value in its former type. -/
theorem frame_sat_holes {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env ψ 0 cvm.type = some (Tys.getD mm default))
    (X : Nat → V) (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) :
    Sat V (D.params ψ ++ Tys).reverse (D.frame ψ ρp X) := by
  unfold LfpDatum.frame
  rw [List.reverse_append]
  refine sat_of_spineFitC hs ?_
  have key : ∀ (n : Nat), n ≤ D.k →
      SpineFit ρp (Tys.take n) ((List.range n).map (D.holeVal ψ ρp X)) := by
    intro n
    induction n with
    | zero => intro _; simp [SpineFit]
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.take_add_one]
      have hTn : Tys[n]? = some (Tys.getD n default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hTn]
      refine (ih (by omega)).append ⟨?_, trivial⟩
      obtain ⟨cvm, caps, hfm, hr⟩ := hTys n (by omega)
      exact holeVal_mem_type mp hD (by omega) hfm hr hX _
  have := key D.k (Nat.le_refl _)
  rwa [List.take_of_length_le (by omega)] at this

set_option maxHeartbeats 3200000 in
/-- **The identification with the recorded clause** (I2 + I3): at every
locally coherent valuation `τ` whose group holes hold the container's
member hole values at the frame `(ρP, Y)` applied to the key's free-hole
form, a spine fits container class `c`'s crest (for the recorded
constructor `(c', j')` of `D`, `c`'s container block) exactly when it
fits `D`'s recorded fields at the frame `D.frame ψ ρP Y` — `ρP` the
key's free-hole form, read. -/
theorem classCrest_spineFit_recorded {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (mp.base2.acval n ψ).liftN 1 k = mp.base2.acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk mp.base2.acval env φ cls H) {isF isG : Expr → Bool}
    (hkf : KeysFOk mp.base2.acval env φ cls (fun h => isF h || isG h) H)
    (hFc : FClosed cls (fun h => isF h || isG h))
    {al : List ConLeche.ClassAlias} (hawf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta mp.base2.acval env φ H (aliasKey a)).isSome)
    (hF : ∀ a ∈ al, (isF a.hole || isG a.hole) = false) {Good : (Nat → V) → Prop}
    (hG : ∀ τ, Good τ → StageCohF V mp.base2.acval env φ cls (fun h => isF h || isG h) H τ)
    (hsem : AliasKeySem V mp.base2.acval env φ cls al H Good)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) (hk : D.names.length = D.k)
    {c : ClassInfo} {cv : ConLeche.ConstantVal} {e0 A : Expr} {n : Nat} (hPis : IsPisN n e0)
    (heq : ((classAbsF cls (fun h => isF h || isG h) e0).replaceFVars
        (ConLeche.classGL cls D.names c H (c.dsA.map (classAbsF cls isF)))).eraseFVarTys
      = ((A.instantiateLevelParams cv.levelParams c.key.lvls).replaceFVars
        (ConLeche.classGR c.nPc H (c.dsA.map (classAbsF cls isF)))).eraseFVarTys)
    {pF : List AnnotTerm} (hlp : c.dsA.length = c.nPc) (hlpF : pF.length = c.nPc)
    (hpF : ∀ i, i < c.nPc → Expr.fvarsBelow H ((c.dsA.map (classAbsF cls isF)).getD i default) ∧
      ((c.dsA.map (classAbsF cls isF)).getD i default).looseBVarsBounded 0 = true ∧
      denoteMeta mp.base2.acval env φ H ((c.dsA.map (classAbsF cls isF)).getD i default)
        = some (pF.getD i default))
    (hL : Expr.fvarsBelow H (classAbsF cls (fun h => isF h || isG h) e0))
    (hA : Expr.fvarsBelow (c.nPc + D.k) A)
    {abC abL ab : List (Nat × Nat × AnnotTerm)} {rC rL r : AnnotTerm}
    (hCr : denoteMeta mp.base2.acval env φ H (ConLeche.classAliasAbs al (ConLeche.classAbs cls e0))
      = some (mkPisAV abC rC))
    (hLr : denoteMeta mp.base2.acval env φ H (classAbsF cls (fun h => isF h || isG h) e0)
      = some (mkPisAV abL rL))
    (hAr : denoteMeta mp.base2.acval env (Level.substFn φ cv.levelParams c.key.lvls) (c.nPc + D.k) A
      = some (mkPisAV ab r))
    (hlC : abC.length = n) (hlL : abL.length = n) (hlA : ab.length = n)
    {Tys : List AnnotTerm} (hlT : Tys.length = D.k)
    (hTys : ∀ mm, mm < D.k → ∃ cvm caps, env.find? (D.member mm) = some (.indInfo cvm caps) ∧
      denoteMeta mp.base2.acval env (Level.substFn φ cv.levelParams c.key.lvls) 0 cvm.type
        = some (Tys.getD mm default))
    {c' j' : Nat}
    (hEq : FieldsEqOn V (D.params (Level.substFn φ cv.levelParams c.key.lvls) ++ Tys).reverse
      (ab.map (·.2.2)) (D.fields (Level.substFn φ cv.levelParams c.key.lvls) c' j'))
    {τ : Nat → V} (hτ : Good τ)
    (hSat : Sat V (D.params (Level.substFn φ cv.levelParams c.key.lvls)).reverse
      (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default) else τ (j - c.nPc + H)))
    {Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn φ cv.levelParams c.key.lvls)) D.N
      (D.idx (Level.substFn φ cv.levelParams c.key.lvls)
        (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
          else τ (j - c.nPc + H))) Y)
    (hgrp : ∀ i mm, i < H → ConLeche.classGrpOf cls D.names c i = some mm →
      τ (H - 1 - i) = (pF.map (interp V τ)).foldl SetTheory.app
        (D.holeVal (Level.substFn φ cv.levelParams c.key.lvls)
          (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
            else τ (j - c.nPc + H)) Y mm))
    (fs : List V) :
    SpineFit τ (abC.map (·.2.2)) fs ↔
      SpineFit (D.frame (Level.substFn φ cv.levelParams c.key.lvls)
        (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
          else τ (j - c.nPc + H)) Y)
        (D.fields (Level.substFn φ cv.levelParams c.key.lvls) c' j') fs := by
  have hAr' : denoteMeta mp.base2.acval env φ (c.nPc + D.names.length)
      (A.instantiateLevelParams cv.levelParams c.key.lvls) = some (mkPisAV ab r) := by
    rw [denotePInstLevels mp.base2 φ cv.levelParams c.key.lvls, hk]; exact hAr
  have hA' : Expr.fvarsBelow (c.nPc + D.names.length)
      (A.instantiateLevelParams cv.levelParams c.key.lvls) := by
    rw [hk]; exact fvarsBelow_instLevelsC cv.levelParams c.key.lvls hA
  have h1 := classCrest_spineFit_frame (φ := φ) mp.base2 hacl hwf hhk hkf hFc hawf hden hF hG hsem
    hPis heq hlp hlpF hpF hL hA' hCr hLr hAr' hlC hlL hlA
    (hv := (List.range D.k).map (D.holeVal (Level.substFn φ cv.levelParams c.key.lvls)
      (fun j => if j < c.nPc then interp V τ (pF.getD (c.nPc - 1 - j) default)
        else τ (j - c.nPc + H)) Y)) (by simp [hk]) hτ
    (fun i mm hi hg => by
      rw [hgrp i mm hi hg, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by rw [← hk]; exact classGrpOf_lt hg)]
      rfl) fs
  rw [h1]
  exact FieldsEqOn.spineFit_iff hEq (frame_sat_holes mp hD hSat hlT hTys Y hY) fs

end ConLeche.Model
