module

public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Annot.BitLevels
import ConLeche.Verify.Inductives.BlockRecInv

public section

/-!
# The equation list's LEVEL-PARAMETER invariance

`heqP` — the equation list reads alike at two level valuations that
agree on a recursor's own `levelParams` — needs every one of the six
components to be ψ-congruent there.  Five of them are readings of
stored data whose parameter-invariance is already in the tree (the
recursor types' readings, the constructors' record `params`,
`tssParams`, `eissParams`, the leaves' `acval_params`); the sixth,
`Rb0`, is the reading of the residue OPENED at the rule's whole frame,
and the opening puts `fvar` openers into the term.

`denoteMeta_params_ext` asks `allLevelParamsDefined` of the read term,
and that predicate looks INSIDE an `fvar`'s type annotation — which
`denoteMeta` never reads (an opener reads as its de Bruijn slot).  So
the kit here is `lpDefF`, the same footprint with the `fvar` types
ignored: the residue has it (it is fvar-free and its parameters are
the stored rule's), an opening at fvars keeps it, and the reading is
ψ-congruent under it.  No opener TYPE has to be tracked, so no
level-parameter twin of the `ConstsBound` kit (over `blockIhPis`, the
openers' types and the binder datum) is needed. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. `lpDefF` — the level footprint `denoteMeta` reads -/

section LpDefF

/-- Are the level parameters `denoteMeta` can read among `ps`?
`Expr.allLevelParamsDefined` with the `fvar` type annotations
IGNORED (an `fvar` reads as its de Bruijn slot). -/
@[expose] def lpDefF (ps : List Name) : Expr → Bool
  | .bvar _ => true
  | .fvar _ _ => true
  | .sort u => u.allParamsDefined ps
  | .const _ us => us.all (Level.allParamsDefined ps)
  | .app f a => lpDefF ps f && lpDefF ps a
  | .lam t b m => lpDefF ps t && lpDefF ps b && m.pw.paramsDefined ps
  | .forallE t b m => lpDefF ps t && lpDefF ps b && m.pw.paramsDefined ps
  | .letE t v b => lpDefF ps t && lpDefF ps v && lpDefF ps b
  | .lit _ => true
  | .proj _ _ e => lpDefF ps e

variable {ps : List Name}

omit [SetTheory V] in
theorem lpDefF_of_allLevelParamsDefined :
    ∀ (e : Expr), e.allLevelParamsDefined ps = true → lpDefF ps e = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, ihf h.1, iha h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihv h.1.2, ihb h.2, Bool.and_self]
  | proj s i e ihe =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [lpDefF, ihe h]
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | lit => intro _; rfl
  | sort u => intro h; simpa [lpDefF, Expr.allLevelParamsDefined] using h
  | const n us => intro h; simpa [lpDefF, Expr.allLevelParamsDefined] using h

omit [SetTheory V] in
theorem lpDefF_instantiate1 {v : Expr} (hv : lpDefF ps v = true) :
    ∀ (e : Expr) (k : Nat), lpDefF ps e = true → lpDefF ps (e.instantiate1 v k) = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, lpDefF]
  case bvar i =>
    split
    · exact hv
    · split <;> rfl

omit [SetTheory V] in
theorem lpDefF_mkAppN :
    ∀ (as : List Expr) {f : Expr}, lpDefF ps f = true → (∀ a ∈ as, lpDefF ps a = true) →
      lpDefF ps (Expr.mkAppN f as) = true
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    show lpDefF ps (Expr.mkAppN (Expr.app f a) as) = true
    refine lpDefF_mkAppN as ?_ (fun x hx => has x (List.mem_cons_of_mem _ hx))
    simp only [lpDefF, hf, has a List.mem_cons_self, Bool.and_self]

omit [SetTheory V] in
theorem lpDefF_stripLams :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr},
      lpDefF ps e = true → e.stripLams n = some (bs, body) → lpDefF ps body = true
  | 0, e, bs, body, he, h => by
    simp only [ConLeche.Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | n + 1, e, bs, body, he, h => by
    match e with
    | .lam ty b mb =>
      simp only [lpDefF, Bool.and_eq_true] at he
      simp only [ConLeche.Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, body₀⟩, hst, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact lpDefF_stripLams n he.1.2 hst
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .forallE _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripLams])

omit [SetTheory V] in
/-- **An opening at fvars keeps the footprint** — whatever the openers'
type annotations. -/
theorem lpDefF_instantiateList {vs : List Expr}
    (hvs : ∀ v ∈ vs, ∃ (i : Nat) (t : Expr), v = .fvar i t) :
    ∀ (e : Expr) (d : Nat), lpDefF ps e = true → lpDefF ps (e.instantiateList vs d) = true := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiateList]
    split
    · rfl
    · split
      · rename_i hj
        obtain ⟨i, t, ht⟩ := hvs _ (List.getElem_mem hj)
        rw [ht, Expr.instantiateList]; rfl
      · rfl
  | fvar => intro d _; rw [Expr.instantiateList]; rfl
  | sort u => intro d h; rw [Expr.instantiateList]; exact h
  | const n us => intro d h; rw [Expr.instantiateList]; exact h
  | lit => intro d _; rw [Expr.instantiateList]; rfl
  | app f a ihf iha =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, ihf d h.1, iha d h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihb (d + 1) h.1.2, h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihb (d + 1) h.1.2, h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihv d h.1.2, ihb (d + 1) h.2, Bool.and_self]
  | proj s i e ihe =>
    intro d h
    simp only [lpDefF] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, ihe d h]

end LpDefF

/-! ## 2. The reading is ψ-congruent at the `lpDefF` footprint

`denoteMeta_params_ext` (`Model/Annot/BitLevels.lean`) with the one
difference in the binder cases: the body is opened at an `fvar`, and
`lpDefF` of an opened body needs nothing of the fvar's annotation. -/

section Ext

variable {env : Env}

theorem denoteMeta_params_extF (m : EnvModel V env)
    {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Expr), lpDefF ps e = true →
      denoteMeta m.acval env φ₁ d e = denoteMeta m.acval env φ₂ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro hd
    rw [denoteMeta, denoteMeta,
      Level.eval_ext (by simpa [lpDefF] using hd) hφ]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci h1 h2 =>
    intro hd
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_pos h2, if_pos h2]
    refine congrArg _ (m.acval_params n ci h1 _ _ fun p hpm => ?_)
    refine Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [lpDefF, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_neg h2, if_neg h2]
  | case5 d n us h1 => intro _; rw [denoteMeta, denoteMeta, h1]
  | case6 d ty body mb ihty ihbody =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (lpDefF_instantiate1 rfl _ 0 hd.1.2)]
    simp only [hpw]
  | case7 d ty body mb ihty ihbody =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (lpDefF_instantiate1 rfl _ 0 hd.1.2)]
    simp only [hpw]
  | case8 d fe a ihf iha =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    rw [denoteMeta, denoteMeta, ← ihf hd.1, ← iha hd.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hd
    rw [denoteMeta, denoteMeta, ← ihe (by simpa [lpDefF] using hd)]
  | case11 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end Ext

/-! ## 3. The six components, ψ-congruent at a recursor's parameters -/

section Components

open ConLeche (BlockParts BlockFieldKind)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A recursor's level parameters ARE the pinned list** — stage (a)'s
`blockRecLpsOk`, carried to the stored record by `checkConstantVal`
(`recStage_lps`' own two steps, kept). -/
theorem recStage_lpsPin
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    r.1.levelParams = if p.toBlockShape.large then p.elim :: p.lps else p.lps := by
  obtain ⟨hpins, hlenR, hall⟩ := recStage_recNames h
  have hnl : i < p.recs.length := by
    have hql := (List.getElem?_eq_some_iff.mp hr).1
    omega
  obtain ⟨rc, q', hrc, hq', -, hcv, -, -⟩ := hall i hnl
  obtain rfl := Option.some.inj (hr.symm.trans hq')
  obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have hlps := List.all_eq_true.mp hpins.1 rc (List.mem_of_getElem? hrc)
  rw [show r.1.levelParams = rc.cvR.levelParams by rw [hcv']]
  by_cases hb : p.toBlockShape.large = true
  · rw [if_pos hb] at hlps ⊢
    exact eq_of_beq hlps
  · rw [if_neg hb] at hlps ⊢
    exact eq_of_beq hlps

/-- The block's own parameters are among every recursor's. -/
theorem recStage_lps_sub
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) : ∀ q ∈ p.lps, q ∈ r.1.levelParams := by
  intro q hq
  rw [recStage_lpsPin h hr]
  split
  · exact List.mem_cons_of_mem _ hq
  · exact hq

/-- **`pdoms`** — the recursor type's binder data, off its reading
(`recStage_tyPis`), which is ψ-congruent at any recursor's
parameters (`blockRecTyAV_params_ext`). -/
theorem blockRulePdomsAV_params (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q)
    {c : Nat} (hc : c < rs.length) :
    blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c := by
  have hrc : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  obtain ⟨-, -, -, -, hM₁, hN₁, -⟩ := recStage_tyPis hμ mpC h hrc ψ₁
  obtain ⟨-, -, -, -, hM₂, hN₂, -⟩ := recStage_tyPis hμ mpC h hrc ψ₂
  have hT := blockRecTyAV_params_ext hμ mpC h hr hq hc
  have hs₁ := stripPisAV_mkPisAV (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c)
    (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c)
  have hs₂ := stripPisAV_mkPisAV (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c)
    (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c)
  rw [← hM₁, hT, hM₂, hN₁, ← hN₂, hs₂] at hs₁
  have hR : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c
      = blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c :=
    congrArg Prod.fst (Option.some.inj hs₁)
  simp only [blockRulePdomsAV, hR]

/-- **`fdoms`** — the constructor's field domains, through the record's
`params` (`blockRuleFdomsAV_eq`). -/
theorem blockRuleFdomsAV_params {mpC : EnvModelM V μ envC}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List ConLeche.RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcd : BlockCtorDataI mpC.base2 env₀ T Tof nIdxOf lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [(blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ₁).1,
    (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ₂).1, (hcd.params ψ₁ ψ₂ hq).1]

/-- **`es`** — the constructor's index readings, through the record's
`params` (`blockRuleEsAV_eq`). -/
theorem blockRuleEsAV_params {mpC : EnvModelM V μ envC}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List ConLeche.RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcd : BlockCtorDataI mpC.base2 env₀ T Tof nIdxOf lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [blockRuleEsAV_eq h hr hcA hrhs hcd hCf hnP ψ₁,
    blockRuleEsAV_eq h hr hcA hrhs hcd hCf hnP ψ₂, (hcd.params ψ₁ ψ₂ hq).2]

/-- **`mk`** — the constructor's leaf at the identity instantiation,
through the leaf's `acval_params` (`blockRuleMkAV_eq`). -/
theorem blockRuleMkAV_params {mpC : EnvModelM V μ envC}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ci : ConstantInfo} (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ p.lps, ψ₁ q = ψ₂ q) :
    blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [blockRuleMkAV_eq h hr hcA hrhs hfind hlps hnP ψ₁,
    blockRuleMkAV_eq h hr hcA hrhs hfind hlps hnP ψ₂]
  have hq' : ∀ q ∈ p.lps, Level.substFn ψ₁ p.lps (p.lps.map Level.param) q
      = Level.substFn ψ₂ p.lps (p.lps.map Level.param) q :=
    Level.substFn_ext hq (fun u hu => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      simp [Level.allParamsDefined, hq]) (List.length_map _)
  rw [mpC.base2.acval_params _ ci hfind _ _ (fun q hqm => hq' q (hlps ▸ hqm))]

omit [SetTheory V] in
/-- Every member of a successful opening is an `fvar`. -/
theorem openPisAtFvars_mem_fvar {n E : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars n e E = some (fvs, o)) :
    ∀ x ∈ fvs, ∃ (i : Nat) (t : Expr), x = .fvar i t := by
  intro x hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index n e E hop j x hj
  exact ⟨_, ty, hty⟩

/-- **The equation list is congruent in its six components** below
`K` and the rule counts. -/
theorem blockIotaEqsAV_congr {K : Nat} {nCt : Nat → Nat}
    {pdoms pdoms' : Nat → List AnnotTerm} {fdoms fdoms' es es' ihs ihs' : Nat → Nat → List AnnotTerm}
    {mk mk' Rb Rb' : Nat → Nat → AnnotTerm}
    (hp : ∀ c, c < K → pdoms c = pdoms' c)
    (hrest : ∀ c, c < K → ∀ j, j < nCt c →
      fdoms c j = fdoms' c j ∧ es c j = es' c j ∧ ihs c j = ihs' c j ∧ mk c j = mk' c j ∧
        Rb c j = Rb' c j) :
    blockIotaEqsAV K nCt pdoms fdoms es ihs mk Rb
      = blockIotaEqsAV K nCt pdoms' fdoms' es' ihs' mk' Rb' := by
  rw [blockIotaEqsAV, blockIotaEqsAV]
  show (List.range K).flatMap _ = (List.range K).flatMap _
  rw [List.flatMap, List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun c hc => ?_)
  have hcK := List.mem_range.mp hc
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrest c hcK j (List.mem_range.mp hj)
  simp only [hp c hcK, h1, h2, h3, h4, h5]

end Components

end ConLeche.Model
