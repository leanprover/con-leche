module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Annot.BitConsCross

public section

/-!
# The canonical constructor crest (M2)

`LfpCtorReads` (`Model/Annot/EnvModelM.lean`) records the reading of a
stored constructor type member-abstracted at the CANONICAL holes and
instantiated at the canonical parameter variables (`canonAbs`,
`canonParams`).  Every variable it introduces is annotated `Sort 0`, so
the crest mentions only the stored type's constants and projections:
it is prefix-bound wherever the type is (`canonCrest_constsBound`) and
crosses every cons the type crosses (`canonCrest_consCrossAt`) — the two
facts the record's transport (`EnvModelM.lfp_ok_transport`'s `hreadC`)
needs at the cons funnel.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Verify
open ConLeche (Env Expr Name Level ConstantInfo instPisWith)

/-! ## Constant replacement -/

theorem constsBound_replaceConsts {env₀ : Env} {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → ConstsBound env₀ e) :
    ∀ (e : Expr), ConstsBound env₀ e → ConstsBound env₀ (e.replaceConsts f) := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceConsts]
  | fvar i ty ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_fvar] at h ⊢
    exact ih h
  | sort u => intro _; simp [ConLeche.Expr.replaceConsts]
  | const c us =>
    intro h
    simp only [ConLeche.Expr.replaceConsts]
    cases hc : f c us with
    | none => exact h
    | some e => exact hf c us e hc
  | lit l => intro _; simp [ConLeche.Expr.replaceConsts]
  | app a b iha ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_app] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, constsBound_proj] at h ⊢
    exact ih h

theorem noProjAt_replaceConsts {T : Name} {q : Nat} {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → ConLeche.Expr.NoProjAt T q e) :
    ∀ (e : Expr), ConLeche.Expr.NoProjAt T q e →
      ConLeche.Expr.NoProjAt T q (e.replaceConsts f) := by
  intro e
  induction e with
  | bvar i => intro _; simp [ConLeche.Expr.replaceConsts]
  | fvar i ty ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_fvar] at h ⊢
    exact ih h
  | sort u => intro _; simp [ConLeche.Expr.replaceConsts]
  | const c us =>
    intro h
    simp only [ConLeche.Expr.replaceConsts]
    cases hc : f c us with
    | none => exact h
    | some e => exact hf c us e hc
  | lit l => intro _; simp [ConLeche.Expr.replaceConsts]
  | app a b iha ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_app] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_lam] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_forallE] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_letE] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ih =>
    intro h
    simp only [ConLeche.Expr.replaceConsts, ConLeche.Expr.noProjAt_proj] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-! ## Instantiation along a telescope -/

theorem constsBound_instPisWith {env₀ : Env} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ConstsBound env₀ a) → ConstsBound env₀ e →
      instPisWith as e = some r → ConstsBound env₀ r
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [constsBound_forallE] at he
      exact constsBound_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (ConstsBound.instantiate1 (has a List.mem_cons_self) b 0 he.2) h'

theorem noProjAt_instPisWith {T : Name} {q : Nat} :
    ∀ {as : List Expr} {e r : Expr}, (∀ a ∈ as, ConLeche.Expr.NoProjAt T q a) →
      ConLeche.Expr.NoProjAt T q e → instPisWith as e = some r → ConLeche.Expr.NoProjAt T q r
  | [], e, r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    match e, h with
    | .forallE t b m, h =>
      have h' : instPisWith as (b.instantiate1 a) = some r := h
      simp only [ConLeche.Expr.noProjAt_forallE] at he
      exact noProjAt_instPisWith (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (ConLeche.Expr.NoProjAt.instantiate1 (has a List.mem_cons_self) b 0 he.2) h'

/-! ## The canonical crest -/

theorem mem_canonParams {nP : Nat} {x : Expr} (h : x ∈ canonParams nP) :
    ∃ i, i < nP ∧ x = .fvar i (.sort .zero) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem mem_canonHoles {nP k : Nat} {x : Expr} (h : x ∈ canonHoles nP k) :
    ∃ mm, mm < k ∧ x = .fvar (nP + mm) (.sort .zero) := by
  obtain ⟨mm, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨mm, List.mem_range.mp hm, rfl⟩

/-- The canonical abstraction's replacements are canonical holes. -/
theorem canonAbs_repl {names lps : List Name} {nP k : Nat} {c : Name} {us : List Level} {e : Expr}
    (h : (fun c us => if us == (canonCtx names lps nP).lps.map Level.param then
        match (canonCtx names lps nP).names.findIdx? (· == c) with
        | some mm => (canonHoles nP k)[mm]?
        | none => none
      else none) c us = some e) :
    ∃ mm, mm < k ∧ e = .fvar (nP + mm) (.sort .zero) := by
  simp only at h
  split at h
  · split at h
    · exact mem_canonHoles (List.mem_of_getElem? h)
    · exact nomatch h
  · exact nomatch h

theorem canonCrest_constsBound {env₀ : Env} {names lps : List Name} {nP k : Nat} {e A : Expr}
    (he : ConstsBound env₀ e)
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k e) = some A) :
    ConstsBound env₀ A := by
  refine constsBound_instPisWith (fun x hx => ?_) ?_ hA
  · obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp
  · refine constsBound_replaceConsts (fun c us r hr => ?_) e he
    obtain ⟨mm, -, rfl⟩ := canonAbs_repl hr
    simp

theorem canonCrest_noProjAt {T : Name} {q : Nat} {names lps : List Name} {nP k : Nat}
    {e A : Expr} (he : ConLeche.Expr.NoProjAt T q e)
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k e) = some A) :
    ConLeche.Expr.NoProjAt T q A := by
  refine noProjAt_instPisWith (fun x hx => ?_) ?_ hA
  · obtain ⟨i, -, rfl⟩ := mem_canonParams hx
    simp
  · refine noProjAt_replaceConsts (fun c us r hr => ?_) e he
    obtain ⟨mm, -, rfl⟩ := canonAbs_repl hr
    simp

theorem canonCrest_consCrossAt {c₀ : ConstantInfo} {names lps : List Name} {nP k : Nat}
    {e A : Expr} (he : ConsCrossAt c₀ e)
    (hA : instPisWith (canonParams nP) (canonAbs names lps nP k e) = some A) :
    ConsCrossAt c₀ A :=
  fun tbl heq q => canonCrest_noProjAt (he tbl heq q) hA

/-! ## M2′ is blind to the holes' annotations -/

/-- **The member-constant test of an abstracted type does not depend on
the holes**, only on the names, the levels and the number of holes: a
hole is a variable, which the test (`nestOcc … 0 0`) never counts. -/
theorem nestOcc_nestAbstract_blind {ctx ctx' : ConLeche.NestCtx} {holes holes' : List Expr}
    (hn : ctx.names = ctx'.names) (hl : ctx.lps = ctx'.lps) (hlen : holes.length = holes'.length)
    (hh : ∀ h ∈ holes, ∃ i ty, h = .fvar i ty) (hh' : ∀ h ∈ holes', ∃ i ty, h = .fvar i ty)
    (names : List Name) :
    ∀ e : Expr, (ConLeche.nestAbstract ctx holes e).nestOcc names 0 0
      = (ConLeche.nestAbstract ctx' holes' e).nestOcc names 0 0 := by
  intro e
  induction e with
  | bvar i => rfl
  | fvar i ty ih =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc]
  | sort u => rfl
  | lit l => rfl
  | const c us =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, hn, hl]
    split
    · split
      · rename_i mm _
        rcases hg : holes[mm]? with _ | x
        · have hg' : holes'[mm]? = none := by
            rw [List.getElem?_eq_none_iff] at hg ⊢; omega
          rw [hg']
        · obtain ⟨x', hg'⟩ : ∃ x', holes'[mm]? = some x' := by
            refine ⟨holes'[mm]'?_, List.getElem?_eq_getElem _⟩
            have := (List.getElem?_eq_some_iff.mp hg).1; omega
          rw [hg']
          obtain ⟨i, ty, rfl⟩ := hh x (List.mem_of_getElem? hg)
          obtain ⟨i', ty', rfl⟩ := hh' x' (List.mem_of_getElem? hg')
          simp [ConLeche.Expr.nestOcc]
      · rfl
    · rfl
  | app a b iha ihb =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc] at iha ihb ⊢
    rw [iha, ihb]
  | lam ty b m iht ihb =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc] at iht ihb ⊢
    rw [iht, ihb]
  | forallE ty b m iht ihb =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc] at iht ihb ⊢
    rw [iht, ihb]
  | letE ty v b iht ihv ihb =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc] at iht ihv ihb ⊢
    rw [iht, ihv, ihb]
  | proj s i e ih =>
    simp only [ConLeche.nestAbstract, ConLeche.Expr.replaceConsts, ConLeche.Expr.nestOcc] at ih ⊢
    rw [ih]

theorem canonHoles_length (nP k : Nat) : (canonHoles nP k).length = k := by
  simp [canonHoles]

theorem canonHoles_getElem? {nP k t : Nat} (ht : t < k) :
    (canonHoles nP k)[t]? = some (.fvar (nP + t) (.sort .zero)) := by
  simp [canonHoles, List.getElem?_range ht]

theorem canonParams_getElem? {nP i : Nat} {x : Expr} (h : (canonParams nP)[i]? = some x) :
    x = .fvar i (.sort .zero) := by
  have hi : i < nP := by
    have := (List.getElem?_eq_some_iff.mp h).1; simpa [canonParams] using this
  simp [canonParams, List.getElem?_range hi] at h
  exact h.symm

theorem canonParams_length (nP : Nat) : (canonParams nP).length = nP := by
  simp [canonParams]

end ConLeche.Model
