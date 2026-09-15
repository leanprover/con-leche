module

public import ConLeche.Model.Inductives.StructData
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructCtorFrames
import ConLeche.Model.Inductives.StructFrame
import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Model.Inductives.MutualFormersKit
public import ConLeche.Model.Inductives.FixStageRec
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.InferLemmas
import ConLeche.Model.AxiomBits
public section

/-!
# A mutual member's index universe (task #315)

The mutual install runs no index-telescope sort check of its own: a
member's index binders are graded and bounded by the *former's own*
data, and the bound comes from the `checkConstantVal` run that
accepted the former's type.

This module carries that route, binder by binder.
`piLevels_of_infer` lists the Π-prefix's domain sorts along an
inference (one per binder, in order); `teleLevels_walk` walks those
sorts along the reading, so that each domain's interpretation lands
in the universe its own sort names; `formerLevels_of` joins the two
at a checked constant, producing the per-binder universes of a
former's telescope as levels evaluated at the *restricted*
assignment (the sorts are the checker's own, and nothing says they
mention only the block's parameters); and `formerIdxOk` turns the
index half of that datum — every index binder under a common bound —
into the `IdxOk`/`FieldsValid` pair the tuple leaf consumes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta
  inferTypeCore ensureSortCore openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit -/

omit [SetTheory V] in
/-- Evaluating a list of levels commutes with indexing. -/
theorem getD_map_eval (f : Name → Nat) (us : List Level) {i : Nat}
    (hi : i < us.length) :
    (us.map (Level.eval f)).getD i 0 = Level.eval f (us.getD i .zero) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-! ## The Π-prefix's domain sorts, listed -/

omit [SetTheory V] in
/-- **The Π-prefix's domains' sorts, listed**: along an opening of an
inferred type, every binder's domain infers a sort of its own — one
per binder, in order — and at a nonzero whole sort each is at most it
(`imax` is then `max`).  The two contents are one walk: the list is
fixed once, the bound read off the nesting. -/
theorem piLevels_of_infer {env : Env} :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {v₀ : Level} {fvs : List Expr}
      {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      inferTypeCore μ env F d e = .ok t →
      ensureSortCore μ env F d t = .ok v₀ →
      ∃ us : List Level, us.length = n ∧
        ∀ (k : Nat) (a : Expr), fvs[k]? = some a →
          ∃ (F' : Nat) (t' : Expr),
            inferTypeCore μ env F' (d + k) a.fvarTypeD = .ok t' ∧
            ensureSortCore μ env F' (d + k) t' = .ok (us.getD k .zero) ∧
            ∀ φ, Level.eval φ v₀ ≠ 0 →
              Level.eval φ (us.getD k .zero) ≤ Level.eval φ v₀
  | 0, F, d, e, t, v₀, fvs, opened, hop, _, _ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact ⟨[], rfl, fun k a hk => nomatch hk⟩
  | n + 1, F, d, e, t, v₀, fvs, opened, hop, h, hens => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, hdom, hwh, hbt, hensb, -, rfl⟩ :=
          ConLeche.inferTypeCore_forall_inv h
        have hv₀ : v₀ = .imax u v := ensureSortCore_sort_eq hens
        subst hv₀
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨us, hlen, hus⟩ := piLevels_of_infer n hop' hbt hensb
          refine ⟨u :: us, by simp [hlen], ?_⟩
          intro k a hk
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            refine ⟨F, tty, by simpa [Expr.fvarTypeD] using hdom, ?_, fun φ hne => ?_⟩
            · rw [Nat.add_zero, ConLeche.ensureSortCore_eq, hwh]; rfl
            · have hv : Level.eval φ v ≠ 0 := fun h0 =>
                hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
              simp only [List.getD_cons_zero, Level.eval, if_neg hv]
              exact Nat.le_max_left _ _
          | succ k =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨F', t', h1, h2, h3⟩ := hus k a hk
            rw [show d + (k + 1) = d + 1 + k from by omega]
            refine ⟨F', t', h1, ?_, fun φ hne => ?_⟩
            · simpa using h2
            · have hv : Level.eval φ v ≠ 0 := fun h0 =>
                hne ((eval_imax_eq_zero_iff φ u v).mpr h0)
              have hle := h3 φ hv
              simp only [List.getD_cons_succ, Level.eval, if_neg hv]
              exact Nat.le_trans (by simpa using hle) (Nat.le_max_right _ _)
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The domains' universes, walked -/

/-- **The telescope's domains land in their own universes**, binder by
binder: at a frame satisfying the earlier domains, the next domain's
reading is graded and lies in `univ (ws k)` whenever the binder's
inferred sort evaluates below `ws k` — the sort claim at the context
opened by the earlier binders. -/
theorem teleLevels_walk (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (ψ : Name → Nat) :
    ∀ (n : Nat) (ws : Nat → Nat) {d : Nat} {e : Expr} {fvs : List Expr}
      {o : Expr} {Δ : List AnnotTerm} {tl : List (Nat × Nat × AnnotTerm)},
      ConLeche.openPisAtFvars n e d = some (fvs, o) → tl.length = n →
      CtxOk mp.base2 ψ d Δ e → Expr.WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      (∀ k a, fvs[k]? = some a →
        denoteMeta mp.base2.acval env ψ (d + k) a.fvarTypeD
          = some (tl.getD k default).2.2) →
      (∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (d + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (d + k) t = .ok u ∧
        Level.eval ψ u ≤ ws k) →
      ∀ k, k < n → ∀ ρ : Nat → V,
        Sat V (((tl.take k).map (·.2.2)).reverse ++ Δ) ρ →
        WellDenotedV V ρ (tl.getD k default).2.2 ∧
          interp V ρ (tl.getD k default).2.2 ∈ˢ (univ (ws k) : V)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, hk, _, _ =>
    absurd hk (Nat.not_lt_zero k)
  | n + 1, ws, d, e, fvs, o, Δ, tl, hop, hlen, hC, hws, hb, hL, hread, hinf,
      k, hk, ρ, hρ => by
    match e, hop, hws, hb with
    | .forallE ty body mb, hop, hws, hb =>
      simp only [ConLeche.openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        cases tl with
        | nil => exact absurd hlen (by simp)
        | cons t0 tl' =>
        have hlen' : tl'.length = n := by simpa using hlen
        have hws2 : Expr.WScoped d ty ∧ Expr.WScoped d body := by
          simp only [Expr.WScoped] at hws; exact hws
        -- the first domain's frame conditions
        have hbty : ty.looseBVarsBounded 0 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.1
        have hbb : body.looseBVarsBounded 1 = true := by
          simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb; exact hb.2
        have hLty : Expr.LeavesBounded ty := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_left _ hl)
        have hLbody : Expr.LeavesBounded body := fun l hl =>
          hL l (by rw [Expr.fvarLeaves]; exact List.mem_append_right _ hl)
        -- the first domain's row
        have hread0 : denoteMeta mp.base2.acval env ψ d ty = some t0.2.2 := by
          have := hread 0 _ rfl
          simpa [Expr.fvarTypeD] using this
        obtain ⟨F, t, u, hi, hens, hle⟩ := hinf 0 _ rfl
        simp only [Nat.add_zero, Expr.fvarTypeD] at hi hens
        have hCty := hC.forallE_ty
        have hrow := (claimsAt_of hμ mp ψ F).sortRow hi hens hws2.1 hbty hLty hCty
          hread0
        cases k with
        | zero =>
          simp only [List.take_zero, List.map_nil, List.reverse_nil,
            List.nil_append] at hρ
          exact ⟨(hrow ρ hρ).1, univ_mono hle _ (hrow ρ hρ).2⟩
        | succ k =>
          -- open the binder, walk on
          have hC' : CtxOk mp.base2 ψ (d + 1) (t0.2.2 :: Δ)
              (body.instantiate1 (.fvar d ty)) :=
            CtxOk.open hC.forallE_body hCty hread0 fun ρ hρ => (hrow ρ hρ).1
          obtain ⟨hws', hb', hL'⟩ := frame_open2 hws2.1 hbty hws2.2 hbb hLty hLbody
          have hread' : ∀ k a, fvs'[k]? = some a →
              denoteMeta mp.base2.acval env ψ (d + 1 + k) a.fvarTypeD
                = some (tl'.getD k default).2.2 := by
            intro k a hk
            have := hread (k + 1) a (by simpa using hk)
            rwa [show d + (k + 1) = d + 1 + k from by omega] at this
          have hinf' : ∀ k a, fvs'[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
              ConLeche.inferTypeCore μ env F (d + 1 + k) a.fvarTypeD = .ok t ∧
              ConLeche.ensureSortCore μ env F (d + 1 + k) t = .ok u ∧
              Level.eval ψ u ≤ ws (k + 1) := by
            intro k a hk
            obtain ⟨F, t, u, h1, h2, h3⟩ := hinf (k + 1) a (by simpa using hk)
            rw [show d + (k + 1) = d + 1 + k from by omega] at h1 h2
            exact ⟨F, t, u, h1, h2, h3⟩
          have hρ' : Sat V (((tl'.take k).map (·.2.2)).reverse ++ (t0.2.2 :: Δ)) ρ := by
            simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc]
              using hρ
          have := teleLevels_walk hμ mp ψ n (fun k => ws (k + 1)) hop' hlen' hC'
            hws' hb' hL' hread' hinf' k (by omega) ρ hρ'
          simpa using this
      · exact nomatch hop
    | .bvar _, hop, _, _ | .fvar _ _, hop, _, _ | .sort _, hop, _, _
    | .const _ _, hop, _, _ | .app _ _, hop, _, _ | .lam _ _ _, hop, _, _
    | .letE _ _ _, hop, _, _ | .lit _, hop, _, _ | .proj _ _ _, hop, _, _ =>
      simp [ConLeche.openPisAtFvars] at hop

/-! ## A member's index telescope, from its former's data alone -/

/-- **A member's index telescope is graded and bounded**, from its
former's binder data alone: the binders' universes are the level fact
`hlv` (`formerLevels_of`) and the walk is the direct route's, with
those levels in place of the checker's sort rows — the mutual install
runs no index-telescope sort check of its own, so this is where the
tuple leaf's `IdxOk` comes from. -/
theorem formerIdxOk {env : Env} {m : EnvModel V env} {cvT : ConstantVal} {nP nIdx : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps) {ψ : Name → Nat} {lv : Nat → Nat}
    (hlv : ∀ i, i < nP + nIdx → ∀ ρ : Nat → V,
      Sat V ((((pps ψ).take i).map (·.2.2)).reverse) ρ →
      interp V ρ ((pps ψ).getD i default).2.2 ∈ˢ (univ (lv i) : V))
    {u : Nat} (hu : ∀ j, j < nIdx → lv (nP + j) ≤ u)
    (ρp : Nat → V) (hρp : Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp) :
    IdxOk u ρp (((pps ψ).drop nP).map (·.2.2)) ∧
      FieldsValid ρp (((pps ψ).drop nP).map (·.2.2)) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓ : (((pps ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hbnd : ∀ j, j < nIdx → ∀ ρ : Nat → V,
      Sat V ((((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + j))) ρ →
      interp V ρ ((((pps ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - (nP + j)) default)
        ∈ˢ (univ u : V) := by
    intro j hj ρ hρ
    have hi : nP + j < nP + nIdx := by omega
    have hget : (pps ψ)[nP + j]? = some ((pps ψ).getD (nP + j) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hFD.len ψ]; omega)]; rfl
    rw [getD_reverse_of_peel (hFD.len ψ) hi hget]
    refine univ_mono (hu j hj) _ (hlv (nP + j) hi ρ ?_)
    rw [drop_reverse_map_eq (hFD.len ψ) (by omega)] at hρ
    exact hρ
  have hρp' : Sat V ((((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_reverse_map_eq (hFD.len ψ) (by omega)]
    exact hρp
  have hok := fieldsOkB_of_frame rfl hΓ okΓ (fun j hj ρ hρ _ => hbnd j hj ρ hρ) 0
    (Nat.zero_le _) ρp hρp'
  have hbd := fieldsBound_of_frame rfl hΓ hbnd 0 (Nat.zero_le _) ρp hρp'
  have hvd := fieldsValid_of_frame rfl hΓ okΓ 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hok hbd hvd
  exact ⟨⟨hok, hbd⟩, hvd⟩

/-! ## The former's per-binder universes -/

/-- **The former's binder universes**, from its `checkConstantVal`
run: one level per binder (the sort the checker inferred for it), and
at every assignment the binder's reading lands in that level's
universe — evaluated at the assignment *restricted* to the constant's
level parameters, since nothing says the checker's sorts mention only
those. -/
theorem formerLevels_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvT cvTa : ConstantVal} {n : Nat} {resSort : Level}
    {bs : List (Expr × ConLeche.BinderMeta)}
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hstrip : cvTa.type.stripPis n = some (bs, .sort resSort))
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa n resSort pps) :
    ∃ us : List Level, us.length = n ∧
      ∀ (ψ : Name → Nat) (i : Nat), i < n → ∀ ρ : Nat → V,
        Sat V ((((pps ψ).take i).map (·.2.2)).reverse) ρ →
        interp V ρ ((pps ψ).getD i default).2.2
          ∈ˢ (univ (Level.eval (restrictΨ cvTa.levelParams ψ) (us.getD i .zero)) : V) := by
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, uT, hann', htp', -, hst,
    hens, rfl⟩ := ConLeche.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hstrip
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  obtain ⟨fvs, hop⟩ := openPisAtFvars_of_stripPis_sort n 0 hstrip
  obtain ⟨us, hlenUs, hus⟩ := piLevels_of_infer (μ := μ) n hop hst hens
  refine ⟨us, hlenUs, ?_⟩
  -- the walk at an arbitrary assignment: every binder's reading lands
  -- in the universe of the sort the checker inferred for it
  have hper : ∀ ψ : Name → Nat, ∀ i, i < n → ∀ ρ : Nat → V,
      Sat V ((((pps ψ).take i).map (·.2.2)).reverse) ρ →
      interp V ρ ((pps ψ).getD i default).2.2
        ∈ˢ (univ (Level.eval ψ (us.getD i .zero)) : V) := by
    intro ψ i hi ρ hρ
    -- the reading, opened at the former's own variables
    obtain ⟨Γ, R, htele, hop'⟩ :=
      opened_of hop htf' hbt' (hFD.read ψ) (fun ρ => hFD.okTy ψ ρ)
    obtain ⟨pps₀, hst₀, hΓ⟩ := stripPisAV_of_piTeleAV htele
    have hstM := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
    rw [hFD.len ψ] at hstM
    obtain ⟨rfl, -⟩ : pps₀ = pps ψ ∧ R = .sort (resSort.eval ψ) := by
      have := hst₀.symm.trans hstM
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this
    -- the per-binder readings and sorts along the opening
    have hread : ∀ k a, fvs[k]? = some a →
        denoteMeta mp.base2.acval env ψ (0 + k) a.fvarTypeD
          = some ((pps ψ).getD k default).2.2 := by
      intro k a hk
      have hkn : k < n := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        rw [openPisAtFvars_length n hop] at this
        omega
      have hp : (pps ψ)[k]? = some ((pps ψ).getD k default) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (l := pps ψ) (i := k)
            (by rw [hFD.len ψ]; omega)]
        rfl
      have := hop'.doms k a hk
      rw [← hΓ, getD_reverse_of_peel (hFD.len ψ) hkn hp] at this
      simpa using this
    have hinf : ∀ k a, fvs[k]? = some a → ∃ (F : Nat) (t : Expr) (u : Level),
        ConLeche.inferTypeCore μ env F (0 + k) a.fvarTypeD = .ok t ∧
        ConLeche.ensureSortCore μ env F (0 + k) t = .ok u ∧
        Level.eval ψ u ≤ Level.eval ψ (us.getD k .zero) := by
      intro k a hk
      obtain ⟨F'', t', h1, h2, -⟩ := hus k a hk
      exact ⟨F'', t', us.getD k .zero, h1, h2, Nat.le_refl _⟩
    exact (teleLevels_walk hμ mp ψ n (fun k => Level.eval ψ (us.getD k .zero))
      hop (hFD.len ψ) (CtxOk.nil hnil) hw hbt' hL hread hinf i hi ρ
      (by simpa using hρ)).2
  -- the universes are recorded at the assignment RESTRICTED to the
  -- constant's level parameters; the readings do not tell the two
  -- apart (`params`), so the membership at one is the other's
  intro ψ i hi ρ hρ
  have hpps : pps (restrictΨ cvT.levelParams ψ) = pps ψ :=
    (hFD.params (restrictΨ cvT.levelParams ψ) ψ
      (restrictΨ_agree cvT.levelParams ψ)).1
  have hmem := hper (restrictΨ cvT.levelParams ψ) i hi ρ (by rw [hpps]; exact hρ)
  rwa [hpps] at hmem

end ConLeche.Model
