module
import ConLeche.Semantics.ConstsBound
import ConLeche.Verify.Shift
import ConLeche.Verify.Inductives.UseSynK
public import ConLeche.Model.Inductives.TargetNestCall
import ConLeche.Verify.InstLevels
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.SubstAV
import ConLeche.Model.Inductives.StructRecKit
public section

/-!
# The relocated holes, syntactically (PRIMREC / NESTKN-NL)

The side conditions `walkCtx_holesDep` asks of a relocated hole type (`relocHolesRK`'s
`relocRK H I (holesAt base tysP) ty`): leaves among the frame and the holes before it,
bvar-closed, constants bound, scoped at its position (`relocTy_syn`); with the structural
helpers `constsBound_instantiateLevelParams`, `wscoped_instantiateLevelParams`,
`constsBound_replaceFVars`, `wscoped_leaf_lt`.
-/

namespace ConLeche.Model
open ConLeche (Env Expr Name Level)
open ConLeche.Semantics

theorem constsBound_instantiateLevelParams {env : Env} (ks : List Name) (us : List Level) :
    ∀ (e : Expr), ConstsBound env (e.instantiateLevelParams ks us) ↔ ConstsBound env e := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams]

theorem wscoped_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (d : Nat), Expr.WScoped d (e.instantiateLevelParams ks us) ↔ Expr.WScoped d e := by
  intro e
  induction e <;> intro d <;> simp_all [Expr.instantiateLevelParams, Expr.WScoped]

theorem constsBound_replaceFVars {env : Env} {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → ConstsBound env b) :
    ∀ (e : Expr), ConstsBound env e → ConstsBound env (e.replaceFVars f) := by
  intro e
  induction e with
  | fvar i ty ih =>
    intro h
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => simpa using h
    | some b => simpa using hf i b hi
  | _ => simp_all [Expr.replaceFVars]

theorem wscoped_leaf_lt : ∀ (e : Expr) {d : Nat}, Expr.WScoped d e →
    ∀ l ∈ e.fvarLeaves, l.1 < d := by
  intro e
  induction e with
  | fvar i ty ih =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h.1
    · exact Nat.lt_trans (ih h.2 l hl) h.1
  | app f a ihf iha =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf h.1 l hl
    · exact iha h.2 l hl
  | lam t b _ iht ihb =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | forallE t b _ iht ihb =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | letE t v b iht ihv ihb =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1 l hl
    · exact ihv h.2.1 l hl
    · exact ihb h.2.2 l hl
  | proj _ _ x ih =>
    intro d h l hl
    simp only [Expr.WScoped] at h
    simp only [Expr.fvarLeaves] at hl
    exact ih h l hl
  | _ => intro d _ l hl; simp [Expr.fvarLeaves] at hl

/-- **A relocated hole type is a well-formed subject of the relocated context**: its leaves
are the frame's or the holes before it, it is bvar-closed, its constants are bound, and it
is scoped at its position — from the home type (scoped among the parameters and the holes
before it) and the instance's parameters (subjects of the frame). -/
theorem relocTy_syn {env : Env} {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {base t : Nat}
    {L : List Expr} {tysP : List Expr} (htl : tysP.length = t)
    (hP : ∀ s, s < t → Expr.WScoped (base + s) (tysP.getD s default) ∧
      ConstsBound env (tysP.getD s default) ∧
      ∀ l ∈ (tysP.getD s default).fvarLeaves, Expr.fvar l.1 l.2 ∈ (holesAt base tysP).reverse ++ L)
    (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, Expr.WScoped (base + t) d ∧ d.looseBVarsBounded 0 = true ∧
      ConstsBound env d ∧ ∀ l ∈ d.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    {ty : Expr} (hw : Expr.WScoped (H.ctx.nP + t) ty) (hb : ty.looseBVarsBounded 0 = true)
    (hc : ConstsBound env ty) :
    (∀ l ∈ (ConLeche.relocRK H I (holesAt base tysP) ty).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (holesAt base tysP).reverse ++ L) ∧
    (ConLeche.relocRK H I (holesAt base tysP) ty).looseBVarsBounded 0 = true ∧
    ConstsBound env (ConLeche.relocRK H I (holesAt base tysP) ty) ∧
    Expr.WScoped (base + t) (ConLeche.relocRK H I (holesAt base tysP) ty) := by
  have hhl : (holesAt base tysP).length = t := by simp [holesAt, htl]
  have hlw : Expr.WScoped (H.ctx.nP + t) (ConLeche.lvlRK H I ty) := by
    unfold ConLeche.lvlRK; split
    · exact hw
    · exact (wscoped_instantiateLevelParams _ _ ty _).mpr hw
  have hlb : (ConLeche.lvlRK H I ty).looseBVarsBounded 0 = true := by
    unfold ConLeche.lvlRK; split
    · exact hb
    · rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
  have hlc : ConstsBound env (ConLeche.lvlRK H I ty) := by
    unfold ConLeche.lvlRK; split
    · exact hc
    · exact (constsBound_instantiateLevelParams _ _ ty).mpr hc
  -- the images
  have himg : ∀ i b, (if i < H.ctx.nP then I.ds[i]?
      else if i < H.ctx.nP + (holesAt base tysP).length then (holesAt base tysP)[i - H.ctx.nP]?
      else none) = some b →
      Expr.WScoped (base + t) b ∧ b.looseBVarsBounded 0 = true ∧ ConstsBound env b ∧
        ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2 ∈ (holesAt base tysP).reverse ++ L := by
    intro i b hib
    split at hib
    · have hm := List.mem_of_getElem? hib
      obtain ⟨h1, h2, h3, h4⟩ := hds b hm
      exact ⟨h1, h2, h3, fun l hl => List.mem_append_right _ (h4 l hl)⟩
    · split at hib
      · rename_i h1 h2
        have hs : i - H.ctx.nP < t := by omega
        have hget : (holesAt base tysP)[i - H.ctx.nP]? = some (Expr.fvar (base + (i - H.ctx.nP))
            (tysP.getD (i - H.ctx.nP) default)) := by
          simp [holesAt, List.getElem?_range (show i - H.ctx.nP < tysP.length by omega)]
        rw [hget] at hib
        obtain rfl := Option.some.inj hib
        obtain ⟨hw', hc', hl'⟩ := hP _ hs
        refine ⟨?_, rfl, by simpa using hc', ?_⟩
        · simp only [Expr.WScoped]
          exact ⟨by omega, hw'⟩
        · intro l hl
          simp only [Expr.fvarLeaves, List.mem_cons] at hl
          rcases hl with rfl | hl
          · exact List.mem_append_left _ (List.mem_reverse.mpr (List.mem_of_getElem? hget))
          · exact hl' l hl
      · exact absurd hib (by simp)
  unfold ConLeche.relocRK
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    rcases ConLeche.Expr.fvarLeaves_replaceFVars_kept _ hlw l hl with ⟨i, b, hib, hlb'⟩ | ⟨-, i, ty', hni, hmem, -⟩
    · exact (himg i b hib).2.2.2 l hlb'
    · have hi := wscoped_leaf_lt _ hlw _ hmem
      exfalso
      simp only at hi
      revert hni
      split
      · rename_i h1; simp [List.getElem?_eq_getElem (show i < I.ds.length by omega)]
      · split
        · rename_i h1 h2
          simp [List.getElem?_eq_getElem (show i - H.ctx.nP < (holesAt base tysP).length by omega)]
        · rename_i h1 h2; exact absurd (by omega) h2
  · exact ConLeche.Expr.looseBVarsBounded_replaceFVars (fun i b h => (himg i b h).2.1) _ 0 hlb
  · exact constsBound_replaceFVars (fun i b h => (himg i b h).2.2.1) _ hlc
  · refine ConLeche.Expr.WScoped_replaceFVars (fun i b h => (himg i b h).1) _ hlw fun l hl hn => ?_
    have hi := wscoped_leaf_lt _ hlw _ hl
    exfalso
    revert hn
    split
    · rename_i h1; simp [List.getElem?_eq_getElem (show l.1 < I.ds.length by omega)]
    · split
      · rename_i h1 h2
        simp [List.getElem?_eq_getElem (show l.1 - H.ctx.nP < (holesAt base tysP).length by omega)]
      · rename_i h1 h2; exact absurd (by omega) h2

theorem holesAt_take (base : Nat) (tys : List Expr) (t : Nat) :
    holesAt base (tys.take t) = (holesAt base tys).take t := by
  apply List.ext_getElem (by simp [holesAt])
  intro i h1 h2
  simp only [holesAt, List.length_map, List.length_range, List.length_take] at h1
  simp [holesAt, List.getD_eq_getElem?_getD, List.getElem?_take, show i < t by omega]

/-- **Every relocated hole slot is a well-formed subject** (`relocTy_syn`, by strong
induction over the slots: the earlier slots' facts are its premise). -/
theorem relocTys_syn {env : Env} {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {base : Nat}
    {L : List Expr} (tysH : List Expr) (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, Expr.WScoped base d ∧ d.looseBVarsBounded 0 = true ∧
      ConstsBound env d ∧ ∀ l ∈ d.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hty : ∀ t, t < tysH.length → Expr.WScoped (H.ctx.nP + t) (tysH.getD t default) ∧
      (tysH.getD t default).looseBVarsBounded 0 = true ∧ ConstsBound env (tysH.getD t default)) :
    ∀ t, t < tysH.length →
      (relocTys H I base tysH []).getD t default
          = ConLeche.relocRK H I (holesAt base ((relocTys H I base tysH []).take t))
            (tysH.getD t default) ∧
      Expr.WScoped (base + t) ((relocTys H I base tysH []).getD t default) ∧
      ((relocTys H I base tysH []).getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound env ((relocTys H I base tysH []).getD t default) ∧
      ∀ l ∈ ((relocTys H I base tysH []).getD t default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ ((holesAt base (relocTys H I base tysH [])).take t).reverse ++ L := by
  have hlen := relocTys_length H I base tysH []
  simp only [List.length_nil, Nat.zero_add] at hlen
  have heq : ∀ t, t < tysH.length → (relocTys H I base tysH []).getD t default
      = ConLeche.relocRK H I (holesAt base ((relocTys H I base tysH []).take t))
        (tysH.getD t default) := by
    intro t ht
    have h := relocTys_getD H I base tysH [] t (by simpa using ht)
    simpa using h
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    refine ⟨heq t ht, ?_⟩
    have hsyn := relocTy_syn (env := env) (H := H) (I := I) (base := base) (t := t) (L := L)
      (tysP := (relocTys H I base tysH []).take t) (by simp [hlen]; omega)
      (fun s hs => by
        obtain ⟨-, hw, -, hc, hl⟩ := ih s hs (by omega)
        have hg : ((relocTys H I base tysH []).take t).getD s default
            = (relocTys H I base tysH []).getD s default := by
          simp [List.getD_eq_getElem?_getD, hs]
        rw [hg]
        refine ⟨hw, hc, fun l hl' => ?_⟩
        have := hl l hl'
        rw [holesAt_take] at ⊢
        rcases List.mem_append.mp this with h1 | h1
        · refine List.mem_append_left _ (List.mem_reverse.mpr ?_)
          have h1' := List.mem_reverse.mp h1
          exact (List.take_prefix_take_left (by omega : s ≤ t)).subset h1'
        · exact List.mem_append_right _ h1)
      hdl (fun d hd => by
        obtain ⟨h1, h2, h3, h4⟩ := hds d hd
        exact ⟨h1.mono (by omega), h2, h3, h4⟩)
      (hty t ht).1 (hty t ht).2.1 (hty t ht).2.2
    rw [← heq t ht, holesAt_take] at hsyn
    exact ⟨hsyn.2.2.2, hsyn.2.1, hsyn.2.2.1, hsyn.1⟩

section Walk

open ConLeche.SetModel SetTheory ConLeche.Term
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V] {envT : Env} {φ : Name → Nat}

/-- The relocated holes' context entries: slot `t`'s home reading substituted by the
instance map at depth `base + t`. -/
@[expose] def relocTsA (nP : Nat) (dsa : List AnnotTerm) (base : Nat) (THs : List AnnotTerm) :
    List AnnotTerm :=
  (List.range THs.length).map fun t =>
    AnnotTerm.substAV (substTau (nP + t) (base + t)
      (relocX nP (dsa.map (AnnotTerm.liftN t · 0)) base (base + t))) (THs.getD t default) 0

/-- **The walk's context extended by a node's relocated holes** (`callRK`'s `hs`): the
frame's context, the holes `relocHolesRK`'s (`relocHolesRK_eq`), each typed by its home
type relocated, filled by `hv` — from the home types' readings at the instance's levels,
their grading at the substituted valuations, and the values' membership at the home
valuation (the holes' values over the instance's key frame). -/
theorem walkCtx_reloc (mT : EnvModel V envT) {H : ConLeche.HomeRK} {I : ConLeche.InstRK}
    {base : Nat} {L : List Expr} (hL : FvarList base L) {Δ : List AnnotTerm} {σ : Nat → V}
    (hW : WalkCtx V mT φ base σ Δ L) (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, Expr.WScoped base d ∧ d.looseBVarsBounded 0 = true ∧
      ConstsBound envT d ∧ ∀ l ∈ d.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval envT φ base I.ds dsa)
    (tysH : List Expr) (THs : List AnnotTerm) (hlen : tysH.length = THs.length)
    (hty : ∀ t, t < tysH.length → Expr.WScoped (H.ctx.nP + t) (tysH.getD t default) ∧
      (tysH.getD t default).looseBVarsBounded 0 = true ∧ ConstsBound envT (tysH.getD t default) ∧
      denoteMeta mT.acval envT (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + t)
        (tysH.getD t default) = some (THs.getD t default))
    (hv : List V) (hvl : hv.length = THs.length)
    (hG : ∀ t, t < THs.length → ∀ ρ : Nat → V,
      Sat V (((relocTsA H.ctx.nP dsa base THs).take t).reverse ++ Δ) ρ →
      (∀ a ∈ dsa.map (AnnotTerm.liftN t · 0), WellDenotedV V ρ a) ∧
      WellDenotedV V (substE V (substTau (H.ctx.nP + t) (base + t)
        (relocX H.ctx.nP (dsa.map (AnnotTerm.liftN t · 0)) base (base + t))) 0 ρ)
        (THs.getD t default))
    (hmem : ∀ t, t < THs.length →
      hv.getD t pt ∈ˢ interp V (consList (hv.take t) (keyFrame dsa base σ)) (THs.getD t default)) :
    FvarList (base + THs.length)
        ((holesAt base (relocTys H I base tysH [])).reverse ++ L) ∧
      WalkCtx V mT φ (base + THs.length) (consList hv σ)
        ((relocTsA H.ctx.nP dsa base THs).reverse ++ Δ)
        ((holesAt base (relocTys H I base tysH [])).reverse ++ L) := by
  have hrl : (relocTys H I base tysH []).length = tysH.length := by
    simpa using relocTys_length H I base tysH []
  have hTl : (relocTsA H.ctx.nP dsa base THs).length = THs.length := by simp [relocTsA]
  have hsyn := relocTys_syn (env := envT) (H := H) (I := I) (base := base) (L := L) tysH hdl hds
    (fun t ht => ⟨(hty t ht).1, (hty t ht).2.1, (hty t ht).2.2.1⟩)
  have h := walkCtx_holesDep (mT := mT) (φ := φ) hL hW (relocTys H I base tysH [])
    (relocTsA H.ctx.nP dsa base THs) hv (by rw [hrl, hTl, hlen]) (by rw [hvl, hTl]) (fun t ht => by
      rw [hTl] at ht
      have htH : t < tysH.length := by omega
      obtain ⟨heq, hw, hb, hc, hlv⟩ := hsyn t htH
      -- the slot, read
      have hdsaT : DenoteMetaSpine mT.acval envT φ (base + t) I.ds
          (dsa.map (AnnotTerm.liftN t · 0)) := by
        have := DenoteMetaSpine.lift (m := mT) (h := base) (D := base + t) (by omega)
          (fun x hx => (hds x hx).1) hdsa
        rwa [show base + t - base = t by omega] at this
      obtain ⟨hrd, hval, hgr⟩ := relocSlot mT (H := H) (I := I) (base := base) (t := t)
        (tysP := (relocTys H I base tysH []).take t) (by simp [hrl]; omega)
        (fun s hs => by
          have hg : ((relocTys H I base tysH []).take t).getD s default
              = (relocTys H I base tysH []).getD s default := by
            simp [List.getD_eq_getElem?_getD, hs]
          rw [hg]; exact (hsyn s (by omega)).2.1)
        hdl (fun d hd => ⟨((hds d hd).1).mono (by omega), (hds d hd).2.1⟩) hdsaT
        (hty t htH).1.fvarsBelow (hty t htH).2.2.2
      have hTg : (relocTsA H.ctx.nP dsa base THs).getD t default
          = AnnotTerm.substAV (substTau (H.ctx.nP + t) (base + t)
            (relocX H.ctx.nP (dsa.map (AnnotTerm.liftN t · 0)) base (base + t)))
            (THs.getD t default) 0 := by
        simp [relocTsA, List.getD_eq_getElem?_getD, List.getElem?_range ht]
      refine ⟨hlv, hb, hc, ?_, ?_, ?_⟩
      · rw [heq, hTg]; exact hrd
      · intro ρ hρ
        rw [hTg]
        obtain ⟨h1, h2⟩ := hG t ht ρ hρ
        exact hgr ρ h1 h2
      · rw [hTg, hval (hv.take t) σ (by simp [hvl]; omega)]
        have hk := keyFrame_lift dsa base (hv.take t) σ
        rw [show (hv.take t).length = t by simp [hvl]; omega] at hk
        rw [hk]
        exact hmem t ht)
  rwa [hTl] at h

/-- A satisfying valuation of a context satisfies its prefix. -/
theorem Sat_append_left {A B : List AnnotTerm} {ρ : Nat → V} (h : Sat V (A ++ B) ρ) :
    Sat V A ρ := by
  intro i X hi
  exact h i X (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi)

/-- **The relocated holes are graded where the home's are** (`walkCtx_reloc`'s `hG`): a
valuation of the relocated context (the frame's `Δ`, the relocated hole types so far) gives,
through the instance map, a valuation of the HOME's context — its parameters' telescope
`Ps` at the instance's key frame (`hΔ`: the instance's parameters satisfy it wherever the
frame is satisfied) and the holes' values over it — where the home's hole types are
graded (`hH`). -/
theorem relocG_of_home {nP base : Nat} {dsa : List AnnotTerm} (hdl : dsa.length = nP)
    {Δ Ps : List AnnotTerm} (THs : List AnnotTerm)
    (hΔ : ∀ σ : Nat → V, Sat V Δ σ →
      (∀ a ∈ dsa, WellDenotedV V σ a) ∧ Sat V Ps (keyFrame dsa base σ))
    (hH : ∀ t, t < THs.length → ∀ ρ : Nat → V, Sat V ((THs.take t).reverse ++ Ps) ρ →
      WellDenotedV V ρ (THs.getD t default)) :
    ∀ t, t < THs.length → ∀ ρ : Nat → V,
      Sat V (((relocTsA nP dsa base THs).take t).reverse ++ Δ) ρ →
      (∀ a ∈ dsa.map (AnnotTerm.liftN t · 0), WellDenotedV V ρ a) ∧
      WellDenotedV V (substE V (substTau (nP + t) (base + t)
        (relocX nP (dsa.map (AnnotTerm.liftN t · 0)) base (base + t))) 0 ρ)
        (THs.getD t default) := by
  intro t ht ρ hρ
  have hTl : (relocTsA nP dsa base THs).length = THs.length := by simp [relocTsA]
  have htl : ((relocTsA nP dsa base THs).take t).length = t := by simp [hTl]; omega
  obtain ⟨vs, σ, hvl, rfl⟩ : ∃ vs σ, vs.length = t ∧ ρ = consList vs σ :=
    ⟨_, _, by simp, (consList_range_reverse t ρ).symm⟩
  have hσ : Sat V Δ σ := by
    have h := Sat_drop hρ t
    rw [List.drop_append_of_le_length (by simp [htl]), List.drop_eq_nil_of_le (by simp [htl]),
      List.nil_append] at h
    have he : (fun j => consList vs σ (j + t)) = σ := by
      funext j; rw [← hvl, consList_apply_add]
    rwa [he] at h
  have hfit : SpineFit σ ((relocTsA nP dsa base THs).take t) vs :=
    spineFit_of_sat_consList (by rw [htl, hvl]) (Sat_append_left hρ)
  obtain ⟨hdsW, hPs⟩ := hΔ σ hσ
  -- the home valuation of every slot
  have hkey : ∀ s, s ≤ t →
      substE V (substTau (nP + s) (base + s)
        (relocX nP (dsa.map (AnnotTerm.liftN s · 0)) base (base + s))) 0 (consList (vs.take s) σ)
        = consList (vs.take s) (keyFrame dsa base σ) := by
    intro s hs
    have hvs : (vs.take s).length = s := by simp; omega
    rw [substE_relocX (by simp [hdl]) hvs σ]
    have hk := keyFrame_lift dsa base (vs.take s) σ
    rw [hvs] at hk
    rw [hk]
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [WellDenotedV_liftN]
    have he : shiftE t 0 (consList vs σ) = σ := by
      funext j; simp only [shiftE, Nat.not_lt_zero, if_false]; rw [← hvl, consList_apply_add]
    rw [he]; exact hdsW b hb
  · have hk := hkey t (Nat.le_refl _)
    rw [List.take_of_length_le (by omega)] at hk
    rw [hk]
    refine hH t ht _ (sat_of_spineFit hPs ?_)
    refine spineFit_of_getD (by simp; omega) fun s hs => ?_
    simp only [List.length_take] at hs
    have hst : s < t := by omega
    have hm := FixKI.spineFit_getD_mem' hfit (l := s) (by rw [htl]; exact hst)
    have hg : ((relocTsA nP dsa base THs).take t).getD s default
        = AnnotTerm.substAV (substTau (nP + s) (base + s)
          (relocX nP (dsa.map (AnnotTerm.liftN s · 0)) base (base + s))) (THs.getD s default) 0 := by
      simp [relocTsA, List.getD_eq_getElem?_getD, hst,
        List.getElem?_range (show s < THs.length by omega)]
    rw [hg, interp_substAV, hkey s (by omega)] at hm
    have hg2 : (THs.take t).getD s default = THs.getD s default := by
      simp [List.getD_eq_getElem?_getD, hst]
    rw [hg2]
    exact hm

end Walk

end ConLeche.Model
