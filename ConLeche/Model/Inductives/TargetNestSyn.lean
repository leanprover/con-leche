module
public import ConLeche.Semantics.ConstsBound
public import ConLeche.Verify.Shift
import ConLeche.Verify.Inductives.UseSynK
public import ConLeche.Model.Inductives.TargetNestCall
import ConLeche.Verify.InstLevels
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

end ConLeche.Model
