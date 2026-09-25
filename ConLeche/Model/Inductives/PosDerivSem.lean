module

public import ConLeche.Verify.Inductives.PosDeriv
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.Subst

public section

/-!
# A syntactic node's key is denoted (lane NESTIND s22, F15)

The coordinator's ruling on F15 (1): the derivation's syntactic rules
(`synNew`/`synHit`) record their SOURCE (`SynSrc`: the key is official's
reading of a raw subterm of the scanned field).  Here: a raw subterm
without loose bound variables of a denoted term is denoted
(`denoteMeta_subOf`), so a syntactic key's parameters are read wherever
its field is (`synSrc_spine`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestKey SynSrc)

/-- A raw subterm without loose bound variables survives an opening. -/
theorem Expr.SubOf.instantiate1 {x : Expr} (hx : x.looseBVarsBounded 0 = true) (v : Expr) :
    ∀ {e : Expr}, ConLeche.Expr.SubOf x e → ∀ k, ConLeche.Expr.SubOf x (e.instantiate1 v k) := by
  intro e h
  induction h with
  | refl =>
    intro k
    rw [ConLeche.Expr.instantiate1_eq_self (ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) hx)]
    exact .refl _
  | appF a _ ih => intro k; exact .appF _ (ih k)
  | appA f _ ih => intro k; exact .appA _ (ih k)
  | lamT b bm _ ih => intro k; exact .lamT _ _ (ih k)
  | lamB t bm _ ih => intro k; exact .lamB _ _ (ih (k + 1))
  | piT b bm _ ih => intro k; exact .piT _ _ (ih k)
  | piB t bm _ ih => intro k; exact .piB _ _ (ih (k + 1))
  | letT v' b _ ih => intro k; exact .letT _ _ (ih k)
  | letV t b _ ih => intro k; exact .letV _ _ (ih k)
  | letB t v' _ ih => intro k; exact .letB _ _ (ih (k + 1))
  | proj s i _ ih => intro k; exact .proj _ _ (ih k)

/-- Raw subterms compose. -/
theorem Expr.SubOf.trans {x y z : Expr} (h₁ : ConLeche.Expr.SubOf x y)
    (h₂ : ConLeche.Expr.SubOf y z) : ConLeche.Expr.SubOf x z := by
  induction h₂ with
  | refl => exact h₁
  | appF a _ ih => exact .appF _ ih
  | appA f _ ih => exact .appA _ ih
  | lamT b bm _ ih => exact .lamT _ _ ih
  | lamB t bm _ ih => exact .lamB _ _ ih
  | piT b bm _ ih => exact .piT _ _ ih
  | piB t bm _ ih => exact .piB _ _ ih
  | letT v b _ ih => exact .letT _ _ ih
  | letV t b _ ih => exact .letV _ _ ih
  | letB t v _ ih => exact .letB _ _ ih
  | proj s i _ ih => exact .proj _ _ ih

/-- An application's arguments are raw subterms of it. -/
theorem Expr.SubOf.of_mem_getAppArgs {x : Expr} :
    ∀ {s : Expr}, x ∈ s.getAppArgs → ConLeche.Expr.SubOf x s
  | .app f a, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact .appF _ (Expr.SubOf.of_mem_getAppArgs hx)
    · exact .appA _ (.refl _)
  | .bvar _, hx | .fvar .., hx | .sort _, hx | .const .., hx | .lit _, hx | .lam .., hx
  | .forallE .., hx | .letE .., hx | .proj .., hx => by simp [Expr.getAppArgs] at hx

universe w

variable {V : Type w} [SetTheory V]
variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

private theorem denoteMeta_subOf_aux {x : Expr} (hx : x.looseBVarsBounded 0 = true) :
    ∀ (n : Nat) (e : Expr), e.sizeB ≤ n → ConLeche.Expr.SubOf x e →
      ∀ {d : Nat} {ea : AnnotTerm}, denoteMeta acval env φ d e = some ea →
        ∃ d' xa, d ≤ d' ∧ denoteMeta acval env φ d' x = some xa := by
  intro n
  induction n with
  | zero =>
    intro e hn
    exact absurd hn (by cases e <;> simp [Expr.sizeB])
  | succ n ih =>
    intro e hn hsub d ea hd
    cases hsub with
    | refl => exact ⟨d, ea, Nat.le_refl _, hd⟩
    | appF a hs =>
      obtain ⟨fa, -, hf, -, -⟩ := denoteMeta_app_inv hd
      exact ih _ (by simp [Expr.sizeB] at hn; omega) hs hf
    | appA f hs =>
      obtain ⟨-, aa, -, ha, -⟩ := denoteMeta_app_inv hd
      exact ih _ (by simp [Expr.sizeB] at hn; omega) hs ha
    | lamT b bm hs =>
      obtain ⟨ta, -, ht, -, -⟩ := denoteMeta_lam_inv hd
      exact ih _ (by simp [Expr.sizeB] at hn; omega) hs ht
    | lamB t bm hs =>
      obtain ⟨-, ba, -, hb, -⟩ := denoteMeta_lam_inv hd
      obtain ⟨d', xa, hle, hxa⟩ := ih _
        (by rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB] at hn; omega)
        (Expr.SubOf.instantiate1 hx _ hs 0) hb
      exact ⟨d', xa, by omega, hxa⟩
    | piT b bm hs =>
      obtain ⟨ta, -, ht, -, -⟩ := denoteMeta_forallE_inv hd
      exact ih _ (by simp [Expr.sizeB] at hn; omega) hs ht
    | piB t bm hs =>
      obtain ⟨-, ba, -, hb, -⟩ := denoteMeta_forallE_inv hd
      obtain ⟨d', xa, hle, hxa⟩ := ih _
        (by rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB] at hn; omega)
        (Expr.SubOf.instantiate1 hx _ hs 0) hb
      exact ⟨d', xa, by omega, hxa⟩
    | letT _ _ _ | letV _ _ _ | letB _ _ _ =>
      rw [denoteMeta] at hd
      exact nomatch hd
    | proj s i hs =>
      obtain ⟨ia, hi, -⟩ := denoteMeta_proj_inv hd
      exact ih _ (by simp [Expr.sizeB] at hn; omega) hs hi

/-- **A raw subterm of a denoted term is denoted** (F15): at some depth at
least the term's, when it has no loose bound variables. -/
theorem denoteMeta_subOf {x e : Expr} (hx : x.looseBVarsBounded 0 = true)
    (hsub : ConLeche.Expr.SubOf x e) {d : Nat} {ea : AnnotTerm}
    (hd : denoteMeta acval env φ d e = some ea) :
    ∃ d' xa, d ≤ d' ∧ denoteMeta acval env φ d' x = some xa :=
  denoteMeta_subOf_aux hx _ e (Nat.le_refl _) hsub hd

/-- **A syntactic key's parameters are read** at every depth `h` they are
scoped below, when the field they come from is read at a depth `≥ h`. -/
theorem synSrc_spine (m : EnvModel V env) {ctx : NestCtx} {hi : Nat} {e : Expr} {key : NestKey}
    (hsrc : SynSrc ctx hi e key) {h : Nat}
    (hds : ∀ x ∈ key.ds, x.looseBVarsBounded 0 = true ∧ Expr.WScoped h x)
    {d : Nat} (hhd : h ≤ d) {ea : AnnotTerm} (hd : denoteMeta m.acval env φ d e = some ea) :
    ∃ dsa, DenoteMetaSpine m.acval env φ h key.ds dsa := by
  obtain ⟨s, hs, hsk⟩ := hsrc
  have hmem := ConLeche.nestSynApp?_ds hsk
  suffices ∀ xs : List Expr, (∀ x ∈ xs, x ∈ key.ds) → ∃ dsa, DenoteMetaSpine m.acval env φ h xs dsa
    from this key.ds fun _ hx => hx
  intro xs
  induction xs with
  | nil => exact fun _ => ⟨[], .nil⟩
  | cons x xs ihx =>
    intro hxs
    obtain ⟨dsa, hdsa⟩ := ihx fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    have hxk := hxs x List.mem_cons_self
    obtain ⟨hb, hw⟩ := hds x hxk
    have hsx : ConLeche.Expr.SubOf x e := Expr.SubOf.trans (Expr.SubOf.of_mem_getAppArgs (hmem x hxk)) hs
    obtain ⟨d', xa, hle, hxa⟩ := denoteMeta_subOf hb hsx hd
    rw [denoteMeta_lift m.acval_closed hw d' (by omega)] at hxa
    obtain ⟨v, hv, -⟩ := Option.map_eq_some_iff.mp hxa
    exact ⟨v :: dsa, .cons hv hdsa⟩

end ConLeche.Model
