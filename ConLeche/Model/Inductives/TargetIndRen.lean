module

public import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.Inductives.BlockHoleRead
public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.Inductives.FixRec

public section

/-!
# Free-variable renamings and the reading (lane RECLIB, B4)

Two terms are `FRen R`-related when they are the same term up to `fvar`
annotations and binder names, their free variables related pointwise by
`R` (the variable `i` of the first facing the variable `j` of the
second with `R i j`).  `Expr.ErasedEq` is the diagonal.

* **The reading is blind to a renaming** (`denoteMeta_fren_interp`):
  two related terms read, at their depths, to terms with one value at
  valuations that agree along `R` — the variable `i` read from below the
  depth `d` facing `j` read from below `d'`.
* The relation survives the operations the target check and the
  clause's walk build their terms with: instantiating a telescope at
  related variables (`instPisWith_fren`, `openPisAtFvars_fren`), the
  walk's field shift (`fren_shiftFromN`) and the two member
  abstractions (`fren_abs`: `nestAbstract` beside `targetAbs`).

This is the transport between the kernel's member-abstracted field types
(parameters, a gap, the fields, then the holes) and the clause's hole
reading (parameters, the holes, then the fields).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx nestAbstract instPisWith openPisAtFvars)

universe w

/-! ## The relation -/

/-- **Two terms related by a variable renaming** `R` (annotations and
binder names ignored, binder metadata kept). -/
@[expose] def FRen (R : Nat → Nat → Prop) : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _, .fvar j _ => R i j
  | .sort u, .sort v => u = v
  | .const n us, .const n' us' => n = n' ∧ us = us'
  | .app f a, .app g b => FRen R f g ∧ FRen R a b
  | .lam ty b m, .lam ty' b' m' => m = m' ∧ FRen R ty ty' ∧ FRen R b b'
  | .forallE ty b m, .forallE ty' b' m' => m = m' ∧ FRen R ty ty' ∧ FRen R b b'
  | .letE ty v b, .letE ty' v' b' => FRen R ty ty' ∧ FRen R v v' ∧ FRen R b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ FRen R e e'
  | _, _ => False

theorem FRen.mono {R S : Nat → Nat → Prop} (hRS : ∀ i j, R i j → S i j) :
    ∀ {a b : Expr}, FRen R a b → FRen S a b := by
  intro a
  induction a with
  | bvar i => intro b h; match b, h with | .bvar _, h => exact h
  | fvar i ty => intro b h; match b, h with | .fvar _ _, h => exact hRS _ _ h
  | sort u => intro b h; match b, h with | .sort _, h => exact h
  | const n us => intro b h; match b, h with | .const _ _, h => exact h
  | app f a ihf iha => intro b h; match b, h with | .app _ _, h => exact ⟨ihf h.1, iha h.2⟩
  | lam ty body m ih1 ih2 =>
    intro b h; match b, h with | .lam _ _ _, h => exact ⟨h.1, ih1 h.2.1, ih2 h.2.2⟩
  | forallE ty body m ih1 ih2 =>
    intro b h; match b, h with | .forallE _ _ _, h => exact ⟨h.1, ih1 h.2.1, ih2 h.2.2⟩
  | letE ty v body ih1 ih2 ih3 =>
    intro b h; match b, h with | .letE _ _ _, h => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | lit l => intro b h; match b, h with | .lit _, h => exact h
  | proj s i e ih => intro b h; match b, h with | .proj _ _ _, h => exact ⟨h.1, h.2.1, ih h.2.2⟩

theorem FRen.symm {R : Nat → Nat → Prop} :
    ∀ {a b : Expr}, FRen R a b → FRen (fun i j => R j i) b a := by
  intro a
  induction a with
  | bvar i => intro b h; match b, h with | .bvar _, h => exact Eq.symm h
  | fvar i ty => intro b h; match b, h with | .fvar _ _, h => exact h
  | sort u => intro b h; match b, h with | .sort _, h => exact Eq.symm h
  | const n us => intro b h; match b, h with | .const _ _, h => exact ⟨h.1.symm, h.2.symm⟩
  | app f a ihf iha => intro b h; match b, h with | .app _ _, h => exact ⟨ihf h.1, iha h.2⟩
  | lam ty body m ih1 ih2 =>
    intro b h; match b, h with | .lam _ _ _, h => exact ⟨h.1.symm, ih1 h.2.1, ih2 h.2.2⟩
  | forallE ty body m ih1 ih2 =>
    intro b h; match b, h with | .forallE _ _ _, h => exact ⟨h.1.symm, ih1 h.2.1, ih2 h.2.2⟩
  | letE ty v body ih1 ih2 ih3 =>
    intro b h; match b, h with | .letE _ _ _, h => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | lit l => intro b h; match b, h with | .lit _, h => exact Eq.symm h
  | proj s i e ih =>
    intro b h; match b, h with | .proj _ _ _, h => exact ⟨h.1.symm, h.2.1.symm, ih h.2.2⟩

theorem FRen.trans {R S : Nat → Nat → Prop} :
    ∀ {a b c : Expr}, FRen R a b → FRen S b c → FRen (fun i k => ∃ j, R i j ∧ S j k) a c := by
  intro a
  induction a with
  | bvar i =>
    intro b c h1 h2
    match b, c, h1, h2 with | .bvar _, .bvar _, h1, h2 => exact Eq.trans h1 h2
  | fvar i ty =>
    intro b c h1 h2
    match b, c, h1, h2 with | .fvar _ _, .fvar _ _, h1, h2 => exact ⟨_, h1, h2⟩
  | sort u =>
    intro b c h1 h2
    match b, c, h1, h2 with | .sort _, .sort _, h1, h2 => exact Eq.trans h1 h2
  | const n us =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .const _ _, .const _ _, h1, h2 => exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  | app f a ihf iha =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .app _ _, .app _ _, h1, h2 => exact ⟨ihf h1.1 h2.1, iha h1.2 h2.2⟩
  | lam ty body m ih1 ih2 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .lam _ _ _, .lam _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, ih1 h1.2.1 h2.2.1, ih2 h1.2.2 h2.2.2⟩
  | forallE ty body m ih1 ih2 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .forallE _ _ _, .forallE _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, ih1 h1.2.1 h2.2.1, ih2 h1.2.2 h2.2.2⟩
  | letE ty v body ih1 ih2 ih3 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .letE _ _ _, .letE _ _ _, h1, h2 =>
      exact ⟨ih1 h1.1 h2.1, ih2 h1.2.1 h2.2.1, ih3 h1.2.2 h2.2.2⟩
  | lit l =>
    intro b c h1 h2
    match b, c, h1, h2 with | .lit _, .lit _, h1, h2 => exact Eq.trans h1 h2
  | proj s i e ih =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .proj _ _ _, .proj _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, ih h1.2.2 h2.2.2⟩

/-- An erasure-equal right side keeps the relation. -/
theorem FRen.trans_erased {R : Nat → Nat → Prop} :
    ∀ {a b c : Expr}, FRen R a b → Expr.ErasedEq b c → FRen R a c := by
  intro a
  induction a with
  | bvar i =>
    intro b c h1 h2
    match b, c, h1, h2 with | .bvar _, .bvar _, h1, h2 => exact Eq.trans h1 h2
  | fvar i ty =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .fvar _ _, .fvar _ _, h1, h2 =>
      have h2' : _ = _ := h2
      subst h2'; exact h1
  | sort u =>
    intro b c h1 h2
    match b, c, h1, h2 with | .sort _, .sort _, h1, h2 => exact Eq.trans h1 h2
  | const n us =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .const _ _, .const _ _, h1, h2 => exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  | app f a ihf iha =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .app _ _, .app _ _, h1, h2 => exact ⟨ihf h1.1 h2.1, iha h1.2 h2.2⟩
  | lam ty body m ih1 ih2 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .lam _ _ _, .lam _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, ih1 h1.2.1 h2.2.1, ih2 h1.2.2 h2.2.2⟩
  | forallE ty body m ih1 ih2 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .forallE _ _ _, .forallE _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, ih1 h1.2.1 h2.2.1, ih2 h1.2.2 h2.2.2⟩
  | letE ty v body ih1 ih2 ih3 =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .letE _ _ _, .letE _ _ _, h1, h2 =>
      exact ⟨ih1 h1.1 h2.1, ih2 h1.2.1 h2.2.1, ih3 h1.2.2 h2.2.2⟩
  | lit l =>
    intro b c h1 h2
    match b, c, h1, h2 with | .lit _, .lit _, h1, h2 => exact Eq.trans h1 h2
  | proj s i e ih =>
    intro b c h1 h2
    match b, c, h1, h2 with
    | .proj _ _ _, .proj _ _ _, h1, h2 =>
      exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, ih h1.2.2 h2.2.2⟩

/-- A term with its variables below `d` is related to itself along any
relation holding on the diagonal below `d`. -/
theorem FRen.refl_of_fvarsBelow {R : Nat → Nat → Prop} {d : Nat} (hR : ∀ i, i < d → R i i) :
    ∀ {a : Expr}, Expr.fvarsBelow d a → FRen R a a := by
  intro a
  induction a with
  | bvar i => intro _; exact rfl
  | fvar i ty => intro h; exact hR i h
  | sort u => intro _; exact rfl
  | const n us => intro _; exact ⟨rfl, rfl⟩
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam ty body m ih1 ih2 => intro h; exact ⟨rfl, ih1 h.1, ih2 h.2⟩
  | forallE ty body m ih1 ih2 => intro h; exact ⟨rfl, ih1 h.1, ih2 h.2⟩
  | letE ty v body ih1 ih2 ih3 => intro h; exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | lit l => intro _; exact rfl
  | proj s i e ih => intro h; exact ⟨rfl, rfl, ih h⟩

/-- Every term is related to itself along the identity. -/
theorem FRen.rfl_eq : ∀ (a : Expr), FRen (fun i j => j = i) a a := by
  intro a
  induction a with
  | bvar i => exact rfl
  | fvar i ty => exact rfl
  | sort u => exact rfl
  | const n us => exact ⟨rfl, rfl⟩
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | lam ty body m ih1 ih2 => exact ⟨rfl, ih1, ih2⟩
  | forallE ty body m ih1 ih2 => exact ⟨rfl, ih1, ih2⟩
  | letE ty v body ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | lit l => exact rfl
  | proj s i e ih => exact ⟨rfl, rfl, ih⟩

theorem FRen.instantiate1 {R : Nat → Nat → Prop} :
    ∀ {e e' v v' : Expr} {k : Nat}, FRen R e e' → FRen R v v' →
      FRen R (e.instantiate1 v k) (e'.instantiate1 v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1]
      split
      · exact hv
      · split
        · exact (rfl : i - 1 = i - 1)
        · exact (rfl : i = i)
  | fvar idx ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j ty', he => exact he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => exact he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => exact he
  | app f a ihf iha =>
    intro e' v v' k he hv
    match e', he with
    | .app g b, he => exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .lam ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | forallE ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .forallE ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .letE ty' vl' body', he => exact ⟨ihty he.1 hv, ihv he.2.1 hv, ihbody he.2.2 hv⟩
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => exact he
  | proj sn i pe ih =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' pe', he => exact ⟨he.1, he.2.1, ih he.2.2 hv⟩

/-! ## Telescopes -/

/-- Two lists pointwise related. -/
@[expose] def FRenL (R : Nat → Nat → Prop) : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => FRen R a b ∧ FRenL R as bs
  | _, _ => False

/-- Instantiation at related arguments gives related results. -/
theorem instPisWith_fren {R : Nat → Nat → Prop} :
    ∀ {as bs : List Expr} {e e' r : Expr}, FRenL R as bs → FRen R e e' →
      instPisWith as e = some r → ∃ r', instPisWith bs e' = some r' ∧ FRen R r r'
  | [], [], e, e', r, _, he, h => by
    simp only [instPisWith, Option.some.injEq] at h
    subst h
    exact ⟨e', rfl, he⟩
  | a :: as, b :: bs, e, e', r, ⟨hab, hrest⟩, he, h => by
    match e, e', he, h with
    | .forallE t₁ b₁ m₁, .forallE t₂ b₂ m₂, he, h =>
      obtain ⟨-, -, hb⟩ := he
      have h' : instPisWith as (b₁.instantiate1 a) = some r := h
      show ∃ r', instPisWith bs (b₂.instantiate1 b) = some r' ∧ _
      exact instPisWith_fren hrest (FRen.instantiate1 hb hab) h'
  | [], _ :: _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, h, _, _ => h.elim

/-- **Opening related telescopes** at two starts: the domains related
along `R` and the variables opened so far. -/
theorem openPisAtFvars_fren :
    ∀ (n : Nat) {R : Nat → Nat → Prop} {e e' : Expr} {d d' : Nat} {xs : List Expr} {r : Expr},
      FRen R e e' → openPisAtFvars n e d = some (xs, r) →
      ∃ xs' r', openPisAtFvars n e' d' = some (xs', r') ∧
        (∀ i x, xs[i]? = some x → ∃ x', xs'[i]? = some x' ∧
          FRen (fun a b => R a b ∨ ∃ l, l < i ∧ a = d + l ∧ b = d' + l)
            x.fvarTypeD x'.fvarTypeD) ∧
        FRen (fun a b => R a b ∨ ∃ l, l < n ∧ a = d + l ∧ b = d' + l) r r'
  | 0, R, e, e', d, d', xs, r, he, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], e', rfl, fun i x hx => by simp at hx, FRen.mono (fun a b h => Or.inl h) he⟩
  | n + 1, R, e, e', d, d', xs, r, he, h => by
    match e, e', he, h with
    | .forallE dom body mb, .forallE dom' body' mb', he, h =>
      obtain ⟨-, hdom, hbody⟩ := he
      simp only [openPisAtFvars] at h
      split at h
      · next fvs r₀ hop =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb : FRen (fun a b => R a b ∨ (a = d ∧ b = d'))
            (body.instantiate1 (.fvar d dom)) (body'.instantiate1 (.fvar d' dom')) :=
          FRen.instantiate1 (FRen.mono (fun a b h => Or.inl h) hbody) (Or.inr ⟨rfl, rfl⟩)
        obtain ⟨xs', r', hop', hxs, hr⟩ := openPisAtFvars_fren n hb hop (d' := d' + 1)
        refine ⟨.fvar d' dom' :: xs', r', ?_, ?_, ?_⟩
        · simp only [openPisAtFvars, hop']
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            subst hx
            exact ⟨_, rfl, FRen.mono (fun a b h => Or.inl h) hdom⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨x', hx', hrel⟩ := hxs i x hx
            refine ⟨x', by simpa using hx', FRen.mono ?_ hrel⟩
            rintro a b (( h | ⟨rfl, rfl⟩) | ⟨l, hl, rfl, rfl⟩)
            · exact Or.inl h
            · exact Or.inr ⟨0, by omega, by omega, by omega⟩
            · exact Or.inr ⟨l + 1, by omega, by omega, by omega⟩
        · refine FRen.mono ?_ hr
          rintro a b (( h | ⟨rfl, rfl⟩) | ⟨l, hl, rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨0, by omega, by omega, by omega⟩
          · exact Or.inr ⟨l + 1, by omega, by omega, by omega⟩
      · exact nomatch h

/-! ## The shift and the two member abstractions -/

theorem fren_shiftFrom (p : Nat) :
    ∀ (e : Expr), FRen (fun i j => j = if i < p then i else i + 1) e (Expr.shiftFrom p e) := by
  intro e
  induction e with
  | bvar i => exact rfl
  | fvar i ty =>
    simp only [Expr.shiftFrom]
    by_cases h : i ≥ p
    · rw [if_pos h]; show _ = _; rw [if_neg (by omega)]
    · rw [if_neg h]; show _ = _; rw [if_pos (by omega)]
  | sort u => exact rfl
  | const n us => exact ⟨rfl, rfl⟩
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | lam ty body m ih1 ih2 => exact ⟨rfl, ih1, ih2⟩
  | forallE ty body m ih1 ih2 => exact ⟨rfl, ih1, ih2⟩
  | letE ty v body ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | lit l => exact rfl
  | proj s i e ih => exact ⟨rfl, rfl, ih⟩

theorem fren_shiftFromN (p : Nat) :
    ∀ (n : Nat) (e : Expr),
      FRen (fun i j => j = if i < p then i else i + n) e (Expr.shiftFromN p n e)
  | 0, e => FRen.mono (fun i j h => by simp [h]) (FRen.rfl_eq e)
  | n + 1, e => by
    show FRen _ e (Expr.shiftFrom p (Expr.shiftFromN p n e))
    refine FRen.mono ?_ (FRen.trans (fren_shiftFromN p n e) (fren_shiftFrom p _))
    rintro i k ⟨j, rfl, rfl⟩
    by_cases h : i < p
    · simp [h]
    · simp only [h, if_false]; rw [if_neg (by omega)]; omega

/-- **The two member abstractions keep a relation**, the holes facing
each other along `R'`: the walk's (`nestAbstract`, over `replaceConsts`)
and the target check's (`targetAbs`). -/
theorem fren_abs {R R' : Nat → Nat → Prop} (ctx : NestCtx) (holes : List Expr)
    (names : List Name) (lvls : List Level) (holesK : List Expr)
    (hnames : ctx.names = names) (hlps : ctx.lps.map Level.param = lvls)
    (hhole : ∀ t, t < names.length → ∃ i j ty ty', holes[t]? = some (.fvar i ty) ∧
      holesK[t]? = some (.fvar j ty') ∧ R' i j)
    (hRR : ∀ i j, R i j → R' i j) :
    ∀ {a b : Expr}, FRen R a b →
      FRen R' (nestAbstract ctx holes a) (ConLeche.targetAbs names lvls holesK b) := by
  intro a
  induction a with
  | bvar i => intro b h; match b, h with | .bvar _, h => exact h
  | fvar i ty => intro b h; match b, h with | .fvar _ _, h => exact hRR _ _ h
  | sort u => intro b h; match b, h with | .sort _, h => exact h
  | const n us =>
    intro b h
    match b, h with
    | .const n' us', h =>
      obtain ⟨rfl, rfl⟩ := h
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs, hnames, hlps]
      by_cases hus : (us == lvls) = true
      · rw [if_pos hus, if_pos hus]
        cases hf : names.findIdx? (· == n) with
        | none => exact ⟨rfl, rfl⟩
        | some t =>
          have ht : t < names.length := by
            obtain ⟨h1, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            exact h1
          obtain ⟨i, j, ty, ty', h1, h2, h3⟩ := hhole t ht
          simp only [h1, Option.getD_some, List.getD_eq_getElem?_getD, h2]
          exact h3
      · rw [if_neg hus, if_neg hus]; exact ⟨rfl, rfl⟩
  | app f a ihf iha =>
    intro b h
    match b, h with
    | .app _ _, h =>
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs] at ihf iha ⊢
      exact ⟨ihf h.1, iha h.2⟩
  | lam ty body m ih1 ih2 =>
    intro b h
    match b, h with
    | .lam _ _ _, h =>
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs] at ih1 ih2 ⊢
      exact ⟨h.1, ih1 h.2.1, ih2 h.2.2⟩
  | forallE ty body m ih1 ih2 =>
    intro b h
    match b, h with
    | .forallE _ _ _, h =>
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs] at ih1 ih2 ⊢
      exact ⟨h.1, ih1 h.2.1, ih2 h.2.2⟩
  | letE ty v body ih1 ih2 ih3 =>
    intro b h
    match b, h with
    | .letE _ _ _, h =>
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs] at ih1 ih2 ih3 ⊢
      exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | lit l => intro b h; match b, h with | .lit _, h => exact h
  | proj s i e ih =>
    intro b h
    match b, h with
    | .proj _ _ _, h =>
      simp only [nestAbstract, Expr.replaceConsts, ConLeche.targetAbs] at ih ⊢
      exact ⟨h.1, h.2.1, ih h.2.2⟩

/-! ## The reading is blind to a renaming -/

section Read

variable {V : Type w} [SetTheory V]

theorem interp_natLitAV_indep {za sa : AnnotTerm}
    (hz : ∀ ρ ρ' : Nat → V, interp V ρ za = interp V ρ' za)
    (hs : ∀ ρ ρ' : Nat → V, interp V ρ sa = interp V ρ' sa) :
    ∀ (n : Nat) (ρ ρ' : Nat → V), interp V ρ (natLitAV za sa n) = interp V ρ' (natLitAV za sa n)
  | 0, ρ, ρ' => hz ρ ρ'
  | n + 1, ρ, ρ' => by
    simp only [natLitAV, interp_app]
    rw [hs ρ ρ', interp_natLitAV_indep hz hs n ρ ρ']

theorem interp_charListAV_indep {nilA consA ofNatA za sa : AnnotTerm}
    (hn : ∀ ρ ρ' : Nat → V, interp V ρ nilA = interp V ρ' nilA)
    (hc : ∀ ρ ρ' : Nat → V, interp V ρ consA = interp V ρ' consA)
    (ho : ∀ ρ ρ' : Nat → V, interp V ρ ofNatA = interp V ρ' ofNatA)
    (hz : ∀ ρ ρ' : Nat → V, interp V ρ za = interp V ρ' za)
    (hs : ∀ ρ ρ' : Nat → V, interp V ρ sa = interp V ρ' sa) :
    ∀ (cs : List Char) (ρ ρ' : Nat → V),
      interp V ρ (charListAV nilA consA ofNatA za sa cs)
        = interp V ρ' (charListAV nilA consA ofNatA za sa cs)
  | [], ρ, ρ' => hn ρ ρ'
  | c :: cs, ρ, ρ' => by
    simp only [charListAV, interp_app]
    rw [hc ρ ρ', ho ρ ρ', interp_natLitAV_indep hz hs _ ρ ρ',
      interp_charListAV_indep hn hc ho hz hs cs ρ ρ']

theorem interp_projAV_congr {σ σ' : Nat → V} :
    ∀ (i : Nat) {a b : AnnotTerm}, interp V σ a = interp V σ' b →
      interp V σ (projAV i a) = interp V σ' (projAV i b)
  | 0, a, b, h => by simp only [projAV, interp_fst, h]
  | i + 1, a, b, h => interp_projAV_congr i (a := .snd a) (b := .snd b) (by simp [h])

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

/-- A constant's or a literal's reading does not read the valuation. -/
theorem interp_denoteMeta_leaf_indep
    (hcl : ∀ (n : Name) (ψ : Name → Nat) (ρ ρ' : Nat → V),
      interp V ρ (acval n ψ) = interp V ρ' (acval n ψ))
    {e : Expr} (he : (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l)) {d : Nat} {A : AnnotTerm}
    (h : denoteMeta acval env φ d e = some A) (σ σ' : Nat → V) :
    interp V σ A = interp V σ' A := by
  rcases he with ⟨n, us, rfl⟩ | ⟨l, rfl⟩
  · rw [denoteMeta] at h
    split at h
    · split at h
      · obtain rfl := Option.some.inj h; exact hcl _ _ σ σ'
      · exact nomatch h
    · exact nomatch h
  · cases l with
    | natVal n =>
      rw [denoteMeta] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact interp_natLitAV_indep (hcl _ _) (hcl _ _) n σ σ'
      · exact nomatch h
    | strVal s =>
      rw [denoteMeta] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only [interp_app]
        rw [hcl _ _ σ σ']
        congr 1
        refine interp_charListAV_indep ?_ ?_ (hcl _ _) (hcl _ _) (hcl _ _) _ σ σ'
        · intro ρ ρ'; simp only [interp_app]; rw [hcl _ _ ρ ρ', hcl _ _ ρ ρ']
        · intro ρ ρ'; simp only [interp_app]; rw [hcl _ _ ρ ρ', hcl _ _ ρ ρ']
      · exact nomatch h

/-- The leaf reading does not read the depth. -/
theorem denoteMeta_leaf_depth {e : Expr} (he : (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (d d' : Nat) : denoteMeta acval env φ d e = denoteMeta acval env φ d' e := by
  rcases he with ⟨n, us, rfl⟩ | ⟨l, rfl⟩
  · rw [denoteMeta, denoteMeta]
  · cases l <;> rw [denoteMeta, denoteMeta]

/-- **THE READING IS BLIND TO A RENAMING**: related terms, read at two
depths, have one value at valuations agreeing along the relation. -/
theorem denoteMeta_fren_interp
    (hcl : ∀ (n : Name) (ψ : Name → Nat) (ρ ρ' : Nat → V),
      interp V ρ (acval n ψ) = interp V ρ' (acval n ψ)) :
    ∀ {e₁ e₂ : Expr} {R : Nat → Nat → Prop}, FRen R e₁ e₂ →
      ∀ (d d' : Nat) (σ σ' : Nat → V),
        (∀ i j, R i j → i < d ∧ j < d' ∧ σ (d - 1 - i) = σ' (d' - 1 - j)) →
        ∀ {A₁ A₂ : AnnotTerm}, denoteMeta acval env φ d e₁ = some A₁ →
          denoteMeta acval env φ d' e₂ = some A₂ → interp V σ A₁ = interp V σ' A₂
  | .bvar i, e₂, R, he, d, d', σ, σ', _, A₁, A₂, h₁, _ => by
    rw [denoteMeta.eq_def] at h₁; exact nomatch h₁
  | .fvar i ty, e₂, R, he, d, d', σ, σ', hR, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .fvar j ty', he =>
      rw [denoteMeta_fvar] at h₁ h₂
      obtain rfl := Option.some.inj h₁
      obtain rfl := Option.some.inj h₂
      exact (hR i j he).2.2
  | .sort u, e₂, R, he, d, d', σ, σ', _, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .sort u', he =>
      obtain rfl : u = u' := he
      rw [denoteMeta_sort] at h₁ h₂
      rw [← Option.some.inj h₁, ← Option.some.inj h₂]; rfl
  | .const n us, e₂, R, he, d, d', σ, σ', _, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rw [denoteMeta_leaf_depth (Or.inl ⟨n, us, rfl⟩) d' d, h₁] at h₂
      obtain rfl := Option.some.inj h₂
      exact interp_denoteMeta_leaf_indep hcl (Or.inl ⟨n, us, rfl⟩) h₁ σ σ'
  | .lit l, e₂, R, he, d, d', σ, σ', _, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .lit l', he =>
      obtain rfl : l = l' := he
      rw [denoteMeta_leaf_depth (Or.inr ⟨l, rfl⟩) d' d, h₁] at h₂
      obtain rfl := Option.some.inj h₂
      exact interp_denoteMeta_leaf_indep hcl (Or.inr ⟨l, rfl⟩) h₁ σ σ'
  | .app f a, e₂, R, he, d, d', σ, σ', hR, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : FRen R f g ∧ FRen R a b := he
      rw [denoteMeta_app] at h₁ h₂
      cases hf : denoteMeta acval env φ d f with
      | none => rw [hf] at h₁; exact nomatch h₁
      | some fa =>
      cases ha : denoteMeta acval env φ d a with
      | none => rw [hf, ha] at h₁; exact nomatch h₁
      | some aa =>
      cases hg : denoteMeta acval env φ d' g with
      | none => rw [hg] at h₂; exact nomatch h₂
      | some ga =>
      cases hb : denoteMeta acval env φ d' b with
      | none => rw [hg, hb] at h₂; exact nomatch h₂
      | some ba =>
      rw [hf, ha] at h₁; rw [hg, hb] at h₂
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h₁ h₂
      subst h₁; subst h₂
      simp only [interp_app]
      rw [denoteMeta_fren_interp hcl h1 d d' σ σ' hR hf hg,
        denoteMeta_fren_interp hcl h2 d d' σ σ' hR ha hb]
  | .forallE ty body m, e₂, R, he, d, d', σ, σ', hR, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .forallE ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ : m = m' ∧ FRen R ty ty' ∧ FRen R body body' := he
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h₁
      obtain ⟨ta', ba', hta', hba', rfl⟩ := denoteMeta_forallE_inv h₂
      have hb : FRen (fun a b => R a b ∨ (a = d ∧ b = d'))
          (body.instantiate1 (.fvar d ty)) (body'.instantiate1 (.fvar d' ty')) :=
        FRen.instantiate1 (FRen.mono (fun a b h => Or.inl h) h2) (Or.inr ⟨rfl, rfl⟩)
      simp only [interp_pi]
      rw [denoteMeta_fren_interp hcl h1 d d' σ σ' hR hta hta']
      congr 1
      funext x
      refine denoteMeta_fren_interp hcl hb (d + 1) (d' + 1) (cons x σ) (cons x σ') ?_ hba hba'
      rintro i j (hij | ⟨rfl, rfl⟩)
      · obtain ⟨hi, hj, hv⟩ := hR i j hij
        refine ⟨by omega, by omega, ?_⟩
        rw [show d + 1 - 1 - i = (d - 1 - i) + 1 by omega,
          show d' + 1 - 1 - j = (d' - 1 - j) + 1 by omega]
        exact hv
      · exact ⟨by omega, by omega, by simp⟩
  | .lam ty body m, e₂, R, he, d, d', σ, σ', hR, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .lam ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ : m = m' ∧ FRen R ty ty' ∧ FRen R body body' := he
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h₁
      obtain ⟨ta', ba', hta', hba', rfl⟩ := denoteMeta_lam_inv h₂
      have hb : FRen (fun a b => R a b ∨ (a = d ∧ b = d'))
          (body.instantiate1 (.fvar d ty)) (body'.instantiate1 (.fvar d' ty')) :=
        FRen.instantiate1 (FRen.mono (fun a b h => Or.inl h) h2) (Or.inr ⟨rfl, rfl⟩)
      simp only [interp_lam]
      rw [denoteMeta_fren_interp hcl h1 d d' σ σ' hR hta hta']
      congr 1
      funext x
      refine denoteMeta_fren_interp hcl hb (d + 1) (d' + 1) (cons x σ) (cons x σ') ?_ hba hba'
      rintro i j (hij | ⟨rfl, rfl⟩)
      · obtain ⟨hi, hj, hv⟩ := hR i j hij
        refine ⟨by omega, by omega, ?_⟩
        rw [show d + 1 - 1 - i = (d - 1 - i) + 1 by omega,
          show d' + 1 - 1 - j = (d' - 1 - j) + 1 by omega]
        exact hv
      · exact ⟨by omega, by omega, by simp⟩
  | .letE ty vl body, e₂, R, he, d, d', σ, σ', _, A₁, A₂, h₁, _ => by
    rw [denoteMeta] at h₁; exact nomatch h₁
  | .proj sn i pe, e₂, R, he, d, d', σ, σ', hR, A₁, A₂, h₁, h₂ => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ : sn = sn' ∧ i = i' ∧ FRen R pe pe' := he
      obtain ⟨ia, hia, hc⟩ := denoteMeta_proj_inv h₁
      obtain ⟨ia', hia', hc'⟩ := denoteMeta_proj_inv h₂
      have hIH := denoteMeta_fren_interp hcl h d d' σ σ' hR hia hia'
      rcases hc with ⟨entry, hfp, rfl⟩ | ⟨hfp, hdec⟩
      · rcases hc' with ⟨entry', hfp', rfl⟩ | ⟨hfp', -⟩
        · rw [hfp] at hfp'
          obtain rfl := Option.some.inj hfp'
          exact interp_projAV_congr _ hIH
        · rw [hfp] at hfp'; exact nomatch hfp'
      · rcases hc' with ⟨entry', hfp', -⟩ | ⟨-, hdec'⟩
        · rw [hfp] at hfp'; exact nomatch hfp'
        · rcases i with _ | _ | i
          · simp only [AnnotTerm.projPair?, Option.some.injEq] at hdec hdec'
            subst hdec; subst hdec'
            simp [hIH]
          · simp only [AnnotTerm.projPair?, Option.some.injEq] at hdec hdec'
            subst hdec; subst hdec'
            simp [hIH]
          · exact nomatch hdec
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Read

end ConLeche.Model
