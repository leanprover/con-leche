module

public import ConLeche.Model.Inductives.ClassRestrict
public import ConLeche.Model.Inductives.ClassComplete
public import ConLeche.Model.Inductives.ClassRecIn
import ConLeche.Model.Inductives.HoleKit

public section

/-!
# Two restrictions read alike at a valuation coherent where they differ (P2d, DESIGN CLASSCHECK / P2D4)

A coherent class `d`, read by a container class `c`, is filled with its
container's carrier at `d`'s OWN frame — `d`'s key with `d`'s free
classes `Fd` abstracted — where `c`'s crest reads `d`'s key with `c`'s
stage classes `F` abstracted.  The two readings of a key parameter `p`
agree at a valuation `τ` when every class recognised inside `p` that
`Fd` abstracts and `F` does not holds, at `τ`, its `F`-key's value, and
`F` abstracts inside `p` only what `Fd` does (the demand)
(`restrict_read_eq`): complete `τ` coherently for `F` (`completeF`), read
P1 between the restrictions `F ⊆ F ∪ Fd` there (`classAbsF_read_restrict`),
note `F ∪ Fd` abstracts `p` as `Fd` does (`classAbsF_congr`), and move
both readings back to `τ` by congruence — each mentions only holes the
completion keeps or holes `τ` already holds coherently.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ClassInfo classOcc?)

universe w

/-- **The class abstraction mentions a variable only if its term does or
a hole recognised at one of its subterms is it.** -/
theorem nestOcc_classAbsSpec_sub (occ : Expr → Option (Expr × Nat)) {i : Nat} :
    ∀ (e : Expr) (m : Option (Expr × Nat)),
      (ConLeche.classAbsSpec occ m e).nestOcc [] i (i + 1) = true →
      e.nestOcc [] i (i + 1) = true ∨
        (∃ x h n, Expr.SubOf x e ∧ occ x = some (h, n) ∧ h.nestOcc [] i (i + 1) = true) ∨
        (∃ h n, m = some (h, n) ∧ h.nestOcc [] i (i + 1) = true) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro m hn
    have liftF : ∀ x, Expr.SubOf x f → Expr.SubOf x (.app f a) := fun x h => Or.inr (Or.inl h)
    have liftA : ∀ x, Expr.SubOf x a → Expr.SubOf x (.app f a) := fun x h => Or.inr (Or.inr h)
    rcases m with _ | ⟨h, _ | n⟩
    · unfold ConLeche.classAbsSpec at hn
      split at hn
      · rename_i h hx
        exact Or.inr (Or.inl ⟨_, h, 0, Expr.SubOf.refl _, hx, hn⟩)
      · rename_i h n hx
        simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rcases ihf _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl ⟨x, h', n', liftF x hs, hx', h2⟩)
          · cases he; exact Or.inr (Or.inl ⟨_, h, n + 1, Expr.SubOf.refl _, hx, h2⟩)
        · rcases iha _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl ⟨x, h', n', liftA x hs, hx', h2⟩)
          · cases he
      · simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rcases ihf _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl ⟨x, h', n', liftF x hs, hx', h2⟩)
          · cases he
        · rcases iha _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
          · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
          · exact Or.inr (Or.inl ⟨x, h', n', liftA x hs, hx', h2⟩)
          · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · rcases ihf _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', liftF x hs, hx', h2⟩)
        · cases he; exact Or.inr (Or.inr ⟨h, n + 1, rfl, h2⟩)
      · rcases iha _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', liftA x hs, hx', h2⟩)
        · cases he
  | lam t b bm iht ihb | forallE t b bm iht ihb =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · rcases iht _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', Or.inr (Or.inl hs), hx', h2⟩)
        · cases he
      · rcases ihb _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', Or.inr (Or.inr hs), hx', h2⟩)
        · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | letE t v b iht ihv ihb =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc, Bool.or_eq_true] at hn
      rcases hn with (hn | hn) | hn
      · rcases iht _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', Or.inr (Or.inl hs), hx', h2⟩)
        · cases he
      · rcases ihv _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', Or.inr (Or.inr (Or.inl hs)), hx', h2⟩)
        · cases he
      · rcases ihb _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
        · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
        · exact Or.inr (Or.inl ⟨x, h', n', Or.inr (Or.inr (Or.inr hs)), hx', h2⟩)
        · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | proj sn si y ihy =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · simp only [ConLeche.classAbsSpec, ConLeche.Expr.nestOcc] at hn
      rcases ihy _ hn with h1 | ⟨x, h', n', hs, hx', h2⟩ | ⟨h', n', he, h2⟩
      · exact Or.inl (by simp [ConLeche.Expr.nestOcc, h1])
      · exact Or.inr (Or.inl ⟨x, h', n', Or.inr hs, hx', h2⟩)
      · cases he
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl hn
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro m hn
    rcases m with _ | ⟨h, _ | n⟩
    · exact Or.inl (by simpa [ConLeche.classAbsSpec] using hn)
    · exact Or.inr (Or.inr ⟨h, 0, rfl, hn⟩)
    · exact Or.inl (by simpa [ConLeche.classAbsSpec] using hn)

/-- `classAbsF`'s mentioned variables: the term's, or a recognised hole
the restriction keeps. -/
theorem nestOcc_classAbsF {cls : List ClassInfo} {F : Expr → Bool} {p : Expr} {i : Nat}
    (h : (classAbsF cls F p).nestOcc [] i (i + 1) = true) :
    p.nestOcc [] i (i + 1) = true ∨
      ∃ x h n, Expr.SubOf x p ∧ classOcc? cls x = some (h, n) ∧ F h = true ∧
        h.nestOcc [] i (i + 1) = true := by
  unfold classAbsF at h
  rcases nestOcc_classAbsSpec_sub _ p none h with h1 | ⟨x, h', n, hs, hx, h2⟩ | ⟨_, _, he, _⟩
  · exact Or.inl h1
  · refine Or.inr ⟨x, h', n, hs, ?_⟩
    unfold occRestrict at hx
    cases hc : classOcc? cls x with
    | none => rw [hc] at hx; exact nomatch hx
    | some q =>
      obtain ⟨h'', n''⟩ := q
      rw [hc] at hx
      simp only at hx
      split at hx
      · rename_i hF
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨rfl, hF, h2⟩
      · exact nomatch hx
  · exact nomatch he

/-- A term below `d` mentions no variable at or above it. -/
theorem nestOcc_nil_lt_of_fvarsBelow {d i : Nat} :
    ∀ {e : Expr}, Expr.fvarsBelow d e → e.nestOcc [] i (i + 1) = true → i < d := by
  intro e
  induction e with
  | fvar j ty _ => intro h hn; simp [Expr.fvarsBelow, ConLeche.Expr.nestOcc] at h hn; omega
  | app f a ihf iha =>
    intro h hn; simp only [Expr.fvarsBelow, ConLeche.Expr.nestOcc, Bool.or_eq_true] at h hn
    rcases hn with hn | hn
    · exact ihf h.1 hn
    · exact iha h.2 hn
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    intro h hn; simp only [Expr.fvarsBelow, ConLeche.Expr.nestOcc, Bool.or_eq_true] at h hn
    rcases hn with hn | hn
    · exact iht h.1 hn
    · exact ihb h.2 hn
  | letE t v b iht ihv ihb =>
    intro h hn; simp only [Expr.fvarsBelow, ConLeche.Expr.nestOcc, Bool.or_eq_true] at h hn
    rcases hn with (hn | hn) | hn
    · exact iht h.1 hn
    · exact ihv h.2.1 hn
    · exact ihb h.2.2 hn
  | proj _ _ y ihy =>
    intro h hn; simp only [Expr.fvarsBelow, ConLeche.Expr.nestOcc] at h hn; exact ihy h hn
  | bvar _ | sort _ | const _ _ | lit _ => intro _ hn; simp [ConLeche.Expr.nestOcc] at hn

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 1600000 in
/-- **Two restrictions read a term alike at a valuation coherent where
they differ** (see the module docstring). -/
theorem restrict_read_eq (m : EnvModel V env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {cls : List ClassInfo} {H lo : Nat} (hwf : ClassOccWF cls H) (hu : HoleIdxUniq cls)
    (hhole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ lo ≤ i ∧ i < H)
    {F Fd : Expr → Bool} (hFc : FClosed cls F) (hFdc : FClosed cls Fd)
    (hkf : KeysFOk m.acval env φ cls F H)
    (hkeyF : ∀ c ∈ cls, c.hole.isSome → F (c.hole.getD default) = false → ∀ i,
      (classKeyF cls F c).nestOcc [] i (i + 1) = true →
      i < lo ∨ ∃ c' ∈ cls, ∃ ty, c'.hole = some (.fvar i ty) ∧ F (.fvar i ty) = true)
    {p : Expr} (hp : Expr.fvarsBelow lo p)
    (hdem : ∀ h, RecIn (classOcc? cls) p h → F h = true → Fd h = true)
    {τ : Nat → V} (hsame : SameF V cls F H τ)
    (hcoh : ∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → RecIn (classOcc? cls) p (.fvar i ty) →
      Fd (.fvar i ty) = true → F (.fvar i ty) = false → ∀ a,
      denoteMeta m.acval env φ H (classKeyF cls F c) = some a → τ (H - 1 - i) = interp V τ a)
    {aF aFd : AnnotTerm} (hsF : Expr.fvarsBelow H (classAbsF cls F p))
    (hsFd : Expr.fvarsBelow H (classAbsF cls Fd p))
    (haF : denoteMeta m.acval env φ H (classAbsF cls F p) = some aF)
    (haFd : denoteMeta m.acval env φ H (classAbsF cls Fd p) = some aFd) :
    interp V τ aFd = interp V τ aF := by
  classical
  let F1 : Expr → Bool := fun h => F h || Fd h
  have hF1c : FClosed cls F1 := by
    intro c hc c' hc' h h' hch hch' hs
    simp only [F1, hFc c hc c' hc' h h' hch hch' hs, hFdc c hc c' hc' h h' hch hch' hs]
  have hcohF : StageCohF V m.acval env φ cls F H (completeF V m.acval env φ cls F H τ) :=
    stageCohF_completeF m hu hhole hkf hFc hkeyF hsame
  have hcohR : StageCohFR V m.acval env φ cls F1 F H (completeF V m.acval env φ cls F H τ) :=
    ⟨fun c hc i ty hch _ hF a ha => hcohF.1 c hc i ty hch hF a ha, hcohF.2⟩
  -- P1 between the restrictions at the completion
  have hag := classAbsF_read_restrict (V := V) (env := env) (φ := φ) hacl hwf hkf hFc hF1c
    (fun h hh => by simp [F1, hh]) p (LocList.nil H) (LocList.nil H)
  have hcong : classAbsF cls F1 p = classAbsF cls Fd p := classAbsF_congr fun h hr => by
    cases hFh : F h
    · simp [F1, hFh]
    · simp [F1, hFh, hdem h hr hFh]
  rw [hcong] at hag
  simp only [Expr.instantiateList_nil, Nat.add_zero] at hag
  rw [haFd, haF] at hag
  have h1 : interp V (completeF V m.acval env φ cls F H τ) aFd
      = interp V (completeF V m.acval env φ cls F H τ) aF := by
    simpa [consList_nil] using hag [] _ rfl hcohR
  -- the completion keeps what the two readings mention
  have hbig : ∀ j, H ≤ j → τ j = completeF V m.acval env φ cls F H τ j := fun j hj =>
    (completeF_keep fun _ _ _ _ _ hi hpe => by omega).symm
  have hkeepF : interp V τ aF = interp V (completeF V m.acval env φ cls F H τ) aF := by
    refine interp_congr_unmentioned m hsF haF (fun i _ hocc => ?_) hbig
    rcases nestOcc_classAbsF hocc with hpi | ⟨x, h, n, -, hx, hFh, hhn⟩
    · exact (completeF_keep_of hu hhole (Or.inl (nestOcc_nil_lt_of_fvarsBelow hp hpi))).symm
    · obtain ⟨c', hc', hch, -⟩ := classOcc_spec hwf hx
      obtain ⟨j, ty, rfl, -, -⟩ := hhole c' hc' _ hch
      have hj : j = i := by simp [ConLeche.Expr.nestOcc] at hhn; omega
      subst hj
      exact (completeF_keep_of hu hhole (Or.inr ⟨c', hc', ty, hch, hFh⟩)).symm
  have hkeepFd : interp V τ aFd = interp V (completeF V m.acval env φ cls F H τ) aFd := by
    refine interp_congr_unmentioned m hsFd haFd (fun i _ hocc => ?_) hbig
    rcases nestOcc_classAbsF hocc with hpi | ⟨x, h, n, hsub, hx, hFdh, hhn⟩
    · exact (completeF_keep_of hu hhole (Or.inl (nestOcc_nil_lt_of_fvarsBelow hp hpi))).symm
    · obtain ⟨c', hc', hch, -⟩ := classOcc_spec hwf hx
      obtain ⟨j, ty, rfl, -, hjH⟩ := hhole c' hc' _ hch
      have hj : j = i := by simp [ConLeche.Expr.nestOcc] at hhn; omega
      subst hj
      cases hFh : F (.fvar j ty) with
      | true => exact (completeF_keep_of hu hhole (Or.inr ⟨c', hc', ty, hch, hFh⟩)).symm
      | false =>
        have hchs : c'.hole.isSome := by rw [hch]; rfl
        have hF' : F (c'.hole.getD default) = false := by rw [hch]; exact hFh
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hkf c' hc' hchs hF').2.2
        rw [hcoh c' hc' j ty hch ⟨x, n, hsub, hx⟩ hFdh hFh a ha]
        exact (completeF_eq_of hu ⟨c', hc', j, ty, a, hch, hjH, rfl, hFh, ha, rfl⟩).symm
  rw [hkeepFd, h1, ← hkeepF]

end ConLeche.Model
