module

public import ConLeche.Modular

public section

/-!
# The local checks from the interface checks and the importer's checks

`ConLeche.Modular.LocalOk` (the hypothesis of the modular theorem) is
the derived notion: a module's interface checked once
(`InterfaceOk`, at every source) and the importer's own checks
(`ImportOk`) give it (`LocalOk.of_interface`).  What a context
constant's laws read is stored in its source's own environment because
the source's interface says so, and stored in the context under the
source's keys because the importer checks the presentation's footprint.
-/

namespace ConLeche.Modular

open ConLeche

/-- A resolution walk carries over to an environment storing more. -/
theorem constsResolve_mono {R R' : Env}
    (hsub : ∀ d, (R.find? d).isSome = true → (R'.find? d).isSome = true) :
    ∀ e : Expr, e.constsResolve R = true → e.constsResolve R' = true := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit l =>
    cases l with
    | natVal _ =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, hsub _ h.2⟩
    | strVal _ =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsub _ h1, hsub _ h2⟩, hsub _ h3⟩, hsub _ h4⟩, hsub _ h5⟩, hsub _ h6⟩,
        hsub _ h7⟩, hsub _ h8⟩, hsub _ h9⟩, hsub _ h10⟩
  | const n _ => intro h; exact hsub n h
  | fvar _ _ ih => intro h; exact ih h
  | app _ _ ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE _ _ iht ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ iht ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s _ _ ih =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hsub s h.1, ih h.2⟩

/-- **Scoping carries over** to an environment storing more, read with a
table lookup that agrees on a type former's table. -/
theorem EntryScoped.mono {R R' C C' : Env} {n : Name} {ci : ConstantInfo}
    (h : EntryScoped R C n ci)
    (hsub : ∀ d, (R.find? d).isSome = true → (R'.find? d).isSome = true)
    (ht : ∀ cv caps, ci = .indInfo cv caps → C'.findTable? n = C.findTable? n) :
    EntryScoped R' C' n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨constsResolve_mono hsub _ h1, fun cv v hh he => constsResolve_mono hsub _ (h2 cv v hh he),
    fun cv mI rP rules he r hr => ?_, fun cv caps he => ?_, fun d hd => hsub d (h5 d hd)⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP rules he r hr
    exact ⟨constsResolve_mono hsub _ a, hsub _ b, fun lvls pins hf p hp =>
      constsResolve_mono hsub _ (c lvls pins hf p hp)⟩
  · obtain ⟨a, b, c, d⟩ := h4 cv caps he
    refine ⟨fun m hm => hsub m (a m hm), fun x hx => hsub x (b x hx), fun he' => hsub _ (c he'),
      fun t htt => ?_⟩
    rw [ht cv caps he] at htt
    obtain ⟨d1, d2⟩ := d t htt
    exact ⟨hsub _ d1, fun b hb => constsResolve_mono hsub _ (d2 b hb)⟩

/-- A name the part of `E` a footprint names stores is stored in `E` and
named by the footprint. -/
theorem find?_readsIn {E : Env} {ns : List Name} {d : Name}
    (h : ((readsIn E ns).find? d).isSome = true) :
    (E.find? d).isSome = true ∧ d ∈ ns := by
  unfold readsIn Env.find? at h
  simp only at h
  rw [List.find?_isSome] at h
  obtain ⟨c, hc, hp⟩ := h
  rw [List.mem_filter] at hc
  have hd : c.name = d := beq_iff_eq.mp hp
  subst hd
  refine ⟨?_, List.contains_iff_mem.mp hc.2⟩
  unfold Env.find?
  rw [List.find?_isSome]
  exact ⟨c, hc.1, by simp⟩

/-- A name `E` stores that a footprint names is in the part of `E` it names. -/
theorem readsIn_isSome {E : Env} {ns : List Name} {d : Name}
    (hE : (E.find? d).isSome = true) (hd : d ∈ ns) : ((readsIn E ns).find? d).isSome = true := by
  unfold readsIn Env.find?
  simp only
  unfold Env.find? at hE
  rw [List.find?_isSome] at hE ⊢
  obtain ⟨c, hc, hcn⟩ := hE
  have hcn' : c.name = d := beq_iff_eq.mp hcn
  refine ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, hcn⟩
  rw [hcn']
  exact List.contains_iff_mem.mpr hd

/-- What module `i` reads alike from module `b` its context stores under
`b`'s keys. -/
theorem of_readsAlike {dev : Nat → Module} {i b : Nat} {d : Name}
    (h : ((readsAlike dev i b).find? d).isSome = true) :
    ((dev i).context.find? d).isSome = true ∧ (dev i).key d = (dev b).key d := by
  unfold readsAlike Env.find? at h
  simp only at h
  rw [List.find?_isSome] at h
  obtain ⟨c, hc, hcn⟩ := h
  rw [List.mem_filter] at hc
  have hd : c.name = d := beq_iff_eq.mp hcn
  subst hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.2

/-- A name module `i`'s context stores under module `b`'s key,
stored by `b`, is in what `i` reads alike from `b`. -/
theorem readsAlike_isSome {dev : Nat → Module} {i b : Nat} {d : Name}
    (hb : ((dev b).own.find? d).isSome = true) (hi : ((dev i).context.find? d).isSome = true)
    (hk : (dev i).key d = (dev b).key d) : ((readsAlike dev i b).find? d).isSome = true := by
  unfold readsAlike Env.find?
  simp only
  rw [List.find?_isSome]
  unfold Env.find? at hb
  rw [List.find?_isSome] at hb
  obtain ⟨c, hc, hcn⟩ := hb
  have hcn' : c.name = d := beq_iff_eq.mp hcn
  refine ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, hcn⟩
  rw [hcn', hk]
  simp only [beq_self_eq_true, Bool.and_true]
  exact hi

/-- **The local checks, derived**: the interfaces of a module's sources
checked once each, and the module's own checks as an importer. -/
theorem LocalOk.of_interface {mode : CheckMode} {pins : List NatOpPinSet} {dev : Nat → Module}
    {i : Nat} (hI : ∀ b < i, InterfaceOk dev b) (hM : ImportOk mode pins dev i) :
    LocalOk mode pins dev i := by
  have pres := hM.presented
  have src {n : Name} {ci : ConstantInfo} (hf : (dev i).context.find? n = some ci) :
      (dev i).src n < i := hM.src_lt n (by rw [hf]; rfl)
  refine { below := hM.below, src_lt := hM.src_lt, nodup := hM.nodup, accepted := hM.accepted,
           compared_own := hM.compared_own, context_le := ?_, scoping := ?_, tables := ?_,
           projs := hM.projs, blocks := hM.blocks, recFam := ?_, tables_mem := hM.tables_mem,
           key_context := hM.key_context, key_own := hM.key_own }
  · intro n ci hf
    obtain ⟨e, he, rfl, -, -⟩ := pres n ci hf
    exact (hI _ (src hf)).refines n e he
  · intro n ci hf
    obtain ⟨e, he, rfl, ht, hr⟩ := pres n ci hf
    have hIb := hI _ (src hf)
    refine (hIb.reads n e he).mono (fun d hd => ?_) (fun cv caps hce => ?_)
    · obtain ⟨hown, hdn⟩ := find?_readsIn hd
      obtain ⟨hc, hk⟩ := hr d hdn
      exact readsAlike_isSome hown hc hk
    · rw [ht, hce]; exact hIb.table n e he cv caps hce
  · intro T ci hf
    obtain ⟨e, he, rfl, ht, -⟩ := pres T ci hf
    rw [ht]
    cases hce : e.ci with
    | indInfo cv caps => exact (hI _ (src hf)).table T e he cv caps hce
    | _ => rfl
  · intro n cv mI rP rules hf r hr cvj nP nF hcj T us hT
    obtain ⟨e, he, hec, -, -⟩ := pres n _ hf
    exact (hI _ (src hf)).recFam n e he cv mI rP rules hec r hr cvj nP nF hcj T us hT

end ConLeche.Modular
