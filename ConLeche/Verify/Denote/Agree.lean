module

public import ConLeche.Verify.Denote.EnvExtend
public import ConLeche.Modular

public section

/-!
# `denote` at two environments that read an expression alike

The modular theorem (`ConLeche/Modular.lean`) reads a context constant's
laws off the import it comes from: the context and the import are two
environments, with two leaf valuations, that agree on the names the
constant's data mention.  `denote_agree` is the reading's half of that:
an expression whose constants (and literal and projection names) are
stored in both, with the same level parameters and leaves, reads alike
at both — `denote` consults the environment only through `find?`'s level
parameters, the projection tables and the two literal guards.
-/

namespace ConLeche.Verify

open ConLeche.Term

open ConLeche (Env Expr Name Level natLitSupported strLitSupported natName natZeroName
  natSuccName stringName stringOfListName listName listNilName listConsName charName
  charOfNatName)

/-- The names a `Nat` literal reads. -/
@[expose] def natLitNames : List Name := [natName, natZeroName, natSuccName]

/-- The names a `String` literal reads. -/
@[expose] def strLitNames : List Name :=
  [natName, natZeroName, natSuccName, stringName, stringOfListName, listName, listNilName,
    listConsName, charName, charOfNatName]

/-- **Two environments read alike at the names of `R`**: a name stored in
`R` and in `E` is stored in `C` and `E` with the same constant value and
the same leaf, and its projection entries are the same; and the literal
guards agree wherever their names are. -/
structure ReadAgree (R C E : Env) (aC aE : Name → (Name → Nat) → Term) : Prop where
  find : ∀ d, (R.find? d).isSome = true → (E.find? d).isSome = true →
    ∃ ciC ciE, C.find? d = some ciC ∧ E.find? d = some ciE ∧
      ciC.toConstantVal = ciE.toConstantVal ∧ aC d = aE d
  proj : ∀ T i, (R.find? T).isSome = true → (E.find? T).isSome = true →
    (∃ cv caps, C.find? T = some (.indInfo cv caps)) → C.findProj? T i = E.findProj? T i
  nat : (∀ n ∈ natLitNames, (R.find? n).isSome = true ∧ (E.find? n).isSome = true) →
    natLitSupported C = natLitSupported E
  str : (∀ n ∈ strLitNames, (R.find? n).isSome = true ∧ (E.find? n).isSome = true) →
    strLitSupported C = strLitSupported E

theorem ReadAgree.levelParamsAt {R C E : Env} {aC aE : Name → (Name → Nat) → Term}
    (h : ReadAgree R C E aC aE) {n : Name} (hR : (R.find? n).isSome = true)
    (hE : (E.find? n).isSome = true) :
    levelParamsAt C n = levelParamsAt E n := by
  obtain ⟨ciC, ciE, hC, hE', hcv, -⟩ := h.find n hR hE
  rw [ConLeche.Verify.levelParamsAt, ConLeche.Verify.levelParamsAt, hC, hE']
  dsimp only
  rw [hcv]

/-- Binder opening keeps the projections' formers. -/
theorem Expr.projsFormer_instantiate1 {C : Env} {d : Nat} {ty : Expr}
    (hty : ConLeche.Modular.Expr.projsFormer C ty = true) :
    ∀ {e : Expr} (k : Nat), ConLeche.Modular.Expr.projsFormer C e = true →
      ConLeche.Modular.Expr.projsFormer C (e.instantiate1 (.fvar d ty) k) = true := by
  intro e
  induction e <;> intro k h <;>
    simp_all [ConLeche.Expr.instantiate1, ConLeche.Modular.Expr.projsFormer]
  case bvar i =>
    split
    · simpa [ConLeche.Modular.Expr.projsFormer] using hty
    · split <;> simp [ConLeche.Modular.Expr.projsFormer]

/-- **An expression read alike at two environments**: its constants
stored in `R` (the part of `C` read as `E` reads it) and in `E`, its
projections of type formers of `C`. -/
theorem denote_agree {R C E : Env} {aC aE : Name → (Name → Nat) → Term} {φ : Name → Nat}
    (h : ReadAgree R C E aC aE) :
    ∀ (d : Nat) (e : Expr), e.constsResolve R = true → e.constsResolve E = true →
      ConLeche.Modular.Expr.projsFormer C e = true →
      denote aC C φ d e = denote aE E φ d e := by
  intro d e
  induction d, e using denote.induct (env := E) with
  | case1 d u => intro _ _ _; rw [denote, denote]
  | case2 d idx ty => intro _ _ _; rw [denote, denote]
  | case3 d n us ci hf hlen =>
    intro hR hE _
    simp only [Expr.constsResolve] at hR hE
    obtain ⟨ciC, ciE, hC, hE', hcv, hl⟩ := h.find n hR hE
    rw [hf] at hE'; obtain rfl := Option.some.inj hE'
    rw [denote, hC, denote, hf]
    simp only [hcv, hl]
  | case4 d n us ci hf hlen =>
    intro hR hE _
    simp only [Expr.constsResolve] at hR hE
    obtain ⟨ciC, ciE, hC, hE', hcv, hl⟩ := h.find n hR hE
    rw [hf] at hE'; obtain rfl := Option.some.inj hE'
    rw [denote, hC, denote, hf]
    simp only [hcv, hl]
  | case5 d n us hf =>
    intro _ hE _
    simp only [Expr.constsResolve, hf] at hE
    exact nomatch hE
  | case6 d ty body ihty ihbody =>
    intro hR hE hP
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    simp only [ConLeche.Modular.Expr.projsFormer, Bool.and_eq_true] at hP
    rw [denote, denote, ihty hR.1 hE.1 hP.1,
      ihbody (Expr.constsResolve_instantiate1 hR.1 0 hR.2)
        (Expr.constsResolve_instantiate1 hE.1 0 hE.2) (Expr.projsFormer_instantiate1 hP.1 0 hP.2)]
  | case7 d ty body ihty ihbody =>
    intro hR hE hP
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    simp only [ConLeche.Modular.Expr.projsFormer, Bool.and_eq_true] at hP
    rw [denote, denote, ihty hR.1 hE.1 hP.1,
      ihbody (Expr.constsResolve_instantiate1 hR.1 0 hR.2)
        (Expr.constsResolve_instantiate1 hE.1 0 hE.2) (Expr.projsFormer_instantiate1 hP.1 0 hP.2)]
  | case8 d f a ihf iha =>
    intro hR hE hP
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    simp only [ConLeche.Modular.Expr.projsFormer, Bool.and_eq_true] at hP
    rw [denote, denote, ihf hR.1 hE.1 hP.1, iha hR.2 hE.2 hP.2]
  | case9 d ty val body ihty ihv ihbody =>
    intro hR hE hP
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    simp only [ConLeche.Modular.Expr.projsFormer, Bool.and_eq_true] at hP
    rw [denote, denote, ihty hR.1.1 hE.1.1 hP.1.1, ihv hR.1.2 hE.1.2 hP.1.2,
      ihbody (Expr.constsResolve_instantiate1 hR.1.1 0 hR.2)
        (Expr.constsResolve_instantiate1 hE.1.1 0 hE.2)
        (Expr.projsFormer_instantiate1 hP.1.1 0 hP.2)]
  | case10 d sn i e ihe =>
    intro hR hE hP
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    simp only [ConLeche.Modular.Expr.projsFormer, Bool.and_eq_true] at hP
    have hT : ∃ cv caps, C.find? sn = some (.indInfo cv caps) := by
      obtain ⟨hP1, -⟩ := hP
      revert hP1
      cases hc : C.find? sn with
      | none => intro h; simp at h
      | some ci => cases ci <;> intro h <;> first | (simp at h; done) | exact ⟨_, _, rfl⟩
    rw [denote, denote, ihe hR.2 hE.2 hP.2, h.proj sn i hR.1 hE.1 hT]
  | case11 d n hsup =>
    intro hR hE _
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    have hg := h.nat (by
      intro m hm
      simp only [natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨hR.1.1, hE.1.1⟩
      · exact ⟨hR.1.2, hE.1.2⟩
      · exact ⟨hR.2, hE.2⟩)
    rw [denote, ite_eq_left (hg ▸ hsup), denote, ite_eq_left hsup]
    obtain ⟨-, -, -, -, -, hz⟩ := h.find natZeroName hR.1.2 hE.1.2
    obtain ⟨-, -, -, -, -, hs⟩ := h.find natSuccName hR.2 hE.2
    rw [hz, hs]
  | case12 d n hsup =>
    intro hR hE _
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    have hg := h.nat (by
      intro m hm
      simp only [natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨hR.1.1, hE.1.1⟩
      · exact ⟨hR.1.2, hE.1.2⟩
      · exact ⟨hR.2, hE.2⟩)
    rw [denote, ite_eq_right (fun h' => hsup (hg ▸ h')), denote, ite_eq_right hsup]
  | case13 d s hsup =>
    intro hR hE _
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩, r10⟩ := hR
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩ := hE
    have hg := h.str (by
      intro m hm
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨r1, e1⟩
      · exact ⟨r2, e2⟩
      · exact ⟨r3, e3⟩
      · exact ⟨r4, e4⟩
      · exact ⟨r5, e5⟩
      · exact ⟨r6, e6⟩
      · exact ⟨r7, e7⟩
      · exact ⟨r8, e8⟩
      · exact ⟨r9, e9⟩
      · exact ⟨r10, e10⟩)
    rw [denote, ite_eq_left (hg ▸ hsup), denote, ite_eq_left hsup,
      h.levelParamsAt r7 e7, h.levelParamsAt r8 e8]
    obtain ⟨-, -, -, -, -, h2⟩ := h.find natZeroName r2 e2
    obtain ⟨-, -, -, -, -, h3⟩ := h.find natSuccName r3 e3
    obtain ⟨-, -, -, -, -, h5⟩ := h.find stringOfListName r5 e5
    obtain ⟨-, -, -, -, -, h7⟩ := h.find listNilName r7 e7
    obtain ⟨-, -, -, -, -, h8⟩ := h.find listConsName r8 e8
    obtain ⟨-, -, -, -, -, h9⟩ := h.find charName r9 e9
    obtain ⟨-, -, -, -, -, h10⟩ := h.find charOfNatName r10 e10
    rw [h2, h3, h5, h7, h8, h9, h10]
  | case14 d s hsup =>
    intro hR hE _
    simp only [Expr.constsResolve, Bool.and_eq_true] at hR hE
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩, r10⟩ := hR
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩ := hE
    have hg := h.str (by
      intro m hm
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨r1, e1⟩
      · exact ⟨r2, e2⟩
      · exact ⟨r3, e3⟩
      · exact ⟨r4, e4⟩
      · exact ⟨r5, e5⟩
      · exact ⟨r6, e6⟩
      · exact ⟨r7, e7⟩
      · exact ⟨r8, e8⟩
      · exact ⟨r9, e9⟩
      · exact ⟨r10, e10⟩)
    rw [denote, ite_eq_right (fun h' => hsup (hg ▸ h')), denote, ite_eq_right hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ _ _
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Verify
