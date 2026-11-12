module

public import ConLeche.Verify.Ground.Compile

public section

/-!
# Two programs, one layout (task #423 soundness, layer (d), item 2(c), first part)

The step simulation relates a run on one program (`PA`, lookups `f₁`/`p₁`)
to a run on another (`PB`, `f₂`/`p₂`): the kept program against a fresh one,
or a program of an environment against one of its extension.  The two
number their nodes, entries, name ids, strings, projection rows and slots
differently; a number of one is related to a number of the other when both
have one key (DESIGN #423 §S.18): two nodes when they are the compile of one
term (`NRel`, `ARel` for argument positions), two entries when they have one
constant and levels (`EntRel`).

This file proves that related nodes have one layout, word for word, up to
the relations on the words: the tag, a variable's index, a λ telescope's
length, its body and its innermost body, the nodes below a `let`, a
projection or a spine, a spine's argument nodes under the head's mask, a
shared argument's slot owner.  Where the layout depends on the lookups (a
spine head's erasure mask, a projection's table row) the lemma asks the
two lookups to agree there; for the kept/fresh instance they are one.
-/

namespace ConLeche.Verify.Ground

open ConLeche

variable {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}

/-! ## The relations -/

/-- **Two entries with one key** (constant and levels). -/
@[expose] def EntRel (PA PB : G4Prog) (kA kB : Nat) : Prop :=
  ∃ iA iB, PA.kInfo[kA]? = some iA ∧ PB.kInfo[kB]? = some iB ∧ infoKey iA = infoKey iB

/-- **Two nodes compiled from one term.** -/
@[expose] def NRel (f₁ : Name → Option ConstantInfo) (p₁ : Name → Nat → Option ProjEntry)
    (f₂ : Name → Option ConstantInfo) (p₂ : Name → Nat → Option ProjEntry) (PA PB : G4Prog)
    (oA oB : Nat) : Prop :=
  ∃ t, Comp f₁ p₁ PA oA t ∧ Comp f₂ p₂ PB oB t

/-- **Two argument-position nodes compiled from one term.** -/
@[expose] def ARel (f₁ : Name → Option ConstantInfo) (p₁ : Name → Nat → Option ProjEntry)
    (f₂ : Name → Option ConstantInfo) (p₂ : Name → Nat → Option ProjEntry) (PA PB : G4Prog)
    (oA oB : Nat) : Prop :=
  ∃ t, CompArg f₁ p₁ PA oA t ∧ CompArg f₂ p₂ PB oB t

/-- The lookups agree on a projection's row. -/
@[expose] def ProjAgree (p₁ p₂ : Name → Nat → Option ProjEntry) : Expr → Prop
  | .proj sn i _ => p₁ sn i = p₂ sn i
  | _ => True

/-- The lookups agree on a spine head's erasure mask. -/
@[expose] def MaskAgree (f₁ f₂ : Name → Option ConstantInfo) (t : Expr) : Prop :=
  maskHead f₁ t.getAppFn = maskHead f₂ t.getAppFn

theorem EntRel.ext {PA PB PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {kA kB : Nat}
    (h : EntRel PA PB kA kB) : EntRel PA' PB' kA kB := by
  obtain ⟨iA, iB, h₁, h₂, h₃⟩ := h
  exact ⟨iA, iB, hA.kInfo_some h₁, hB.kInfo_some h₂, h₃⟩

theorem NRel.ext {PA PB PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {oA oB : Nat}
    (h : NRel f₁ p₁ f₂ p₂ PA PB oA oB) : NRel f₁ p₁ f₂ p₂ PA' PB' oA oB := by
  obtain ⟨t, h₁, h₂⟩ := h
  exact ⟨t, h₁.extR hA, h₂.extR hB⟩

theorem ARel.ext {PA PB PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {oA oB : Nat}
    (h : ARel f₁ p₁ f₂ p₂ PA PB oA oB) : ARel f₁ p₁ f₂ p₂ PA' PB' oA oB := by
  obtain ⟨t, h₁, h₂⟩ := h
  exact ⟨t, h₁.extR hA, h₂.extR hB⟩

/-! ## λ telescopes -/

/-- A term's leading λ count and the body under them. -/
@[expose] def lamTel : Expr → Nat × Expr
  | .lam _ b => ((lamTel b).1 + 1, (lamTel b).2)
  | e => (0, e)

/-- **A λ node's telescope fields** are the term's: its length and the
compile of the innermost body. -/
theorem Comp.lam_tel {P : G4Prog} : ∀ {o : Nat} {ty b : Expr}, Comp f₁ p₁ P o (.lam ty b) →
    P.code[o + 2]? = some (lamTel (.lam ty b)).1 ∧
      ∃ inner, P.code[o + 3]? = some inner ∧ Comp f₁ p₁ P inner (lamTel (.lam ty b)).2
  | o, ty, b, .lam (b := bo) (tn := tn) (inner := inner) h₀ h₁ h₂ h₃ hb htel => by
    rcases htel with ⟨hb2, hbtn, hbin, htn⟩ | ⟨hb2, rfl, rfl⟩
    · obtain ⟨ty', b', rfl⟩ := hb.lam_tag.mp hb2
      obtain ⟨e₁, inner', e₂, e₃⟩ := Comp.lam_tel hb
      rw [hbtn] at e₁
      rw [hbin] at e₂; obtain rfl := Option.some.inj e₂
      refine ⟨?_, inner, h₃, ?_⟩
      · rw [h₂]; simp only [lamTel] at e₁ ⊢; congr 1; have := Option.some.inj e₁; omega
      · simpa [lamTel] using e₃
    · have e : lamTel (.lam ty b) = (1, b) := by
        cases b with
        | lam => exact absurd ((hb.lam_tag).mpr ⟨_, _, rfl⟩) hb2
        | _ => rfl
      rw [e]; exact ⟨h₂, _, h₃, hb⟩

/-! ## One term, one layout -/

section
variable {PA PB : G4Prog}

/-- **The tag.** -/
theorem comp2_tag {oA oB : Nat} {t : Expr} (hA : Comp f₁ p₁ PA oA t) (hB : Comp f₂ p₂ PB oB t)
    (hp : ProjAgree p₁ p₂ t) : PA.code[oA]? = PB.code[oB]? := by
  cases hA <;> cases hB <;> simp_all [ProjAgree]

/-- A variable's index. -/
theorem comp2_bvar {oA oB i : Nat} (hA : Comp f₁ p₁ PA oA (.bvar i)) (hB : Comp f₂ p₂ PB oB (.bvar i)) :
    PA.code[oA + 1]? = some i ∧ PB.code[oB + 1]? = some i := by
  cases hA; cases hB; exact ⟨by assumption, by assumption⟩

/-- **A λ**: the body nodes, the telescope's length, the innermost bodies. -/
theorem comp2_lam {oA oB : Nat} {ty b : Expr} (hA : Comp f₁ p₁ PA oA (.lam ty b))
    (hB : Comp f₂ p₂ PB oB (.lam ty b)) :
    (∃ bA bB, PA.code[oA + 1]? = some bA ∧ PB.code[oB + 1]? = some bB ∧
      Comp f₁ p₁ PA bA b ∧ Comp f₂ p₂ PB bB b) ∧
    PA.code[oA + 2]? = some (lamTel (.lam ty b)).1 ∧ PB.code[oB + 2]? = some (lamTel (.lam ty b)).1 ∧
    ∃ iA iB, PA.code[oA + 3]? = some iA ∧ PB.code[oB + 3]? = some iB ∧
      Comp f₁ p₁ PA iA (lamTel (.lam ty b)).2 ∧ Comp f₂ p₂ PB iB (lamTel (.lam ty b)).2 := by
  obtain ⟨tA, iA, h₃A, hiA⟩ := hA.lam_tel
  obtain ⟨tB, iB, h₃B, hiB⟩ := hB.lam_tel
  refine ⟨?_, tA, tB, iA, iB, h₃A, h₃B, hiA, hiB⟩
  cases hA with
  | lam _ h₁ _ _ hb _ =>
    cases hB with
    | lam _ h₁' _ _ hb' _ => exact ⟨_, _, h₁, h₁', hb, hb'⟩

/-- **A `let`**: the value's argument nodes and the body's nodes. -/
theorem comp2_letE {oA oB : Nat} {ty v b : Expr} (hA : Comp f₁ p₁ PA oA (.letE ty v b))
    (hB : Comp f₂ p₂ PB oB (.letE ty v b)) :
    (∃ vA vB, PA.code[oA + 1]? = some vA ∧ PB.code[oB + 1]? = some vB ∧
      CompArg f₁ p₁ PA vA v ∧ CompArg f₂ p₂ PB vB v) ∧
    ∃ bA bB, PA.code[oA + 2]? = some bA ∧ PB.code[oB + 2]? = some bB ∧
      Comp f₁ p₁ PA bA b ∧ Comp f₂ p₂ PB bB b := by
  cases hA with
  | letE _ h₁ h₂ hv hb =>
    cases hB with
    | letE _ h₁' h₂' hv' hb' => exact ⟨⟨_, _, h₁, h₁', hv, hv'⟩, _, _, h₂, h₂', hb, hb'⟩

/-- **A constant**: two entries with one key. -/
theorem comp2_const {oA oB : Nat} {c : Name} {us : List Level} (hA : Comp f₁ p₁ PA oA (.const c us))
    (hB : Comp f₂ p₂ PB oB (.const c us)) :
    ∃ kA kB, PA.code[oA + 1]? = some kA ∧ PB.code[oB + 1]? = some kB ∧ EntRel PA PB kA kB := by
  cases hA with
  | const _ h₁ h₂ h₃ =>
    cases hB with
    | const _ h₁' h₂' h₃' => exact ⟨_, _, h₁, h₁', _, _, h₂, h₂', h₃.trans h₃'.symm⟩

/-- A numeral. -/
theorem comp2_natLit {oA oB n : Nat} (hA : Comp f₁ p₁ PA oA (.lit (.natVal n)))
    (hB : Comp f₂ p₂ PB oB (.lit (.natVal n))) :
    PA.code[oA + 1]? = some n ∧ PB.code[oB + 1]? = some n := by
  cases hA; cases hB; exact ⟨by assumption, by assumption⟩

/-- **A string literal**: two string indices with one string. -/
theorem comp2_strLit {oA oB : Nat} {s : String} (hA : Comp f₁ p₁ PA oA (.lit (.strVal s)))
    (hB : Comp f₂ p₂ PB oB (.lit (.strVal s))) :
    ∃ sA sB, PA.code[oA + 1]? = some sA ∧ PB.code[oB + 1]? = some sB ∧
      PA.strs[sA]? = some s ∧ PB.strs[sB]? = some s := by
  cases hA with
  | strLit _ h₁ h₂ =>
    cases hB with
    | strLit _ h₁' h₂' => exact ⟨_, _, h₁, h₁', h₂, h₂'⟩

/-- **A projection** (the lookups agree on its row): two rows with one
content, the projected nodes. -/
theorem comp2_proj {oA oB i : Nat} {sn : Name} {e : Expr} (hA : Comp f₁ p₁ PA oA (.proj sn i e))
    (hB : Comp f₂ p₂ PB oB (.proj sn i e)) (hp : p₁ sn i = p₂ sn i) (h7 : PA.code[oA]? = some 7) :
    ∃ qA qB pj, PA.code[oA + 1]? = some (qA + 1) ∧ PB.code[oB + 1]? = some (qB + 1) ∧
      PA.projs[qA]? = some pj ∧ PB.projs[qB]? = some pj ∧
      ∃ eA eB, PA.code[oA + 2]? = some eA ∧ PB.code[oB + 2]? = some eB ∧
        Comp f₁ p₁ PA eA e ∧ Comp f₂ p₂ PB eB e := by
  cases hA with
  | proj hf h₀ h₁ h₂ h₃ he =>
    cases hB with
    | proj hf' h₀' h₁' h₂' h₃' he' =>
      rw [hp, hf'] at hf; obtain rfl := Option.some.inj hf
      exact ⟨_, _, _, h₁, h₁', h₂, h₂', _, _, h₃, h₃', he, he'⟩
    | projNone hf' _ => rw [hp, hf'] at hf; cases hf
  | projNone _ h₀ => rw [h₀] at h7; cases h7

/-- **A spine** (the lookups agree on its head's mask): the head nodes, the
argument count, and argument by argument either both erased or two
argument-position nodes of one term. -/
theorem comp2_app {oA oB : Nat} {f x : Expr} (hA : Comp f₁ p₁ PA oA (.app f x))
    (hB : Comp f₂ p₂ PB oB (.app f x)) (hm : MaskAgree f₁ f₂ (.app f x)) :
    (∃ hA' hB', PA.code[oA + 1]? = some hA' ∧ PB.code[oB + 1]? = some hB' ∧
      Comp f₁ p₁ PA hA' (Expr.app f x).getAppFn ∧ Comp f₂ p₂ PB hB' (Expr.app f x).getAppFn) ∧
    PA.code[oA + 2]? = some (Expr.app f x).getAppArgs.length ∧
    PB.code[oB + 2]? = some (Expr.app f x).getAppArgs.length ∧
    ∀ j, j < (Expr.app f x).getAppArgs.length → ∃ aA aB, PA.code[oA + 3 + j]? = some aA ∧
      PB.code[oB + 3 + j]? = some aB ∧
      ((PA.code[aA]? = some 8 ∧ PB.code[aB]? = some 8) ∨
        ∃ a, CompArg f₁ p₁ PA aA a ∧ CompArg f₂ p₂ PB aB a) := by
  cases hA with
  | app _ h₁ h₂ hn hh ha =>
    cases hB with
    | app _ h₁' h₂' hn' hh' ha' =>
      subst hn hn'
      refine ⟨⟨_, _, h₁, h₁', hh, hh'⟩, h₂, h₂', fun j hj => ?_⟩
      unfold MaskAgree at hm
      rw [← hm] at ha'
      exact args2 ha ha' j hj
where
  /-- The argument nodes, from the `i`-th on. -/
  args2 {mask : Array Bool} {pA pB : Nat} : ∀ {i : Nat} {xs : List Expr},
      CompArgs f₁ p₁ PA mask pA i xs → CompArgs f₂ p₂ PB mask pB i xs →
      ∀ (d : Nat), d < xs.length → ∃ aA aB, PA.code[pA + d]? = some aA ∧
        PB.code[pB + d]? = some aB ∧
        ((PA.code[aA]? = some 8 ∧ PB.code[aB]? = some 8) ∨
          ∃ a, CompArg f₁ p₁ PA aA a ∧ CompArg f₂ p₂ PB aB a)
    | _, [], _, _, _, h => absurd h (Nat.not_lt_zero _)
    | i, x :: xs, hA, hB, d, hd => by
      cases hA with
      | erased h₀ hm₁ h₈ hr =>
        cases hB with
        | erased h₀' _ h₈' hr' =>
          rcases d with _ | d
          · exact ⟨_, _, h₀, h₀', .inl ⟨h₈, h₈'⟩⟩
          · obtain ⟨aA, aB, e₁, e₂, e₃⟩ := args2 hr hr' d (by simp at hd; omega)
            exact ⟨aA, aB, by rw [show pA + (d + 1) = pA + 1 + d by omega]; exact e₁,
              by rw [show pB + (d + 1) = pB + 1 + d by omega]; exact e₂, e₃⟩
        | arg _ hm₂ _ _ => rw [hm₁] at hm₂; cases hm₂
      | arg h₀ hm₁ hx hr =>
        cases hB with
        | erased _ hm₂ _ _ => rw [hm₁] at hm₂; cases hm₂
        | arg h₀' _ hx' hr' =>
          rcases d with _ | d
          · exact ⟨_, _, h₀, h₀', .inr ⟨x, hx, hx'⟩⟩
          · obtain ⟨aA, aB, e₁, e₂, e₃⟩ := args2 hr hr' d (by simp at hd; omega)
            exact ⟨aA, aB, by rw [show pA + (d + 1) = pA + 1 + d by omega]; exact e₁,
              by rw [show pB + (d + 1) = pB + 1 + d by omega]; exact e₂, e₃⟩

/-- **An argument position**: a shared node on both sides (slots owned by
the term, the wrapped nodes compiled from it), or a plain node on both. -/
theorem comp2_arg {oA oB : Nat} {a : Expr} (hA : CompArg f₁ p₁ PA oA a) (hB : CompArg f₂ p₂ PB oB a) :
    (∃ slA slB eA eB, PA.code[oA]? = some 9 ∧ PB.code[oB]? = some 9 ∧
      PA.code[oA + 1]? = some slA ∧ PB.code[oB + 1]? = some slB ∧
      SlotOwn PA slA (.inl a) ∧ SlotOwn PB slB (.inl a) ∧
      PA.code[oA + 2]? = some eA ∧ PB.code[oB + 2]? = some eB ∧
      Comp f₁ p₁ PA eA a ∧ Comp f₂ p₂ PB eB a) ∨
    (Comp f₁ p₁ PA oA a ∧ Comp f₂ p₂ PB oB a) := by
  cases hA with
  | shared hs hb hcn h₀ h₁ h₂ hc =>
    cases hB with
    | shared _ _ hcn' h₀' h₁' h₂' hc' =>
      exact .inl ⟨_, _, _, _, h₀, h₀', h₁, h₁', ⟨_, hcn, h₁⟩, ⟨_, hcn', h₁'⟩, h₂, h₂', hc, hc'⟩
    | plain hn _ => exact absurd hb (hn hs)
  | plain hn hc =>
    cases hB with
    | shared hs hb _ _ _ _ _ => exact absurd hb (hn hs)
    | plain _ hc' => exact .inr ⟨hc, hc'⟩

end

end ConLeche.Verify.Ground
