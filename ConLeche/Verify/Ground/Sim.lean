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

/-! ## Related entries -/

/-- Two entries of one key have one shape (their information up to the rule
base), where the lookups agree on the constant. -/
theorem EntRel.shape {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) :
    ∃ iA iB, PA.kInfo[kA]? = some iA ∧ PB.kInfo[kB]? = some iB ∧ infoKey iA = infoKey iB ∧
      (f₁ (infoKey iA).1 = f₂ (infoKey iA).1 → iA.unbased = iB.unbased) := by
  obtain ⟨iA, iB, h₁, h₂, h₃⟩ := h
  refine ⟨iA, iB, h₁, h₂, h₃, fun hf => ?_⟩
  rw [hIA.kind kA iA h₁, hIB.kind kB iB h₂, ← h₃]
  unfold keyInfo; rw [hf]

/-- **One tag** for two entries of one key (the lookups agreeing on the
constant, the `Nat` flags equal). -/
theorem EntRel.tag {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) (hn : PA.natOk = PB.natOk)
    (hf : ∀ iA, PA.kInfo[kA]? = some iA → f₁ (infoKey iA).1 = f₂ (infoKey iA).1) :
    PA.kTag[kA]? = PB.kTag[kB]? := by
  obtain ⟨iA, iB, h₁, h₂, h₃, hs⟩ := h.shape hIA hIB
  have hsh := hs (hf iA h₁)
  have eA := hIA.ents kA (lt_of_some h₁)
  have eB := hIB.ents kB (lt_of_some h₂)
  unfold EntOK at eA eB
  rw [h₁] at eA; rw [h₂] at eB
  cases iA <;> cases iB <;> simp only [G4Info.unbased, reduceCtorEq] at hsh
  · -- definitions
    simp only [G4Info.defn.injEq] at hsh
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hsh
    rw [hIA.defTag kA _ _ _ _ h₁, hIB.defTag kB _ _ _ _ h₂, hn]
  · obtain ⟨-, h1, -⟩ := eA; obtain ⟨-, h1', -⟩ := eB; rw [h1, h1']
  · obtain ⟨_, _, -, -, -, -, h1, -⟩ := eA; obtain ⟨_, _, -, -, -, -, h1', -⟩ := eB; rw [h1, h1']
  · rw [eA, eB]

/-- **Two recursor entries of one key**: one recursor at one level list, the
rule bases apart. -/
theorem EntRel.recr {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {lps : List Name} {us : List Level} {mI rP bA nr : Nat}
    {isK isEta : Bool} (hi : PA.kInfo[kA]? = some (.recr c lps us mI rP bA nr isK isEta))
    (hf : f₁ c = f₂ c) :
    ∃ bB, PB.kInfo[kB]? = some (.recr c lps us mI rP bB nr isK isEta) ∧
      RecOK f₁ p₁ PA kA c lps us mI rP bA nr isK isEta ∧ RecOK f₂ p₂ PB kB c lps us mI rP bB nr isK isEta := by
  obtain ⟨iA, iB, h₁, h₂, -, hs⟩ := h.shape hIA hIB
  rw [hi] at h₁; obtain rfl := Option.some.inj h₁
  have hsh := hs hf
  cases iB <;> simp only [G4Info.unbased] at hsh <;> cases hsh
  refine ⟨_, h₂, ?_, ?_⟩
  · have := hIA.ents kA (lt_of_some hi); unfold EntOK at this; rw [hi] at this; exact this
  · have := hIB.ents kB (lt_of_some h₂); unfold EntOK at this; rw [h₂] at this; exact this

/-- **Two constructor entries of one key.** -/
theorem EntRel.ctor {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {us : List Level} {nP nF : Nat}
    (hi : PA.kInfo[kA]? = some (.ctor c us nP nF)) (hf : f₁ c = f₂ c) :
    PB.kInfo[kB]? = some (.ctor c us nP nF) ∧ CtorOK f₁ PA kA c us nP nF ∧ CtorOK f₂ PB kB c us nP nF := by
  obtain ⟨iA, iB, h₁, h₂, -, hs⟩ := h.shape hIA hIB
  rw [hi] at h₁; obtain rfl := Option.some.inj h₁
  have hsh := hs hf
  cases iB <;> simp only [G4Info.unbased] at hsh <;> cases hsh
  refine ⟨h₂, ?_, ?_⟩
  · have := hIA.ents kA (lt_of_some hi); unfold EntOK at this; rw [hi] at this; exact this
  · have := hIB.ents kB (lt_of_some h₂); unfold EntOK at this; rw [h₂] at this; exact this

/-- **Two definition entries of one key.** -/
theorem EntRel.defn {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {lps : List Name} {us : List Level} {v : Expr}
    (hi : PA.kInfo[kA]? = some (.defn c lps us v)) (hf : f₁ c = f₂ c) :
    PB.kInfo[kB]? = some (.defn c lps us v) ∧ DefnOK f₁ p₁ PA kA c lps us v ∧
      DefnOK f₂ p₂ PB kB c lps us v := by
  obtain ⟨iA, iB, h₁, h₂, -, hs⟩ := h.shape hIA hIB
  rw [hi] at h₁; obtain rfl := Option.some.inj h₁
  have hsh := hs hf
  cases iB <;> simp only [G4Info.unbased] at hsh <;> cases hsh
  refine ⟨h₂, ?_, ?_⟩
  · have := hIA.ents kA (lt_of_some hi); unfold EntOK at this; rw [hi] at this; exact this
  · have := hIB.ents kB (lt_of_some h₂); unfold EntOK at this; rw [h₂] at this; exact this

/-! ## The words of related entries -/

/-- **Two name ids of one name.** -/
@[expose] def NidRel (PA PB : G4Prog) (iA iB : Nat) : Prop :=
  ∃ c : Name, PA.nids[c]? = some iA ∧ PB.nids[c]? = some iB

/-- Name ids are related one to one. -/
theorem NidRel.iff {PA PB : G4Prog} (hA : NidOK PA) (hB : NidOK PB) {iA iB jA jB : Nat}
    (h : NidRel PA PB iA iB) (h' : NidRel PA PB jA jB) : iA = jA ↔ iB = jB := by
  obtain ⟨c, h₁, h₂⟩ := h
  obtain ⟨c', h₁', h₂'⟩ := h'
  constructor
  · rintro rfl; obtain rfl := hA.2 c c' iA h₁ h₁'; rw [h₂] at h₂'; exact Option.some.inj h₂'
  · rintro rfl; obtain rfl := hB.2 c c' iB h₂ h₂'; rw [h₁] at h₁'; exact Option.some.inj h₁'

/-- Entries are related one to one (each side registers an entry at its key). -/
theorem EntRel.iff {PA PB : G4Prog} (hA : CompInv f₁ p₁ PA) (hB : CompInv f₂ p₂ PB) {kA kB kA' kB' : Nat}
    (h : EntRel PA PB kA kB) (h' : EntRel PA PB kA' kB') : kA' = kA ↔ kB' = kB := by
  obtain ⟨iA, iB, h₁, h₂, h₃⟩ := h
  obtain ⟨iA', iB', h₁', h₂', h₃'⟩ := h'
  have eA := hA.kMapAll _ _ h₁; have eA' := hA.kMapAll _ _ h₁'
  have eB := hB.kMapAll _ _ h₂; have eB' := hB.kMapAll _ _ h₂'
  constructor
  · rintro rfl
    rw [h₁] at h₁'; obtain rfl := Option.some.inj h₁'
    rw [← h₃', h₃] at eB'; rw [eB] at eB'; exact (Option.some.inj eB').symm
  · rintro rfl
    rw [h₂] at h₂'; obtain rfl := Option.some.inj h₂'
    rw [h₃', ← h₃] at eA'; rw [eA] at eA'; exact (Option.some.inj eA').symm

/-- **A constructor's arity** is one word on both sides of related entries
(the lookups agreeing on the name). -/
theorem EntRel.arity_ctor {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {cv : ConstantVal} {nP nF : Nat}
    (hc : ∀ iA, PA.kInfo[kA]? = some iA → f₁ (infoKey iA).1 = some (.ctorInfo cv nP nF) ∧
      f₂ (infoKey iA).1 = some (.ctorInfo cv nP nF)) :
    PA.kArity[kA]? = some (g4Pis cv.type 0) ∧ PB.kArity[kB]? = some (g4Pis cv.type 0) := by
  obtain ⟨iA, iB, h₁, h₂, h₃⟩ := h
  obtain ⟨c₁, c₂⟩ := hc iA h₁
  exact ⟨hIA.ctorAr kA iA cv nP nF h₁ c₁, hIB.ctorAr kB iB cv nP nF h₂ (h₃ ▸ c₂)⟩

/-- **Two constructor entries of one key**: one tag, one arity, one level
count, their name ids related. -/
theorem EntRel.ctorW {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {us : List Level} {nP nF : Nat}
    (hi : PA.kInfo[kA]? = some (.ctor c us nP nF)) (hf : f₁ c = f₂ c) :
    PB.kInfo[kB]? = some (.ctor c us nP nF) ∧ PA.kTag[kA]? = some 1 ∧ PB.kTag[kB]? = some 1 ∧
      PA.kArity[kA]? = PB.kArity[kB]? ∧ PA.kD[kA]? = PB.kD[kB]? ∧
      ∃ iA iB, PA.kB[kA]? = some iA ∧ PB.kB[kB]? = some iB ∧ NidRel PA PB iA iB := by
  obtain ⟨hB, ⟨⟨cv, h₁, h₂⟩, h₃, ⟨i, h₄, h₅⟩, h₆⟩, ⟨⟨cv', h₁', h₂'⟩, h₃', ⟨i', h₄', h₅'⟩, h₆'⟩⟩ :=
    h.ctor hIA hIB hi hf
  rw [hf, h₁'] at h₁
  obtain rfl : cv = cv' := by cases h₁; rfl
  exact ⟨hB, h₃, h₃', by rw [h₂, h₂'], by rw [h₆, h₆'], i, i', h₅, h₅', c, h₄, h₄'⟩

/-- **Two definition entries of one key**: one tag, one operation word for
an accelerated one, the compiled bodies of one term where both are compiled. -/
theorem EntRel.defnW {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {lps : List Name} {us : List Level} {v : Expr}
    (hi : PA.kInfo[kA]? = some (.defn c lps us v)) (hf : f₁ c = f₂ c) (hn : PA.natOk = PB.natOk) :
    PB.kInfo[kB]? = some (.defn c lps us v) ∧ PA.kTag[kA]? = PB.kTag[kB]? ∧
      (PA.kTag[kA]? = some 3 → PA.kE[kA]? = PB.kE[kB]?) ∧
      ∃ wA wB, PA.kCode[kA]? = some wA ∧ PB.kCode[kB]? = some wB ∧
        CodeOK f₁ p₁ PA wA (v.instantiateLevelParams lps us) ∧
        CodeOK f₂ p₂ PB wB (v.instantiateLevelParams lps us) := by
  obtain ⟨hB, ⟨-, -, t₁, w, c₁, d₁⟩, ⟨-, -, t₂, w', c₂, d₂⟩⟩ := h.defn hIA hIB hi hf
  have eT : PA.kTag[kA]? = PB.kTag[kB]? := by
    rw [hIA.defTag kA _ _ _ _ hi, hIB.defTag kB _ _ _ _ hB, hn]
  refine ⟨hB, eT, fun h3 => ?_, w, w', c₁, c₂, d₁, d₂⟩
  rcases t₁ with t₁ | ⟨-, -, -, -, e₁⟩
  · rw [t₁] at h3; cases h3
  · rcases t₂ with t₂ | ⟨-, -, -, -, e₂⟩
    · rw [← eT, h3] at t₂; cases t₂
    · rw [e₁, e₂]

/-- Related entries name one constant. -/
theorem EntRel.name {PA PB : G4Prog} {kA kB : Nat} (h : EntRel PA PB kA kB) :
    PA.entryName kA = PB.entryName kB := by
  obtain ⟨iA, iB, h₁, h₂, h₃⟩ := h
  unfold G4Prog.entryName; rw [h₁, h₂]
  cases iA <;> cases iB <;> simp_all [infoKey]

/-- The K word's entry: none on both sides, or related entries. -/
@[expose] def KfabRel (PA PB : G4Prog) (fA fB : Nat) : Prop :=
  (fA = 0 ∧ fB = 0) ∨ ∃ cA cB, fA = cA + 1 ∧ fB = cB + 1 ∧ EntRel PA PB cA cB

theorem KfabKey.rel {PA PB : G4Prog} {c : Name} {us : List Level} {fA fB : Nat}
    (hA : KfabKey f₁ PA c us fA) (hB : KfabKey f₂ PB c us fB) (hf : f₁ = f₂ ∨ kfabKey f₁ c us = kfabKey f₂ c us) :
    KfabRel PA PB fA fB := by
  have e : kfabKey f₁ c us = kfabKey f₂ c us := by rcases hf with rfl | e; rfl; exact e
  rcases hA with ⟨h₁, rfl⟩ | ⟨key, kc, info, h₁, rfl, h₃, h₄⟩
  · rcases hB with ⟨-, rfl⟩ | ⟨key', -, -, h₁', -⟩
    · exact .inl ⟨rfl, rfl⟩
    · rw [e, h₁'] at h₁; cases h₁
  · rcases hB with ⟨h₁', -⟩ | ⟨key', kc', info', h₁', rfl, h₃', h₄'⟩
    · rw [e, h₁'] at h₁; cases h₁
    · rw [e, h₁'] at h₁; obtain rfl := Option.some.inj h₁
      exact .inr ⟨kc, kc', rfl, rfl, info, info', h₃, h₃', h₄.trans h₄'.symm⟩

/-- **Two recursor entries of one key**: one tag, arity, prefix, rule count
and flag word up to the K entry, which is related; the rule bases apart. -/
theorem EntRel.recW {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {lps : List Name} {us : List Level} {mI rP bA nr : Nat}
    {isK isEta : Bool} (hi : PA.kInfo[kA]? = some (.recr c lps us mI rP bA nr isK isEta))
    (hf : f₁ c = f₂ c) (hk : kfabKey f₁ c us = kfabKey f₂ c us) :
    ∃ bB, PB.kInfo[kB]? = some (.recr c lps us mI rP bB nr isK isEta) ∧
      PA.kTag[kA]? = some 2 ∧ PB.kTag[kB]? = some 2 ∧
      PA.kArity[kA]? = some mI ∧ PB.kArity[kB]? = some mI ∧
      PA.kB[kA]? = some rP ∧ PB.kB[kB]? = some rP ∧
      PA.kC[kA]? = some bA ∧ PB.kC[kB]? = some bB ∧
      PA.kD[kA]? = some nr ∧ PB.kD[kB]? = some nr ∧
      ∃ fA fB, PA.kE[kA]? = some ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * fA) ∧
        PB.kE[kB]? = some ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * fB) ∧
        KfabRel PA PB fA fB := by
  obtain ⟨bB, hB, ⟨cv, rules, -, -, -, -, t₁, a₁, b₁, c₁, d₁, -⟩,
    ⟨cv', rules', -, -, -, -, t₂, a₂, b₂, c₂, d₂, -⟩⟩ := h.recr hIA hIB hi hf
  obtain ⟨fA, e₁, k₁⟩ := hIA.kfab kA _ _ _ _ _ _ _ _ _ hi
  obtain ⟨fB, e₂, k₂⟩ := hIB.kfab kB _ _ _ _ _ _ _ _ _ hB
  exact ⟨bB, hB, t₁, t₂, a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂, fA, fB, e₁, e₂, k₁.rel k₂ (.inr hk)⟩

/-- The recursor entry's rules: both sides store rows for one rule list. -/
theorem EntRel.recRows {PA PB : G4Prog} (hIA : Inv f₁ p₁ PA) (hIB : Inv f₂ p₂ PB) {kA kB : Nat}
    (h : EntRel PA PB kA kB) {c : Name} {lps : List Name} {us : List Level} {mI rP bA nr : Nat}
    {isK isEta : Bool} (hi : PA.kInfo[kA]? = some (.recr c lps us mI rP bA nr isK isEta))
    (hf : f₁ c = f₂ c) :
    ∃ bB cv rules, PB.kInfo[kB]? = some (.recr c lps us mI rP bB nr isK isEta) ∧
      f₁ c = some (.recInfo cv mI rP isK rules) ∧ nr = rules.length ∧
      ∀ i (hr : i < rules.length), RowOK f₁ p₁ PA (bA + i) isK lps us rules[i] ∧
        RowOK f₂ p₂ PB (bB + i) isK lps us rules[i] := by
  obtain ⟨bB, hB, ⟨cv, rules, h₁, -, -, -, -, -, -, -, -, hn, -, -, hr⟩,
    ⟨cv', rules', h₁', -, -, -, -, -, -, -, -, -, -, -, hr'⟩⟩ := h.recr hIA hIB hi hf
  rw [hf, h₁'] at h₁
  obtain ⟨rfl, rfl⟩ : cv' = cv ∧ rules' = rules := by cases h₁; exact ⟨rfl, rfl⟩
  exact ⟨bB, cv', rules', hB, hf ▸ h₁', hn, fun i hi => ⟨hr i hi, hr' i hi⟩⟩

/-! ## Projection rows -/

/-- **Two projection rows with one content.** -/
@[expose] def PrjRel (PA PB : G4Prog) (qA qB : Nat) : Prop :=
  ∃ pj, PA.projs[qA]? = some pj ∧ PB.projs[qB]? = some pj

/-- Related projection rows have equal words, their name ids related. -/
theorem PrjRel.words {PA PB : G4Prog} (hIA : TabInv f₁ p₁ PA) (hIB : TabInv f₂ p₂ PB) {qA qB : Nat}
    (h : PrjRel PA PB qA qB) :
    PA.pNP[qA]? = PB.pNP[qB]? ∧ PA.pIdx[qA]? = PB.pIdx[qB]? ∧ PA.pNF[qA]? = PB.pNF[qB]? ∧
      PA.pNl[qA]? = PB.pNl[qB]? ∧ PA.pAlw[qA]? = PB.pAlw[qB]? ∧
      ∃ iA iB, PA.pNid[qA]? = some iA ∧ PB.pNid[qB]? = some iB ∧ NidRel PA PB iA iB := by
  obtain ⟨pj, h₁, h₂⟩ := h
  obtain ⟨sn, i, en, e₁, -, ⟨ni, n₁, n₂⟩, a₁, a₂, a₃, a₄, a₅⟩ := hIA.prjs qA (lt_of_some h₁)
  obtain ⟨sn', i', en', e₂, -, ⟨ni', n₁', n₂'⟩, b₁, b₂, b₃, b₄, b₅⟩ := hIB.prjs qB (lt_of_some h₂)
  rw [h₁] at e₁; rw [h₂, e₁] at e₂
  simp only [Option.some.injEq, G4Proj.mk.injEq] at e₂
  obtain ⟨rfl, -, rfl, -, -, -, -, rfl⟩ := e₂
  exact ⟨by rw [a₂, b₂], by rw [a₁, b₁], by rw [a₃, b₃], by rw [a₄, b₄], by rw [a₅, b₅],
    ni, ni', n₂, n₂', en.ctor, n₁, n₁'⟩

/-! ## Rule rows -/

/-- **Two rows of one rule** (at one recursor's levels): the stored rule,
fields, parameters and case flag equal, the name ids related, the compiled
right-hand sides of one term where both are compiled (the lookups agreeing
on the constructor and on the case-3 test, which reads its family). -/
theorem RowOK.rel {PA PB : G4Prog} {rA rB : Nat} {isK : Bool} {lps : List Name} {us : List Level}
    {rl : RecRule} (hA : RowOK f₁ p₁ PA rA isK lps us rl) (hB : RowOK f₂ p₂ PB rB isK lps us rl)
    (hf : f₁ rl.ctor = f₂ rl.ctor) (h3 : ruleCase3 f₁ isK lps us rl = ruleCase3 f₂ isK lps us rl) :
    PA.rules[rA]? = PB.rules[rB]? ∧ PA.rNF[rA]? = PB.rNF[rB]? ∧ PA.rCP[rA]? = PB.rCP[rB]? ∧
      PA.rC3[rA]? = PB.rC3[rB]? ∧
      (∃ iA iB, PA.rNid[rA]? = some iA ∧ PB.rNid[rB]? = some iB ∧ NidRel PA PB iA iB) ∧
      ∃ wA wB, PA.ruleCode[rA]? = some wA ∧ PB.ruleCode[rB]? = some wB ∧
        CodeOK f₁ p₁ PA wA (rl.rhs.instantiateLevelParams lps us) ∧
        CodeOK f₂ p₂ PB wB (rl.rhs.instantiateLevelParams lps us) := by
  obtain ⟨a₁, a₂, a₃, a₄, ⟨i, a₅, a₆⟩, w, a₇, a₈⟩ := hA
  obtain ⟨b₁, b₂, b₃, b₄, ⟨i', b₅, b₆⟩, w', b₇, b₈⟩ := hB
  have e₁ : gCtorParams f₁ rl.ctor = gCtorParams f₂ rl.ctor := by unfold gCtorParams; rw [hf]
  refine ⟨by rw [a₁, b₁, e₁, h3], by rw [a₂, b₂], by rw [a₃, b₃, e₁], by rw [a₄, b₄, h3],
    ⟨i, i', a₆, b₆, rl.ctor, a₅, b₅⟩, w, w', a₇, b₇, a₈, b₈⟩

/-- **`g4FindRule` answers alike** on two row ranges whose rows match the two
name ids alike: the same offset. -/
theorem findRule_rel (rA rB : Array Nat) (cA cB : Nat) :
    ∀ (n iA iB : Nat), (∀ j, j < n → (rA[iA + j]! = cA ↔ rB[iB + j]! = cB)) →
      ∃ d, g4FindRule rA cA n iA = iA + d ∧ g4FindRule rB cB n iB = iB + d
  | 0, iA, iB, _ => ⟨0, rfl, rfl⟩
  | n + 1, iA, iB, h => by
    simp only [g4FindRule]
    by_cases hA : rA[iA]! = cA
    · have hB : rB[iB]! = cB := (h 0 (by omega)).mp hA
      simp only [hA, hB, beq_self_eq_true, ↓reduceIte]; exact ⟨0, rfl, rfl⟩
    · have hB : ¬rB[iB]! = cB := fun e => hA ((h 0 (by omega)).mpr e)
      simp only [beq_iff_eq, hA, hB, ↓reduceIte]
      obtain ⟨d, e₁, e₂⟩ := findRule_rel rA rB cA cB n (iA + 1) (iB + 1) fun j hj => by
        have := h (j + 1) (by omega)
        rwa [show iA + (j + 1) = iA + 1 + j by omega, show iB + (j + 1) = iB + 1 + j by omega] at this
      exact ⟨d + 1, by rw [e₁]; omega, by rw [e₂]; omega⟩

end ConLeche.Verify.Ground
