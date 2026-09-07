import Lech.Verify.Direct.SumRec
import Lech.Kernel.Direct.RecParts

/-!
# The generated recursive recursor, unfolded (task #188)

`Lech/Verify/Direct/SumRec.lean`'s syntactic kit with the inductive
hypotheses threaded: the unfoldings of the recursive generators
(`directMinorTyR`, `directMinorsPisR`/`directMinorsLamsR`,
`directRecTyR`, `directRecRhsR`), and the closed spellings the
readings need.

The one genuinely new piece is `instSeq_directIdxAt`: a recursive
field's index expression is spelled at the field's own frame (the
parameters and the `i` earlier fields) and moved to the recursor's
frame `p⃗ x⃗ f⃗ ih⃗` by `directIdxAt`'s two lifts; instantiating there at
the frame's own variables undoes both lifts and leaves the expression
instantiated at the parameters and the `i` earlier field variables
alone — twice `instSeq_liftLooseBVars_mid`.

`Expr.shiftFromN` (`Expr.shiftFrom`, iterated) is here too: the
reading of those index expressions moves from the constructor's own
opening to the recursor's frame by inserting the `o` extra slots just
after the parameters, which is exactly that shift (its `denoteP` side
is `Lech/SetP/DirectFix/FixRecReadP.lean`).
-/

namespace Lech

open Expr

/-! ## The recursive generators, unfolded -/

/-- `directMinorTyR`, unfolded to its three steps. -/
theorem directMinorTyR_unfold {C : Name} {lps : List Name} {nP nF o : Nat} {pw : PropWhen}
    {cty mty : Expr} {recIdx : List Nat}
    (h : directMinorTyR C lps nP nF o pw cty recIdx = some mty) :
    ∃ (cbs fbs : List (Expr × BinderMeta)) (crest0 res : Expr),
      cty.stripPis nP = some (cbs, crest0) ∧
      crest0.stripPis nF = some (fbs, res) ∧
      Expr.replacePisPw pw nF (crest0.liftLooseBVars o 0)
        (directIhPis nF o pw (directFieldIdxOf cty nP nF) recIdx 0
          ((Expr.mkAppN (.bvar (nF + o - 1))
            ((res.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF) ++
              [directCtorSpineAt C lps o nP nF])).liftLooseBVars recIdx.length 0))
        = some mty := by
  unfold directMinorTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, r, hr, hmty⟩ := h
  exact ⟨q.1, r.1, q.2, r.2, hq, hr, hmty⟩

/-- The recursive minors' `∀`-telescope, one constructor peeled. -/
theorem directMinorsPisR_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {recIdx : List Nat} {cs : List (Name × Nat × Expr × List Nat)}
    {o : Nat} {body mins : Expr}
    (h : directMinorsPisR lps nP pw ((C, nF, cty, recIdx) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTyR C lps nP nF o pw cty recIdx = some mty ∧
      directMinorsPisR lps nP pw cs (o + 1) body = some rest ∧
      mins = .forallE mty rest ⟨pw⟩ := by
  unfold directMinorsPisR at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

/-- The recursive minors' `λ`-telescope, one constructor peeled. -/
theorem directMinorsLamsR_cons {lps : List Name} {nP : Nat} {pw : PropWhen} {C : Name}
    {nF : Nat} {cty : Expr} {recIdx : List Nat} {cs : List (Name × Nat × Expr × List Nat)}
    {o : Nat} {body mins : Expr}
    (h : directMinorsLamsR lps nP pw ((C, nF, cty, recIdx) :: cs) o body = some mins) :
    ∃ mty rest, directMinorTyR C lps nP nF o pw cty recIdx = some mty ∧
      directMinorsLamsR lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam mty rest ⟨pw⟩ := by
  unfold directMinorsLamsR at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmin⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmin.symm⟩

/-- The empty recursive `∀`-telescope is its body. -/
theorem directMinorsPisR_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsPisR lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsPisR, Option.some.injEq] at h
  exact h.symm

/-- The empty recursive `λ`-telescope is its body. -/
theorem directMinorsLamsR_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : directMinorsLamsR lps nP pw [] o body = some mins) : mins = body := by
  simp only [directMinorsLamsR, Option.some.injEq] at h
  exact h.symm

/-- `directRecTyR`, unfolded to its five steps (`directRecTyI_unfold`
with the recursive minors). -/
theorem directRecTyR_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty recTy : Expr} {ctors : List (Name × Nat × Expr × List Nat)}
    (h : directRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ (tbs : List (Expr × BinderMeta)) (itele motiveTy major minors : Expr),
      tty.stripPis nP = some (tbs, itele) ∧
      directMotiveTyI T lps nP nIdx (directElimLevel elim large) itele = some motiveTy ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nIdx
        (itele.liftLooseBVars (ctors.length + 1) 0)
        (.forallE (directFamI T lps nP nIdx (ctors.length + 1) 0)
          (Expr.mkAppN (.bvar (nIdx + ctors.length + 1)) (directPsAt 1 nIdx ++ [.bvar 0]))
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some major ∧
      directMinorsPisR lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1 major
        = some minors ∧
      Expr.replacePisPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.forallE motiveTy minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some recTy := by
  unfold directRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, motiveTy, hmot, major, hmaj, minors, hmin, hr⟩ := h
  exact ⟨q.1, q.2, motiveTy, major, minors, hq, hmot, hmaj, hmin, hr⟩

/-- `directRecRhsR` at rule `j`, unfolded. -/
theorem directRecRhsR_unfold {T : Name} {lps : List Name} {elim : Name} {large : Bool}
    {nP nIdx : Nat} {tty rhs : Expr} {ctors : List (Name × Nat × Expr × List Nat)} {j : Nat}
    {recC : Name} {rlvls : List Level}
    (h : directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some rhs) :
    ∃ (C : Name) (nF : Nat) (cty : Expr) (recIdx : List Nat)
      (tbs cbs : List (Expr × BinderMeta))
      (itele motiveTy crest0 inner minors : Expr),
      ctors[j]? = some (C, nF, cty, recIdx) ∧
      tty.stripPis nP = some (tbs, itele) ∧
      directMotiveTyI T lps nP nIdx (directElimLevel elim large) itele = some motiveTy ∧
      cty.stripPis nP = some (cbs, crest0) ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nF
        (crest0.liftLooseBVars (ctors.length + 1) 0)
        (directRuleBodyR recC rlvls nP ctors.length nF j recIdx
          (directFieldIdxOf cty nP nF)) = some inner ∧
      directMinorsLamsR lps nP (Level.zeronessOf (directElimLevel elim large)) ctors 1 inner
        = some minors ∧
      Expr.pisToLamsPw (Level.zeronessOf (directElimLevel elim large)) nP tty
        (.lam motiveTy minors
          ⟨Level.zeronessOf (directElimLevel elim large)⟩) = some rhs := by
  unfold directRecRhsR at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    obtain ⟨C, nF, cty, recIdx⟩ := c
    rw [hj] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tq, htq, motiveTy, hmot, q, hq, inner, hinner, minors, hminors, hr⟩ := h
    exact ⟨C, nF, cty, recIdx, tq.1, q.1, tq.2, motiveTy, q.2, inner, minors, rfl, htq, hmot,
      hq, hinner, hminors, hr⟩

/-! ## The index expression at the recursor's frame -/

/-- A lift raises the loose-bvar bound by the lift's amount. -/
theorem Expr.looseBVarsBounded_liftLooseBVars (k : Nat) :
    ∀ (e : Expr) {b c : Nat}, e.looseBVarsBounded b = true →
      (e.liftLooseBVars k c).looseBVarsBounded (b + k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro b c hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.liftLooseBVars]
    split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | fvar _ _ _ => intro b c _; rfl
  | sort _ => intro b c _; rfl
  | const _ _ => intro b c _; rfl
  | lit _ => intro b c _; rfl
  | app f a ihf iha =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf hb.1, iha hb.2⟩
  | lam ty body _ ihty ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty hb.1, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | forallE ty body _ ihty ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨ihty hb.1, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | letE ty v body ihty ihv ihb =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    refine ⟨⟨ihty hb.1.1, ihv hb.1.2⟩, ?_⟩
    have := ihb (b := b + 1) (c := c + 1) hb.2
    rw [show b + 1 + k = b + k + 1 from by omega] at this
    exact this
  | proj _ _ e ih =>
    intro b c hb
    simp only [Expr.liftLooseBVars, Expr.looseBVarsBounded] at hb ⊢
    exact ih hb

/-- **`directIdxAt`, instantiated at the recursor's frame.**  The
frame is `p⃗ x⃗ f⃗ ih⃗` (parameters, `o` extras, `nF` fields, `l`
inductive hypotheses); field `i`'s index expression mentions only the
parameters and the `i` earlier fields, so both of `directIdxAt`'s
lifts are undone by the frame's own instantiation
(`instSeq_liftLooseBVars_mid`, once per lift). -/
theorem instSeq_directIdxAt (P X F I : List Expr) {nP o nF l i : Nat} {e : Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true)
    (hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true)
    (hi : i ≤ nF) (heb : e.looseBVarsBounded (nP + i) = true) :
    instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1) (directIdxAt nF o i l e)
      = instSeq (P ++ F.take i) (nP + i - 1) e := by
  have hq : (e.liftLooseBVars (nF - i + l) 0).looseBVarsBounded (P.length + (nF + l)) = true := by
    have := Expr.looseBVarsBounded_liftLooseBVars (nF - i + l) e (b := nP + i) (c := 0) heb
    exact Expr.looseBVarsBounded_mono (by rw [hP]; omega) this
  -- the outer lift: the `o` extras
  have h1 : instSeq (P ++ X) (nP + o + nF + l - 1)
      ((e.liftLooseBVars (nF - i + l) 0).liftLooseBVars o (nF + l))
      = instSeq P (nP + nF + l - 1) (e.liftLooseBVars (nF - i + l) 0) := by
    have h := instSeq_liftLooseBVars_mid P X (c := nF + l) hclP hq
    rw [hP, hX] at h
    rw [show nP + o + nF + l - 1 = nP + o + (nF + l) - 1 from by omega,
      show nP + nF + l - 1 = nP + (nF + l) - 1 from by omega]
    exact h
  -- the inner lift: the fields at and after `i`, and the hypotheses
  have hsplit : P ++ X ++ F ++ I = (P ++ X) ++ (F ++ I) := by simp
  have hsplit2 : P ++ (F ++ I) = (P ++ F.take i) ++ (F.drop i ++ I) := by
    rw [List.append_assoc, ← List.append_assoc (F.take i), List.take_append_drop]
  have hlen2 : (F.drop i ++ I).length = nF - i + l := by simp [hF, hI]
  have hcl2 : ∀ a ∈ P ++ F.take i, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclP a h
    · exact hclF a (List.mem_of_mem_take h)
  have hlenPF : (P ++ F.take i).length = nP + i := by simp [hP, hF]; omega
  have h2 : instSeq (P ++ (F ++ I)) (nP + nF + l - 1) (e.liftLooseBVars (nF - i + l) 0)
      = instSeq (P ++ F.take i) (nP + i - 1) e := by
    rw [hsplit2]
    have := instSeq_liftLooseBVars_mid (P ++ F.take i) (F.drop i ++ I) (c := 0) hcl2
      (by rw [hlenPF, Nat.add_zero]; exact heb)
    rw [hlenPF, hlen2, Nat.add_zero, Nat.add_zero] at this
    rw [show nP + nF + l - 1 = nP + i + (nF - i + l) - 1 from by omega]
    exact this
  rw [hsplit, Expr.instSeq_append (P ++ X) (F ++ I)]
  show instSeq (F ++ I) (nP + o + nF + l - 1 - (P ++ X).length)
      (instSeq (P ++ X) (nP + o + nF + l - 1)
        ((e.liftLooseBVars (nF - i + l) 0).liftLooseBVars o (nF + l))) = _
  rw [h1, show (P ++ X).length = nP + o from by simp [hP, hX],
    show nP + o + nF + l - 1 - (nP + o) = nP + nF + l - 1 - P.length from by rw [hP]; omega,
    ← Expr.instSeq_append P (F ++ I), h2]

/-! ## Iterated variable shifts -/

/-- `Expr.shiftFrom p`, iterated `n` times: insert `n` fresh variable
slots at index `p`. -/
def Expr.shiftFromN (p : Nat) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.shiftFrom p (Expr.shiftFromN p n e)

/-- A term without free variables is fixed by the shift. -/
theorem Expr.shiftFromN_eq_self_of_not_hasFvar {p : Nat} :
    ∀ (n : Nat) {e : Expr}, e.hasFvar = false → Expr.shiftFromN p n e = e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    show Expr.shiftFrom p (Expr.shiftFromN p n e) = e
    rw [Expr.shiftFromN_eq_self_of_not_hasFvar n h, Expr.shiftFrom_eq_self_of_not_hasFvar h]

/-- A shift bumps a free variable at or above the cut by one. -/
theorem Expr.shiftFromN_fvar (p : Nat) :
    ∀ (n idx : Nat) (ty : Expr),
      ∃ (ty' : Expr),
        Expr.shiftFromN p n (Expr.fvar idx ty)
          = Expr.fvar (if idx < p then idx else idx + n) ty'
  | 0, idx, nm, ty => ⟨nm, ty, by
      show Expr.fvar idx ty = _
      by_cases h : idx < p
      · rw [if_pos h]
      · rw [if_neg h, Nat.add_zero]⟩
  | n + 1, idx, nm, ty => by
    obtain ⟨nm', ty', hn⟩ := Expr.shiftFromN_fvar p n idx nm ty
    by_cases h : idx < p
    · refine ⟨nm', ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_pos h, if_pos h]
      simp only [Expr.shiftFrom, if_neg (show ¬ idx ≥ p from by omega)]
    · refine ⟨nm', Expr.shiftFrom p ty', ?_⟩
      show Expr.shiftFrom p (Expr.shiftFromN p n (Expr.fvar idx ty)) = _
      rw [hn, if_neg h, if_neg h,
        show idx + (n + 1) = idx + n + 1 from by omega]
      simp only [Expr.shiftFrom, if_pos (show idx + n ≥ p from by omega)]

/-- Well-scopedness survives a shift, one slot up. -/
theorem Expr.WScoped_shiftFrom {p : Nat} :
    ∀ {e : Expr} {d : Nat}, Expr.WScoped d e → Expr.WScoped (d + 1) (Expr.shiftFrom p e) := by
  intro e
  induction e with
  | bvar i => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | sort u => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | const n us => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | lit l => intro d _; simp [Expr.shiftFrom, Expr.WScoped]
  | fvar idx ty ih =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom]
    split
    · simp only [Expr.WScoped]
      exact ⟨by omega, ih hw.2⟩
    · simp only [Expr.WScoped]
      exact ⟨by omega, hw.2⟩
  | app f a ihf iha =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty b bi ihty ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihb hw.2⟩
  | forallE ty b bi ihty ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihb hw.2⟩
  | letE ty v b ihty ihv ihb =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ⟨ihty hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i e ih =>
    intro d hw
    simp only [Expr.WScoped] at hw
    simp only [Expr.shiftFrom, Expr.WScoped]
    exact ih hw

/-- Well-scopedness survives an iterated shift, `n` slots up. -/
theorem Expr.WScoped_shiftFromN {p : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat},
      Expr.WScoped d e → Expr.WScoped (d + n) (Expr.shiftFromN p n e)
  | 0, _, _, hw => hw
  | n + 1, e, d, hw => by
    show Expr.WScoped (d + (n + 1)) (Expr.shiftFrom p (Expr.shiftFromN p n e))
    rw [show d + (n + 1) = d + n + 1 from by omega]
    exact Expr.WScoped_shiftFrom (Expr.WScoped_shiftFromN (p := p) n hw)

/-- A shift commutes with an instantiation sequence. -/
theorem Expr.shiftFrom_instSeq (p : Nat) :
    ∀ (sp : List Expr) (t : Nat) (e : Expr),
      Expr.shiftFrom p (instSeq sp t e)
        = instSeq (sp.map (Expr.shiftFrom p)) t (Expr.shiftFrom p e)
  | [], _, _ => rfl
  | a :: sp, t, e => by
    show Expr.shiftFrom p (instSeq sp (t - 1) (e.instantiate1 a t)) = _
    rw [Expr.shiftFrom_instSeq p sp (t - 1) (e.instantiate1 a t),
      Expr.shiftFrom_instantiate1_gen e t]
    rfl

/-- An iterated shift commutes with an instantiation sequence. -/
theorem Expr.shiftFromN_instSeq (p : Nat) :
    ∀ (n : Nat) (sp : List Expr) (t : Nat) (e : Expr),
      Expr.shiftFromN p n (instSeq sp t e)
        = instSeq (sp.map (Expr.shiftFromN p n)) t (Expr.shiftFromN p n e)
  | 0, sp, t, e => by simp [Expr.shiftFromN]
  | n + 1, sp, t, e => by
    show Expr.shiftFrom p (Expr.shiftFromN p n (instSeq sp t e)) = _
    rw [Expr.shiftFromN_instSeq p n sp t e, Expr.shiftFrom_instSeq p]
    simp only [List.map_map]
    rfl

/-- Well-scopedness survives an instantiation sequence at well-scoped
arguments. -/
theorem Expr.instSeq_WScoped {d : Nat} :
    ∀ (sp : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ sp, Expr.WScoped d a) → Expr.WScoped d e → Expr.WScoped d (instSeq sp t e)
  | [], _, _, _, he => he
  | a :: sp, t, _e, hsp, he =>
    Expr.instSeq_WScoped sp (t - 1) (fun x hx => hsp x (List.mem_cons_of_mem _ hx))
      (Expr.WScoped.instantiate1_gen (hsp a List.mem_cons_self) t he)

/-! ## The rule body's spines -/

/-- The recursor's leading spine `p⃗ motive m⃗` in a rule body,
instantiated at the frame's own variables: the parameter and the extra
variables themselves. -/
theorem map_instSeq_directRecPrefixAt (tfvs extras xFvs : List Expr) {nP n nF : Nat}
    (hlenT : tfvs.length = nP) (hlenE : extras.length = n + 1) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true) :
    (directRecPrefixAt nP n nF 0).map
        (fun a => instSeq xFvs (nF - 1) (instSeq (tfvs ++ extras) (nP + n + nF) a))
      = tfvs ++ extras := by
  have hcl : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlen : (tfvs ++ extras).length = nP + n + 1 := by simp [hlenT, hlenE]; omega
  have hlenR : (directRecPrefixAt nP n nF 0).length = nP + n + 1 := by
    simp [directRecPrefixAt, directPsAt]
    omega
  have hlA : (directPsAt (0 + nF + n + 1) nP).length = nP := by simp [directPsAt]
  have hlAB : (directPsAt (0 + nF + n + 1) nP ++ [Expr.bvar (0 + nF + n)]).length = nP + 1 := by
    simp [directPsAt]
  have hget : ∀ k : Nat, k < nP + n + 1 →
      (directRecPrefixAt nP n nF 0)[k]? = some (Expr.bvar (nP + n + nF - k)) := by
    intro k hk
    unfold directRecPrefixAt
    by_cases hkp : k < nP
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      simp only [directPsAt, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (List.range nP).length from by simp; omega),
        List.getElem_range, Option.map_some, Option.some.injEq]
      congr 1
      omega
    · by_cases hkm : k = nP
      · subst hkm
        rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), hlA,
          Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), hlAB]
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem
            (show k - (nP + 1) < (List.range n).length from by simp; omega),
          List.getElem_range, Option.map_some, Option.some.injEq]
        congr 1
        omega
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  by_cases hk : k < nP + n + 1
  · rw [hget k hk, List.getElem?_eq_getElem (show k < (tfvs ++ extras).length from by
      rw [hlen]; omega)]
    simp only [Option.map_some, Option.some.injEq]
    have hb := Expr.instSeq_bvar (tfvs ++ extras) (nP + n + nF) (nP + n + nF - k) hcl
      (by omega) (by rw [hlen]; omega)
    rw [show nP + n + nF - (nP + n + nF - k) = k from by omega,
      List.getElem?_eq_getElem (show k < (tfvs ++ extras).length from by rw [hlen]; omega)] at hb
    rw [← Option.some.inj hb]
    exact Expr.instSeq_eq_self _ _ (hcl _ (List.getElem_mem _))
  · rw [List.getElem?_eq_none (by rw [hlenR]; omega),
      List.getElem?_eq_none (by rw [hlen]; omega)]
    rfl

end Lech
