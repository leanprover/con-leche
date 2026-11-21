module

public import ConLeche.Rules.Rel

@[expose] public section

/-!
# The rules at a refinement (task #469)

`env₁` **refines** `env₂` (`EnvRefines`): every constant `env₁` stores is `env₂`'s constant of
that name, or the axiom of its constant value (its statement: a definition, theorem or opaque
presented without its value), and every table `env₁` stores is `env₂`'s.  `env₂` may store more.

**Every derivation at a refinement is a derivation at the refined environment**
(`Red.refine` and its thirteen siblings, one mutual structural recursion).  Every premise of every
rule reads the environment positively: a constant stored as a given kind (a definition to
unfold, a recursor, a constructor, a family), a constant's stored type (which a statement keeps),
a table entry, or a literal's constants stored.  A statement answers the kind-reads `none`, so
it never makes a premise hold that fails at `env₂`; the one read that looks through a definition
without unfolding it, `isProofFast`'s identity-wrapper walk (`unwrapIdDefs`), stops earlier at a
statement and answers only where `env₂`'s walk answers the same (`proofPW_refine`).

This is the strongest form of "a run at a refinement agrees with the run at the refined
environment" that holds: the RUNS do not agree.  At `env₁` reduction stops at a statement,
`isDefEq` answers `false` where `env₂` unfolds and answers `true`, and a reduction that
succeeds at both can succeed with a different term, since a sub-reduction that stops at a
statement makes the checker take another path (where `two` is a statement, `Nat.add two 1` is
not folded to the literal `3` but unfolded, so ι on it binds a recursor application where `env₂`
binds the literal `2`; `tests/ConLecheTests/RefineTests.lean`).  What carries over is the derivation, so with the bridge
(`Verify/Rules/Bridge.lean`) every accepting run at `env₁` is sound in every model of `env₂`.
-/

namespace ConLeche.Rules

open ConLeche

/-- **`f₁` refines `f₂`**: every constant `f₁` finds is `f₂`'s, or the axiom of its value. -/
def FindRefines (f₁ f₂ : Name → Option ConstantInfo) : Prop :=
  ∀ n ci, f₁ n = some ci → ∃ ci₂, f₂ n = some ci₂ ∧ (ci = ci₂ ∨ ci = .axiomInfo ci₂.toConstantVal)

/-- **`env₁` refines `env₂`**: its constants are `env₂`'s or their statements, its tables
`env₂`'s. -/
structure EnvRefines (env₁ env₂ : Env) : Prop where
  find : FindRefines env₁.find? env₂.find?
  table : ∀ T t, env₁.findTable? T = some t → env₂.findTable? T = some t

variable {f₁ f₂ : Name → Option ConstantInfo}

namespace FindRefines

/-- A constant found keeps its constant value. -/
theorem cv (h : FindRefines f₁ f₂) {n : Name} {ci : ConstantInfo} (hf : f₁ n = some ci) :
    ∃ ci₂, f₂ n = some ci₂ ∧ ci₂.toConstantVal = ci.toConstantVal := by
  obtain ⟨ci₂, h₂, rfl | rfl⟩ := h n ci hf
  · exact ⟨_, h₂, rfl⟩
  · exact ⟨_, h₂, rfl⟩

/-- A constant found that is no axiom is the same constant. -/
theorem same (h : FindRefines f₁ f₂) {n : Name} {ci : ConstantInfo} (hf : f₁ n = some ci)
    (hax : ∀ cv, ci ≠ .axiomInfo cv) : f₂ n = some ci := by
  obtain ⟨ci₂, h₂, rfl | rfl⟩ := h n ci hf
  · exact h₂
  · exact absurd rfl (hax _)

theorem isSome (h : FindRefines f₁ f₂) {n : Name} (hs : (f₁ n).isSome = true) :
    (f₂ n).isSome = true := by
  cases hf : f₁ n with
  | none => rw [hf] at hs; exact nomatch hs
  | some ci =>
    obtain ⟨ci₂, h₂, -⟩ := h n ci hf
    rw [h₂]; rfl

end FindRefines

variable {env₁ env₂ : Env}

namespace EnvRefines

theorem findProj (h : EnvRefines env₁ env₂) {T : Name} {i : Nat} {e : ProjEntry}
    (hp : env₁.findProj? T i = some e) : env₂.findProj? T i = some e := by
  unfold Env.findProj? at hp ⊢
  cases ht : env₁.findTable? T with
  | none => rw [ht] at hp; exact nomatch hp
  | some t => rw [ht] at hp; rw [h.table T t ht]; exact hp

theorem unfoldDefinition (h : EnvRefines env₁ env₂) {e e' : Expr}
    (hu : unfoldDefinition env₁ e = some e') : unfoldDefinition env₂ e = some e' := by
  unfold ConLeche.unfoldDefinition at hu ⊢
  cases hfn : e.getAppFn with
  | const n us =>
    rw [hfn] at hu
    dsimp only at hu ⊢
    cases hf : env₁.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some ci =>
      rw [hf] at hu
      cases ci with
      | defnInfo cv v hint =>
        rw [h.find.same hf (fun _ h => nomatch h)]
        exact hu
      | _ => exact nomatch hu
  | _ => rw [hfn] at hu; exact nomatch hu

theorem natLitStored (h : EnvRefines env₁ env₂) (hs : ConLeche.natLitStored env₁ = true) :
    ConLeche.natLitStored env₂ = true := by
  simp only [ConLeche.natLitStored, Bool.and_eq_true] at hs ⊢
  exact ⟨⟨h.find.isSome hs.1.1, h.find.isSome hs.1.2⟩, h.find.isSome hs.2⟩

theorem strLitStored (h : EnvRefines env₁ env₂) (hs : ConLeche.strLitStored env₁ = true) :
    ConLeche.strLitStored env₂ = true := by
  simp only [ConLeche.strLitStored, Bool.and_eq_true] at hs ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  exact ⟨⟨⟨⟨⟨⟨⟨h.natLitStored hn, h.find.isSome h1⟩, h.find.isSome h2⟩, h.find.isSome h3⟩,
    h.find.isSome h4⟩, h.find.isSome h5⟩, h.find.isSome h6⟩, h.find.isSome h7⟩

theorem etaRescueTable (h : EnvRefines env₁ env₂) {T ctor : Name} {cvj cvT : ConstantVal}
    {caps : IndCaps} {tbl : ProjTable}
    (ht : etaRescueTable? (env₁.findTable? T) ctor cvj cvT caps = some tbl) :
    etaRescueTable? (env₂.findTable? T) ctor cvj cvT caps = some tbl := by
  rw [h.table T tbl (etaRescueTable?_inv ht).1]
  rwa [(etaRescueTable?_inv ht).1] at ht

theorem unitLikeShape (h : EnvRefines env₁ env₂) {w tele : Expr} {n : Nat}
    (hs : ConLeche.unitLikeShape env₁ w = some (tele, n)) :
    ConLeche.unitLikeShape env₂ w = some (tele, n) := by
  unfold ConLeche.unitLikeShape at hs ⊢
  cases hfn : w.getAppFn with
  | const S us =>
    rw [hfn] at hs
    dsimp only at hs ⊢
    cases hf : env₁.find? S with
    | none => rw [hf] at hs; exact nomatch hs
    | some ci =>
      rw [hf] at hs
      cases ci with
      | indInfo cvS caps =>
        rw [h.find.same hf (fun _ h => nomatch h)]
        dsimp only at hs ⊢
        split at hs
        · rename_i hc
          rw [ite_eq_left hc]
          cases ht : env₁.findTable? S with
          | none => rw [ht] at hs; exact nomatch hs
          | some tbl =>
            rw [ht] at hs
            rw [h.table S tbl ht]
            dsimp only at hs ⊢
            split at hs
            · rename_i hl
              rw [ite_eq_left hl]
              cases hc' : env₁.find? tbl.ctor with
              | none => rw [hc'] at hs; exact nomatch hs
              | some ci' =>
                rw [hc'] at hs
                cases ci' with
                | ctorInfo cvC a b =>
                  rw [h.find.same hc' (fun _ h => nomatch h)]
                  exact hs
                | _ => exact nomatch hs
            · exact nomatch hs
        · exact nomatch hs
      | _ => exact nomatch hs
  | _ => rw [hfn] at hs; exact nomatch hs

theorem andRescueSlots (h : EnvRefines env₁ env₂) {c : Name} {nP : Nat}
    (hs : ConLeche.andRescueSlots env₁ c nP = true) : ConLeche.andRescueSlots env₂ c nP = true := by
  simp only [ConLeche.andRescueSlots, andRescueSlotsOf, List.all_eq_true] at hs ⊢
  intro j hj
  have := hs j hj
  cases hp : env₁.findProj? andName j with
  | none => rw [hp] at this; exact nomatch this
  | some e => rw [hp] at this; rw [h.findProj hp]; exact this

theorem ctorFamily (h : EnvRefines env₁ env₂) {induct : Name} {p : ConstantVal × IndCaps}
    (hc : ConLeche.ctorFamily env₁.find? induct = some p) :
    ConLeche.ctorFamily env₂.find? induct = some p := by
  unfold ConLeche.ctorFamily at hc ⊢
  cases hf : env₁.find? induct with
  | none => rw [hf] at hc; exact nomatch hc
  | some ci =>
    rw [hf] at hc
    cases ci with
    | indInfo cvT caps =>
      rw [h.find.same hf (fun _ h => nomatch h)]
      exact hc
    | _ => exact nomatch hc

theorem iotaNoCert (h : EnvRefines env₁ env₂) {isK : Bool} {induct : Name} {n : Nat}
    (hc : ConLeche.iotaNoCert env₁.find? isK induct n = true) :
    ConLeche.iotaNoCert env₂.find? isK induct n = true := by
  unfold ConLeche.iotaNoCert at hc ⊢
  cases isK with
  | true => rfl
  | false =>
    simp only [Bool.false_or] at hc ⊢
    cases hf : ConLeche.ctorFamily env₁.find? induct with
    | none => rw [hf] at hc; exact nomatch hc
    | some p => rw [hf] at hc; rw [h.ctorFamily hf]; exact hc

theorem projGuardRows (h : EnvRefines env₁ env₂) {entry : ProjEntry} {us : List Level}
    {rows : List (Nat × Expr)} (hr : ConLeche.projGuardRows env₁.find? entry us = some rows) :
    ConLeche.projGuardRows env₂.find? entry us = some rows := by
  unfold ConLeche.projGuardRows at hr ⊢
  cases hf : env₁.find? entry.ctor with
  | none => rw [hf] at hr; exact nomatch hr
  | some ci =>
    rw [hf] at hr
    obtain ⟨ci₂, h₂, hcv⟩ := h.find.cv hf
    rw [h₂]
    dsimp only at hr ⊢
    rw [hcv]
    exact hr

end EnvRefines

/-! ## `isProofFast` at a refinement -/

theorem Expr.getAppFn_forallE {d b : Expr} : (Expr.forallE d b).getAppFn = .forallE d b := rfl

/-- Not headed by a constant: where an identity-wrapper walk stops whatever is stored. -/
def NoConstHead (e : Expr) : Prop := ∀ c us, e.getAppFn ≠ .const c us

theorem unwrapIdDefs_refine (h : FindRefines f₁ f₂) :
    ∀ (fuel : Nat) (e : Expr), NoConstHead (unwrapIdDefs f₁ fuel e) →
      unwrapIdDefs f₂ fuel e = unwrapIdDefs f₁ fuel e
  | 0, _, _ => rfl
  | fuel + 1, e, hn => by
    unfold unwrapIdDefs at hn ⊢
    cases hfn : e.getAppFn with
    | const c us =>
      rw [hfn] at hn
      dsimp only at hn ⊢
      cases hf : f₁ c with
      | none => rw [hf] at hn; exact absurd hfn (hn c us)
      | some ci =>
        rw [hf] at hn
        cases ci with
        | defnInfo cv v hint =>
          rw [h.same hf (fun _ h => nomatch h)]
          dsimp only at hn ⊢
          cases hl : lamProj? 0 v with
          | none => rfl
          | some kj =>
            rw [hl] at hn
            dsimp only at hn ⊢
            split <;> split at hn <;>
              first
                | exact unwrapIdDefs_refine h fuel _ hn
                | rfl
                | simp_all
        | _ => exact absurd hfn (hn c us)
    | _ => rfl

theorem peelPisW_refine (h : FindRefines f₁ f₂) :
    ∀ (n : Nat) (t r : Expr), peelPisW f₁ n t = some r → NoConstHead r → peelPisW f₂ n t = some r
  | 0, t, r, hp, hn => by
    simp only [peelPisW, Option.some.injEq] at hp ⊢
    subst hp
    exact unwrapIdDefs_refine h 4 t hn
  | k + 1, .forallE _ b, r, hp, hn => by
    simp only [peelPisW] at hp ⊢
    exact peelPisW_refine h k b r hp hn
  | k + 1, t, r, hp, hn => by
    cases t
    case forallE => simp only [peelPisW] at hp ⊢; exact peelPisW_refine h k _ r hp hn
    all_goals
      simp only [peelPisW] at hp ⊢
      cases hu : unwrapIdDefs f₁ 4 _ with
      | forallE d b =>
        rw [hu] at hp
        rw [unwrapIdDefs_refine h 4 _ (by rw [hu]; intro c us; exact nofun), hu]
        exact peelPisW_refine h k b r hp hn
      | _ => rw [hu] at hp; exact nomatch hp

theorem residualPW_peel_refine (h : FindRefines f₁ f₂) {n : Nat} {t : Expr} {p : PropWhen}
    (hr : residualPW (peelPisW f₁ n t) = some p) : residualPW (peelPisW f₂ n t) = some p := by
  cases hp : peelPisW f₁ n t with
  | none => rw [hp] at hr; exact nomatch hr
  | some r =>
    rw [hp] at hr
    cases r with
    | sort u =>
      rw [peelPisW_refine h n t _ hp (fun c us => nofun)]
      exact hr
    | _ => exact nomatch hr

theorem headTypePW_refine (h : FindRefines f₁ f₂) {root : Expr} {d : Nat} {e : Expr} {n : Nat}
    {p : PropWhen} (hh : headTypePW f₁ root d e n = some p) :
    headTypePW f₂ root d e n = some p := by
  cases e with
  | const I us =>
    simp only [headTypePW] at hh ⊢
    cases hf : f₁ I with
    | none => rw [hf] at hh; exact nomatch hh
    | some ci =>
      rw [hf] at hh
      obtain ⟨ci₂, h₂, hcv⟩ := h.cv hf
      rw [h₂]
      dsimp only at hh ⊢
      rw [hcv]
      split
      · rename_i hl
        simp only [hl, ↓reduceIte] at hh
        cases hq : residualPW (peelPisW f₁ n ci.toConstantVal.type) with
        | none => rw [hq] at hh; exact nomatch hh
        | some q => rw [hq] at hh; rw [residualPW_peel_refine h hq]; exact hh
      · rename_i hl
        simp only [hl, ↓reduceIte] at hh; exact nomatch hh
  | fvar _ ty =>
    simp only [headTypePW] at hh ⊢
    exact residualPW_peel_refine h hh
  | bvar i =>
    simp only [headTypePW] at hh ⊢
    split
    · rename_i hi
      simp only [hi, ↓reduceIte] at hh
      cases hb : root.binderDom (d - 1 - i) with
      | none => rw [hb] at hh; exact nomatch hh
      | some D => rw [hb] at hh; exact residualPW_peel_refine h hh
    · rename_i hi
      simp only [hi, ↓reduceIte] at hh; exact nomatch hh
  | _ => simp [headTypePW] at hh

theorem typeSortPWGo_refine (h : FindRefines f₁ f₂) {root : Expr} :
    ∀ (e : Expr) (d : Nat) {p : PropWhen}, typeSortPWGo f₁ root e d = some p →
      typeSortPWGo f₂ root e d = some p
  | .forallE _ b, d, p, hh => by
    simp only [typeSortPWGo] at hh ⊢
    exact typeSortPWGo_refine h b (d + 1) hh
  | .sort _, _, _, hh => by simpa [typeSortPWGo] using hh
  | e, d, p, hh => by
    cases e
    case forallE => simp only [typeSortPWGo] at hh ⊢; exact typeSortPWGo_refine h _ _ hh
    case sort => simpa [typeSortPWGo] using hh
    all_goals
      simp only [typeSortPWGo] at hh ⊢
      exact headTypePW_refine h hh

theorem typeSortPW_refine (h : FindRefines f₁ f₂) {T : Expr} {p : PropWhen}
    (hh : typeSortPW f₁ T = some p) : typeSortPW f₂ T = some p :=
  typeSortPWGo_refine h T 0 hh

theorem proofPW_refine (h : EnvRefines env₁ env₂) :
    ∀ (a : Expr) {p : PropWhen}, proofPW env₁.find? env₁.findTable? a = some p →
      proofPW env₂.find? env₂.findTable? a = some p
  | .lam _ b, _, hh => by simp only [proofPW] at hh ⊢; exact proofPW_refine h b hh
  | .letE _ _ b, _, hh => by simp only [proofPW] at hh ⊢; exact proofPW_refine h b hh
  | .app f _, _, hh => by simp only [proofPW] at hh ⊢; exact proofPW_refine h f hh
  | .const c us, p, hh => by
    simp only [proofPW, headProofPW] at hh ⊢
    cases hf : env₁.find? c with
    | none => rw [hf] at hh; exact nomatch hh
    | some ci =>
      rw [hf] at hh
      obtain ⟨ci₂, h₂, hcv⟩ := h.find.cv hf
      rw [h₂]
      dsimp only at hh ⊢
      rw [hcv]
      split
      · rename_i hl
        simp only [hl, ↓reduceIte] at hh
        cases hq : typeSortPW env₁.find? ci.toConstantVal.type with
        | none => rw [hq] at hh; exact nomatch hh
        | some q => rw [hq] at hh; rw [typeSortPW_refine h.find hq]; exact hh
      · rename_i hl
        simp only [hl, ↓reduceIte] at hh; exact nomatch hh
  | .fvar _ ty, _, hh => by
    simp only [proofPW, headProofPW] at hh ⊢
    exact typeSortPW_refine h.find hh
  | .sort _, _, hh => by simpa [proofPW, headProofPW] using hh
  | .forallE _ _, _, hh => by simpa [proofPW, headProofPW] using hh
  | .lit _, _, hh => by simpa [proofPW, headProofPW] using hh
  | .proj S i _, p, hh => by
    simp only [proofPW, headProofPW] at hh ⊢
    cases ht : env₁.findTable? S with
    | none => rw [ht] at hh; exact nomatch hh
    | some tbl =>
      rw [ht] at hh
      rw [h.table S tbl ht]
      dsimp only at hh ⊢
      split
      · rename_i hi
        simp only [hi, ↓reduceIte] at hh
        cases hq : typeSortPW env₁.find? (tbl.entry i).body with
        | none => rw [hq] at hh; exact nomatch hh
        | some q => rw [hq] at hh; rw [typeSortPW_refine h.find hq]; exact hh
      · rename_i hi
        simp only [hi, ↓reduceIte] at hh; exact nomatch hh
  | .bvar _, _, hh => by simp [proofPW, headProofPW] at hh

theorem EnvRefines.isProofFast (h : EnvRefines env₁ env₂) {a : Expr}
    (hp : ConLeche.isProofFast env₁.find? env₁.findTable? a = true) :
    ConLeche.isProofFast env₂.find? env₂.findTable? a = true := by
  unfold ConLeche.isProofFast at hp ⊢
  cases hq : proofPW env₁.find? env₁.findTable? a with
  | none => rw [hq] at hp; exact nomatch hp
  | some q => rw [hq] at hp; rw [proofPW_refine h a hq]; exact hp

/-! ## The derivations -/

mutual

/-- **A reduction at a refinement is a reduction at the refined environment.** -/
theorem Red.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {e e' : Expr}, Red env₁ d e e' → Red env₂ d e e'
  | _, _, _, .refl => .refl
  | _, _, _, .trans h₁ h₂ => .trans (Red.refine h h₁) (Red.refine h h₂)
  | _, _, _, .appFn h₁ => .appFn (Red.refine h h₁)
  | _, _, _, .projArg h₁ => .projArg (Red.refine h h₁)
  | _, _, _, .beta => .beta
  | _, _, _, .zeta => .zeta
  | _, _, _, .delta hu => .delta (h.unfoldDefinition hu)
  | _, _, _, .natLit hs => .natLit (h.natLitStored hs)
  | _, _, _, .strLit hs => .strLit (h.strLitStored hs)
  | _, _, _, .natSucc hs hw hn => .natSucc (h.natLitStored hs) (Red.refine h hw) hn
  | _, _, _, .natOp hc hwa hn₁ hwb hn₂ hr =>
    .natOp hc (Red.refine h hwa) hn₁ (Red.refine h hwb) hn₂ hr
  | _, _, _, .proj hent hhead hi hlen hus hctor hcerts =>
    .proj (h.findProj hent) hhead hi hlen hus (h.find.same hctor (fun _ h => nomatch h)) hcerts
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hcase hlv
      hparams hcertR hcertC hres hidx =>
    .iota hhead (h.find.same hrec (fun _ h => nomatch h)) hlen hus (Red.refine h hmajor) hmhead
      (h.find.same hctor (fun _ h => nomatch h)) hrule hmlen (IotaCaseS.refine h hcase) hlv
      (fun hc => DefEqList.refine h (hparams hc)) hcertR (fun hc => CertsF.refine h (hcertC hc))
      hres (fun hc hne => DefEqList.refine h (hidx hc hne))
  | _, _, _, .rescueK hrec hk hctor hind htm htmaj hthead hlv hnP hfab hws
      hb hlv' htf hdf htp http hv hv0 =>
    .rescueK (h.find.same hrec (fun _ h => nomatch h)) hk
      (h.find.same hctor (fun _ h => nomatch h)) (h.find.same hind (fun _ h => nomatch h))
      (Infer.refine h htm) (Red.refine h htmaj) hthead hlv hnP hfab hws hb hlv'
      (Infer.refine h htf) (DefEq.refine h hdf) (Infer.refine h htp) (Infer.refine h http)
      (Red.refine h hv) hv0
  | _, _, _, .rescueEta hrec hctor hind htbl htm htmaj hthead hlen hlv hfab hws hb hlv' =>
    .rescueEta (h.find.same hrec (fun _ h => nomatch h))
      (h.find.same hctor (fun _ h => nomatch h)) (h.find.same hind (fun _ h => nomatch h))
      (h.etaRescueTable htbl) (Infer.refine h htm) (Red.refine h htmaj) hthead hlen hlv hfab hws
      hb hlv'
  | _, _, _, .rescueAnd hrec hctor hind htm htmaj hthead hlen hlv hslots
      hfab hws hb hlv' htf hdf htp http hv hv0 =>
    .rescueAnd (h.find.same hrec (fun _ h => nomatch h))
      (h.find.same hctor (fun _ h => nomatch h)) (h.find.same hind (fun _ h => nomatch h))
      (Infer.refine h htm) (Red.refine h htmaj) hthead hlen hlv (h.andRescueSlots hslots) hfab
      hws hb hlv' (Infer.refine h htf) (DefEq.refine h hdf) (Infer.refine h htp)
      (Infer.refine h http) (Red.refine h hv) hv0

/-- **A definitional equality at a refinement holds at the refined environment.** -/
theorem DefEq.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {a b : Expr}, DefEq env₁ d a b → DefEq env₂ d a b
  | _, _, _, .refl => .refl
  | _, _, _, .symm h₁ => .symm (DefEq.refine h h₁)
  | _, _, _, .redL hr h₁ => .redL (Red.refine h hr) (DefEq.refine h h₁)
  | _, _, _, .sort hs => .sort hs
  | _, _, _, .fvar => .fvar
  | _, _, _, .const hs => .const hs
  | _, _, _, .natZero => .natZero
  | _, _, _, .natSucc h₁ => .natSucc (DefEq.refine h h₁)
  | _, _, _, .forallE hty hbody => .forallE (DefEq.refine h hty) (DefEq.refine h hbody)
  | _, _, _, .lams h₁ => .lams (DefEqLams.refine h h₁)
  | _, _, _, .app hf ha => .app (DefEq.refine h hf) (DefEq.refine h ha)
  | _, _, _, .proj h₁ => .proj (DefEq.refine h h₁)
  | _, _, _, .eta hneu htb hwtb hty hbody ht₁ htB =>
    .eta hneu (Infer.refine h htb) (Red.refine h hwtb) (DefEq.refine h hty)
      (DefEq.refine h hbody) (Infer.refine h ht₁) (DefEq.refine h htB)
  | _, _, _, .proofFast ha hb => .proofFast (h.isProofFast ha) (h.isProofFast hb)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    .proofIrrel (Infer.refine h hta) (Infer.refine h htta) (Red.refine h hu) hu0
      (Infer.refine h htb) (Infer.refine h httb) (Red.refine h hv) hv0
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind htbl heta hetaCtor hplen hus hlps
      hlv hparams hfields =>
    .structEta (Infer.refine h htb) (Red.refine h hwtb) hhead
      (h.find.same hctor (fun _ h => nomatch h)) hlen hthead
      (h.find.same hind (fun _ h => nomatch h)) (h.table _ _ htbl) heta hetaCtor hplen hus hlps
      hlv (DefEqList.refine h hparams) (DefEqList.refine h hfields)
  | _, _, _, .unitLike hta hwta hna hu htb hwtb hnb hd =>
    .unitLike (Infer.refine h hta) (Red.refine h hwta) hna (UnitLike.refine h hu)
      (Infer.refine h htb) (Red.refine h hwtb) hnb (DefEq.refine h hd)
  | _, _, _, .etaExpand hna hnb hta htb hd hx =>
    .etaExpand hna hnb (Infer.refine h hta) (Infer.refine h htb) (DefEq.refine h hd)
      (DefEqExpand.refine h hx)

theorem DefEqExpand.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {a b T : Expr}, DefEqExpand env₁ d a b T → DefEqExpand env₂ d a b T
  | _, _, _, _, .done h₁ => .done (DefEq.refine h h₁)
  | _, _, _, _, .step h₁ => .step (DefEqExpand.refine h h₁)

theorem UnitLike.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {T : Expr}, UnitLike env₁ d T → UnitLike env₂ d T
  | _, _, .pi hr hu => .pi (Red.refine h hr) (UnitLike.refine h hu)
  | _, _, .struct hr hs hf => .struct (Red.refine h hr) (h.unitLikeShape hs) (UnitFields.refine h hf)

theorem UnitFields.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {tele : Expr} {n : Nat}, UnitFields env₁ d tele n → UnitFields env₂ d tele n
  | _, _, _, .nil => .nil
  | _, _, _, .prop hi hr hz hf => .prop (Infer.refine h hi) (Red.refine h hr) hz (UnitFields.refine h hf)
  | _, _, _, .unit hu hf => .unit (UnitLike.refine h hu) (UnitFields.refine h hf)

theorem DefEqLams.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {a b : Expr}, DefEqLams env₁ d a b → DefEqLams env₂ d a b
  | _, _, _, .refl => .refl
  | _, _, _, .inner hty hbody ht₁ ht₂ ht =>
    .inner (DefEq.refine h hty) (DefEq.refine h hbody) (Infer.refine h ht₁) (Infer.refine h ht₂)
      (DefEq.refine h ht)
  | _, _, _, .outer hty hbody => .outer (DefEq.refine h hty) (DefEqLams.refine h hbody)

/-- **An inference at a refinement is an inference at the refined environment.** -/
theorem Infer.refine (h : EnvRefines env₁ env₂) :
    ∀ {g : Grade} {d : Nat} {e t : Expr}, Infer env₁ g d e t → Infer env₂ g d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar hi => .fvar hi
  | g, d, _, _, .const (us := us) hf hus => by
    obtain ⟨ci₂, h₂, hcv⟩ := h.find.cv hf
    have := Infer.const (g := g) (d := d) (us := us) h₂ (by rw [hcv]; exact hus)
    rw [hcv] at this
    exact this
  | _, _, _, _, .natLit hs => .natLit (h.natLitStored hs)
  | _, _, _, _, .strLit hs => .strLit (h.strLitStored hs)
  | _, _, _, _, .forallE hs hu hbs hv =>
    .forallE (Infer.refine h hs) (Red.refine h hu) (Infer.refine h hbs) (Red.refine h hv)
  | _, _, _, _, .lam hs hu hbt =>
    .lam (fun hg => Infer.refine h (hs hg)) (fun hg => Red.refine h (hu hg)) (Infer.refine h hbt)
  | _, _, _, _, .letE hs hu htv hd hb =>
    .letE (fun hg => Infer.refine h (hs hg)) (fun hg => Red.refine h (hu hg))
      (fun hg => Infer.refine h (htv hg)) (fun hg => DefEq.refine h (hd hg)) (Infer.refine h hb)
  | _, _, _, _, .app htf hw hta hd =>
    .app (Infer.refine h htf) (Red.refine h hw) (fun hg => Infer.refine h (hta hg))
      (fun hg => DefEq.refine h (hd hg))
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hg =>
    .proj (Infer.refine h htpe) (Red.refine h hte) hhead (h.findProj hent) hlen hus
      (ProjGuard.refine h hg)

theorem FormerSort.refine (h : EnvRefines env₁ env₂) :
    ∀ {d n : Nat} {e : Expr} {s : Level}, FormerSort env₁ d n e s → FormerSort env₂ d n e s
  | _, _, _, _, .sort hr => .sort (Red.refine h hr)
  | _, _, _, _, .pi hr hrest => .pi (Red.refine h hr) (FormerSort.refine h hrest)

theorem IotaCase.refine (h : EnvRefines env₁ env₂) :
    ∀ {isK : Bool} {induct : Name} {us : List Level} {c3 : Bool},
      IotaCase env₁ isK induct us c3 → IotaCase env₂ isK induct us c3
  | _, _, _, _, .three => .three
  | _, _, _, _, .k => .k
  | _, _, _, _, .never hfam hlen hnz => .never (h.ctorFamily hfam) hlen hnz
  | _, _, _, _, .walk hfam hlen hnone hs hnv =>
    .walk (h.ctorFamily hfam) hlen hnone (FormerSort.refine h hs) hnv

theorem IotaCaseS.refine (h : EnvRefines env₁ env₂) :
    ∀ {isK : Bool} {induct : Name} {us : List Level} {c3 : Bool},
      IotaCaseS env₁ isK induct us c3 → IotaCaseS env₂ isK induct us c3
  | _, _, _, _, .stored hs => .stored (h.iotaNoCert hs)
  | _, _, _, _, .use hc => .use (IotaCase.refine h hc)

theorem GuardRows.refine (h : EnvRefines env₁ env₂) :
    ∀ {guardSort : Level} {rows : List (Nat × Expr)}, GuardRows env₁ guardSort rows →
      GuardRows env₂ guardSort rows
  | _, _, .nil => .nil
  | _, _, .row hi hr hz hrest =>
    .row (Infer.refine h hi) (Red.refine h hr) hz (GuardRows.refine h hrest)

theorem ProjGuard.refine (h : EnvRefines env₁ env₂) :
    ∀ {entry : ProjEntry} {us : List Level}, ProjGuard env₁ entry us → ProjGuard env₂ entry us
  | _, _, .notProp hT hs hz => .notProp (h.find.same hT (fun _ h => nomatch h)) hs hz
  | _, _, .prop hT hs hz hr hg =>
    .prop (h.find.same hT (fun _ h => nomatch h)) hs hz (h.projGuardRows hr)
      (GuardRows.refine h hg)
  | _, _, .never hT hs hf hnv =>
    .never (h.find.same hT (fun _ h => nomatch h)) hs (FormerSort.refine h hf) hnv
  | _, _, .mayVanish hT hs hf hnv hr hg =>
    .mayVanish (h.find.same hT (fun _ h => nomatch h)) hs (FormerSort.refine h hf) hnv
      (h.projGuardRows hr) (GuardRows.refine h hg)

theorem CertsF.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {ty : Expr} {args : List Expr}, CertsF env₁ d ty args → CertsF env₂ d ty args
  | _, _, _, .nil => .nil
  | _, _, _, .cert hta hd hrest =>
    .cert (Infer.refine h hta) (DefEq.refine h hd) (CertsF.refine h hrest)

theorem DefEqList.refine (h : EnvRefines env₁ env₂) :
    ∀ {d : Nat} {as bs : List Expr}, DefEqList env₁ d as bs → DefEqList env₂ d as bs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h₁ hs => .cons (DefEq.refine h h₁) (DefEqList.refine h hs)

end

end ConLeche.Rules
