module

import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step1I
public import ConLeche.Verify.Ground.Step1N
import ConLeche.Verify.Ground.Step3
import ConLeche.Verify.Ground.Step4
public import ConLeche.Verify.EnvWF

public section

/-!
# The run: the induction over the fuel (task #423 soundness, layer (c))

Every transition of `g4Run` keeps the machine invariant `MInv` (the
`step_*` lemmas of `Run.lean` and `Step*.lean`) and the run's flag facts
`RunOK`; a run that ends in `.done` ends in mode 1 at an empty stack, where
the focus says the value's term is an erased reduct of the start term.
The induction (`run_sound`) is one case per branch of `g4Run`, by mode
(`run_mode0` … `run_mode4`).
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached ConLeche.Rules

/-- **The run's claim at fuel `n`**: from a state with the invariant, a run
that finishes leaves a state with the invariant, in mode 1 at the empty
stack, holding the answer. -/
@[expose] def RunSound (env : Env) (t₀ : Expr) (n : Nat) : Prop :=
  ∀ (s : MS) (oc : Nat → Expr) (fl : List Fr), MInv env t₀ oc s fl → RunOK env s.P →
    ∀ {v : Nat} {val : Array Nat} {P' : G4Prog} {sl : Array Nat} {cells st left : Nat},
      s.run env.find? env.findProj? n = .done v val P' sl cells st left →
      ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
        s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr} {n : Nat}
  {v : Nat} {val : Array Nat} {P' : G4Prog} {sl : Array Nat} {cells st left : Nat}

/-- The modes the invariant admits. -/
theorem MInv.mode_le (h : MInv env t₀ oc s fl) : s.mode ≤ 4 := by
  have hf := h.focus
  unfold Focus at hf
  split at hf <;> first | omega | exact hf.elim

/-- The induction hypothesis at a state whose mode the run's arguments spell
as a literal. -/
theorem RunSound.app (ih : RunSound env t₀ n) {s : MS} {m : Nat} (h : MInv env t₀ oc s fl)
    (hR : RunOK env s.P)
    (hrun : g4Run env.find? env.findProj? n s.P s.cel s.val s.ev s.fs s.argA s.slots s.mem s.mH m s.pc
      s.env s.x s.st = .done v val P' sl cells st left)
    (hm : s.mode = m) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  subst hm; exact ih s oc fl h hR hrun

/-- A code node's tag is one of the compiler's. -/
theorem Den.code_le {P : G4Prog} {o : Nat} {e : Expr} (h : Den P o e) : P.code[o]! ≤ 9 := by
  have : ∃ x, P.code[o]? = some x ∧ x ≤ 9 := by
    cases h <;> exact ⟨_, by assumption, by decide⟩
  obtain ⟨x, hx, hle⟩ := this
  rw [getElem!_def, hx]; exact hle

/-- **Mode 0**, evaluating a node. -/
theorem run_mode0 (ih : RunSound env t₀ n) (hR : RunOK env s.P) (h : MInv env t₀ oc s fl)
    (hm : s.mode = 0)
    (hrun : s.run env.find? env.findProj? (n + 1) = .done v val P' sl cells st left) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  unfold MS.run at hrun
  rw [hm, g4Run.eq_2] at hrun
  split at hrun
  next hc => exact ih.app (step_bvar h hm hc) hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_spine h hm hc) hR hrun (by first | rfl | exact hm)
  next hc =>
    split at hrun
    next htop =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htop
      obtain ⟨fl', h'⟩ := step_lam_call h hm hc htop.1 htop.2
      exact ih.app h' hR hrun (by first | rfl | exact hm)
    next => exact ih.app (step_lam_value h hm hc) hR hrun (by first | rfl | exact hm)
  next hc =>
    obtain ⟨oc', h'⟩ := step_let h hm hc
    exact ih.app h' hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_const h hm hc) hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_natLit h hm hc) hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_strLit h hm hc) hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_proj h hm hc) hR hrun (by first | rfl | exact hm)
  next hc =>
    dsimp only at hrun
    split at hrun
    next hs =>
      exact ih.app (step_shared_hit h hm hc (by simpa using hs)) hR hrun (by first | rfl | exact hm)
    next hs =>
      obtain ⟨oc', h'⟩ := step_shared_miss h hm hc (by simpa using hs)
      exact ih.app h' hR hrun (by first | rfl | exact hm)
  next h0 h1 h2 h3 h4 h5 h6 h7 h9 =>
    have hf := h.focus
    simp only [Focus, hm] at hf
    obtain ⟨u, ⟨s0, cs, hd, -⟩, -⟩ := hf
    have := hd.code_le
    have h8 : s.P.code[s.pc]! = 8 := by
      simp only [imp_false] at h0 h1 h2 h3 h4 h5 h6 h7 h9
      omega
    exact ih.app (step_neutral h hm h8) hR hrun (by first | rfl | exact hm)

/-- **Mode 4**, pushing a spine's arguments. -/
theorem run_mode4 (ih : RunSound env t₀ n) (hR : RunOK env s.P) (h : MInv env t₀ oc s fl)
    (hm : s.mode = 4)
    (hrun : s.run env.find? env.findProj? (n + 1) = .done v val P' sl cells st left) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  unfold MS.run at hrun
  rcases hx : s.x with _ | j
  · rw [hm, hx, g4Run.eq_3] at hrun
    exact ih.app (step_args_done h hm hx) hR hrun (by first | rfl | exact hm)
  rw [hm, hx, g4Run.eq_4] at hrun
  split at hrun
  next hc => exact ih.app (step_arg_var h hm hx rfl hc) hR hrun (by first | rfl | exact hm)
  next hc =>
    obtain ⟨oc', h'⟩ := step_arg_lam h hm hx rfl hc
    exact ih.app h' hR hrun (by first | rfl | exact hm)
  next hc =>
    obtain ⟨oc', h'⟩ := step_arg_nat h hm hx rfl hc
    exact ih.app h' hR hrun (by first | rfl | exact hm)
  next hc => exact ih.app (step_arg_neutral h hm hx rfl hc) hR hrun (by first | rfl | exact hm)
  next hc =>
    dsimp only at hrun
    split at hrun
    next hs => exact ih.app (step_arg_const_hit h hm hx rfl hc (by simpa using hs)) hR hrun (by first | rfl | exact hm)
    next =>
      obtain ⟨oc', h'⟩ := step_arg_const_miss h hm hx rfl hc
      exact ih.app h' hR hrun (by first | rfl | exact hm)
  next hc =>
    dsimp only at hrun
    split at hrun
    next hs => exact ih.app (step_arg_shared_hit h hm hx rfl hc (by simpa using hs)) hR hrun (by first | rfl | exact hm)
    next =>
      obtain ⟨oc', h'⟩ := step_arg_shared_miss h hm hx rfl hc
      exact ih.app h' hR hrun (by first | rfl | exact hm)
  next =>
    obtain ⟨oc', h'⟩ := step_arg_thunk h hm hx rfl
    exact ih.app h' hR hrun (by first | rfl | exact hm)

/-- **Mode 2**, entering a cell. -/
theorem run_mode2 (ih : RunSound env t₀ n) (hR : RunOK env s.P) (h : MInv env t₀ oc s fl)
    (hm : s.mode = 2)
    (hrun : s.run env.find? env.findProj? (n + 1) = .done v val P' sl cells st left) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  unfold MS.run at hrun
  rw [hm, g4Run.eq_5] at hrun
  split at hrun
  next hs => exact ih.app (step_enter_value h hm hs) hR hrun (by first | rfl | exact hm)
  next =>
    split at hrun
    next hs => exact ih.app (step_enter_thunk h hm (by simpa using hs)) hR hrun (by first | rfl | exact hm)
    next => exact nomatch hrun

/-- A table entry's tag is one of `g4Entry`'s. -/
theorem Inv.tag_cases {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    {P : G4Prog} (hI : Inv find? findProj? P) {k : Nat} (hk : k < P.kInfo.size) :
    P.kTag[k]? = some 0 ∨ P.kTag[k]? = some 1 ∨ P.kTag[k]? = some 2 ∨ P.kTag[k]? = some 3 ∨
      P.kTag[k]? = some 5 := by
  have he := hI.ents k hk
  unfold EntOK at he
  split at he
  · exact .inr (.inr (.inr (.inr he)))
  · rcases he.2.2.1 with h0 | ⟨h3, -⟩
    · exact .inl h0
    · exact .inr (.inr (.inr (.inl h3)))
  · exact .inr (.inl he.2.1)
  · obtain ⟨-, -, -, -, -, -, ht, -⟩ := he
    exact .inr (.inr (.inl ht))
  · rename_i hn; rw [Array.getElem?_eq_getElem hk] at hn; cases hn

/-- The dispatch's tag at a definition: `0` or `3` (at `pc = 1` the focus
records `3`). -/
theorem MInv.tag03 (h : MInv env t₀ oc s fl) (hm : s.mode = 3)
    {d : Nat} (hd : (if (s.pc == 1) = true then 0 else s.P.kTag[s.x]!) = d)
    (ht : d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 5) :
    s.P.kTag[s.x]? = some 0 ∨ s.P.kTag[s.x]? = some 3 := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hk, h1, -⟩ := hf
  by_cases hp : s.pc = 1
  · exact .inr (h1 hp)
  · have hp' : (s.pc == 1) = false := by simpa using hp
    simp only [hp', Bool.false_eq_true, ↓reduceIte] at hd
    subst hd
    have hs : s.P.kTag.size = s.P.kInfo.size := h.store.prog.sizes
    rcases h.store.prog.tag_cases hk with e | e | e | e | e
    · exact .inl e
    · exact absurd (get!_of_some e) ht.1
    · exact absurd (get!_of_some e) ht.2.1
    · exact .inr e
    · exact absurd (get!_of_some e) ht.2.2

/-- **Mode 3**, dispatching a constant entry. -/
theorem run_mode3 (hwf : EnvWF env) (ih : RunSound env t₀ n) (hR : RunOK env s.P)
    (h : MInv env t₀ oc s fl) (hm : s.mode = 3)
    (hrun : s.run env.find? env.findProj? (n + 1) = .done v val P' sl cells st left) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  have hk : s.x < s.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  have hsz := h.store.prog.szs.1
  have hts : s.P.kTag.size = s.P.kInfo.size := h.store.prog.sizes
  unfold MS.run at hrun
  rw [hm, g4Run.eq_6] at hrun
  generalize hd : (if (s.pc == 1) = true then 0 else s.P.kTag[s.x]!) = d at hrun
  split at hrun
  next =>
    obtain ⟨fl', h'⟩ := step_collect h hm (w0 := 1) (.inl rfl)
    exact ih.app h' hR hrun rfl
  next ht =>
    have ht2 : s.P.kTag[s.x]? = some 2 := by
      split at hd
      · exact absurd hd (by decide)
      · rw [← hd]; exact some_of_lt (by omega)
    have hmI : s.P.kArity[s.x]? = some s.P.kArity[s.x]! := some_of_lt (by omega)
    dsimp only at hrun
    split at hrun
    next =>
      obtain ⟨fl', h'⟩ := step_collect h hm (w0 := 4) (.inr rfl)
      exact ih.app h' hR hrun rfl
    next hna =>
      split at hrun
      next =>
        split at hrun
        next hhit =>
          obtain ⟨fl', h'⟩ := step_memo_hit h hm (n := s.P.kArity[s.x]! + 1) (by omega) (by omega)
            (by simpa using hhit)
          exact ih.app h' hR hrun rfl
        next =>
          split at hrun
          next h4 =>
            obtain ⟨oc', fl', h'⟩ := step_rec_K h hm ht2 hmI (by omega) h4 _
            exact ih.app h' hR hrun rfl
          next =>
            obtain ⟨oc', fl', h'⟩ := step_rec_miss h hm ht2 hmI (by omega) _
            exact ih.app h' hR hrun rfl
      next hg => exact absurd (by decide) hg
  next =>
    obtain ⟨fl', h'⟩ := step_neutral_entry h hm
    exact ih.app h' hR hrun rfl
  next h1 h2 h5 =>
    have h03 := h.tag03 hm hd ⟨h1, h2, h5⟩
    dsimp only at hrun
    split at hrun
    next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have h3 : s.P.kTag[s.x]! = 3 := by
        split at hd
        · omega
        · omega
      obtain ⟨fl', h'⟩ := step_natop_push h hm h3 hc.2
      exact ih.app h' hR hrun rfl
    next =>
      split at hrun
      next =>
        obtain ⟨fl', h'⟩ := step_collect h hm (w0 := 4) (.inr rfl)
        exact ih.app h' hR hrun rfl
      next =>
        split at hrun
        next hc0 =>
          split at hrun
          next c lps us v hi =>
            have h' := step_delta_compile h hm hi
            have hc := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P
              (v.instantiateLevelParams lps us) h.store.prog
            have hR' := (hR.ext (ExtR.refl s.P |>.trans_ext hc.2.1)).ext (ExtR.codes _
              ((g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).2.kCode.set! s.x
                ((g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).1 + 1))
              (g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).2.ruleCode)
            exact ih.app h' hR' hrun hm
          next => exact nomatch hrun
        next hc0 =>
          have hc : s.P.kCode[s.x]! ≠ 0 := by simpa using hc0
          split at hrun
          next hmemo =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hmemo
            split at hrun
            next hhit =>
              obtain ⟨fl', h'⟩ := step_memo_hit h hm (n := g4CountArgs s.fs s.fs.size 0) hmemo.2
                (Nat.le_refl _) (by simpa using hhit)
              exact ih.app h' hR hrun rfl
            next =>
              obtain ⟨oc', fl', h'⟩ := step_delta_miss hwf h hm h03 hc _
              exact ih.app h' hR hrun rfl
          next =>
            exact ih.app (step_delta_body hwf h hm h03 hc) hR hrun rfl
/-- In mode 1 the node registers are not read. -/
theorem MInv.setPcEnv (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (p e : Nat) :
    MInv env t₀ oc { s with pc := p, env := e } fl := by
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  have hf := h.focus
  simp only [Focus, hm] at hf ⊢
  exact hf

/-- **Mode 1**, returning a value to the frames. -/
theorem run_mode1 (hwf : EnvWF env) (ih : RunSound env t₀ n) (hR : RunOK env s.P)
    (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hrun : s.run env.find? env.findProj? (n + 1) = .done v val P' sl cells st left) :
    ∃ (s' : MS) (oc' : Nat → Expr), MInv env t₀ oc' s' [] ∧ RunOK env s'.P ∧ s'.mode = 1 ∧
      s'.x = v ∧ s'.val = val ∧ s'.P = P' ∧ s'.slots = sl ∧ s'.cel.size >>> 2 = cells := by
  unfold MS.run at hrun
  rw [hm, g4Run.eq_7 env.find? env.findProj? s.P s.cel s.val s.ev s.fs s.argA s.slots s.mem s.mH 1 s.pc
    s.env s.x s.st n (by decide) (by decide) (by decide) (by decide)] at hrun
  split at hrun
  next h0 =>
    -- the run is done: the stack is empty
    simp only [G4Out.done.injEq] at hrun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, -⟩ := hrun
    have h0' : s.fs.size = 0 := by simpa using h0
    have hst := h.stack
    rw [h0'] at hst
    cases hst
    exact ⟨s, oc, h, hR, hm, rfl, rfl, rfl, rfl, rfl⟩
  next h0 =>
  have hn : 0 < s.fs.size := by
    have : s.fs.size ≠ 0 := by simpa using h0
    omega
  split at hrun
  next ht =>
    obtain ⟨fl', h'⟩ := step_pop_update h hm hn ht
    exact ih.app h' hR hrun rfl
  next ht =>
    dsimp only at hrun
    split at hrun
    next hv =>
      obtain ⟨h1, hc⟩ := step_arg_enter h hm hv
      obtain ⟨fl', h'⟩ := step_lam_call h1 rfl hc hn ht
      exact ih.app h' hR hrun rfl
    next hv =>
      obtain ⟨fl', h'⟩ := step_arg_ctor h hm hv
      exact ih.app h' hR hrun rfl
    next hv =>
      obtain ⟨fl', h'⟩ := step_arg_pap h hm hv
      exact ih.app h' hR hrun rfl
    next =>
      obtain ⟨fl', h'⟩ := step_arg_pop h hm
      exact ih.app h' hR hrun rfl
  next ht =>
    dsimp only at hrun
    split at hrun
    next hv =>
      split at hrun
      next => exact nomatch hrun
      next hok =>
        have hok' : s.P.natOk = true := by simpa using hok
        split at hrun
        next h0 => exact ih.app (step_iota_zero hR h hm hv hok' h0) hR hrun rfl
        next m hm1 =>
          obtain ⟨oc', h'⟩ := step_iota_succ hR h hm hv hok' hm1
          exact ih.app h' hR hrun rfl
    next hv =>
      split at hrun
      next => exact nomatch hrun
      next hok =>
        have hok' : s.P.strOk = true := by simpa using hok
        have h' := step_iota_str hR h hm hv hok'
        have hc := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P
          (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!) h.store.prog
        exact ih.app h' (hR.ext (ExtR.refl s.P |>.trans_ext hc.2.1)) hrun rfl
    next hv =>
      generalize hk : s.fs[s.fs.size - 4]! = k at hrun
      generalize hri : g4FindRule s.P.rNid s.P.kB[s.val[g4X4 s.x + 1]!]! s.P.kD[k]! s.P.kC[k]! = ri at hrun
      split at hrun
      next => exact nomatch hrun
      next hc1 =>
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at hc1
        split at hrun
        next => exact nomatch hrun
        next hcl =>
          have hcl' : s.val[g4X4 s.x + 3]! = s.P.rCP[ri]! + s.P.rNF[ri]! := by simpa using hcl
          split at hrun
          next => exact nomatch hrun
          next hc3 =>
            have hc3' : s.P.rC3[ri]! = 0 := by simpa using hc3
            split at hrun
            next hrc =>
              split at hrun
              next c lps us mI rP base nr isK isEta hik =>
                have h' := step_iota_compile hwf h hm hn ht hv hk hc1.1 hri hc1.2 hcl' hc3' hik
                have hcp := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P
                  ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us) h.store.prog
                have hR' := (hR.ext (ExtR.refl s.P |>.trans_ext hcp.2.1)).ext (ExtR.codes _
                  (g4Comp env.find? env.findProj? g4CompFuel s.P
                    ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).2.kCode
                  ((g4Comp env.find? env.findProj? g4CompFuel s.P
                    ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).2.ruleCode.set! ri
                    ((g4Comp env.find? env.findProj? g4CompFuel s.P
                      ((s.P.rules[ri]!).rhs.instantiateLevelParams lps us)).1 + 1)))
                exact ih.app (h'.setPcEnv hm 0 0) hR' hrun hm
              next => exact nomatch hrun
            next hrc =>
              have hrc' : s.P.ruleCode[ri]! ≠ 0 := by simpa using hrc
              split at hrun
              next hb =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hb
                obtain ⟨fl', h'⟩ := step_iota_bind hwf h hm hn ht hv hk hc1.1 hri hc1.2 hcl' hc3' hrc'
                  hb.1 hb.2
                exact ih.app h' hR hrun rfl
              next =>
                obtain ⟨fl', h'⟩ := step_iota_frames hwf h hm hn ht hv hk hc1.1 hri hc1.2 hcl' hc3' hrc'
                exact ih.app h' hR hrun rfl
    next hv =>
      split at hrun
      next => exact nomatch hrun
      next =>
        split at hrun
        next => exact nomatch hrun
        next =>
          obtain ⟨fl', h'⟩ := step_iota_pop h hm hn ht
          exact ih.app h' hR hrun rfl
    next =>
      obtain ⟨fl', h'⟩ := step_iota_pop h hm hn ht
      exact ih.app h' hR hrun rfl
  next ht =>
    dsimp only at hrun
    split at hrun
    next =>
      obtain ⟨fl', h'⟩ := step_proj_pop h hm hn ht
      exact ih.app h' hR hrun rfl
    next hpi =>
      have hpi' : s.fs[s.fs.size - 2]! ≠ 0 := by simpa using hpi
      split at hrun
      next hv =>
        -- (the `pAlw` disjunct's `match` is split first; the claim does not read it)
        split at hrun
        all_goals
          split at hrun
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc5⟩, hc6⟩, -⟩ := hc
            obtain ⟨fl', h'⟩ := step_proj_ctor h hm hn ht hpi' hv hc1 hc2 hc3 hc4 hc5 hc6
            exact ih.app h' hR hrun rfl
          · exact nomatch hrun
      next hv =>
        split at hrun
        next => exact nomatch hrun
        next hok =>
          have hok' : s.P.strOk = true := by simpa using hok
          obtain ⟨fl', h'⟩ := step_proj_str hR h hm hn ht hv hok'
          have hc := (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P
            (strLitToConstructor s.P.strs[s.val[g4X4 s.x + 1]!]!) h.store.prog
          exact ih.app h' (hR.ext (ExtR.refl s.P |>.trans_ext hc.2.1)) hrun rfl
      next =>
        obtain ⟨fl', h'⟩ := step_proj_pop h hm hn ht
        exact ih.app h' hR hrun rfl
  next ht =>
    dsimp only at hrun
    split at hrun
    next hv =>
      obtain ⟨fl', h'⟩ := step_succ_lit h hm hn ht hv
      exact ih.app h' hR hrun rfl
    next hv =>
      split at hrun
      next hz =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hz
        obtain ⟨fl', h'⟩ := step_succ_zero hR h hm hn ht hv hz.1 hz.2
        exact ih.app h' hR hrun rfl
      next =>
        split at hrun
        next hs =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          obtain ⟨fl', h'⟩ := step_succ_succ hR h hm hn ht hv hs.1 hs.2
          exact ih.app h' hR hrun rfl
        next =>
          obtain ⟨fl', h'⟩ := step_succ_pop h hm hn ht
          exact ih.app h' hR hrun rfl
    next =>
      obtain ⟨fl', h'⟩ := step_succ_pop h hm hn ht
      exact ih.app h' hR hrun rfl
  next h2 h1 h3 h4 h7 =>
    dsimp only at hrun
    have ht56 := FS.top_lit h.stack hn h1 h2 h3 h4 h7
    -- the engine's reading, as `litRd`/`litM`
    generalize hM : (if s.val[g4X4 s.x]! == 2 then s.val[g4X4 s.x + 1]! else if (if s.val[g4X4 s.x]! == 2 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kZero && s.val[g4X4 s.x + 3]! == 0 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kSucc && s.val[g4X4 s.x + 3]! == 1 then 1 else 2 : Nat) == 0 then 0 else if (if s.val[g4X4 s.x]! == 2 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kZero && s.val[g4X4 s.x + 3]! == 0 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kSucc && s.val[g4X4 s.x + 3]! == 1 then 1 else 2 : Nat) == 1 then s.argA[s.val[g4X4 s.x + 2]!]! else 0 : Nat) = mm at hrun
    generalize hRD : (if s.val[g4X4 s.x]! == 2 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kZero && s.val[g4X4 s.x + 3]! == 0 then 0 else if s.val[g4X4 s.x]! == 1 && s.val[g4X4 s.x + 1]! == s.P.kSucc && s.val[g4X4 s.x + 3]! == 1 then 1 else 2 : Nat) = rd at hrun
    have hM' : litM s.P s.val s.argA s.x = mm := hM
    have hRD' : litRd s.P s.val s.x = rd := hRD
    split at hrun
    next =>
      obtain ⟨fl', h'⟩ := step_lit_succ hR h hm hn ht56 hRD'
      rw [hM'] at h'
      exact ih.app h' hR hrun rfl
    next =>
      split at hrun
      next h5 =>
        have h5' : s.fs[s.fs.size - 1]! &&& 15 = 5 := by simpa using h5
        obtain ⟨fl', h'⟩ := step_natA_lit hR h hm hn h5' hRD'
        rw [hM'] at h'
        exact ih.app h' hR hrun rfl
      next h5 =>
        have h6 : s.fs[s.fs.size - 1]! &&& 15 = 6 := by
          rcases ht56 with e | e
          · exact absurd (by simp [e]) h5
          · exact e
        split at hrun
        next => exact nomatch hrun
        next =>
          split at hrun
          next hk0 =>
            split at hrun
            next => exact nomatch hrun
            next =>
              obtain ⟨fl', h'⟩ := step_natB_nat hR h hm hn h6 hRD' hk0
              rw [hM'] at h'
              exact ih.app h' hR hrun rfl
          next hk1 =>
            obtain ⟨fl', h'⟩ := step_natB_bool hR h hm hn h6 hRD' hk1
            rw [hM'] at h'
            exact ih.app h' hR hrun rfl
          next => exact nomatch hrun
    next =>
      split at hrun
      next h5 =>
        have h5' : s.fs[s.fs.size - 1]! &&& 15 = 5 := by simpa using h5
        obtain ⟨fl', h'⟩ := step_natA_delta h hm hn h5'
        exact ih.app h' hR hrun rfl
      next h5 =>
        have h6 : s.fs[s.fs.size - 1]! &&& 15 = 6 := by
          rcases ht56 with e | e
          · exact absurd (by simp [e]) h5
          · exact e
        obtain ⟨fl', h'⟩ := step_natB_delta h hm hn h6
        exact ih.app h' hR hrun rfl

/-- **The run is sound** (the induction over the fuel): a run from a state
with the invariant that finishes ends in mode 1 at the empty stack, the
invariant holding there. -/
theorem run_sound (hwf : EnvWF env) (t₀ : Expr) : ∀ n, RunSound env t₀ n
  | 0 => fun s _ _ _ _ _ _ _ _ _ _ _ hrun => by
    unfold MS.run at hrun; rw [g4Run.eq_1] at hrun; exact nomatch hrun
  | n + 1 => fun s oc fl h hR _ _ _ _ _ _ _ hrun => by
    have ih := run_sound hwf t₀ n
    have hle := h.mode_le
    rcases hm : s.mode with _ | _ | _ | _ | _ | m
    · exact run_mode0 ih hR h hm hrun
    · exact run_mode1 hwf ih hR h hm hrun
    · exact run_mode2 ih hR h hm hrun
    · exact run_mode3 hwf ih hR h hm hrun
    · exact run_mode4 ih hR h hm hrun
    · omega

end

end ConLeche.Verify.Ground
