import Setlec.Verify.DiscI3
import Setlec.Verify.BinderLoop

/-!
# Interned binder-loop walks (task #72)

Simulation walks relating the interned binder-telescope loops
(`inferLamsI`/`annotatePisI`/`annotateLamsI`,
`Setlec/Kernel/CoreI.lean`) to their pure mirrors
(`Setlec/Verify/BinderLoop.lean`) at the fueled record, and the *tail
compositions*: each loop, in its body-case context, `SimAt`-simulates
the chained body's own tail — the mirror simulation composed with the
loop's soundness against the chained spec (`SimAt.wr`) and the result
scoping recovered from the chained run (`SimAt.wp`).  The value
relation inside the loop walks is denotation only (`RelD`); the tail
compositions restore `RelE`.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Setlec

variable {mode : CheckMode}

open EStore Expr

variable {env : Env} {f : Nat}

/-- Denotation-only result relation for the loop walks. -/
def RelD (s : IState) (j : EIdx) (v : Expr) : Prop :=
  s.store.denoteT j = some v

/-- Pushing on the accumulator array conses on its reversed read
(task #97: the loops keep the opened fvars innermost-**last**; the
mirrors' lists stay innermost-first). -/
theorem toListRev_push {α} (a : Array α) (x : α) :
    (a.push x).toList.reverse = x :: a.toList.reverse := by
  simp

theorem toListRev_singleton {α} (x : α) :
    (#[x] : Array α).toList.reverse = [x] := by
  simp

theorem toListRev_empty {α} :
    (#[] : Array α).toList.reverse = ([] : List α) := by
  simp

/-! ## Stack relations -/

/-- Pointwise relation of `inferLamsI` stack entries. -/
def DenILE (s : IState) : InferLamEntry → InferLamEntryX → Prop
  | (n, tyo, mb), (nx, tyox, mbx) =>
    s.store.denoteN n = some nx ∧ s.store.denoteT tyo = some tyox ∧
    denoteBM s.store.denoteL mb = some mbx

def DenILStk (s : IState) : List InferLamEntry → List InferLamEntryX → Prop
  | [], [] => True
  | e :: r, ex :: rx => DenILE s e ex ∧ DenILStk s r rx
  | _, _ => False

theorem DenILE.mono {s s' : IState} (hext : Ext s.store s'.store)
    {e : InferLamEntry} {ex : InferLamEntryX} (h : DenILE s e ex) :
    DenILE s' e ex := by
  obtain ⟨n, tyo, mb⟩ := e
  obtain ⟨nx, tyox, mbx⟩ := ex
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨denoteN_mono hext h1, denoteT_mono hext h2, denoteBM_mono hext h3⟩

theorem DenILStk.mono {s s' : IState} (hext : Ext s.store s'.store) :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX},
      DenILStk s stk stkx → DenILStk s' stk stkx
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨h.1.mono hext, DenILStk.mono hext h.2⟩

/-- Pointwise relation of annotation-loop stack entries, indexed by
the head entry's binder level (each entry's annotated domain is
well-scoped at its own level, for the out-phase inferences). -/
def DenAStk (s : IState) (d : Nat) :
    List AnnotBinderEntry → List AnnotBinderEntryX → Nat → Prop
  | [], [], _ => True
  | (n, ty', bi) :: r, (nx, tyx', bix) :: rx, j =>
    (s.store.denoteN n = some nx ∧
      denoteBM s.store.denoteL bi = some bix ∧
      s.store.denoteT ty' = some tyx' ∧
      WScoped (d + j) tyx') ∧ DenAStk s d r rx (j - 1)
  | _, _, _ => False

theorem DenAStk.mono {s s' : IState} (hext : Ext s.store s'.store)
    {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat}, DenAStk s d stk stkx j → DenAStk s' d stk stkx j
  | [], [], _, _ => trivial
  | (_, _, _) :: _, (_, _, _) :: _, _, h =>
    ⟨⟨denoteN_mono hext h.1.1, denoteBM_mono hext h.1.2.1,
      denoteT_mono hext h.1.2.2.1,
      h.1.2.2.2⟩,
      DenAStk.mono hext h.2⟩

/-! ## The infer-λ loop walks -/

theorem inferLamsOutI_sim {d : Nat} :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX} {j : Nat}
      {cur : EIdx} {curx : Expr} {prevPw : PropWhen} {s₀ : IState},
      ISOK mode env s₀ → DenILStk s₀ stk stkx →
      s₀.store.denoteT cur = some curx →
      SimAt mode env s₀ RelD (inferLamsOutI mode d stk j cur prevPw)
        (inferLamsOut (m := FueledM) mode d stkx j curx prevPw) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j cur curx prevPw s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenILStk])
  | cons e rest ihOut =>
    obtain ⟨n, tyo, mb⟩ := e
    intro stkx j cur curx prevPw s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenILStk])
    | cons ex rx =>
      obtain ⟨nx, tyox, mbx⟩ := ex
      obtain ⟨⟨hnnm, htyo, hmb⟩, hrest⟩ := hstk
      show SimAt mode env s₀ RelD
        (do
          if mode.verified && !(mb.pw.equiv prevPw) then
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
          let tyAbs ← abstractRangeM tyo d j
          let node ← internI (.forallE n tyAbs cur mb)
          inferLamsOutI mode d rest (j - 1) node mb.pw)
        (do
          if mode.verified && !(mbx.pw.equiv prevPw) then
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
          inferLamsOut (m := FueledM) mode d rx (j - 1)
            (Expr.forallE nx (tyox.abstractRange d j) curx mbx) mbx.pw)
      rw [show mbx.pw = (mb : IBinderMeta).pw from denoteBM_pw hmb]
      split
      · exact SimAt.throw_bind
      refine SimAt.bind_left (abstractRangeM_eff hs htyo)
        (fun s₃ tyAbs hs₃ hext₃ hQab => ?_)
      have hnd : denoteNode s₃.store.denoteT s₃.store.denoteL
          s₃.store.denoteN (.forallE n tyAbs cur mb)
          = some (.forallE nx (tyox.abstractRange d j) curx mbx) := by
        rw [denoteNode, hQab, denoteT_mono hext₃ hcur,
          denoteBM_mono hext₃ hmb, denoteN_mono hext₃ hnnm]
        rfl
      refine SimAt.bind_left (internI_eff hs₃ hnd)
        (fun s₄ node hs₄ hext₄ hQnode => ?_)
      exact ihOut hs₄ (DenILStk.mono (hext₃.trans hext₄) hrest) hQnode

theorem inferLamsLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List InferLamEntry} {stkx : List InferLamEntryX} {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenILStk s₀ stk stkx)
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (inferLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferLamsLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold inferLamsLeafI inferLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  -- the λ-chain guard (task #152): the residual's head shape, read on
  -- both sides of the denotation
  refine SimAt.view ?_
  obtain ⟨nd, hn, hc, hd⟩ :=
    denoteT_some_inv (denoteT_mono (hext₁.trans hext₂) ht)
  rw [hn]
  -- the fold's initial neighbour, resolved per residual head (both
  -- sides read the same head)
  cases nd
  case lam nmN tyN bodyN mbN =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyxx, htyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyxx, hbodyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bmx, hbmx, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nmx, hnmx, rfl⟩ := hd
    dsimp only
    refine SimAt.bind_left (abstractRangeM_eff hs₂ hbtd)
      (fun s₅ cur hs₅ hext₅ hQcur => ?_)
    refine SimAt.view ?_
    rw [Ext.getNode hext₅ hn]
    dsimp only [Expr.lamPw]
    rw [show bmx.pw = (mbN : IBinderMeta).pw from denoteBM_pw hbmx]
    exact inferLamsOutI_sim hs₅
      (DenILStk.mono (((hext₁.trans hext₂)).trans hext₅) hstk) hQcur
  all_goals
    (first | invert_node hd | cases hd)
    dsimp only [Expr.lamPw]
    by_cases hv : mode.verified = true
    case neg =>
      simp only [if_neg hv]
      refine SimAt.bind_left (abstractRangeM_eff hs₂ hbtd)
        (fun s₅ cur hs₅ hext₅ hQcur => ?_)
      refine SimAt.view ?_
      rw [Ext.getNode hext₅ hn]
      dsimp only
      cases hstk0 : stk with
      | nil =>
        cases hstkx0 : stkx with
        | nil =>
          exact inferLamsOutI_sim hs₅ trivial hQcur
        | cons _ _ =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [DenILStk])
      | cons e0 r0 =>
        cases hstkx0 : stkx with
        | nil =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [DenILStk])
        | cons e0x r0x =>
          rw [hstk0, hstkx0] at hstk
          obtain ⟨n0, ty0, mb0⟩ := e0
          obtain ⟨n0x, ty0x, mb0x⟩ := e0x
          dsimp only
          rw [show mb0x.pw = (mb0 : IBinderMeta).pw
            from denoteBM_pw hstk.1.2.2]
          exact inferLamsOutI_sim hs₅
            (DenILStk.mono (((hext₁.trans hext₂)).trans hext₅) hstk)
            hQcur
    simp only [if_pos hv]
    refine SimAt.bind (ih.infer hs₂ hbtd hwbt)
      (fun s₃ btt bttx hs₃ hext₃ hPbtt => ?_)
    obtain ⟨hbttd, hwbtt⟩ := hPbtt
    refine SimAt.bind (ih.whnf hs₃ hbttd hwbtt)
      (fun s₄ wbt wx hs₄ hext₄ hPw => ?_)
    obtain ⟨hwd, hww⟩ := hPw
    refine SimAt.view ?_
    obtain ⟨nd', hn', hc', hd'⟩ := denoteT_some_inv hwd
    rw [hn']
    cases nd' with
    | sort v =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lv, hlv, rfl⟩ := hd'
      dsimp only
      -- the leaf validation (task #161): both sides read the same
      -- datum of the same sort; then the fold, per stack head
      cases hstk0 : stk with
      | nil =>
        cases hstkx0 : stkx with
        | nil =>
          dsimp only
          refine SimAt.bind_left (abstractRangeM_eff hs₄
            (denoteT_mono (hext₃.trans hext₄) hbtd))
            (fun s₅ cur hs₅ hext₅ hQcur => ?_)
          refine SimAt.view ?_
          rw [Ext.getNode ((hext₃.trans hext₄).trans hext₅) hn]
          dsimp only
          exact inferLamsOutI_sim hs₅ trivial hQcur
        | cons _ _ =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [DenILStk])
      | cons e0 r0 =>
        cases hstkx0 : stkx with
        | nil =>
          rw [hstk0, hstkx0] at hstk
          exact absurd hstk (by simp [DenILStk])
        | cons e0x r0x =>
          rw [hstk0, hstkx0] at hstk
          obtain ⟨n0, ty0, mb0⟩ := e0
          obtain ⟨n0x, ty0x, mb0x⟩ := e0x
          dsimp only
          refine SimAt.withStore ?_
          obtain ⟨-, hzeq⟩ := zeronessOfLIGo_spec (st := s₄.store) v
            (memo := {}) PWMemoInv.empty
            (p := (s₄.store.zeronessOfLIGo {} v).1)
            (memo' := (s₄.store.zeronessOfLIGo {} v).2) rfl
          rw [hzeq lv hlv]
          rw [show mb0x.pw = (mb0 : IBinderMeta).pw
            from denoteBM_pw hstk.1.2.2]
          split
          case isFalse => exact SimAt.throw_bind
          refine SimAt.bind_left (abstractRangeM_eff hs₄
            (denoteT_mono (hext₃.trans hext₄) hbtd))
            (fun s₅ cur hs₅ hext₅ hQcur => ?_)
          refine SimAt.view ?_
          rw [Ext.getNode ((hext₃.trans hext₄).trans hext₅) hn]
          dsimp only
          exact inferLamsOutI_sim hs₅
            (DenILStk.mono ((((hext₁.trans hext₂).trans hext₃).trans
              hext₄).trans hext₅) hstk) hQcur
    | bvar i => cases hd'; exact SimAt.throw
    | fvar idx nm tt => invert_node hd'; exact SimAt.throw
    | const nm us => invert_node hd'; exact SimAt.throw
    | app f' a' => invert_node hd'; exact SimAt.throw
    | lam nm tt b mm => invert_node hd'; exact SimAt.throw
    | forallE nm tt b mm => invert_node hd'; exact SimAt.throw
    | letE nm tt vv b => invert_node hd'; exact SimAt.throw
    | lit l => cases hd'; exact SimAt.throw
    | proj sp i e' => invert_node hd'; exact SimAt.throw

theorem inferLamsI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List InferLamEntry} {stkx : List InferLamEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenILStk s₀ stk stkx →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferLams mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt mode env s₀ RelD
      (do
        match ← viewI t with
        | some (.lam n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match ← viewI wtty with
          | some (.sort _) => do
            let fv ← internI (.fvar (d + k) n tyo)
            inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
              (fvs.push fv) ((n, tyo, mb) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ => inferLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv ht
    rw [hn]
    cases nd with
    | lam nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨tyx, hty, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bodyx, hbody, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nmx, hnmx, hd⟩ := hd
      subst hd
      obtain ⟨mbbi, mbpw⟩ := mb
      dsimp only
      obtain rfl : bm = ⟨mbbi, mbpw⟩ := by
        simpa [denoteBM] using hbmDen.symm
      rw [inferLams_succ_lam]
      have hlamL : (Expr.lam nmx tyx bodyx ⟨mbbi, mbpw⟩).instantiateList
          ws = Expr.lam nmx (tyx.instantiateList ws)
            (bodyx.instantiateList ws 1) ⟨mbbi, mbpw⟩ := by
        simp [Expr.instantiateList]
      have hwcomp : WScoped (d + k) (tyx.instantiateList ws)
          ∧ WScoped (d + k) (bodyx.instantiateList ws 1) := by
        rw [hlamL] at hw
        simpa only [WScoped] using hw
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hext₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimAt.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hext₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      refine SimAt.view ?_
      obtain ⟨nd', hn', hc', hd'⟩ := denoteT_some_inv hwd
      rw [hn']
      cases nd' with
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd'
        obtain ⟨lu, hlu, rfl⟩ := hd'
        have hext₁₃ := hext₂.trans hext₃
        have hfvd : denoteNode s₃.store.denoteT s₃.store.denoteL
            s₃.store.denoteN (.fvar (d + k) nm tyo)
            = some (.fvar (d + k) nmx (tyx.instantiateList ws)) := by
          rw [denoteNode, denoteT_mono hext₁₃ hQtyo,
            denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmx]
          rfl
        refine SimAt.bind_left (internI_eff hs₃ hfvd)
          (fun s₄ fv hs₄ hext₄ hQfv => ?_)
        have hextAll := ((hext₁.trans hext₂).trans hext₃).trans hext₄
        have hwopen : WScoped (d + (k + 1))
            (bodyx.instantiateList
              (Expr.fvar (d + k) nmx (tyx.instantiateList ws) :: ws)) := by
          rw [Expr.instantiateList_cons]
          have := WScoped.instantiate1 (n := nmx) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        refine inferLamsI_sim ih fuel hs₄
          (denoteT_mono hextAll hbody)
          (by rw [toListRev_push]
              exact ⟨hQfv, hfvs.mono hextAll⟩)
          (⟨⟨denoteN_mono hextAll hnmx,
            denoteT_mono (hext₁₃.trans hext₄) hQtyo,
            (by
              show denoteBM s₄.store.denoteL ⟨mbbi, mbpw⟩ = some ⟨mbbi, mbpw⟩
              rfl)⟩,
            DenILStk.mono hextAll hstk⟩)
          hwopen
        | bvar i => cases hd'; exact SimAt.throw
        | fvar idx nm' tt => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' tt b mm => invert_node hd'; exact SimAt.throw
        | forallE nm' tt b mm => invert_node hd'; exact SimAt.throw
        | letE nm' tt vv b => invert_node hd'; exact SimAt.throw
        | lit l => cases hd'; exact SimAt.throw
        | proj sp i e' => invert_node hd'; exact SimAt.throw
    | bvar i =>
      cases hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | fvar idx nm tt =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | sort u =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | const nm us =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | app f' a' =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | forallE nm tt b mm =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | letE nm tt vv b =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | lit l =>
      cases hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
    | proj sp i e' =>
      invert_node hd
      rw [inferLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferLamsLeafI_sim ih hs ht hfvs hstk hw

/-! ## The infer-∀ loop walks (task #100 stage 6: the ∀-rule infers
its codomain sort, so the interned side runs a telescope loop) -/

/-- Pointwise denotation of `inferPisI`'s domain-sort stack. -/
def DenLStk (s : IState) :
    List (LIdx × PropWhen) → List (Level × PropWhen) → Prop
  | [], [] => True
  | (u, pw) :: r, (ux, pwx) :: rx =>
    (s.store.denoteL u = some ux ∧ pw = pwx) ∧ DenLStk s r rx
  | _, _ => False

theorem DenLStk.mono {s s' : IState} (hext : Ext s.store s'.store) :
    ∀ {stk : List (LIdx × PropWhen)} {stkx : List (Level × PropWhen)},
      DenLStk s stk stkx → DenLStk s' stk stkx
  | [], [], _ => trivial
  | (_, _) :: _, (_, _) :: _, h =>
    ⟨⟨denoteL_mono hext h.1.1, h.1.2⟩, DenLStk.mono hext h.2⟩

theorem inferPisOutI_sim :
    ∀ {stk : List (LIdx × PropWhen)} {stkx : List (Level × PropWhen)}
      {v : LIdx} {lv : Level} {memo : EStore.PWMemo} {s₀ : IState},
      ISOK mode env s₀ → DenLStk s₀ stk stkx →
      s₀.store.denoteL v = some lv →
      PWMemoInv s₀.store memo →
      SimAt mode env s₀
        (fun s iv ivx => s.store.denoteL iv = some ivx)
        (inferPisOutI mode stk v memo)
        (inferPisOut (m := FueledM) mode stkx lv) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx v lv memo s₀ hs hstk hv _hminv
    cases stkx with
    | nil => exact SimAt.pure hs hv
    | cons ux rx => exact absurd hstk (by simp [DenLStk])
  | cons upw rest ih =>
    obtain ⟨u, pw⟩ := upw
    intro stkx v lv memo s₀ hs hstk hv hminv
    cases stkx with
    | nil => exact absurd hstk (by simp [DenLStk])
    | cons uxp rx =>
      obtain ⟨ux, pwx⟩ := uxp
      obtain ⟨⟨hu, rfl⟩, hrest⟩ := hstk
      show SimAt mode env s₀ _
        (do
          let (pv, memo) ← withStore fun st =>
            st.zeronessOfLIGo memo v
          if mode.verified && !(pv.equiv pw) then
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
          internLM (.imax u v) >>= fun v' =>
            inferPisOutI mode rest v' memo)
        (do
          if mode.verified && !((Level.zeronessOf lv).equiv pw) then
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
          inferPisOut (m := FueledM) mode rx (.imax ux lv))
      refine SimAt.withStore ?_
      obtain ⟨hminv', hzeq⟩ := zeronessOfLIGo_spec (st := s₀.store) v
        (memo := memo) hminv
        (p := (s₀.store.zeronessOfLIGo memo v).1)
        (memo' := (s₀.store.zeronessOfLIGo memo v).2) rfl
      dsimp only
      rw [hzeq lv hv]
      split
      · exact SimAt.throw_bind
      refine SimAt.bind_left (internLM_eff hs (n := .imax u v)
        (l := .imax ux lv) (by rw [denoteLNode, hu, hv]; rfl))
        (fun s₁ v' hs₁ hext₁ hv' => ?_)
      exact ih (stkx := rx) (lv := .imax ux lv) hs₁
        (DenLStk.mono hext₁ hrest) hv' (PWMemoInv.mono hext₁ hminv')

theorem inferPisLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List (LIdx × PropWhen)} {stkx : List (Level × PropWhen)}
    {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenLStk s₀ stk stkx)
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (inferPisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferPisLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold inferPisLeafI inferPisLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimAt.bind (ih.whnf hs₂ hbtd hwbt)
    (fun s₃ wbt wx hs₃ hext₃ hPw => ?_)
  obtain ⟨hwd, hww⟩ := hPw
  refine SimAt.view ?_
  obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv hwd
  rw [hn]
  cases nd with
  | sort v =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lv, hlv, rfl⟩ := hd
    dsimp only
    refine SimAt.bind (inferPisOutI_sim hs₃
      (DenLStk.mono ((hext₁.trans hext₂).trans hext₃) hstk) hlv
      PWMemoInv.empty) (fun s₄ iv ivx hs₄ hext₄ hiv => ?_)
    exact SimAt.of_eff (internI_eff hs₄ (n := .sort iv)
      (x := .sort ivx) (by rw [denoteNode, hiv]; rfl))
      _ (fun s r hQ => hQ)
  | bvar i => cases hd; exact SimAt.throw
  | fvar idx nm tt => invert_node hd; exact SimAt.throw
  | const nm us => invert_node hd; exact SimAt.throw
  | app f' a' => invert_node hd; exact SimAt.throw
  | lam nm tt b mm => invert_node hd; exact SimAt.throw
  | forallE nm tt b mm => invert_node hd; exact SimAt.throw
  | letE nm tt vv b => invert_node hd; exact SimAt.throw
  | lit l => cases hd; exact SimAt.throw
  | proj sp i e' => invert_node hd; exact SimAt.throw

theorem inferPisI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List (LIdx × PropWhen)} {stkx : List (Level × PropWhen)}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenLStk s₀ stk stkx →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs
          stk)
        (inferPis mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferPisLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt mode env s₀ RelD
      (do
        match ← viewI t with
        | some (.forallE n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match ← viewI wtty with
          | some (.sort u) => do
            let fv ← internI (.fvar (d + k) n tyo)
            inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel body
              (k + 1) (fvs.push fv) ((u, mb.pw) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ =>
          inferPisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs
            stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv ht
    rw [hn]
    cases nd with
    | forallE nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨tyx, hty, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bodyx, hbody, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nmx, hnmx, hd⟩ := hd
      subst hd
      rw [inferPis_succ_pi]
      have hpiL : (Expr.forallE nmx tyx bodyx bm).instantiateList
          ws = Expr.forallE nmx (tyx.instantiateList ws)
            (bodyx.instantiateList ws 1) bm := by
        simp [Expr.instantiateList]
      have hwcomp : WScoped (d + k) (tyx.instantiateList ws)
          ∧ WScoped (d + k) (bodyx.instantiateList ws 1) := by
        rw [hpiL] at hw
        simpa only [WScoped] using hw
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.infer hs₁ hQtyo hwcomp.1)
        (fun s₂ tty ttyx hs₂ hext₂ hPtty => ?_)
      obtain ⟨httyd, hwtty⟩ := hPtty
      refine SimAt.bind (ih.whnf hs₂ httyd hwtty)
        (fun s₃ wtty wx hs₃ hext₃ hPw => ?_)
      obtain ⟨hwd, hww⟩ := hPw
      refine SimAt.view ?_
      obtain ⟨nd', hn', hc', hd'⟩ := denoteT_some_inv hwd
      rw [hn']
      cases nd' with
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd'
        obtain ⟨lu, hlu, rfl⟩ := hd'
        have hext₁₃ := hext₂.trans hext₃
        have hfvd : denoteNode s₃.store.denoteT s₃.store.denoteL
            s₃.store.denoteN (.fvar (d + k) nm tyo)
            = some (.fvar (d + k) nmx (tyx.instantiateList ws)) := by
          rw [denoteNode, denoteT_mono hext₁₃ hQtyo,
            denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmx]
          rfl
        refine SimAt.bind_left (internI_eff hs₃ hfvd)
          (fun s₄ fv hs₄ hext₄ hQfv => ?_)
        have hextAll := ((hext₁.trans hext₂).trans hext₃).trans hext₄
        have hwopen : WScoped (d + (k + 1))
            (bodyx.instantiateList
              (Expr.fvar (d + k) nmx (tyx.instantiateList ws) :: ws)) := by
          rw [Expr.instantiateList_cons]
          have := WScoped.instantiate1 (n := nmx) hwcomp.1 0 hwcomp.2
          simpa [Nat.add_assoc] using this
        exact inferPisI_sim ih fuel hs₄
          (denoteT_mono hextAll hbody)
          (by rw [toListRev_push]
              exact ⟨hQfv, hfvs.mono hextAll⟩)
          ⟨⟨denoteL_mono hext₄ hlu,
            (denoteBM_pw hbmDen).symm⟩, DenLStk.mono hextAll hstk⟩
          hwopen
      | bvar i => cases hd'; exact SimAt.throw
      | fvar idx nm' tt => invert_node hd'; exact SimAt.throw
      | const nm' us => invert_node hd'; exact SimAt.throw
      | app f' a' => invert_node hd'; exact SimAt.throw
      | lam nm' tt b mm => invert_node hd'; exact SimAt.throw
      | forallE nm' tt b mm => invert_node hd'; exact SimAt.throw
      | letE nm' tt vv b => invert_node hd'; exact SimAt.throw
      | lit l => cases hd'; exact SimAt.throw
      | proj sp i e' => invert_node hd'; exact SimAt.throw
    | bvar i =>
      cases hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | fvar idx nm tt =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | sort u =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | const nm us =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | app f' a' =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | lam nm tt b mm =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | letE nm tt vv b =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | lit l =>
      cases hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw
    | proj sp i e' =>
      invert_node hd
      rw [inferPis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact inferPisLeafI_sim ih hs ht hfvs hstk hw

/-! ## The ∀-annotation loop walks -/

theorem annotateBindersOutI_sim
    {mk : NIdx → EIdx → EIdx → IBinderMeta → ENode}
    {mkX : Name → Expr → Expr → BinderMeta → Expr}
    (hmk : ∀ (s : IState) (n : NIdx) (nx : Name) (ty : EIdx) (tyx : Expr)
      (b : EIdx) (bx : Expr) (mi : IBinderMeta) (mx : BinderMeta),
      s.store.denoteN n = some nx → s.store.denoteT ty = some tyx →
      s.store.denoteT b = some bx →
      denoteBM s.store.denoteL mi = some mx →
      denoteNode s.store.denoteT s.store.denoteL s.store.denoteN
        (mk n ty b mi) = some (mkX nx tyx bx mx)) {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat} {pw? : Option PropWhen} {cur : EIdx} {curx : Expr}
      {s₀ : IState},
      ISOK mode env s₀ → DenAStk s₀ d stk stkx j →
      s₀.store.denoteT cur = some curx →
      SimAt mode env s₀ RelD (annotateBindersOutI mk d pw? stk j cur)
        (annotateBindersOut (m := FueledM) mkX d pw? stkx j curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j pw? cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenAStk])
  | cons e rest ihOut =>
    obtain ⟨n, ty', bi⟩ := e
    intro stkx j pw? cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenAStk])
    | cons ex rx =>
      obtain ⟨nx, tyx', bix⟩ := ex
      obtain ⟨⟨hnnm, hbmr, hty', hwty'⟩, hrest⟩ := hstk
      show SimAt mode env s₀ RelD
        (do
          let tyAbs ← abstractRangeM ty' d j
          let node ← internI (mk n tyAbs cur (annotBinderMetaI pw? bi))
          annotateBindersOutI mk d
            (pw?.map fun _ => (annotBinderMetaI pw? bi).pw)
            rest (j - 1) node)
        (annotateBindersOut (m := FueledM) mkX d
          (pw?.map fun _ => (annotBinderMeta pw? bix).pw) rx (j - 1)
          (mkX nx (tyx'.abstractRange d j) curx (annotBinderMeta pw? bix)))
      -- task #161 P5: `denoteBM` is the identity on both fields, so the
      -- two folds thread the same datum (`denoteBM_annotBinderMeta`)
      rw [show (pw?.map fun _ => (annotBinderMetaI pw? bi).pw)
          = (pw?.map fun _ => (annotBinderMeta pw? bix).pw) from by
        have hpw : bix.pw = bi.pw := denoteBM_pw hbmr
        cases pw? with
        | none => rfl
        | some p =>
          simp only [Option.map_some, annotBinderMetaI, annotBinderMeta, hpw]
          split <;> simp [hpw]]
      refine SimAt.bind_left (abstractRangeM_eff hs hty')
        (fun s₁ tyAbs hs₁ hext₁ hQab => ?_)
      have hnd : denoteNode s₁.store.denoteT s₁.store.denoteL
          s₁.store.denoteN (mk n tyAbs cur (annotBinderMetaI pw? bi))
          = some (mkX nx (tyx'.abstractRange d j) curx
              (annotBinderMeta pw? bix)) :=
        hmk s₁ n nx tyAbs (tyx'.abstractRange d j) cur curx
          (annotBinderMetaI pw? bi) (annotBinderMeta pw? bix)
          (denoteN_mono hext₁ hnnm) hQab (denoteT_mono hext₁ hcur)
          (denoteBM_annotBinderMeta pw? (denoteBM_mono hext₁ hbmr))
      refine SimAt.bind_left (internI_eff hs₁ hnd)
        (fun s₂ node hs₂ hext₂ hQnode => ?_)
      exact ihOut hs₂
        (DenAStk.mono (hext₁.trans hext₂) hrest) hQnode

/-- **The telescope datum's walk (task #161 P5).**  Both sides read the
annotated residual's head first — a ∀ residual hands on its own
datum (the chain rule) — and only otherwise pay the one inference the
telescope's collapse needs. -/
theorem annotatePisPwI_sim (ih : SSimI mode env f) {d k : Nat}
    {leaf' : EIdx} {leafx : Expr} {s₀ : IState}
    (hs : ISOK mode env s₀) (hl : s₀.store.denoteT leaf' = some leafx)
    (hw : WScoped (d + k) leafx) :
    SimAt mode env s₀
      (fun _ (v : Option PropWhen) (vx : Option PropWhen) => v = vx)
      (annotatePisPwI mode (coreKnotI mode (mkFEnv env) f) d k leaf')
      (annotatePisPw mode (fueledFns mode env) d k leafx) := by
  unfold annotatePisPwI annotatePisPw
  by_cases hv : mode.verified = true
  case neg =>
    simp only [if_neg hv]
    exact SimAt.pure hs rfl
  simp only [if_pos hv]
  refine SimAt.view ?_
  obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv hl
  rw [hn]
  cases nd
  case forallE nmN tyN bodyN mbN =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyxx, htyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyxx, hbodyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bmx, hbmx, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nmx, hnmx, rfl⟩ := hd
    dsimp only [Expr.forallPw]
    rw [show bmx.pw = (mbN : IBinderMeta).pw from denoteBM_pw hbmx]
    exact SimAt.pure hs rfl
  all_goals
    (first | invert_node hd | cases hd)
    dsimp only [Expr.forallPw]
    refine SimAt.bind (ih.infer hs hl hw)
      (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
    obtain ⟨hbtd, hwbt⟩ := hPbt
    refine SimAt.bind (ih.whnf hs₂ hbtd hwbt)
      (fun s₃ wbt wx hs₃ hext₃ hPw => ?_)
    obtain ⟨hwd, hww⟩ := hPw
    refine SimAt.view ?_
    obtain ⟨nd', hn', hc', hd'⟩ := denoteT_some_inv hwd
    rw [hn']
    cases nd'
    case sort v =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lv, hlv, rfl⟩ := hd'
      dsimp only
      refine SimAt.withStore ?_
      obtain ⟨-, hzeq⟩ := zeronessOfLIGo_spec (st := s₃.store) v
        (memo := {}) PWMemoInv.empty
        (p := (s₃.store.zeronessOfLIGo {} v).1)
        (memo' := (s₃.store.zeronessOfLIGo {} v).2) rfl
      rw [hzeq lv hlv]
      exact SimAt.pure hs₃ rfl
    all_goals
      (first | invert_node hd' | cases hd')
      exact SimAt.throw

/-- The λ twin of `annotatePisPwI_sim`. -/
theorem annotateLamsPwI_sim (ih : SSimI mode env f) {d k : Nat}
    {leaf' : EIdx} {leafx : Expr} {s₀ : IState}
    (hs : ISOK mode env s₀) (hl : s₀.store.denoteT leaf' = some leafx)
    (hw : WScoped (d + k) leafx) :
    SimAt mode env s₀
      (fun _ (v : Option PropWhen) (vx : Option PropWhen) => v = vx)
      (annotateLamsPwI mode (coreKnotI mode (mkFEnv env) f) d k leaf')
      (annotateLamsPw mode (fueledFns mode env) d k leafx) := by
  unfold annotateLamsPwI annotateLamsPw
  by_cases hv : mode.verified = true
  case neg =>
    simp only [if_neg hv]
    exact SimAt.pure hs rfl
  simp only [if_pos hv]
  refine SimAt.view ?_
  obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv hl
  rw [hn]
  cases nd
  case lam nmN tyN bodyN mbN =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyxx, htyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyxx, hbodyx, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bmx, hbmx, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nmx, hnmx, rfl⟩ := hd
    dsimp only [Expr.lamPw]
    rw [show bmx.pw = (mbN : IBinderMeta).pw from denoteBM_pw hbmx]
    exact SimAt.pure hs rfl
  all_goals
    (first | invert_node hd | cases hd)
    dsimp only [Expr.lamPw]
    refine SimAt.bind (ih.infer hs hl hw)
      (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
    obtain ⟨hbtd, hwbt⟩ := hPbt
    refine SimAt.bind (ih.infer hs₂ hbtd hwbt)
      (fun s₃ btt bttx hs₃ hext₃ hPbtt => ?_)
    obtain ⟨hbttd, hwbtt⟩ := hPbtt
    refine SimAt.bind (ih.whnf hs₃ hbttd hwbtt)
      (fun s₄ wbtt wx hs₄ hext₄ hPw => ?_)
    obtain ⟨hwd, hww⟩ := hPw
    refine SimAt.view ?_
    obtain ⟨nd', hn', hc', hd'⟩ := denoteT_some_inv hwd
    rw [hn']
    cases nd'
    case sort v =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lv, hlv, rfl⟩ := hd'
      dsimp only
      refine SimAt.withStore ?_
      obtain ⟨-, hzeq⟩ := zeronessOfLIGo_spec (st := s₄.store) v
        (memo := {}) PWMemoInv.empty
        (p := (s₄.store.zeronessOfLIGo {} v).1)
        (memo' := (s₄.store.zeronessOfLIGo {} v).2) rfl
      rw [hzeq lv hlv]
      exact SimAt.pure hs₄ rfl
    all_goals
      (first | invert_node hd' | cases hd')
      exact SimAt.throw

theorem annotatePisLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenAStk s₀ d stk stkx (k - 1))
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (annotatePisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotatePisLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold annotatePisLeafI annotatePisLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  -- task #161 P5: the telescope's datum, computed once on the annotated
  -- residual, then threaded outward by the rebuild fold
  refine SimAt.bind (annotatePisPwI_sim ih hs₂ hld hwl)
    (fun s₄ pw? pw?x hs₄ hext₄ hPpw => ?_)
  subst hPpw
  refine SimAt.bind_left (abstractRangeM_eff hs₄ (denoteT_mono hext₄ hld))
    (fun s₅ cur hs₅ hext₅ hQcur => ?_)
  exact annotateBindersOutI_sim
    (fun s n nx ty tyx b bx mi mx hn hty hb hbm => by
      rw [denoteNode, hty, hb, hbm, hn]; rfl)
    hs₅
    (DenAStk.mono (((hext₁.trans hext₂).trans hext₄).trans hext₅) hstk)
    hQcur

theorem annotatePisI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (annotatePis mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt mode env s₀ RelD
      (do
        match ← viewI t with
        | some (.forallE n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI mode (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb) :: stk)
        | _ => annotatePisLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv ht
    rw [hn]
    cases nd with
    | forallE nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨tyx, hty, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bodyx, hbody, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nmx, hnmx, hd⟩ := hd
      subst hd
      rw [annotatePis_succ_pi]
      have hpiL : (Expr.forallE nmx tyx bodyx bm).instantiateList ws
          = Expr.forallE nmx (tyx.instantiateList ws)
            (bodyx.instantiateList ws 1) bm := by
        simp [Expr.instantiateList]
      have hwcomp : WScoped (d + k) (tyx.instantiateList ws)
          ∧ WScoped (d + k) (bodyx.instantiateList ws 1) := by
        rw [hpiL] at hw
        simpa only [WScoped] using hw
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hext₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      have hfvd : denoteNode s₂.store.denoteT s₂.store.denoteL
          s₂.store.denoteN (.fvar (d + k) nm ty')
          = some (.fvar (d + k) nmx tyx') := by
        rw [denoteNode, hty'd,
          denoteN_mono (hext₁.trans hext₂) hnmx]
        rfl
      refine SimAt.bind_left (internI_eff hs₂ hfvd)
        (fun s₃ fv hs₃ hext₃ hQfv => ?_)
      have hextAll := (hext₁.trans hext₂).trans hext₃
      have hwopen : WScoped (d + (k + 1))
          (bodyx.instantiateList (Expr.fvar (d + k) nmx tyx' :: ws)) := by
        rw [Expr.instantiateList_cons]
        have := WScoped.instantiate1 (n := nmx)
          (WScoped.mono (Nat.le_refl _) hwty') 0 hwcomp.2
        simpa [Nat.add_assoc] using this
      refine annotatePisI_sim ih fuel hs₃ (denoteT_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          denoteBM_mono hextAll hbmDen, denoteT_mono hext₃ hty'd,
          (by simpa using hwty')⟩,
          (by simpa using DenAStk.mono hextAll hstk)⟩)
        hwopen
    | bvar i =>
      cases hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | fvar idx nm tt =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | sort u =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | const nm us =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | app f' a' =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | lam nm tt b mm =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | letE nm tt vv b =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | lit l =>
      cases hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
    | proj sp i e' =>
      invert_node hd
      rw [annotatePis_succ_ne_pi _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotatePisLeafI_sim ih hs ht hfvs hstk hw

/-! ## The λ-annotation loop walks -/

theorem annotateLamsLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenAStk s₀ d stk stkx (k - 1))
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (annotateLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotateLamsLeaf mode (fueledFns mode env) d tx k ws stkx) := by
  unfold annotateLamsLeafI annotateLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  -- task #161 P5: the telescope's datum, computed once on the annotated
  -- residual, then threaded outward by the rebuild fold
  refine SimAt.bind (annotateLamsPwI_sim ih hs₂ hld hwl)
    (fun s₄ pw? pw?x hs₄ hext₄ hPpw => ?_)
  subst hPpw
  refine SimAt.bind_left (abstractRangeM_eff hs₄ (denoteT_mono hext₄ hld))
    (fun s₆ cur hs₆ hext₆ hQcur => ?_)
  exact annotateBindersOutI_sim
    (fun s n nx ty tyx b bx mi mx hn hty hb hbm => by
      rw [denoteNode, hty, hb, hbm, hn]; rfl)
    hs₆
    (DenAStk.mono (((hext₁.trans hext₂).trans hext₄).trans hext₆) hstk)
    hQcur

theorem annotateLamsI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (annotateLams mode (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt mode env s₀ RelD
      (do
        match ← viewI t with
        | some (.lam n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI mode (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb) :: stk)
        | _ => annotateLamsLeafI mode (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denoteT_some_inv ht
    rw [hn]
    cases nd with
    | lam nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨tyx, hty, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bodyx, hbody, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nmx, hnmx, hd⟩ := hd
      subst hd
      rw [annotateLams_succ_lam]
      have hlamL : (Expr.lam nmx tyx bodyx bm).instantiateList ws
          = Expr.lam nmx (tyx.instantiateList ws)
            (bodyx.instantiateList ws 1) bm := by
        simp [Expr.instantiateList]
      have hwcomp : WScoped (d + k) (tyx.instantiateList ws)
          ∧ WScoped (d + k) (bodyx.instantiateList ws 1) := by
        rw [hlamL] at hw
        simpa only [WScoped] using hw
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hext₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      have hfvd : denoteNode s₂.store.denoteT s₂.store.denoteL
          s₂.store.denoteN (.fvar (d + k) nm ty')
          = some (.fvar (d + k) nmx tyx') := by
        rw [denoteNode, hty'd,
          denoteN_mono (hext₁.trans hext₂) hnmx]
        rfl
      refine SimAt.bind_left (internI_eff hs₂ hfvd)
        (fun s₃ fv hs₃ hext₃ hQfv => ?_)
      have hextAll := (hext₁.trans hext₂).trans hext₃
      have hwopen : WScoped (d + (k + 1))
          (bodyx.instantiateList (Expr.fvar (d + k) nmx tyx' :: ws)) := by
        rw [Expr.instantiateList_cons]
        have := WScoped.instantiate1 (n := nmx) hwty' 0 hwcomp.2
        simpa [Nat.add_assoc] using this
      refine annotateLamsI_sim ih fuel hs₃ (denoteT_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          denoteBM_mono hextAll hbmDen, denoteT_mono hext₃ hty'd,
          (by simpa using hwty')⟩,
          (by simpa using DenAStk.mono hextAll hstk)⟩)
        hwopen
    | bvar i =>
      cases hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | fvar idx nm tt =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | sort u =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | const nm us =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | app f' a' =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | forallE nm tt b mm =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | letE nm tt vv b =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | lit l =>
      cases hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
    | proj sp i e' =>
      invert_node hd
      rw [annotateLams_succ_ne_lam _ (fun _ _ _ _ h => Expr.noConfusion h)]
      exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw

/-! ## Tail compositions: the loops against the chained bodies' own
tails, with the result scoping recovered from the chained run -/

private theorem inferLamTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx bodyx : Expr) (mbx : BinderMeta) (F : Nat) :
    ((do
      let bt ← (fueledFns mode env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx))
      if mode.verified then
        match bodyx.lamPw with
        | some pwI =>
          unless mbx.pw.equiv pwI do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
        | none => do
          let btt ← (fueledFns mode env).infer (d + 1) bt
          let vb ← ensureSort (fueledFns mode env) env (d + 1) btt
          unless (Level.zeronessOf vb).equiv mbx.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
      pure (Expr.forallE nm tyx (bt.abstract1 d) mbx)) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => (do
          if mode.verified then
            match bodyx.lamPw with
            | some pwI =>
              unless mbx.pw.equiv pwI do
                throw (.notImplemented
                  "sort-annotation mismatch (lam-cod-chain)")
            | none => do
              let btt ← inferTypeCore mode env F (d + 1) bt
              let vb ← ensureSortCore mode env F (d + 1) btt
              unless (Level.zeronessOf vb).equiv mbx.pw do
                throw (.notImplemented
                  "sort-annotation mismatch (lam-cod-leaf)")
          pure (Expr.forallE nm tyx (bt.abstract1 d) mbx))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  by_cases hv : mode.verified = true
  case neg => rw [if_neg hv, if_neg hv]; rfl
  rw [if_pos hv, if_pos hv]
  cases hbp : bodyx.lamPw with
  | some pwI =>
    dsimp only
    by_cases hc : mbx.pw.equiv pwI = true
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl
  | none =>
    dsimp only
    rw [FueledM.atF_bind]
    congr 1
    funext btt
    rw [FueledM.atF_bind, ensureSort_atF]
    congr 1
    funext vb
    by_cases hc : (Level.zeronessOf vb).equiv mbx.pw = true
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl

/-- The λ-inference loop against `inferBody`'s own λ-tail (task #100
stage 6: the tail is a pure rebuild — the λ-annotation re-check died
with the stored annotations). -/
theorem inferLamsI_tail_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : EIdx} {bodyx tyx : Expr} {nm : NIdx}
    {nmx : Name} {mbbi : BinderInfo} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hty : s₀.store.denoteT t = some tyx)
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx))
    (hwty : WScoped d tyx) (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, mbpw⟩)])
      (do
        let bt ← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx))
        if mode.verified then
          match bodyx.lamPw with
          | some pwI =>
            unless (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none => do
            let btt ← (fueledFns mode env).infer (d + 1) bt
            let vb ← ensureSort (fueledFns mode env) env (d + 1) btt
            unless (Level.zeronessOf vb).equiv
                (⟨mbbi, mbpw⟩ : BinderMeta).pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        pure (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (inferLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, mbpw⟩)])
      (inferLams mode (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d nmx tyx]
        [(nmx, tyx, ⟨mbbi, mbpw⟩)]) := by
    refine inferLamsI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, hty, rfl⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [(nmx, tyx, ⟨mbbi, mbpw⟩)] F res rfl
      (by
        intro x hx
        rcases List.mem_singleton.mp hx with rfl
        exact ⟨_, _, _, rfl⟩)
      hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferLamsTail at htail
    revert htail
    cases hbp : bodyx.lamPw with
    | some pwI =>
      intro htail
      have hbl : bodyx.isLam = true := by
        cases bodyx <;> first | rfl | exact nomatch hbp
      simp only [hbl, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte] at htail
      unfold inferLamsWrap at htail
      dsimp only
      by_cases hg : (mode.verified
          && !((⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI)) = true
      · rw [if_pos hg] at htail
        exact nomatch htail
      rw [if_neg hg] at htail
      by_cases hv : mode.verified = true
      · rw [if_pos hv]
        have hpw : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true := by
          by_cases hc : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true
          · exact hc
          · exact absurd (by simp [hv, hc]) hg
        rw [if_pos hpw]
        exact htail
      · rw [if_neg hv]
        exact htail
    | none =>
      intro htail
      have hbl : bodyx.isLam = false := by
        cases bodyx <;> first | rfl | exact nomatch hbp
      simp only [hbl, Bool.not_false, Bool.and_true] at htail
      dsimp only
      by_cases hv : mode.verified = true
      case neg =>
        rw [if_neg hv] at htail ⊢
        unfold inferLamsWrap at htail
        rw [if_neg (by simp [hv])] at htail
        exact htail
      rw [if_pos hv] at htail ⊢
      rw [infer_def] at htail
      obtain ⟨btt, hbtt, htail⟩ := bind_okB htail
      rw [hbtt, okB_bind]
      rw [ensureSort_def] at htail
      obtain ⟨v, hvv, htail⟩ := bind_okB htail
      rw [hvv, okB_bind]
      try dsimp only at htail ⊢
      by_cases hz : (Level.zeronessOf v).equiv
          (⟨mbbi, mbpw⟩ : BinderMeta).pw = true
      case neg =>
        rw [if_neg hz] at htail
        exact nomatch htail
      rw [if_pos hz] at htail
      rw [if_pos hz]
      unfold inferLamsWrap at htail
      rw [if_neg (by simp [PropWhen.equiv_refl])] at htail
      exact htail
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferLamTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv F hbt
        (WScoped.instantiate1 hwty 0 hwbody)
    have hres : vv = Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩ := by
      revert hF
      by_cases hv : mode.verified = true
      case neg =>
        rw [if_neg hv]
        intro hF
        injection hF with hres
        exact hres.symm
      rw [if_pos hv]
      cases bodyx.lamPw with
      | some pwI =>
        dsimp only
        by_cases hc : (⟨mbbi, mbpw⟩ : BinderMeta).pw.equiv pwI = true
        · rw [if_pos hc]
          intro hF
          injection hF with hres
          exact hres.symm
        · rw [if_neg hc]
          intro hF
          exact nomatch hF
      | none =>
        dsimp only
        intro hF
        obtain ⟨btt, -, hF⟩ := bind_okB hF
        obtain ⟨v, -, hF⟩ := bind_okB hF
        revert hF
        by_cases hc : (Level.zeronessOf v).equiv
            (⟨mbbi, mbpw⟩ : BinderMeta).pw = true
        · rw [if_pos hc]
          intro hF
          injection hF with hres
          exact hres.symm
        · rw [if_neg hc]
          intro hF
          exact nomatch hF
    subst hres
    exact (by
      simp only [WScoped]
      exact ⟨hwty, WScoped.abstract1 0 hwbt⟩ :
      WScoped d (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi, mbpw⟩))

private theorem inferPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx bodyx : Expr) (lu : Level) (pw : PropWhen) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode env) env (d + 1)
        (← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nm tyx)))
      if mode.verified then
        unless (Level.zeronessOf v).equiv pw do
          throw (.notImplemented "sort-annotation mismatch (forall-cod)")
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => ensureSortCore mode env F (d + 1) bt >>= fun v =>
        (do
          if mode.verified then
            unless (Level.zeronessOf v).equiv pw do
              throw (.notImplemented
                "sort-annotation mismatch (forall-cod)")
          pure (Expr.sort (.imax lu v)))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  congr 1
  funext v
  by_cases hv : mode.verified = true
  case neg => rw [if_neg hv, if_neg hv]; rfl
  rw [if_pos hv, if_pos hv]
  by_cases hz : (Level.zeronessOf v).equiv pw = true
  · rw [if_pos hz, if_pos hz]; rfl
  · rw [if_neg hz, if_neg hz]; rfl

/-- The ∀-inference loop against `inferBody`'s own ∀-tail (task #100
stage 6: the codomain sort is inferred, not read off an annotation). -/
theorem inferPisI_tail_sim (ih : SSimI mode env f)
    {d fuel : Nat} {b fv : EIdx} {bodyx tyx : Expr}
    {nmx : Name} {u : LIdx} {lu : Level} {pw : PropWhen} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hlu : s₀.store.denoteL u = some lu)
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx))
    (hwty : WScoped d tyx) (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(u, pw)])
      (do
        let v ← ensureSort (fueledFns mode env) env (d + 1)
          (← (fueledFns mode env).infer (d + 1)
            (bodyx.instantiate1 (.fvar d nmx tyx)))
        if mode.verified then
          unless (Level.zeronessOf v).equiv pw do
            throw (.notImplemented
              "sort-annotation mismatch (forall-cod)")
        pure (Expr.sort (.imax lu v))) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (inferPisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(u, pw)])
      (inferPis mode (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx] [(lu, pw)]) := by
    refine inferPisI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hlu, rfl⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferPis_atF] at hF
    obtain ⟨F', hchain⟩ := inferPis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [(lu, pw)] F res rfl (Nat.le_refl 1) hF
    refine ⟨F', ?_⟩
    rw [inferPiTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferPisWrap at hwrap
    obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hv
    have hv' : ensureSortCore mode env F' (d + 1) bt = .ok v := hv
    rw [hv', okB_bind]
    dsimp only at hwrap ⊢
    by_cases hver : mode.verified = true
    case neg =>
      rw [if_neg hver] at hwrap ⊢
      unfold inferPisWrap at hwrap
      exact hwrap
    rw [if_pos hver] at hwrap ⊢
    by_cases hz : (Level.zeronessOf v).equiv pw = true
    case neg =>
      rw [if_neg hz] at hwrap
      exact nomatch hwrap
    rw [if_pos hz] at hwrap ⊢
    unfold inferPisWrap at hwrap
    exact hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferPiTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨v, hv, hF⟩ := bind_okB hF
    revert hF
    by_cases hver : mode.verified = true
    case neg =>
      rw [if_neg hver]
      intro hF
      injection hF with hres
      subst hres
      simp [WScoped]
    rw [if_pos hver]
    by_cases hz : (Level.zeronessOf v).equiv pw = true
    · rw [if_pos hz]
      intro hF
      injection hF with hres
      subst hres
      simp [WScoped]
    · rw [if_neg hz]
      intro hF
      exact nomatch hF

private theorem annPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx' bodyx : Expr) (mx : BinderMeta) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx'))
      if mode.verified && !pwWritten mx.pw then
        annotPwPi (fueledFns mode env) env (d + 1) body' >>= fun pw =>
          pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
      else pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, mx.pw⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx'))
        >>= fun body' =>
        if mode.verified && !pwWritten mx.pw then
          annotPwPi (pureFns mode env F) env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.forallE nm tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  simp only [FueledM.atF_ite]
  split
  · rw [FueledM.atF_bind, annotPwPi_atF]
    rfl
  · rfl

/-- The ∀-annotation loop against `annotateBody`'s own ∀-tail (pure
post-erasure: the pass computes nothing at binders). -/
theorem annotatePisI_tail_sim (ih : SSimI mode env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx' : Expr} {nm : NIdx} {nmx : Name}
    {mi : IBinderMeta} {mx : BinderMeta} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbm : denoteBM s₀.store.denoteL mi = some mx)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hty' : s₀.store.denoteT ty' = some tyx')
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        if mode.verified && !pwWritten mx.pw then
          annotPwPi (fueledFns mode env) env (d + 1) body' >>= fun pw =>
            pure (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.forallE nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (annotatePisI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (annotatePis mode (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)]) := by
    refine annotatePisI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, hbm, hty', (hwty' : WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotatePis_atF] at hF
    obtain ⟨F', hchain⟩ := annotatePis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annPiTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    -- the chained tail at a one-entry stack IS `annotateBody`'s own
    -- ∀/λ clause: one write, then the rebuilt node (task #161 P5)
    rw [annotatePisWrap_cons] at hwrap
    simpa only [annotatePisWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
      Nat.add_zero] using hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annPiTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    -- the node's scoping does not depend on the written datum
    have hnode : ∀ pw : PropWhen,
        WScoped d (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩) :=
      fun _ => by
        simp only [WScoped]
        exact ⟨hwty', WScoped.abstract1 0 hwb⟩
    revert hF
    split
    · intro hF
      obtain ⟨pw, -, hF⟩ := bind_okB hF
      injection hF with hres
      exact hres ▸ hnode pw
    · intro hF
      injection hF with hres
      exact hres ▸ hnode mx.pw

private theorem annLamTail_atF {env : Env} (d : Nat) (nmx : Name)
    (tyx' bodyx : Expr) (mx : BinderMeta) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx'))
      if mode.verified && !pwWritten mx.pw then
        annotPwLam (fueledFns mode env) env (d + 1) body' >>= fun pw =>
          pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
      else pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, mx.pw⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nmx tyx'))
        >>= fun body' =>
        if mode.verified && !pwWritten mx.pw then
          annotPwLam (pureFns mode env F) env (d + 1) body' >>= fun pw =>
            pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.lam nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  simp only [FueledM.atF_ite]
  split
  · rw [FueledM.atF_bind, annotPwLam_atF]
    rfl
  · rfl

/-- The λ-annotation loop against `annotateBody`'s own λ-tail. -/
theorem annotateLamsI_tail_sim (ih : SSimI mode env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx' : Expr} {nm : NIdx} {nmx : Name}
    {mi : IBinderMeta} {mx : BinderMeta} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbm : denoteBM s₀.store.denoteL mi = some mx)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hty' : s₀.store.denoteT ty' = some tyx')
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        if mode.verified && !pwWritten mx.pw then
          annotPwLam (fueledFns mode env) env (d + 1) body' >>= fun pw =>
            pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩)
        else pure (Expr.lam nmx tyx' (body'.abstract1 d)
          ⟨mx.bi, mx.pw⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (annotateLamsI mode (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', mi)])
      (annotateLams mode (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)]) := by
    refine annotateLamsI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, hbm, hty', (hwty' : WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotateLams_atF] at hF
    obtain ⟨F', hchain⟩ := annotateLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', mx)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annLamTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    -- the chained tail at a one-entry stack IS `annotateBody`'s own
    -- ∀/λ clause: one write, then the rebuilt node (task #161 P5)
    rw [annotateLamsWrap_cons] at hwrap
    simpa only [annotateLamsWrap_nil, show (1 : Nat) - 1 = 0 from rfl,
      Nat.add_zero] using hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annLamTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    -- the node's scoping does not depend on the written datum
    have hnode : ∀ pw : PropWhen,
        WScoped d (Expr.lam nmx tyx' (body'.abstract1 d) ⟨mx.bi, pw⟩) :=
      fun _ => by
        simp only [WScoped]
        exact ⟨hwty', WScoped.abstract1 0 hwb⟩
    revert hF
    split
    · intro hF
      obtain ⟨pw, -, hF⟩ := bind_okB hF
      injection hF with hres
      exact hres ▸ hnode pw
    · intro hF
      injection hF with hres
      exact hres ▸ hnode mx.pw

end Setlec
