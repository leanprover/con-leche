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
    (s.store.denoteN n = some nx ∧ bi = bix ∧
      s.store.denoteT ty' = some tyx' ∧
      WScoped (d + j) tyx') ∧ DenAStk s d r rx (j - 1)
  | _, _, _ => False

theorem DenAStk.mono {s s' : IState} (hext : Ext s.store s'.store)
    {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat}, DenAStk s d stk stkx j → DenAStk s' d stk stkx j
  | [], [], _, _ => trivial
  | (_, _, _) :: _, (_, _, _) :: _, _, h =>
    ⟨⟨denoteN_mono hext h.1.1, h.1.2.1, denoteT_mono hext h.1.2.2.1,
      h.1.2.2.2⟩,
      DenAStk.mono hext h.2⟩

/-! ## The infer-λ loop walks -/

theorem inferLamsOutI_sim {d : Nat} :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX} {j : Nat}
      {cur : EIdx} {curx : Expr} {s₀ : IState},
      ISOK mode env s₀ → DenILStk s₀ stk stkx →
      s₀.store.denoteT cur = some curx →
      SimAt mode env s₀ RelD (inferLamsOutI d stk j cur)
        (inferLamsOut (m := FueledM) d stkx j curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenILStk])
  | cons e rest ihOut =>
    obtain ⟨n, tyo, mb⟩ := e
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenILStk])
    | cons ex rx =>
      obtain ⟨nx, tyox, mbx⟩ := ex
      obtain ⟨⟨hnnm, htyo, hmb⟩, hrest⟩ := hstk
      show SimAt mode env s₀ RelD
        (do
          let tyAbs ← abstractRangeM tyo d j
          let node ← internI (.forallE n tyAbs cur mb)
          inferLamsOutI d rest (j - 1) node)
        (inferLamsOut (m := FueledM) d rx (j - 1)
          (Expr.forallE nx (tyox.abstractRange d j) curx mbx))
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
      (inferLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferLamsLeaf (fueledFns mode env) d tx k ws stkx) := by
  unfold inferLamsLeafI inferLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimAt.bind_left (abstractRangeM_eff hs₂ hbtd)
    (fun s₅ cur hs₅ hext₅ hQcur => ?_)
  exact inferLamsOutI_sim hs₅
    (DenILStk.mono (((hext₁.trans hext₂)).trans hext₅) hstk) hQcur

theorem inferLamsI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List InferLamEntry} {stkx : List InferLamEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenILStk s₀ stk stkx →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferLams (fueledFns mode env) d fuel tx k ws stkx)
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
            inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
              (fvs.push fv) ((n, tyo, mb) :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ => inferLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
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
      obtain ⟨mbbi⟩ := mb
      dsimp only
      obtain rfl : bm = ⟨mbbi⟩ := by
        simpa [denoteBM] using hbmDen.symm
      rw [inferLams_succ_lam]
      have hlamL : (Expr.lam nmx tyx bodyx ⟨mbbi⟩).instantiateList
          ws = Expr.lam nmx (tyx.instantiateList ws)
            (bodyx.instantiateList ws 1) ⟨mbbi⟩ := by
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
              show denoteBM s₄.store.denoteL ⟨mbbi⟩ = some ⟨mbbi⟩
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
def DenLStk (s : IState) : List LIdx → List Level → Prop
  | [], [] => True
  | u :: r, ux :: rx => s.store.denoteL u = some ux ∧ DenLStk s r rx
  | _, _ => False

theorem DenLStk.mono {s s' : IState} (hext : Ext s.store s'.store) :
    ∀ {stk : List LIdx} {stkx : List Level},
      DenLStk s stk stkx → DenLStk s' stk stkx
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨denoteL_mono hext h.1, DenLStk.mono hext h.2⟩

theorem inferPisOutI_eff :
    ∀ {stk : List LIdx} {stkx : List Level} {v : LIdx} {lv : Level}
      {s₀ : IState},
      ISOK mode env s₀ → DenLStk s₀ stk stkx → s₀.store.denoteL v = some lv →
      IEff mode env s₀
        (fun s iv => s.store.denoteL iv = some (inferPisOut stkx lv))
        (inferPisOutI stk v) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx v lv s₀ hs hstk hv
    cases stkx with
    | nil => exact IEff.pure hs hv
    | cons ux rx => exact absurd hstk (by simp [DenLStk])
  | cons u rest ih =>
    intro stkx v lv s₀ hs hstk hv
    cases stkx with
    | nil => exact absurd hstk (by simp [DenLStk])
    | cons ux rx =>
      obtain ⟨hu, hrest⟩ := hstk
      show IEff mode env s₀ _
        (internLM (.imax u v) >>= fun v' => inferPisOutI rest v')
      refine IEff.bind (internLM_eff hs (n := .imax u v)
        (l := .imax ux lv) (by rw [denoteLNode, hu, hv]; rfl))
        (fun s₁ v' hs₁ hext₁ hv' => ?_)
      exact ih (stkx := rx) (lv := .imax ux lv) hs₁
        (DenLStk.mono hext₁ hrest) hv'

theorem inferPisLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List LIdx} {stkx : List Level} {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenLStk s₀ stk stkx)
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (inferPisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (inferPisLeaf (fueledFns mode env) d tx k ws stkx) := by
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
    refine SimAt.of_eff (IEff.bind (inferPisOutI_eff hs₃
      (DenLStk.mono ((hext₁.trans hext₂).trans hext₃) hstk) hlv)
      (fun s₄ iv hs₄ hext₄ hiv => internI_eff hs₄ (n := .sort iv)
        (x := .sort (inferPisOut stkx lv)) (by rw [denoteNode, hiv]; rfl)))
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
      {stk : List LIdx} {stkx : List Level} {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenLStk s₀ stk stkx →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (inferPis (fueledFns mode env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferPisLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt mode env s₀ RelD
      (do
        match ← viewI t with
        | some (.forallE n ty body _mb) => do
          let tyo ← instListRevM ty fvs
          let tty ← (coreKnotI mode (mkFEnv env) f).infer (d + k) tyo
          let wtty ← (coreKnotI mode (mkFEnv env) f).whnf (d + k) tty
          match ← viewI wtty with
          | some (.sort u) => do
            let fv ← internI (.fvar (d + k) n tyo)
            inferPisI (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
              (fvs.push fv) (u :: stk)
          | _ => throw (.invalid "expected a sort")
        | _ => inferPisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
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
          ⟨denoteL_mono hext₄ hlu, DenLStk.mono hextAll hstk⟩
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
    {mk : NIdx → EIdx → EIdx → BinderInfo → ENode}
    {mkX : Name → Expr → Expr → BinderInfo → Expr}
    (hmk : ∀ (s : IState) (n : NIdx) (nx : Name) (ty : EIdx) (tyx : Expr)
      (b : EIdx) (bx : Expr) (bi : BinderInfo),
      s.store.denoteN n = some nx → s.store.denoteT ty = some tyx →
      s.store.denoteT b = some bx →
      denoteNode s.store.denoteT s.store.denoteL s.store.denoteN
        (mk n ty b bi) = some (mkX nx tyx bx bi)) {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat} {cur : EIdx} {curx : Expr} {s₀ : IState},
      ISOK mode env s₀ → DenAStk s₀ d stk stkx j →
      s₀.store.denoteT cur = some curx →
      SimAt mode env s₀ RelD (annotateBindersOutI mk d stk j cur)
        (annotateBindersOut (m := FueledM) mkX d stkx j curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenAStk])
  | cons e rest ihOut =>
    obtain ⟨n, ty', bi⟩ := e
    intro stkx j cur curx s₀ hs hstk hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenAStk])
    | cons ex rx =>
      obtain ⟨nx, tyx', bix⟩ := ex
      obtain ⟨⟨hnnm, rfl, hty', hwty'⟩, hrest⟩ := hstk
      show SimAt mode env s₀ RelD
        (do
          let tyAbs ← abstractRangeM ty' d j
          let node ← internI (mk n tyAbs cur bi)
          annotateBindersOutI mk d rest (j - 1) node)
        (annotateBindersOut (m := FueledM) mkX d rx (j - 1)
          (mkX nx (tyx'.abstractRange d j) curx bi))
      refine SimAt.bind_left (abstractRangeM_eff hs hty')
        (fun s₁ tyAbs hs₁ hext₁ hQab => ?_)
      have hnd : denoteNode s₁.store.denoteT s₁.store.denoteL
          s₁.store.denoteN (mk n tyAbs cur bi)
          = some (mkX nx (tyx'.abstractRange d j) curx bi) :=
        hmk s₁ n nx tyAbs (tyx'.abstractRange d j) cur curx bi
          (denoteN_mono hext₁ hnnm) hQab (denoteT_mono hext₁ hcur)
      refine SimAt.bind_left (internI_eff hs₁ hnd)
        (fun s₂ node hs₂ hext₂ hQnode => ?_)
      exact ihOut hs₂
        (DenAStk.mono (hext₁.trans hext₂) hrest) hQnode

theorem annotatePisLeafI_sim (ih : SSimI mode env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : IState}
    (hs : ISOK mode env s₀) (ht : s₀.store.denoteT t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenAStk s₀ d stk stkx (k - 1))
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt mode env s₀ RelD
      (annotatePisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotatePisLeaf (fueledFns mode env) d tx k ws stkx) := by
  unfold annotatePisLeafI annotatePisLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  refine SimAt.bind_left (abstractRangeM_eff hs₂ hld)
    (fun s₅ cur hs₅ hext₅ hQcur => ?_)
  exact annotateBindersOutI_sim
    (fun s n nx ty tyx b bx bi hn hty hb => by
      rw [denoteNode, hty, hb, hn]; rfl)
    hs₅
    (DenAStk.mono ((hext₁.trans hext₂).trans hext₅) hstk) hQcur

theorem annotatePisI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (annotatePisI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (annotatePis (fueledFns mode env) d fuel tx k ws stkx)
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
          annotatePisI (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb.bi) :: stk)
        | _ => annotatePisLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
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
      have hbi : (mb : IBinderMeta).bi = bm.bi := by
        obtain ⟨bi0⟩ := mb
        simp only [denoteBM, Option.some.injEq] at hbmDen
        subst hbmDen
        rfl
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
      rw [hbi]
      refine annotatePisI_sim ih fuel hs₃ (denoteT_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          rfl, denoteT_mono hext₃ hty'd,
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
      (annotateLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
      (annotateLamsLeaf (fueledFns mode env) d tx k ws stkx) := by
  unfold annotateLamsLeafI annotateLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  refine SimAt.bind_left (abstractRangeM_eff hs₂ hld)
    (fun s₆ cur hs₆ hext₆ hQcur => ?_)
  exact annotateBindersOutI_sim
    (fun s n nx ty tyx b bx bi hn hty hb => by
      rw [denoteNode, hty, hb, hn]; rfl)
    hs₆
    (DenAStk.mono ((hext₁.trans hext₂).trans hext₆) hstk) hQcur

theorem annotateLamsI_sim (ih : SSimI mode env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK mode env s₀ → s₀.store.denoteT t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt mode env s₀ RelD
        (annotateLamsI (coreKnotI mode (mkFEnv env) f) d fuel t k fvs stk)
        (annotateLams (fueledFns mode env) d fuel tx k ws stkx)
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
          annotateLamsI (coreKnotI mode (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb.bi) :: stk)
        | _ => annotateLamsLeafI (coreKnotI mode (mkFEnv env) f) d t k fvs stk)
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
      have hbi : (mb : IBinderMeta).bi = bm.bi := by
        obtain ⟨bi0⟩ := mb
        simp only [denoteBM, Option.some.injEq] at hbmDen
        subst hbmDen
        rfl
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
      rw [hbi]
      refine annotateLamsI_sim ih fuel hs₃ (denoteT_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          rfl, denoteT_mono hext₃ hty'd,
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
      pure (Expr.forallE nm tyx (bt.abstract1 d) mbx)) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => pure (Expr.forallE nm tyx (bt.abstract1 d) mbx)) := by
  rw [FueledM.atF_bind]
  rfl

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
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi⟩)])
      (do
        let bt ← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx))
        pure (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi⟩)])
      (inferLams (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d nmx tyx]
        [(nmx, tyx, ⟨mbbi⟩)]) := by
    refine inferLamsI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, hty, rfl⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [(nmx, tyx, ⟨mbbi⟩)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferLamsWrap at hwrap
    exact hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferLamTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv F hbt
        (WScoped.instantiate1 hwty 0 hwbody)
    exact (by
      simp only [WScoped]
      exact ⟨hwty, WScoped.abstract1 0 hwbt⟩ :
      WScoped d (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi⟩))

private theorem inferPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx bodyx : Expr) (lu : Level) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode env) env (d + 1)
        (← (fueledFns mode env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nm tyx)))
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt => ensureSortCore mode env F (d + 1) bt >>= fun v =>
        pure (Expr.sort (.imax lu v))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

/-- The ∀-inference loop against `inferBody`'s own ∀-tail (task #100
stage 6: the codomain sort is inferred, not read off an annotation). -/
theorem inferPisI_tail_sim (ih : SSimI mode env f)
    {d fuel : Nat} {b fv : EIdx} {bodyx tyx : Expr}
    {nmx : Name} {u : LIdx} {lu : Level} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hlu : s₀.store.denoteL u = some lu)
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx))
    (hwty : WScoped d tyx) (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv] [u])
      (do
        let v ← ensureSort (fueledFns mode env) env (d + 1)
          (← (fueledFns mode env).infer (d + 1)
            (bodyx.instantiate1 (.fvar d nmx tyx)))
        pure (Expr.sort (.imax lu v))) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (inferPisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv] [u])
      (inferPis (fueledFns mode env) d fuel bodyx 1 [Expr.fvar d nmx tyx]
        [lu]) := by
    refine inferPisI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨hlu, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferPis_atF] at hF
    obtain ⟨F', hchain⟩ := inferPis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [lu] F res rfl (Nat.le_refl 1) hF
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
    unfold inferPisWrap at hwrap
    exact hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferPiTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨v, hv, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    simp [WScoped]

private theorem annPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx' bodyx : Expr) (bi : BinderInfo) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx'))
      pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨bi⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx'))
        >>= fun body' =>
        pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨bi⟩)) := by
  rw [FueledM.atF_bind]
  rfl

/-- The ∀-annotation loop against `annotateBody`'s own ∀-tail (pure
post-erasure: the pass computes nothing at binders). -/
theorem annotatePisI_tail_sim (ih : SSimI mode env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx' : Expr} {nm : NIdx} {nmx : Name}
    {bi : BinderInfo} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hty' : s₀.store.denoteT ty' = some tyx')
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (annotatePisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        pure (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨bi⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (annotatePisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (annotatePis (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)]) := by
    refine annotatePisI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, rfl, hty', (hwty' : WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotatePis_atF] at hF
    obtain ⟨F', hchain⟩ := annotatePis_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annPiTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    unfold annotatePisWrap at hwrap
    exact hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annPiTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    exact (by
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwb⟩ :
      WScoped d (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨bi⟩))

private theorem annLamTail_atF {env : Env} (d : Nat) (nmx : Name)
    (tyx' bodyx : Expr) (bi : BinderInfo) (F : Nat) :
    ((do
      let body' ← (fueledFns mode env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx'))
      pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi⟩))
      : FueledM Expr).val F
    = (annotateCore mode env F (d + 1) (bodyx.instantiate1 (.fvar d nmx tyx'))
        >>= fun body' =>
        pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi⟩)) := by
  rw [FueledM.atF_bind]
  rfl

/-- The λ-annotation loop against `annotateBody`'s own λ-tail. -/
theorem annotateLamsI_tail_sim (ih : SSimI mode env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx' : Expr} {nm : NIdx} {nmx : Name}
    {bi : BinderInfo} {s₀ : IState}
    (hs : ISOK mode env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denoteT b = some bodyx)
    (hty' : s₀.store.denoteT ty' = some tyx')
    (hfv : s₀.store.denoteT fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx) :
    SimAt mode env s₀ (RelE d)
      (annotateLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (do
        let body' ← (fueledFns mode env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt mode env s₀ RelD
      (annotateLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (annotateLams (fueledFns mode env) d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)]) := by
    refine annotateLamsI_sim ih fuel hs hbody
      (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, rfl, hty', (hwty' : WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotateLams_atF] at hF
    obtain ⟨F', hchain⟩ := annotateLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [annLamTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore mode env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    unfold annotateLamsWrap at hwrap
    exact hwrap
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annLamTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    exact (by
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwb⟩ :
      WScoped d (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi⟩))

end Setlec
