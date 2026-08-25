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

open EStore Expr

variable {env : Env} {f : Nat}

/-- Denotation-only result relation for the loop walks. -/
def RelD (s : IState) (j : EIdx) (v : Expr) : Prop :=
  s.store.denote j = some v

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
    s.store.denoteN n = some nx ∧ s.store.denote tyo = some tyox ∧
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
  exact ⟨denoteN_mono hext h1, denote_mono hext h2, denoteBM_mono hext h3⟩

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
      s.store.denote ty' = some tyx' ∧
      WScoped (d + j) tyx') ∧ DenAStk s d r rx (j - 1)
  | _, _, _ => False

theorem DenAStk.mono {s s' : IState} (hext : Ext s.store s'.store)
    {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat}, DenAStk s d stk stkx j → DenAStk s' d stk stkx j
  | [], [], _, _ => trivial
  | (_, _, _) :: _, (_, _, _) :: _, _, h =>
    ⟨⟨denoteN_mono hext h.1.1, h.1.2.1, denote_mono hext h.1.2.2.1,
      h.1.2.2.2⟩,
      DenAStk.mono hext h.2⟩

/-! ## The infer-λ loop walks -/

theorem inferLamsOutI_sim {d : Nat} :
    ∀ {stk : List InferLamEntry} {stkx : List InferLamEntryX} {j : Nat}
      {cur : EIdx} {curx : Expr} {s₀ : IState},
      ISOK env s₀ → DenILStk s₀ stk stkx →
      s₀.store.denote cur = some curx →
      SimAt env s₀ RelD (inferLamsOutI d stk j cur)
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
      show SimAt env s₀ RelD
        (do
          let tyAbs ← abstractRangeM tyo d j
          let node ← internI (.forallE n tyAbs cur mb)
          match rest with
          | [] => pure node
          | _ :: _ => inferLamsOutI d rest (j - 1) node)
        _
      rw [inferLamsOut_cons' (m := FueledM) nx tyox mbx rx j curx]
      refine SimAt.bind_left (abstractRangeM_eff hs htyo)
        (fun s₃ tyAbs hs₃ hext₃ hQab => ?_)
      have hnd : denoteNode s₃.store.denote s₃.store.denoteL
          s₃.store.denoteN (.forallE n tyAbs cur mb)
          = some (.forallE nx (tyox.abstractRange d j) curx mbx) := by
        rw [denoteNode, hQab, denote_mono hext₃ hcur,
          denoteBM_mono hext₃ hmb,
          denoteN_mono hext₃ hnnm]
        rfl
      refine SimAt.bind_left (internI_eff hs₃ hnd)
        (fun s₄ node hs₄ hext₄ hQnode => ?_)
      cases rest with
      | nil =>
        cases rx with
        | nil => exact SimAt.pure hs₄ hQnode
        | cons ex2 rx2 => exact absurd hrest (by simp [DenILStk])
      | cons e2 r2 =>
        cases rx with
        | nil => exact absurd hrest (by cases e2; simp [DenILStk])
        | cons ex2 rx2 =>
          exact ihOut hs₄
            (DenILStk.mono (hext₃.trans hext₄) hrest) hQnode

theorem inferLamsLeafI_sim (ih : SSimI env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List InferLamEntry} {stkx : List InferLamEntryX} {s₀ : IState}
    (hs : ISOK env s₀) (ht : s₀.store.denote t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenILStk s₀ stk stkx)
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt env s₀ RelD
      (inferLamsLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      (inferLamsLeaf (fueledFns env) d tx k ws stkx) := by
  unfold inferLamsLeafI inferLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.infer hs₁ hQob hw)
    (fun s₂ bt btx hs₂ hext₂ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimAt.bind_left (abstractRangeM_eff hs₂ hbtd)
    (fun s₅ cur hs₅ hext₅ hQcur => ?_)
  exact inferLamsOutI_sim hs₅
    (DenILStk.mono ((hext₁.trans hext₂).trans hext₅) hstk) hQcur

theorem inferLamsI_sim (ih : SSimI env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List InferLamEntry} {stkx : List InferLamEntryX}
      {s₀ : IState},
      ISOK env s₀ → s₀.store.denote t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenILStk s₀ stk stkx →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt env s₀ RelD
        (inferLamsI (coreKnotI (mkFEnv env) f) d fuel t k fvs stk)
        (inferLams (fueledFns env) d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact inferLamsLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt env s₀ RelD
      (do
        match ← viewI t with
        | some (.lam n ty body mb) =>
          match mb.cod with
          | some _ => do
            let tyo ← instListRevM ty fvs
            let tty ← (coreKnotI (mkFEnv env) f).infer (d + k) tyo
            let wtty ← (coreKnotI (mkFEnv env) f).whnf (d + k) tty
            match ← viewI wtty with
            | some (.sort _) => do
              let fv ← internI (.fvar (d + k) n tyo)
              inferLamsI (coreKnotI (mkFEnv env) f) d fuel body (k + 1)
                (fvs.push fv) ((n, tyo, mb) :: stk)
            | _ => throw (.invalid "expected a sort")
          | none =>
            throw (.internal "unannotated λ-binder reached inferType")
        | _ => inferLamsLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denote_some_inv ht
    have hn := getNode_of_stored hn
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
      obtain ⟨mbbi, mbcod⟩ := mb
      dsimp only
      cases mbcod with
      | none =>
        simp only [denoteBM, Option.some.injEq] at hbmDen
        subst hbmDen
        rw [inferLams_succ_lam_none]
        exact SimAt.throw
      | some v =>
        simp only [denoteBM, Option.map_eq_some_iff] at hbmDen
        obtain ⟨lv, hlv, rfl⟩ := hbmDen
        rw [inferLams_succ_lam]
        have hlamL : (Expr.lam nmx tyx bodyx
              ⟨mbbi, some lv⟩).instantiateList
            ws = Expr.lam nmx (tyx.instantiateList ws)
              (bodyx.instantiateList ws 1) ⟨mbbi, some lv⟩ := by
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
        obtain ⟨nd', hn', hc', hd'⟩ := denote_some_inv hwd
        have hn' := getNode_of_stored hn'
        rw [hn']
        cases nd' with
        | sort u =>
          rw [denoteNode, Option.map_eq_some_iff] at hd'
          obtain ⟨lu, hlu, rfl⟩ := hd'
          have hext₁₃ := hext₂.trans hext₃
          have hfvd : denoteNode s₃.store.denote s₃.store.denoteL
              s₃.store.denoteN (.fvar (d + k) nm tyo)
              = some (.fvar (d + k) nmx (tyx.instantiateList ws)) := by
            rw [denoteNode, denote_mono hext₁₃ hQtyo,
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
            (denote_mono hextAll hbody)
            (by rw [toListRev_push]
                exact ⟨hQfv, hfvs.mono hextAll⟩)
            (⟨⟨denoteN_mono hextAll hnmx,
              denote_mono (hext₁₃.trans hext₄) hQtyo,
              (by
                show denoteBM s₄.store.denoteL ⟨mbbi, some v⟩
                  = some ⟨mbbi, some lv⟩
                simp only [denoteBM,
                  denoteL_mono (hextAll) hlv]
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

/-! ## The ∀-annotation loop walks -/

theorem annotatePisOutI_sim (ih : SSimI env f) {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat} {v : LIdx} {lv : Level} {cur : EIdx} {curx : Expr}
      {s₀ : IState},
      ISOK env s₀ → DenAStk s₀ d stk stkx j →
      s₀.store.denoteL v = some lv →
      s₀.store.denote cur = some curx →
      SimAt env s₀ RelD (annotatePisOutI (coreKnotI (mkFEnv env) f) d stk j v cur)
        (annotatePisOut (fueledFns env) d stkx j lv curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j v lv cur curx s₀ hs hstk hlv hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenAStk])
  | cons e rest ihOut =>
    obtain ⟨n, ty', bi⟩ := e
    intro stkx j v lv cur curx s₀ hs hstk hlv hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenAStk])
    | cons ex rx =>
      obtain ⟨nx, tyx', bix⟩ := ex
      obtain ⟨⟨hnnm, rfl, hty', hwty'⟩, hrest⟩ := hstk
      show SimAt env s₀ RelD
        (do
          let tyAbs ← abstractRangeM ty' d j
          let node ← internI (.forallE n tyAbs cur ⟨bi, some v⟩)
          match rest with
          | [] => pure node
          | _ :: _ => do
            let tty ← (coreKnotI (mkFEnv env) f).infer (d + j) ty'
            let wtty ← (coreKnotI (mkFEnv env) f).whnf (d + j) tty
            match ← viewI wtty with
            | some (.sort u) => do
              let v' ← internLM (.imax u v)
              annotatePisOutI (coreKnotI (mkFEnv env) f) d rest (j - 1)
                v' node
            | _ => throw (.invalid "expected a sort"))
        _
      rw [annotatePisOut_cons' (m := FueledM) nx tyx' bi rx j lv curx]
      refine SimAt.bind_left (abstractRangeM_eff hs hty')
        (fun s₁ tyAbs hs₁ hext₁ hQab => ?_)
      have hnd : denoteNode s₁.store.denote s₁.store.denoteL
          s₁.store.denoteN (.forallE n tyAbs cur ⟨bi, some v⟩)
          = some (.forallE nx (tyx'.abstractRange d j) curx
              ⟨bi, some lv⟩) := by
        rw [denoteNode, hQab, denote_mono hext₁ hcur,
          denoteN_mono hext₁ hnnm]
        simp only [denoteBM, denoteL_mono hext₁ hlv]
        rfl
      refine SimAt.bind_left (internI_eff hs₁ hnd)
        (fun s₂ node hs₂ hext₂ hQnode => ?_)
      have hext₀₂ := hext₁.trans hext₂
      cases rest with
      | nil =>
        cases rx with
        | nil => exact SimAt.pure hs₂ hQnode
        | cons ex2 rx2 => exact absurd hrest (by simp [DenAStk])
      | cons e2 r2 =>
        cases rx with
        | nil => exact absurd hrest (by obtain ⟨a, b, c⟩ := e2; simp [DenAStk])
        | cons ex2 rx2 =>
          refine SimAt.bind (ih.infer hs₂
            (denote_mono hext₀₂ hty') hwty')
            (fun s₃ tty ttyx hs₃ hext₃ hPtty => ?_)
          obtain ⟨httyd, hwtty⟩ := hPtty
          refine SimAt.bind (ih.whnf hs₃ httyd hwtty)
            (fun s₄ wtty wx hs₄ hext₄ hPw => ?_)
          obtain ⟨hwd, hww⟩ := hPw
          refine SimAt.view ?_
          obtain ⟨nd, hn, hc, hd⟩ := denote_some_inv hwd
          have hn := getNode_of_stored hn
          rw [hn]
          cases nd with
          | sort u =>
            rw [denoteNode, Option.map_eq_some_iff] at hd
            obtain ⟨lu, hlu, rfl⟩ := hd
            refine SimAt.bind_left (internLM_eff hs₄ (n := .imax u v)
              (l := .imax lu lv) (by
                rw [denoteLNode, hlu, denoteL_mono
                  (((hext₀₂.trans hext₃).trans hext₄)) hlv]
                rfl))
              (fun s₅ v' hs₅ hext₅ hv' => ?_)
            have hextAll := (((hext₀₂.trans hext₃).trans hext₄).trans hext₅)
            exact ihOut hs₅ (DenAStk.mono hextAll hrest) hv'
              (denote_mono (((hext₃.trans hext₄).trans hext₅)) hQnode)
          | bvar i => cases hd; exact SimAt.throw
          | fvar idx nm tt => invert_node hd; exact SimAt.throw
          | const nm us => invert_node hd; exact SimAt.throw
          | app f' a' => invert_node hd; exact SimAt.throw
          | lam nm tt b mm => invert_node hd; exact SimAt.throw
          | forallE nm tt b mm => invert_node hd; exact SimAt.throw
          | letE nm tt vv b => invert_node hd; exact SimAt.throw
          | lit l => cases hd; exact SimAt.throw
          | proj sp i e' => invert_node hd; exact SimAt.throw

theorem annotatePisLeafI_sim (ih : SSimI env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : IState}
    (hs : ISOK env s₀) (ht : s₀.store.denote t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenAStk s₀ d stk stkx (k - 1))
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt env s₀ RelD
      (annotatePisLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      (annotatePisLeaf (fueledFns env) env d tx k ws stkx) := by
  unfold annotatePisLeafI annotatePisLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  refine SimAt.bind (ih.infer hs₂ hld hwl)
    (fun s₃ tb tbx hs₃ hext₃ hPtb => ?_)
  obtain ⟨htbd, hwtb⟩ := hPtb
  refine SimAt.bind (ensureSortI_sim ih hs₃ htbd hwtb)
    (fun s₄ v lv hs₄ hext₄ hPv => ?_)
  refine SimAt.bind_left (abstractRangeM_eff hs₄
    (denote_mono (hext₃.trans hext₄) hld))
    (fun s₅ cur hs₅ hext₅ hQcur => ?_)
  exact annotatePisOutI_sim ih hs₅
    (DenAStk.mono ((((hext₁.trans hext₂).trans hext₃).trans
      hext₄).trans hext₅) hstk)
    (denoteL_mono hext₅ hPv) hQcur

theorem annotatePisI_sim (ih : SSimI env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK env s₀ → s₀.store.denote t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt env s₀ RelD
        (annotatePisI (coreKnotI (mkFEnv env) f) d fuel t k fvs stk)
        (annotatePis (fueledFns env) env d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotatePisLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt env s₀ RelD
      (do
        match ← viewI t with
        | some (.forallE n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotatePisI (coreKnotI (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb.bi) :: stk)
        | _ => annotatePisLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denote_some_inv ht
    have hn := getNode_of_stored hn
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
        obtain ⟨bi0, cod0⟩ := mb
        cases cod0 with
        | none =>
          simp only [denoteBM, Option.some.injEq] at hbmDen
          subst hbmDen
          rfl
        | some vv =>
          simp only [denoteBM, Option.map_eq_some_iff] at hbmDen
          obtain ⟨lvv, hlvv, rfl⟩ := hbmDen
          rfl
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hext₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      have hfvd : denoteNode s₂.store.denote s₂.store.denoteL
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
      refine annotatePisI_sim ih fuel hs₃ (denote_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          rfl, denote_mono hext₃ hty'd,
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

theorem annotateLamsOutI_sim (ih : SSimI env f) {d : Nat} :
    ∀ {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {j : Nat} {v : LIdx} {lv : Level} {cur : EIdx} {curx : Expr}
      {s₀ : IState},
      ISOK env s₀ → DenAStk s₀ d stk stkx j →
      s₀.store.denoteL v = some lv →
      s₀.store.denote cur = some curx →
      SimAt env s₀ RelD
        (annotateLamsOutI (coreKnotI (mkFEnv env) f) d stk j v cur)
        (annotateLamsOut (fueledFns env) d stkx j lv curx) := by
  intro stk
  induction stk with
  | nil =>
    intro stkx j v lv cur curx s₀ hs hstk hlv hcur
    cases stkx with
    | nil => exact SimAt.pure hs hcur
    | cons ex rx => exact absurd hstk (by simp [DenAStk])
  | cons e rest ihOut =>
    obtain ⟨n, ty', bi⟩ := e
    intro stkx j v lv cur curx s₀ hs hstk hlv hcur
    cases stkx with
    | nil => exact absurd hstk (by simp [DenAStk])
    | cons ex rx =>
      obtain ⟨nx, tyx', bix⟩ := ex
      obtain ⟨⟨hnnm, rfl, hty', hwty'⟩, hrest⟩ := hstk
      show SimAt env s₀ RelD
        (do
          let tyAbs ← abstractRangeM ty' d j
          let node ← internI (.lam n tyAbs cur ⟨bi, some v⟩)
          match rest with
          | [] => pure node
          | _ :: _ => do
            let tty ← (coreKnotI (mkFEnv env) f).infer (d + j) ty'
            let wtty ← (coreKnotI (mkFEnv env) f).whnf (d + j) tty
            match ← viewI wtty with
            | some (.sort u) => do
              unless ← liftFueled "level comparison" (← isEquivLM v v) do
                throw (.invalid
                  "λ-annotation does not match the body's sort")
              let v' ← internLM (.imax u v)
              annotateLamsOutI (coreKnotI (mkFEnv env) f) d rest (j - 1)
                v' node
            | _ => throw (.invalid "expected a sort"))
        _
      rw [annotateLamsOut_cons' (m := FueledM) nx tyx' bi rx j lv curx]
      refine SimAt.bind_left (abstractRangeM_eff hs hty')
        (fun s₁ tyAbs hs₁ hext₁ hQab => ?_)
      have hnd : denoteNode s₁.store.denote s₁.store.denoteL
          s₁.store.denoteN (.lam n tyAbs cur ⟨bi, some v⟩)
          = some (.lam nx (tyx'.abstractRange d j) curx
              ⟨bi, some lv⟩) := by
        rw [denoteNode, hQab, denote_mono hext₁ hcur,
          denoteN_mono hext₁ hnnm]
        simp only [denoteBM, denoteL_mono hext₁ hlv]
        rfl
      refine SimAt.bind_left (internI_eff hs₁ hnd)
        (fun s₂ node hs₂ hext₂ hQnode => ?_)
      have hext₀₂ := hext₁.trans hext₂
      cases rest with
      | nil =>
        cases rx with
        | nil => exact SimAt.pure hs₂ hQnode
        | cons ex2 rx2 => exact absurd hrest (by simp [DenAStk])
      | cons e2 r2 =>
        cases rx with
        | nil => exact absurd hrest (by obtain ⟨a, b, c⟩ := e2; simp [DenAStk])
        | cons ex2 rx2 =>
          refine SimAt.bind (ih.infer hs₂
            (denote_mono hext₀₂ hty') hwty')
            (fun s₃ tty ttyx hs₃ hext₃ hPtty => ?_)
          obtain ⟨httyd, hwtty⟩ := hPtty
          refine SimAt.bind (ih.whnf hs₃ httyd hwtty)
            (fun s₄ wtty wx hs₄ hext₄ hPw => ?_)
          obtain ⟨hwd, hww⟩ := hPw
          refine SimAt.view ?_
          obtain ⟨nd, hn, hc, hd⟩ := denote_some_inv hwd
          have hn := getNode_of_stored hn
          rw [hn]
          cases nd with
          | sort u =>
            rw [denoteNode, Option.map_eq_some_iff] at hd
            obtain ⟨lu, hlu, rfl⟩ := hd
            have hext₀₄ := (hext₀₂.trans hext₃).trans hext₄
            refine SimAt.bind_left (isEquivLM_eff hs₄
              (denoteL_mono hext₀₄ hlv) (denoteL_mono hext₀₄ hlv))
              (fun s₅ o hs₅ hext₅ ho => ?_)
            subst ho
            refine SimAt.bind (SimAt.liftFueled _ _ hs₅)
              (fun s₆ ok ok' hs₆ hext₆ hPok => ?_)
            obtain rfl : ok = ok' := hPok
            cases ok with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact SimAt.throw_bind
            | true =>
              simp only [↓reduceIte]
              have hext₄₆ := hext₅.trans hext₆
              refine SimAt.bind_left (internLM_eff hs₆ (n := .imax u v)
                (l := .imax lu lv) (by
                  rw [denoteLNode, denoteL_mono hext₄₆ hlu,
                    denoteL_mono (hext₀₄.trans hext₄₆) hlv]
                  rfl))
                (fun s₇ v' hs₇ hext₇ hv' => ?_)
              have hextAll := (hext₀₄.trans hext₄₆).trans hext₇
              exact ihOut hs₇ (DenAStk.mono hextAll hrest) hv'
                (denote_mono ((((hext₃.trans hext₄).trans hext₄₆).trans
                  hext₇)) hQnode)
          | bvar i => cases hd; exact SimAt.throw
          | fvar idx nm tt => invert_node hd; exact SimAt.throw
          | const nm us => invert_node hd; exact SimAt.throw
          | app f' a' => invert_node hd; exact SimAt.throw
          | lam nm tt b mm => invert_node hd; exact SimAt.throw
          | forallE nm tt b mm => invert_node hd; exact SimAt.throw
          | letE nm tt vv b => invert_node hd; exact SimAt.throw
          | lit l => cases hd; exact SimAt.throw
          | proj sp i e' => invert_node hd; exact SimAt.throw

theorem annotateLamsLeafI_sim (ih : SSimI env f) {d : Nat}
    {t : EIdx} {tx : Expr} {k : Nat} {fvs : Array EIdx} {ws : List Expr}
    {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
    {s₀ : IState}
    (hs : ISOK env s₀) (ht : s₀.store.denote t = some tx)
    (hfvs : DenL s₀.store fvs.toList.reverse ws) (hstk : DenAStk s₀ d stk stkx (k - 1))
    (hw : WScoped (d + k) (tx.instantiateList ws)) :
    SimAt env s₀ RelD
      (annotateLamsLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      (annotateLamsLeaf (fueledFns env) env d tx k ws stkx) := by
  unfold annotateLamsLeafI annotateLamsLeaf
  refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hfvs)
    (fun s₁ ob hs₁ hext₁ hQob => ?_)
  refine SimAt.bind (ih.annotate hs₁ hQob hw)
    (fun s₂ leaf' leafx hs₂ hext₂ hPl => ?_)
  obtain ⟨hld, hwl⟩ := hPl
  refine SimAt.bind (ih.infer hs₂ hld hwl)
    (fun s₃ bt btx hs₃ hext₃ hPbt => ?_)
  obtain ⟨hbtd, hwbt⟩ := hPbt
  refine SimAt.bind (ih.infer hs₃ hbtd hwbt)
    (fun s₄ tbt tbtx hs₄ hext₄ hPtbt => ?_)
  obtain ⟨htbtd, hwtbt⟩ := hPtbt
  refine SimAt.bind (ensureSortI_sim ih hs₄ htbtd hwtbt)
    (fun s₅ v lv hs₅ hext₅ hPv => ?_)
  refine SimAt.bind_left (abstractRangeM_eff hs₅
    (denote_mono ((hext₃.trans hext₄).trans hext₅) hld))
    (fun s₆ cur hs₆ hext₆ hQcur => ?_)
  exact annotateLamsOutI_sim ih hs₆
    (DenAStk.mono (((((hext₁.trans hext₂).trans hext₃).trans
      hext₄).trans hext₅).trans hext₆) hstk)
    (denoteL_mono hext₆ hPv) hQcur

theorem annotateLamsI_sim (ih : SSimI env f) {d : Nat} :
    ∀ (fuel : Nat) {t : EIdx} {tx : Expr} {k : Nat}
      {fvs : Array EIdx} {ws : List Expr}
      {stk : List AnnotBinderEntry} {stkx : List AnnotBinderEntryX}
      {s₀ : IState},
      ISOK env s₀ → s₀.store.denote t = some tx →
      DenL s₀.store fvs.toList.reverse ws → DenAStk s₀ d stk stkx (k - 1) →
      WScoped (d + k) (tx.instantiateList ws) →
      SimAt env s₀ RelD
        (annotateLamsI (coreKnotI (mkFEnv env) f) d fuel t k fvs stk)
        (annotateLams (fueledFns env) env d fuel tx k ws stkx)
  | 0, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    exact annotateLamsLeafI_sim ih hs ht hfvs hstk hw
  | fuel + 1, t, tx, k, fvs, ws, stk, stkx, s₀ => by
    intro hs ht hfvs hstk hw
    show SimAt env s₀ RelD
      (do
        match ← viewI t with
        | some (.lam n ty body mb) => do
          let tyo ← instListRevM ty fvs
          let ty' ← (coreKnotI (mkFEnv env) f).annotate (d + k) tyo
          let fv ← internI (.fvar (d + k) n ty')
          annotateLamsI (coreKnotI (mkFEnv env) f) d fuel body (k + 1)
            (fvs.push fv) ((n, ty', mb.bi) :: stk)
        | _ => annotateLamsLeafI (coreKnotI (mkFEnv env) f) d t k fvs stk)
      _
    refine SimAt.view ?_
    obtain ⟨nd, hn, hc, hd⟩ := denote_some_inv ht
    have hn := getNode_of_stored hn
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
        obtain ⟨bi0, cod0⟩ := mb
        cases cod0 with
        | none =>
          simp only [denoteBM, Option.some.injEq] at hbmDen
          subst hbmDen
          rfl
        | some vv =>
          simp only [denoteBM, Option.map_eq_some_iff] at hbmDen
          obtain ⟨lvv, hlvv, rfl⟩ := hbmDen
          rfl
      refine SimAt.bind_left (instListRevM_eff (d := 0) hs hty hfvs)
        (fun s₁ tyo hs₁ hext₁ hQtyo => ?_)
      refine SimAt.bind (ih.annotate hs₁ hQtyo hwcomp.1)
        (fun s₂ ty' tyx' hs₂ hext₂ hPty' => ?_)
      obtain ⟨hty'd, hwty'⟩ := hPty'
      have hfvd : denoteNode s₂.store.denote s₂.store.denoteL
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
      refine annotateLamsI_sim ih fuel hs₃ (denote_mono hextAll hbody)
        (by rw [toListRev_push]
            exact ⟨hQfv, hfvs.mono hextAll⟩)
        (⟨⟨denoteN_mono hext₃ (denoteN_mono (hext₁.trans hext₂) hnmx),
          rfl, denote_mono hext₃ hty'd,
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
    (tyx bodyx : Expr) (mbbi : BinderInfo) (lv : Level) (F : Nat) :
    ((do
      let bt ← (fueledFns env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx))
      pure (Expr.forallE nm tyx (bt.abstract1 d) ⟨mbbi, some lv⟩))
      : FueledM Expr).val F
    = (inferTypeCore env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx))
        >>= fun bt =>
        pure (Expr.forallE nm tyx (bt.abstract1 d) ⟨mbbi, some lv⟩)) := by
  rw [FueledM.atF_bind]
  rfl

theorem inferLamsI_tail_sim (ih : SSimI env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : EIdx} {bodyx tyx : Expr} {nm : NIdx}
    {nmx : Name}
    {mbbi : BinderInfo} {v : LIdx} {lv : Level} {s₀ : IState}
    (hs : ISOK env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denote b = some bodyx)
    (hty : s₀.store.denote t = some tyx)
    (hlv : s₀.store.denoteL v = some lv)
    (hfv : s₀.store.denote fv = some (.fvar d nmx tyx))
    (hwty : WScoped d tyx) (hwbody : WScoped d bodyx) :
    SimAt env s₀ (RelE d)
      (inferLamsI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, some v⟩)])
      (do
        let bt ← (fueledFns env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx))
        pure (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi, some lv⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx]) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty 0 hwbody
  have hcore : SimAt env s₀ RelD
      (inferLamsI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, t, ⟨mbbi, some v⟩)])
      (inferLams (fueledFns env) d fuel bodyx 1 [Expr.fvar d nmx tyx]
        [(nmx, tyx, ⟨mbbi, some lv⟩)]) := by
    refine inferLamsI_sim ih fuel hs hbody (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, hty, ?_⟩, trivial⟩ hwopen
    show denoteBM s₀.store.denoteL ⟨mbbi, some v⟩ = some ⟨mbbi, some lv⟩
    simp only [denoteBM, hlv]
    rfl
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx] [(nmx, tyx, ⟨mbbi, some lv⟩)] F res rfl hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx)]
      exact hbt
    rw [hbt', okB_bind]
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
      WScoped d (Expr.forallE nmx tyx (bt.abstract1 d) ⟨mbbi, some lv⟩))

private theorem annPiTail_atF {env : Env} (d : Nat) (nm : Name)
    (tyx' bodyx : Expr) (bi : BinderInfo) (F : Nat) :
    ((do
      let body' ← (fueledFns env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nm tyx'))
      let v ← ensureSort (fueledFns env) env (d + 1)
        (← (fueledFns env).infer (d + 1) body')
      pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨bi, some v⟩))
      : FueledM Expr).val F
    = (annotateCore env F (d + 1) (bodyx.instantiate1 (.fvar d nm tyx'))
        >>= fun body' => inferTypeCore env F (d + 1) body' >>= fun tb =>
        ensureSortCore env F (d + 1) tb >>= fun v =>
        pure (Expr.forallE nm tyx' (body'.abstract1 d) ⟨bi, some v⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  rw [FueledM.atF_bind]
  congr 1
  funext tb
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

theorem annotatePisI_tail_sim (ih : SSimI env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx' : Expr} {nm : NIdx} {nmx : Name} {bi : BinderInfo}
    {s₀ : IState}
    (hs : ISOK env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denote b = some bodyx)
    (hty' : s₀.store.denote ty' = some tyx')
    (hfv : s₀.store.denote fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx) :
    SimAt env s₀ (RelE d)
      (annotatePisI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (do
        let body' ← (fueledFns env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        let v ← ensureSort (fueledFns env) env (d + 1)
          (← (fueledFns env).infer (d + 1) body')
        pure (Expr.forallE nmx tyx' (body'.abstract1 d) ⟨bi, some v⟩)) := by
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt env s₀ RelD
      (annotatePisI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (annotatePis (fueledFns env) env d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)]) := by
    refine annotatePisI_sim ih fuel hs hbody (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
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
    have hbody'' : annotateCore env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    unfold annotatePisWrap at hwrap
    obtain ⟨tb, htb, hwrap⟩ := bind_okB hwrap
    rw [infer_def] at htb
    have htb' : inferTypeCore env F' (d + 1) body' = .ok tb := htb
    rw [htb', okB_bind]
    obtain ⟨lvv, hlvv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hlvv
    have hlvv' : ensureSortCore env F' (d + 1) tb = .ok lvv := hlvv
    rw [hlvv', okB_bind]
    unfold annotatePisWrap at hwrap
    injection hwrap with hres
    rw [← hres]
    rfl
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annPiTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    obtain ⟨tb, htb, hF⟩ := bind_okB hF
    obtain ⟨lvv, hlvv, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    exact (by
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwb⟩ :
      WScoped d (Expr.forallE nmx tyx' (body'.abstract1 d)
        ⟨bi, some lvv⟩))

private theorem annLamTail_atF {env : Env} (d : Nat) (nmx : Name)
    (tyx' bodyx : Expr) (bi : BinderInfo) (F : Nat) :
    ((do
      let body' ← (fueledFns env).annotate (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx'))
      let bt ← (fueledFns env).infer (d + 1) body'
      let v ← ensureSort (fueledFns env) env (d + 1)
        (← (fueledFns env).infer (d + 1) bt)
      pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi, some v⟩))
      : FueledM Expr).val F
    = (annotateCore env F (d + 1) (bodyx.instantiate1 (.fvar d nmx tyx'))
        >>= fun body' => inferTypeCore env F (d + 1) body' >>= fun bt =>
        inferTypeCore env F (d + 1) bt >>= fun tbt =>
        ensureSortCore env F (d + 1) tbt >>= fun v =>
        pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi, some v⟩)) := by
  rw [FueledM.atF_bind]
  congr 1
  funext body'
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind]
  congr 1
  funext tbt
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

theorem annotateLamsI_tail_sim (ih : SSimI env f) {d fuel : Nat}
    {b ty' fv : EIdx} {bodyx tyx tyx' : Expr} {nm : NIdx} {nmx : Name}
    {bi : BinderInfo} {bm : BinderMeta} {s₀ : IState}
    (hs : ISOK env s₀)
    (hnm : s₀.store.denoteN nm = some nmx)
    (hbody : s₀.store.denote b = some bodyx)
    (hty' : s₀.store.denote ty' = some tyx')
    (hfv : s₀.store.denote fv = some (.fvar d nmx tyx'))
    (hwty' : WScoped d tyx') (hwbody : WScoped d bodyx)
    (hbnd0 : (Expr.lam nmx tyx bodyx bm).looseBVarsBounded 0 = true)
    (htyRun : ∃ F, annotateCore env F d tyx = .ok tyx') :
    SimAt env s₀ (RelE d)
      (annotateLamsI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (do
        let body' ← (fueledFns env).annotate (d + 1)
          (bodyx.instantiate1 (.fvar d nmx tyx'))
        let bt ← (fueledFns env).infer (d + 1) body'
        let v ← ensureSort (fueledFns env) env (d + 1)
          (← (fueledFns env).infer (d + 1) bt)
        pure (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi, some v⟩)) := by
  have hbcomp : tyx.looseBVarsBounded 0 = true
      ∧ bodyx.looseBVarsBounded 1 = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbnd0
  have hwopen : WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
    rw [instList_single]
    exact WScoped.instantiate1 hwty' 0 hwbody
  have hcore : SimAt env s₀ RelD
      (annotateLamsI (coreKnotI (mkFEnv env) f) d fuel b 1 #[fv]
        [(nm, ty', bi)])
      (annotateLams (fueledFns env) env d fuel bodyx 1
        [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)]) := by
    refine annotateLamsI_sim ih fuel hs hbody (by rw [toListRev_singleton]; exact DenL.cons hfv DenL.nil)
      ⟨⟨hnm, rfl, hty', (hwty' : WScoped (d + 0) tyx')⟩, trivial⟩ hwopen
  refine SimAt.wp (SimAt.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [annotateLams_atF] at hF
    have htyB' : tyx'.looseBVarsBounded 0 = true := by
      obtain ⟨F₀, hr⟩ := htyRun
      exact annotateCore_looseBVars F₀ _ hr hbcomp.1
    have hstk : ALStkOK d [(nmx, tyx', bi)] (1 - 1) := by
      refine ⟨⟨htyB', (hwty' : WScoped (d + 0) tyx'), trivial⟩, trivial⟩
    have hcons : AStkLeafCond d [(nmx, tyx', bi)] (1 - 1)
        (bodyx.instantiateList [Expr.fvar d nmx tyx']) := by
      refine ⟨?_, trivial⟩
      rw [instList_single]
      exact (Expr.LeafCond_opened hwty' hwbody 0 :
        Expr.LeafCond (d + 0) nmx tyx' _)
    have hbopen : (bodyx.instantiateList
        [Expr.fvar d nmx tyx']).looseBVarsBounded 0 = true := by
      rw [instList_single]
      exact looseBVarsBounded_instantiate1 _ 0 hbcomp.2
    obtain ⟨F', hchain⟩ := annotateLams_sound fuel bodyx 1
      [Expr.fvar d nmx tyx'] [(nmx, tyx', bi)] F res rfl hstk hcons hbopen
      hwopen hF
    refine ⟨F', ?_⟩
    rw [annLamTail_atF]
    obtain ⟨body', hbody', hwrap⟩ := bind_okB hchain
    have hbody'' : annotateCore env F' (d + 1)
        (bodyx.instantiate1 (.fvar d nmx tyx')) = .ok body' := by
      rw [← instList_single bodyx (Expr.fvar d nmx tyx')]
      exact hbody'
    rw [hbody'', okB_bind]
    unfold annotateLamsWrap at hwrap
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hwrap
    rw [infer_def] at hbt
    have hbt' : inferTypeCore env F' (d + 1) body' = .ok bt := hbt
    rw [hbt', okB_bind]
    obtain ⟨tbt, htbt, hwrap⟩ := bind_okB hwrap
    rw [infer_def] at htbt
    have htbt' : inferTypeCore env F' (d + 1) bt = .ok tbt := htbt
    rw [htbt', okB_bind]
    obtain ⟨lvv, hlvv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hlvv
    have hlvv' : ensureSortCore env F' (d + 1) tbt = .ok lvv := hlvv
    rw [hlvv', okB_bind]
    unfold annotateLamsWrap at hwrap
    injection hwrap with hres
    rw [← hres]
    rfl
  case hsc =>
    intro s v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [annLamTail_atF] at hF
    obtain ⟨body', hbody', hF⟩ := bind_okB hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨tbt, htbt, hF⟩ := bind_okB hF
    obtain ⟨lvv, hlvv, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    have hwb : WScoped (d + 1) body' :=
      annotateCore_WScoped F _ hbody'
        (WScoped.instantiate1 hwty' 0 hwbody)
    exact (by
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwb⟩ :
      WScoped d (Expr.lam nmx tyx' (body'.abstract1 d) ⟨bi, some lvv⟩))

end Setlec
