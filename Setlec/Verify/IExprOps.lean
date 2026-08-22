import Setlec.Verify.IExpr
import Setlec.Kernel.CoreI

/-!
# Specs for the interned core's arena operations (task #26)

Commutation of the spine/telescope/readback operations of
`Setlec/Kernel/IExpr.lean` with the structural denotation, the
`FEnv` name-index agreement with `Env.find?`, and the agreement of the
indexed guard twins (`Setlec/Kernel/CoreI.lean`) with their `Env`
originals.  Everything is stated over well-formed stores (`EStore.WF`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore

/-! ## The pointwise list relation -/

/-- Pointwise denotation of an index list. -/
def DenL (st : EStore) : List EIdx → List Expr → Prop
  | [], [] => True
  | i :: is, x :: xs => st.denote i = some x ∧ DenL st is xs
  | _, _ => False

namespace DenL

theorem nil {st : EStore} : DenL st [] [] := trivial

theorem cons {st : EStore} {i : EIdx} {x : Expr} {is : List EIdx}
    {xs : List Expr} (h : st.denote i = some x) (hs : DenL st is xs) :
    DenL st (i :: is) (x :: xs) := ⟨h, hs⟩

theorem length_eq {st : EStore} :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      is.length = xs.length
  | [], [], _ => rfl
  | _ :: is, _ :: xs, ⟨_, hs⟩ => by
    simpa using length_eq (is := is) (xs := xs) hs
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem mono {st st' : EStore} (hext : Ext st st') :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs → DenL st' is xs
  | [], [], _ => trivial
  | _ :: is, _ :: xs, ⟨h, hs⟩ =>
    ⟨denote_mono hext h, mono hext (is := is) (xs := xs) hs⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem append {st : EStore} :
    ∀ {is is' : List EIdx} {xs xs' : List Expr}, DenL st is xs →
      DenL st is' xs' → DenL st (is ++ is') (xs ++ xs')
  | [], _, [], _, _, h' => h'
  | _ :: is, _, _ :: xs, _, ⟨h, hs⟩, h' =>
    ⟨h, append (is := is) (xs := xs) hs h'⟩
  | [], _, _ :: _, _, h, _ | _ :: _, _, [], _, h, _ => nomatch h

theorem take {st : EStore} (k : Nat) :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      DenL st (is.take k) (xs.take k) := by
  induction k with
  | zero => intro is xs _; exact trivial
  | succ k ih =>
    intro is xs h
    match is, xs, h with
    | [], [], _ => exact trivial
    | i :: is, x :: xs, ⟨h, hs⟩ =>
      exact ⟨h, ih hs⟩

theorem drop {st : EStore} (k : Nat) :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      DenL st (is.drop k) (xs.drop k) := by
  induction k with
  | zero => intro is xs h; exact h
  | succ k ih =>
    intro is xs h
    match is, xs, h with
    | [], [], _ => exact trivial
    | i :: is, x :: xs, ⟨_, hs⟩ =>
      exact ih hs

theorem getD {st : EStore} {d0 : EIdx} {x0 : Expr}
    (hd : st.denote d0 = some x0) :
    ∀ {is : List EIdx} {xs : List Expr} (k : Nat), DenL st is xs →
      st.denote (is.getD k d0) = some (xs.getD k x0)
  | [], [], _, _ => hd
  | i :: is, x :: xs, k, ⟨h, hs⟩ => by
    cases k with
    | zero => simpa using h
    | succ k =>
      simpa using getD hd (is := is) (xs := xs) k hs
  | [], _ :: _, _, h | _ :: _, [], _, h => nomatch h

end DenL

/-! ## Spine operations -/

theorem getAppFnI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {e : EIdx} {x : Expr}, st.denote e = some x →
      st.denote (st.getAppFnI e) = some x.getAppFn := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x hx
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    cases n with
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨xf, hf, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨xa, ha, rfl⟩ := hd
      have hflt : f < e := hc f (by simp [ENode.children])
      rw [getAppFnI, hn]
      dsimp only
      rw [dif_pos hflt]
      rw [show Expr.getAppFn (.app xf xa) = xf.getAppFn from rfl]
      exact ih f hflt hf
    | bvar i =>
      cases hd; rw [getAppFnI, hn]; exact hx
    | sort u => cases hd; rw [getAppFnI, hn]; exact hx
    | const nm us => cases hd; rw [getAppFnI, hn]; exact hx
    | lit l => cases hd; rw [getAppFnI, hn]; exact hx
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx

theorem getAppArgsI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {e : EIdx} {x : Expr}, st.denote e = some x →
      DenL st (st.getAppArgsI e) x.getAppArgs := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x hx
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    cases n with
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨xf, hf, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨xa, ha, rfl⟩ := hd
      have hflt : f < e := hc f (by simp [ENode.children])
      rw [getAppArgsI, hn]
      dsimp only
      rw [dif_pos hflt]
      rw [show Expr.getAppArgs (.app xf xa) = xf.getAppArgs ++ [xa] from rfl]
      exact DenL.append (ih f hflt hf) ⟨ha, trivial⟩
    | bvar i => cases hd; rw [getAppArgsI, hn]; exact trivial
    | sort u => cases hd; rw [getAppArgsI, hn]; exact trivial
    | const nm us => cases hd; rw [getAppArgsI, hn]; exact trivial
    | lit l => cases hd; rw [getAppArgsI, hn]; exact trivial
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [getAppArgsI, hn]; exact trivial
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppArgsI, hn]; exact trivial
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppArgsI, hn]; exact trivial
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppArgsI, hn]; exact trivial
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [getAppArgsI, hn]; exact trivial

/-- Interning a node whose children denote in the current (well-formed)
store. -/
theorem intern_spec {st : EStore} {n : ENode} {a : Expr} (hwf : st.WF)
    (hd : denoteNode st.denote n = some a) :
    (st.intern n).2.WF ∧ Ext st (st.intern n).2 ∧
      (st.intern n).2.denote (st.intern n).1 = some a := by
  have hc : ∀ c ∈ n.children, c < st.nodes.size := by
    intro c hcin
    obtain ⟨b, hb⟩ := denoteNode_children_some hd c hcin
    exact denote_lt_size hb
  exact ⟨intern_wf hwf hc, intern_ext st n,
    by rw [intern_denote hwf hc]; exact hd⟩

theorem mkAppNI_spec :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      ∀ {f : EIdx} {x : Expr}, st.denote f = some x → DenL st args xs →
      (st.mkAppNI f args).2.WF ∧ Ext st (st.mkAppNI f args).2 ∧
        (st.mkAppNI f args).2.denote (st.mkAppNI f args).1
          = some (Expr.mkAppN x xs)
  | [], xs, st, hwf, f, x, hf, hargs => by
    match xs, hargs with
    | [], _ => exact ⟨hwf, Ext.refl st, hf⟩
  | a :: as, xs, st, hwf, f, x, hf, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      have hd : denoteNode st.denote (.app f a) = some (.app x xa) := by
        rw [denoteNode, hf, ha]; rfl
      obtain ⟨hwf₁, hext₁, hfa⟩ := intern_spec hwf hd
      rw [show st.mkAppNI f (a :: as) =
        (st.intern (.app f a)).2.mkAppNI (st.intern (.app f a)).1 as from rfl]
      obtain ⟨hwf₂, hext₂, hres⟩ :=
        mkAppNI_spec (args := as) (xs := xs) hwf₁ hfa (hs.mono hext₁)
      exact ⟨hwf₂, hext₁.trans hext₂, hres⟩

theorem instSpineI_spec :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      ∀ {t : Nat} {e : EIdx} {x : Expr},
      st.denote e = some x → DenL st args xs →
      (st.instSpineI args t e).2.WF ∧ Ext st (st.instSpineI args t e).2 ∧
        (st.instSpineI args t e).2.denote (st.instSpineI args t e).1
          = some (Expr.instSpine xs t x)
  | [], xs, st, hwf, t, e, x, he, hargs => by
    match xs, hargs with
    | [], _ => exact ⟨hwf, Ext.refl st, he⟩
  | a :: as, xs, st, hwf, t, e, x, he, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      obtain ⟨hwf₁, hext₁, he'⟩ := instantiate1I_spec (d := t) hwf he ha
      rw [show st.instSpineI (a :: as) t e =
        (st.instantiate1I e a t).2.instSpineI as (t - 1)
          (st.instantiate1I e a t).1 from rfl]
      obtain ⟨hwf₂, hext₂, hres⟩ :=
        instSpineI_spec (args := as) (xs := xs) hwf₁ he' (hs.mono hext₁)
      exact ⟨hwf₂, hext₁.trans hext₂, hres⟩

/-- Relation of an optional index to an optional expression under a
store. -/
def OptDen (st : EStore) : Option EIdx → Option Expr → Prop
  | none, none => True
  | some i, some x => st.denote i = some x
  | _, _ => False

theorem OptDen.mono {st st' : EStore} (hext : Ext st st') :
    ∀ {o : Option EIdx} {ox : Option Expr}, OptDen st o ox →
      OptDen st' o ox
  | none, none, _ => trivial
  | some _, some _, h => denote_mono hext h
  | none, some _, h | some _, none, h => nomatch h

theorem piResidualI_spec :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      ∀ {e : EIdx} {x : Expr},
      st.denote e = some x → DenL st args xs →
      (st.piResidualI e args).2.WF ∧ Ext st (st.piResidualI e args).2 ∧
        OptDen (st.piResidualI e args).2 (st.piResidualI e args).1
          (piResidual x xs)
  | [], xs, st, hwf, e, x, he, hargs => by
    match xs, hargs with
    | [], _ => exact ⟨hwf, Ext.refl st, he⟩
  | a :: as, xs, st, hwf, e, x, he, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
      cases n with
      | forallE nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, ht, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨eb, hb, rfl⟩ := hd
        obtain ⟨hwf₁, hext₁, hb'⟩ := instantiate1I_spec (d := 0) hwf hb ha
        rw [piResidualI, hn]
        dsimp only
        rw [show piResidual (.forallE nm et eb m) (xa :: xs) =
          piResidual (eb.instantiate1 xa) xs from rfl]
        obtain ⟨hwf₂, hext₂, hres⟩ :=
          piResidualI_spec (args := as) (xs := xs) hwf₁ hb' (hs.mono hext₁)
        exact ⟨hwf₂, hext₁.trans hext₂, hres⟩
      | app f a =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, _, rfl⟩ := hd
        rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | bvar i => cases hd; rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | sort u => cases hd; rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | const nm us => cases hd; rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | lit l => cases hd; rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨t', _, rfl⟩ := hd
        rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | lam nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨eb, _, rfl⟩ := hd
        rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | letE nm t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨eb, _, rfl⟩ := hd
        rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨ee, _, rfl⟩ := hd
        rw [piResidualI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩

/-- `Expr.instPis` and the core's `piResidual` are the same function. -/
theorem instPis_eq_piResidual :
    ∀ (e : Expr) (as : List Expr), e.instPis as = piResidual e as
  | _, [] => rfl
  | .forallE _ _ b _, a :: as => instPis_eq_piResidual (b.instantiate1 a) as
  | .bvar _, _ :: _ | .fvar _ _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem pisToLamsI_spec :
    ∀ {k : Nat} {st : EStore}, st.WF →
      ∀ {e body : EIdx} {x xb : Expr},
      st.denote e = some x → st.denote body = some xb →
      (st.pisToLamsI k e body).2.WF ∧ Ext st (st.pisToLamsI k e body).2 ∧
        OptDen (st.pisToLamsI k e body).2 (st.pisToLamsI k e body).1
          (Expr.pisToLams k x xb)
  | 0, st, hwf, e, body, x, xb, he, hb => ⟨hwf, Ext.refl st, hb⟩
  | k + 1, st, hwf, e, body, x, xb, he, hb => by
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
    cases n with
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, ht, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, hbb, rfl⟩ := hd
      obtain ⟨hwf₁, hext₁, hres₁⟩ :=
        pisToLamsI_spec (k := k) hwf hbb hb (e := b) (body := body)
      rw [pisToLamsI, hn]
      dsimp only
      rw [show Expr.pisToLams (k + 1) (.forallE nm et eb m) xb =
        (Expr.pisToLams k eb xb).map (fun bx => .lam nm et bx ⟨m.bi, none⟩)
        from rfl]
      rcases hgo : st.pisToLamsI k b body with ⟨o, st₁⟩
      rw [hgo] at hres₁ hwf₁ hext₁
      cases o with
      | none =>
        cases hox : Expr.pisToLams k eb xb with
        | none => exact ⟨hwf₁, hext₁, by simp [OptDen]⟩
        | some bx => rw [hox] at hres₁; exact nomatch hres₁
      | some bidx =>
        cases hox : Expr.pisToLams k eb xb with
        | none => rw [hox] at hres₁; exact nomatch hres₁
        | some bx =>
          rw [hox] at hres₁
          have hd' : denoteNode st₁.denote (.lam nm t bidx ⟨m.bi, none⟩)
              = some (.lam nm et bx ⟨m.bi, none⟩) := by
            rw [denoteNode, denote_mono hext₁ ht, hres₁]; rfl
          obtain ⟨hwf₂, hext₂, hres₂⟩ := intern_spec hwf₁ hd'
          exact ⟨hwf₂, hext₁.trans hext₂, hres₂⟩
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨ef, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨ea, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | bvar i => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | sort u => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | const nm us => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | lit l => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩

theorem stripPisBodyI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {k : Nat} {e : EIdx} {x : Expr}, st.denote e = some x →
      OptDen st (st.stripPisBodyI k e) ((x.stripPis k).map (·.2)) := by
  intro k
  induction k with
  | zero =>
    intro e x he
    simpa [stripPisBodyI, Expr.stripPis, OptDen] using he
  | succ k ih =>
    intro e x he
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
    cases n with
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, ht, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, hbb, rfl⟩ := hd
      have := ih (e := b) hbb
      rw [stripPisBodyI, hn]
      dsimp only
      rw [show Expr.stripPis (k + 1) (.forallE nm et eb m) =
        (eb.stripPis k).map (fun p => ((nm, et, m) :: p.1, p.2)) from rfl]
      cases hs : eb.stripPis k with
      | none => rw [hs] at this; simpa using this
      | some p => rw [hs] at this; simpa using this
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨ef, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨ea, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | bvar i => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | sort u => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | const nm us => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | lit l => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial

/-! ## Readback -/

/-- Invariant of the readback memo: every entry is the denotation. -/
def RInv (st : EStore) (memo : Std.HashMap EIdx Expr) : Prop :=
  ∀ i x, memo[i]? = some x → st.denote i = some x

theorem RInv.empty {st : EStore} : RInv st {} := by
  intro i x h
  simp at h

theorem RInv.insert {st : EStore} {memo : Std.HashMap EIdx Expr}
    {e : EIdx} {x : Expr} (h : RInv st memo) (hx : st.denote e = some x) :
    RInv st (memo.insert e x) := by
  intro i y hy
  rw [Std.HashMap.getElem?_insert] at hy
  by_cases hk : e = i
  · subst hk
    rw [if_pos (by simp)] at hy
    cases hy
    exact hx
  · rw [if_neg (by simpa using hk)] at hy
    exact h i y hy

theorem readbackGo_spec {st : EStore} (_hwf : st.WF) :
    ∀ (e : EIdx) {x : Expr} {memo : Std.HashMap EIdx Expr}
      {r : Option Expr} {memo' : Std.HashMap EIdx Expr},
      st.denote e = some x → RInv st memo →
      readbackGo st memo e = (r, memo') →
      r = some x ∧ RInv st memo' := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x memo r memo' hx hinv hgo
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    unfold readbackGo at hgo
    cases hm : memo[e]? with
    | some y =>
      rw [hm] at hgo
      injection hgo with h1 h2
      subst h1; subst h2
      have := hinv e y hm
      rw [hx] at this
      exact ⟨by injection this with h; rw [h], hinv⟩
    | none =>
      rw [hm, hn] at hgo
      cases n with
      | bvar i =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hx⟩
      | sort u =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hx⟩
      | const nm us =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hx⟩
      | lit l =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hx⟩
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨xt, ht, rfl⟩ := hd
        have hlt : t < e := hc t (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hgt : readbackGo st memo t with ⟨rt, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih t hlt ht hinv hgt
        rw [hgt] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₁.insert hx⟩
      | app f a =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xf, hf, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xa, ha, rfl⟩ := hd
        have hltf : f < e := hc f (by simp [ENode.children])
        have hlta : a < e := hc a (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltf, hlta⟩] at hgo
        rcases hgf : readbackGo st memo f with ⟨rf, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih f hltf hf hinv hgf
        rcases hga : readbackGo st memo₁ a with ⟨ra, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih a hlta ha hinv₁ hga
        rw [hgf] at hgo
        dsimp only at hgo
        rw [hga] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₂.insert hx⟩
      | lam nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hb, rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : readbackGo st memo t with ⟨rt, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih t hltt ht hinv hgt
        rcases hgb : readbackGo st memo₁ b with ⟨rb, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih b hltb hb hinv₁ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₂.insert hx⟩
      | forallE nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hb, rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : readbackGo st memo t with ⟨rt, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih t hltt ht hinv hgt
        rcases hgb : readbackGo st memo₁ b with ⟨rb, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih b hltb hb hinv₁ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₂.insert hx⟩
      | letE nm t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xv, hv, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hb, rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltv : v < e := hc v (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltv, hltb⟩] at hgo
        rcases hgt : readbackGo st memo t with ⟨rt, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih t hltt ht hinv hgt
        rcases hgv : readbackGo st memo₁ v with ⟨rv, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih v hltv hv hinv₁ hgv
        rcases hgb : readbackGo st memo₂ b with ⟨rb, memo₃⟩
        obtain ⟨rfl, hinv₃⟩ := ih b hltb hb hinv₂ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgv] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₃.insert hx⟩
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨xe, he, rfl⟩ := hd
        have hlt : e' < e := hc e' (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hge : readbackGo st memo e' with ⟨re, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih e' hlt he hinv hge
        rw [hge] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₁.insert hx⟩

/-- On a well-formed store, `readbackI` computes the denotation. -/
theorem readbackI_spec {st : EStore} (hwf : st.WF) {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) : st.readbackI e = some x := by
  rcases hgo : readbackGo st {} e with ⟨r, memo'⟩
  obtain ⟨rfl, -⟩ := readbackGo_spec hwf e hx RInv.empty hgo
  rw [readbackI, hgo]

/-! ## The `FEnv` index agrees with `Env.find?` -/

private theorem foldr_index_find? (n : Name) :
    ∀ (l : List ConstantInfo),
      (l.foldr (fun ci m => m.insert ci.name ci)
        (∅ : Std.HashMap Name ConstantInfo))[n]? =
        l.find? (fun ci => ci.name == n)
  | [] => by simp
  | ci :: l => by
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons]
    by_cases hn : ci.name == n
    · rw [if_pos hn, hn]
    · rw [if_neg hn, foldr_index_find? n l]
      rw [show (ci.name == n) = false by simpa using hn]

/-- The per-entry-call name index computes `Env.find?`. -/
theorem mkFEnv_find? (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n :=
  foldr_index_find? n env.consts

/-- The indexed projection lookup computes `Env.findProj?`. -/
theorem mkFEnv_findProj? (env : Env) (T : Name) (i : Nat) :
    (mkFEnv env).findProj? T i = env.findProj? T i := by
  rw [FEnv.findProj?, Env.findProj?, mkFEnv_find?]
  rfl

/-! ## Guard twins agree with the `Env` versions -/

theorem natLitSupportedF_eq (env : Env) :
    natLitSupportedF (mkFEnv env) = natLitSupported env := by
  simp only [natLitSupportedF, natLitSupported, mkFEnv_find?]

theorem strLitSupportedF_eq (env : Env) :
    strLitSupportedF (mkFEnv env) = strLitSupported env := by
  simp only [strLitSupportedF, strLitSupported, mkFEnv_find?,
    natLitSupportedF_eq]

theorem natOpGuardF_eq (env : Env) (c : Name) :
    natOpGuardF (mkFEnv env) c = natOpGuard env c := by
  simp only [natOpGuardF, natOpGuard, mkFEnv_find?, natLitSupportedF_eq]
  rfl

/-! ## Node classifiers agree with the `Expr` versions -/

theorem isUnitLikeTyI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (_hwf : st.WF) (hx : st.denote e = some x) :
    isUnitLikeTyI (mkFEnv env) st e = isUnitLikeTy env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
  rw [isUnitLikeTyI, hn]
  cases n with
  | const nm us =>
    cases hd
    dsimp only
    rw [show isUnitLikeTy env (.const nm us) =
      ((match env.find? nm with
        | some (.indInfo _ _) => true
        | _ => false) &&
      (match env.find? (nm.str "rec") with
        | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false) &&
      reservedBasisNames.contains (nm.str "rec")) from rfl]
    rw [mkFEnv_find?, mkFEnv_find?]
    rfl
  | bvar i => cases hd; rfl
  | sort u => cases hd; rfl
  | lit l => cases hd; rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, rfl⟩ := hd
    rfl
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, rfl⟩ := hd
    rfl
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, rfl⟩ := hd
    rfl

/-- A denoted head node is the denotation's `getAppFn` head shape:
convenience inversion pairing `getAppFnI_spec` with `denote_some_inv`. -/
theorem head_node_spec {st : EStore} (hwf : st.WF) {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) :
    ∃ n, st.nodes[st.getAppFnI e]? = some n ∧
      denoteNode st.denote n = some x.getAppFn := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  exact ⟨n, hn, hd⟩

theorem isCtorAppI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (hwf : st.WF) (hx : st.denote e = some x) :
    isCtorAppI (mkFEnv env) st e = isCtorApp env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  rw [isCtorAppI, hn, isCtorApp]
  cases n with
  | const nm us =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
    dsimp only
    rw [mkFEnv_find?]
    rfl
  | bvar i =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | sort u =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | lit l =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]

theorem headHintI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (hwf : st.WF) (hx : st.denote e = some x) :
    headHintI (mkFEnv env) st e = headHint env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  rw [headHintI, hn, headHint]
  cases n with
  | const nm us =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
    dsimp only
    rw [mkFEnv_find?]
    rfl
  | bvar i =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | sort u =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | lit l =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]

theorem rawNatLitI?_spec {st : EStore} {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) :
    rawNatLitI? st e = rawNatLit? x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
  rw [rawNatLitI?, hn]
  cases n with
  | const nm us =>
    cases hd
    cases us with
    | nil => rfl
    | cons u us => rfl
  | bvar i => cases hd; rfl
  | sort u => cases hd; rfl
  | lit l =>
    cases hd
    cases l with
    | natVal k => rfl
    | strVal s => rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, rfl⟩ := hd
    rfl
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, rfl⟩ := hd
    rfl
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, rfl⟩ := hd
    rfl

theorem sameConstHeadsI_spec {st : EStore} {a b : EIdx} {xa xb : Expr}
    (hwf : st.WF) (ha : st.denote a = some xa) (hb : st.denote b = some xb) :
    sameConstHeadsI st a b = sameConstHeads xa xb := by
  obtain ⟨na, hna, hca, hda⟩ := denote_some_inv ha
  obtain ⟨nb, hnb, hcb, hdb⟩ := denote_some_inv hb
  rw [sameConstHeadsI, hna, hnb]
  cases na with
  | app f₁ a₁ =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨xf₁, hf₁, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨xa₁, ha₁, rfl⟩ := hda
    cases nb with
    | app f₂ a₂ =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨xf₂, hf₂, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨xa₂, ha₂, rfl⟩ := hdb
      rw [show sameConstHeads (.app xf₁ xa₁) (.app xf₂ xa₂) =
        (match xf₁.getAppFn, xf₂.getAppFn with
          | .const n₁ _, .const n₂ _ => n₁ == n₂
          | _, _ => false) from rfl]
      obtain ⟨m₁, hm₁, -, hdm₁⟩ := denote_some_inv (getAppFnI_spec hwf hf₁)
      obtain ⟨m₂, hm₂, -, hdm₂⟩ := denote_some_inv (getAppFnI_spec hwf hf₂)
      dsimp only
      rw [hm₁, hm₂]
      cases m₁ with
      | const n₁ us₁ =>
        have h₁ := Option.some.inj hdm₁
        cases m₂ with
        | const n₂ us₂ =>
          have h₂ := Option.some.inj hdm₂
          rw [← h₁, ← h₂]
        | bvar i => rw [← Option.some.inj hdm₂, ← h₁]
        | sort u => rw [← Option.some.inj hdm₂, ← h₁]
        | lit l => rw [← Option.some.inj hdm₂, ← h₁]
        | fvar idx nm t =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨t', _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | app f a' =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨ef, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨ea, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | lam nm t b' m =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | forallE nm t b' m =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | letE nm t v b' =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.bind_eq_some_iff] at hdm₂
          obtain ⟨ev, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | proj s j e' =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨ee, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
      | bvar i =>
        rw [← Option.some.inj hdm₁]
      | sort u =>
        rw [← Option.some.inj hdm₁]
      | lit l =>
        rw [← Option.some.inj hdm₁]
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨t', _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | app f a' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨ef, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨ea, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | lam nm t b' m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | forallE nm t b' m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | letE nm t v b' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.bind_eq_some_iff] at hdm₁
        obtain ⟨ev, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨ee, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
    | bvar i => cases hdb; rfl
    | sort u => cases hdb; rfl
    | const nm us => cases hdb; rfl
    | lit l => cases hdb; rfl
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨t', _, rfl⟩ := hdb
      rfl
    | lam nm t b' m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨eb, _, rfl⟩ := hdb
      rfl
    | forallE nm t b' m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨eb, _, rfl⟩ := hdb
      rfl
    | letE nm t v b' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.bind_eq_some_iff] at hdb
      obtain ⟨ev, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨eb, _, rfl⟩ := hdb
      rfl
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨ee, _, rfl⟩ := hdb
      rfl
  | bvar i => cases hda; rfl
  | sort u => cases hda; rfl
  | const nm us => cases hda; rfl
  | lit l => cases hda; rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨t', _, rfl⟩ := hda
    rfl
  | lam nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨eb, _, rfl⟩ := hda
    rfl
  | forallE nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨eb, _, rfl⟩ := hda
    rfl
  | letE nm t v b' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.bind_eq_some_iff] at hda
    obtain ⟨ev, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨eb, _, rfl⟩ := hda
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨ee, _, rfl⟩ := hda
    rfl

/-! ## The fabrication leaf-subset guard -/

/-- The `Expr`-side leaf list lifted to `Option` types. -/
def leavesL (A : List (Nat × Name × Expr)) : List (Nat × Name × Option Expr) :=
  A.map fun l => (l.1, l.2.1, some l.2.2)

theorem leavesExp_eq_leavesL (x : Expr) : leavesExp x = leavesL x.fvarLeaves :=
  rfl

/-- Every element of an interned leaf list denotes (read off the
`leavesDen`/`leavesL` correspondence). -/
private theorem leaves_denote {st : EStore} {A : List (Nat × Name × EIdx)}
    {A' : List (Nat × Name × Expr)} (h : leavesDen st A = leavesL A') :
    ∀ l ∈ A, ∃ x, st.denote l.2.2 = some x := by
  intro l hl
  have : (l.1, l.2.1, st.denote l.2.2) ∈ leavesL A' := by
    rw [← h]
    exact List.mem_map_of_mem hl
  obtain ⟨l', -, hl'⟩ := List.mem_map.mp this
  exact ⟨l'.2.2, congrArg (·.2.2) hl'.symm⟩

/-- Membership transfer along the denotation of leaf lists (denotation
is injective on well-formed stores, so `contains` transfers in both
directions). -/
private theorem leaves_contains {st : EStore} (hwf : st.WF)
    {B : List (Nat × Name × EIdx)} {B' : List (Nat × Name × Expr)}
    (hB : leavesDen st B = leavesL B')
    {l : Nat × Name × EIdx} {x : Expr} (hx : st.denote l.2.2 = some x) :
    B.contains l = B'.contains (l.1, l.2.1, x) := by
  rcases l with ⟨i, nm, t⟩
  simp only at hx
  simp only [List.contains_eq_mem, decide_eq_decide]
  constructor
  · intro hmem
    have hmm : ((i, nm, st.denote t) : Nat × Name × Option Expr)
        ∈ leavesL B' := by
      rw [← hB]
      exact List.mem_map_of_mem hmem
    obtain ⟨⟨a, b, c⟩, hl', heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hc⟩ := heq
    rw [hx] at hc
    obtain rfl : c = x := Option.some.inj hc
    exact hl'
  · intro hmem
    have hmm : ((i, nm, some x) : Nat × Name × Option Expr)
        ∈ leavesDen st B := by
      rw [hB]
      exact List.mem_map_of_mem hmem
    obtain ⟨⟨a, b, c⟩, hl', heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hc⟩ := heq
    obtain rfl : c = t := denote_inj hwf hc hx
    exact hl'

/-- The interned fabrication guard (`fvarLeavesI`-subset) agrees with
the `Expr`-level one. -/
theorem leafGuardI_spec {st : EStore} (hwf : st.WF) {fab base : EIdx}
    {xf xb : Expr} (hf : st.denote fab = some xf)
    (hb : st.denote base = some xb) :
    ((st.fvarLeavesI fab).all fun l => (st.fvarLeavesI base).contains l)
      = (xf.fvarLeaves.all fun l => xb.fvarLeaves.contains l) := by
  have hA := (fvarLeavesI_spec hwf hf).trans (leavesExp_eq_leavesL xf)
  have hB := (fvarLeavesI_spec hwf hb).trans (leavesExp_eq_leavesL xb)
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h l' hl'
    rcases l' with ⟨i, nm, x⟩
    have hmm : ((i, nm, some x) : Nat × Name × Option Expr)
        ∈ leavesDen st (st.fvarLeavesI fab) := by
      rw [hA]
      exact List.mem_map_of_mem hl'
    obtain ⟨⟨a, b, c⟩, hl, heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hc⟩ := heq
    have := h _ hl
    rw [leaves_contains hwf hB (l := (a, b, c)) hc] at this
    exact this
  · intro h l hl
    obtain ⟨x, hx⟩ := leaves_denote hA l hl
    rw [leaves_contains hwf hB hx]
    have hmm : ((l.1, l.2.1, st.denote l.2.2) : Nat × Name × Option Expr)
        ∈ leavesL xf.fvarLeaves := by
      rw [← hA]
      exact List.mem_map_of_mem hl
    obtain ⟨⟨a, b, c⟩, hl', heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, hc⟩ := heq
    rw [hx] at hc
    obtain rfl : c = x := Option.some.inj hc
    have heql : ((l.1, l.2.1, c) : Nat × Name × Expr) = (a, b, c) := by
      simp [h1, h2]
    rw [heql]
    exact h _ hl'

end Setlec
