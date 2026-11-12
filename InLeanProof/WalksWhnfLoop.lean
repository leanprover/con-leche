module

public import InLeanProof.WalksIota
public import InLeanProof.KnotAssembly
import ConLeche.Verify.Cached.DiscC4
/- `Lean.QuotKind`'s derived `BEq` is not exposed by `Lean.Declaration`; the
quotient eliminators' arity read compares kinds. -/
import all Lean.Declaration

/-!
# InLean's body walks, part 3: the head-normalization loops (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC4.lean`'s whnf half: the reduction loop and
its body (`whnfLoopI`, `whnfBodyI`), the peel loop (`betaPeelI`), and the
head-normalization loop and body (`whnfCoreLoopI`, `whnfCoreBodyI`, over the
named step specs `WhnfAppSpecI`/`ReduceProjSpecI` of `KnotI.lean`), each by
its cached twin's `sym … => vcgen … <;> finish` script.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary -/

theorem whnfLoopFuel_eq : InLean.whnfLoopFuel = ConLeche.whnfLoopFuel := by
  with_unfolding_all rfl

/-- A definition's unfolding of a closed term is closed (`EnvWF`'s). -/
theorem lbb_unfoldDefinition (henv : ConLeche.EnvWF env) {e e₂ : ConLeche.Expr}
    (h : ConLeche.unfoldDefinition env e = some e₂) (hb : e.looseBVarsBounded 0 = true) :
    e₂.looseBVarsBounded 0 = true :=
  ConLeche.unfoldDefinition_looseBVars henv h hb

/-! ## The reduction loop -/

section WhnfLoop

variable {fe : InLean.FEnv} {lv : Nat}

/-- **The reduction loop** (`whnfLoopC_spec`'s twin), by induction on the
shared step budget. -/
theorem whnfLoopI_specI (ih : KnotSpecI mode mi eager env fe lv) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hdom : EnvDomI fe env) (hdef : EnvDefnI fe env) {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ i = true →
      ConLeche.Expr.WScoped d (TrS s₀ i) → (TrS s₀ i).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.whnfLoopI mi fe eager lv d n i
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs (ConLeche.whnfLoop (ConLeche.fueledFns mode eager env) env d n (TrS s₀ i)) (TrS s' v) ∧
        ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind] => vcgen [InLean.whnfLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind, ConLeche.whnfLoop, ConLeche.whnfStep,
        ConLeche.unfoldDefinition_WScoped henv, lbb_unfoldDefinition henv] =>
      vcgen [InLean.whnfLoopI.eq_def, ih.whnfCore, reduceNatI_specI ih hdom,
        unfoldDefinitionI_specI (mode := mode) (eager := eager) hfe hdef, ihn] <;> finish

/-- **The reduction body** (`whnfBodyC_spec`'s twin). -/
theorem whnfBodyI_specI (ih : KnotSpecI mode mi eager env fe lv) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hdom : EnvDomI fe env) (hdef : EnvDefnI fe env) :
    BodySpecI mode eager env (InLean.whnfBodyI mi fe eager lv)
      (ConLeche.whnfBody (ConLeche.fueledFns mode eager env) env) := by
  intro s₀ d i hs hok hw hc
  sym only [conleche_grind, ConLeche.whnfBody, whnfLoopFuel_eq] =>
    vcgen [InLean.whnfBodyI.eq_def, whnfLoopI_specI ih henv hfe hdom hdef] <;> finish

end WhnfLoop

/-! ## The peel loop -/

section Peel

variable {fe : InLean.FEnv} {lv : Nat}

attribute [conleche_grind =] TrS_mkAppN OkS_mkAppN

/-- An application of a closed head to closed arguments is closed. -/
theorem lbb_mkAppN_closed {f : ConLeche.Expr} {xs : List ConLeche.Expr}
    (hf : f.looseBVarsBounded 0 = true) (hxs : AllClosed xs = true) :
    (ConLeche.Expr.mkAppN f xs).looseBVarsBounded 0 = true :=
  ConLeche.looseBVarsBounded_mkAppN hf (by
    simp only [AllClosed, List.all_eq_true] at hxs; exact hxs)
grind_pattern [conleche_grind] lbb_mkAppN_closed => f.looseBVarsBounded 0, ConLeche.Expr.mkAppN f xs

/-- The peel step keeps a closed instantiated lambda closed at a closed value. -/
theorem lbb_lamPeel {dom body a : ConLeche.Expr} {acc : List ConLeche.Expr}
    (h : ((ConLeche.Expr.lam dom body).instantiateList acc).looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) :
    (body.instantiateList (a :: acc)).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
  rw [ConLeche.Expr.instantiateList_cons]
  exact lbb_instantiate1 ha h.2
grind_pattern [conleche_grind] lbb_lamPeel =>
  ((ConLeche.Expr.lam dom body).instantiateList acc).looseBVarsBounded 0,
  body.instantiateList (a :: acc)

/-- Opening a closed lambda at a closed value: the loop's first peel. -/
theorem lbb_lamOpen {dom body a : ConLeche.Expr}
    (h : (ConLeche.Expr.lam dom body).looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) :
    (body.instantiateList [a]).looseBVarsBounded 0 = true :=
  lbb_lamPeel (acc := []) (by rw [ConLeche.Expr.instantiateList_nil]; exact h) ha
grind_pattern [conleche_grind] lbb_lamOpen =>
  (ConLeche.Expr.lam dom body).looseBVarsBounded 0, body.instantiateList [a]

/-- The pure peel loop at a translated head, stepped in InLean's shape (its
match on InLean's `stripTop`). -/
theorem betaPeelW_TrS_cons {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (s : InLean.CState) {t : Expr} (ht : OkS s t = true)
    (acc : List ConLeche.Expr) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.betaPeelW mode r env d (TrS s t) acc (a :: rest) =
      match EO.stripTop t with
      | .lam _ _ body _ => ConLeche.betaPeelW mode r env d (TrS s body) (a :: acc) rest
      | _ => pure (.cont (ConLeche.Expr.mkAppN ((TrS s t).instantiateList acc) (a :: rest))) := by
  rw [← OkS_stripTop s t] at ht
  conv => lhs; rw [← TrS_stripTop s t]
  conv => rhs; rw [← TrS_stripTop s t]
  generalize hx : EO.stripTop t = x at ht
  cases x with
  | lam n dom body bi => rw [TrS_lam, ConLeche.betaPeelW.eq_2]
  | fvar id => rw [TrS_fvar ht, ConLeche.betaPeelW.eq_def]
  | mvar _ => rw [OkS_mvar] at ht; cases ht
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rw [ConLeche.betaPeelW.eq_def]; rfl

/-- The unmemoised substitution of a peeled group, through the translation
(`TrS_instI`). -/
@[conleche_grind =] theorem TrS_instI_eq {s : InLean.CState} {e : Expr} {vs : List Expr}
    (he : OkS s e = true) (hv : OkSL s vs = true) (hcl : AllClosed (TrSL s vs) = true) :
    TrS s (e.instI vs.toArray) = (TrS s e).instantiateList (TrSL s vs) :=
  (TrS_instI he hv hcl).2

/-- `TrS_instI_eq` at the array as the program's equations state it. -/
@[conleche_grind =] theorem TrS_instI_mk {s : InLean.CState} {e : Expr} {vs : List Expr}
    (he : OkS s e = true) (hv : OkSL s vs = true) (hcl : AllClosed (TrSL s vs) = true) :
    TrS s (e.instI (Array.mk vs)) = (TrS s e).instantiateList (TrSL s vs) :=
  (TrS_instI he hv hcl).2

theorem OkS_instI_mk {s : InLean.CState} {e : Expr} {vs : List Expr}
    (he : OkS s e = true) (hv : OkSL s vs = true) (hcl : AllClosed (TrSL s vs) = true) :
    OkS s (e.instI (Array.mk vs)) = true :=
  (TrS_instI he hv hcl).1
grind_pattern [conleche_grind] OkS_instI_mk => OkS s (e.instI (Array.mk vs))

theorem OkS_instI {s : InLean.CState} {e : Expr} {vs : List Expr}
    (he : OkS s e = true) (hv : OkSL s vs = true) (hcl : AllClosed (TrSL s vs) = true) :
    OkS s (e.instI vs.toArray) = true :=
  (TrS_instI he hv hcl).1
grind_pattern [conleche_grind] OkS_instI => OkS s (e.instI vs.toArray)

/-- **The peel loop** (`betaPeelC_spec`'s twin), over the spine `args[i:]`,
by induction on the arguments left. -/
theorem betaPeelI_specI {d : Nat} :
    ∀ (n : Nat) {args : Array Expr} {i : Nat} {t : Expr} {acc : List Expr} {s₀ : InLean.CState},
      args.size - i = n →
      CSOKI mode eager env s₀ → OkS s₀ t = true → OkSL s₀ acc = true →
      AllClosed (TrSL s₀ acc) = true →
      ConLeche.Expr.WScoped d ((TrS s₀ t).instantiateList (TrSL s₀ acc)) →
      ((TrS s₀ t).instantiateList (TrSL s₀ acc)).looseBVarsBounded 0 = true →
      OkSL s₀ args.toList = true → AllWS d (TrSL s₀ args.toList) →
      AllClosed (TrSL s₀ args.toList) = true →
      ⦃fun s => s = s₀⦄ InLean.betaPeelI mi fe eager lv d t acc args i
      ⦃fun w s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkStep s' w = true ∧
          Runs (ConLeche.betaPeelW mode (ConLeche.fueledFns mode eager env) env d (TrS s₀ t)
            (TrSL s₀ acc) (TrSL s₀ (args.toList.drop i))) (TrStep s' w) ∧
          StepWS d (TrStep s' w) ∧ StepClosed (TrStep s' w) = true; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro args i _ _ _ hn _ _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.betaPeelW.eq_1,
        toList_drop_of_ge (A := args) (i := i) (by omega)] =>
      vcgen [InLean.betaPeelI.eq_def] <;> finish
  | succ n ihr =>
    intro args i _ _ _ hn _ ht _ _ _ _ _ _ _
    sym only [conleche_grind, toList_drop_of_lt (A := args) (i := i) (by omega),
        betaPeelW_TrS_cons _ _ _ ht] =>
      vcgen [InLean.betaPeelI.eq_def, ihr (args := args) (i := i + 1) (by omega)] <;> finish

end Peel

/-! ## The head-normalization loop and its memo policy

The twins of `DiscC4.lean`'s loop lemmas.  The loop (`whnfCoreLoopI`) looks
every key up and stores the keys of a chain at its end; its answer is stated
against the chained `whnfCore` directly.  The keys waiting for the answer
satisfy `PendOKI` at the current state: each, read there, answers what the
current term answers. -/

section CoreLoop

variable {fe : InLean.FEnv} {lv : Nat}

/-- A stuck head translates to a stuck head. -/
theorem isStuckHeadC_TrS {s : InLean.CState} {h : Expr} (hh : InLean.isStuckHeadC h = true)
    (hok : OkS s h = true) : ConLeche.Cached.isStuckHeadC (TrS s h) = true := by
  cases h with
  | fvar id => rw [TrS_fvar hok]; rfl
  | _ => first | rfl | simp [InLean.isStuckHeadC] at hh

/-- A step InLean takes alike in the two modes translates to one con-leche
takes alike (`whnfCoreCheapSafeC`'s twin, read through `mdata`). -/
theorem whnfCoreCheapSafeC_TrS {s : InLean.CState} {e : Expr} (hok : OkS s e = true)
    (h : InLean.whnfCoreCheapSafeC (Expr.getAppFnT e) e = true) :
    ConLeche.Cached.whnfCoreCheapSafeC (TrS s e).getAppFn (TrS s e) = true := by
  rw [← TrS_getAppFnT]
  unfold InLean.whnfCoreCheapSafeC at h
  rw [← TrS_stripTop s e]
  have hokh : OkS s (Expr.getAppFnT e) = true := OkS_getAppFnT s hok
  generalize Expr.getAppFnT e = hd at h hokh
  generalize EO.stripTop e = x at h
  cases x with
  | app f a =>
    simp only [TrS_app, ConLeche.Cached.whnfCoreCheapSafeC]
    cases hd with
    | lam => rw [TrS_lam]
    | fvar id => rw [TrS_fvar hokh]; rfl
    | _ => first | rfl | simp [InLean.isStuckHeadC] at h
  | letE => simp only [TrS_letE]; rfl
  | _ => simp at h

/-- The keys pending in the loop (`PendOK`'s twin), read at the state `s`:
each, well scoped, answers what `e` answers (in the mode `c`). -/
@[expose] def PendOKI (eager : Bool) (env : ConLeche.Env) (c : Bool) (d : Nat)
    (s : InLean.CState) (pend : List Expr) (e : Expr) : Prop :=
  ∀ k ∈ pend, OkS s k = true ∧ ConLeche.Expr.WScoped d (TrS s k) ∧
    ∀ v, Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s e)) v →
      Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s k)) v

@[conleche_grind] theorem PendOKI.nil {c : Bool} {d : Nat} {s : InLean.CState} {e : Expr} :
    PendOKI eager env c d s [] e := by
  intro k hk; exact nomatch hk

/-- The pending keys, read at a later state. -/
theorem PendOKI.tab {c : Bool} {d : Nat} {s s' : InLean.CState} {pend : List Expr} {e : Expr}
    (hp : PendOKI eager env c d s pend e) (ht : TabLe s s') (he : OkS s e = true) :
    PendOKI eager env c d s' pend e := by
  intro k hk
  obtain ⟨hok, hw, hr⟩ := hp k hk
  refine ⟨okS_of_tabLe ht hok, by rw [TrS_of_tabLe ht hok]; exact hw, fun v hv => ?_⟩
  rw [TrS_of_tabLe ht hok]
  exact hr v (by rw [← TrS_of_tabLe ht he]; exact hv)

/-- The term itself joins its pending keys. -/
theorem PendOKI.self {c : Bool} {d : Nat} {s : InLean.CState} {pend : List Expr} {e : Expr}
    (hp : PendOKI eager env c d s pend e) (hok : OkS s e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s e)) :
    PendOKI eager env c d s (e :: pend) e := by
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨hok, hw, fun _ h => h⟩
  · exact hp k hk

/-- The keys past a step on `e`, the term joining them where it is stored. -/
theorem PendOKI.pushSelf {b c : Bool} {d : Nat} {s : InLean.CState} {pend : List Expr} {e : Expr}
    (hp : PendOKI eager env c d s pend e) (hok : OkS s e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s e)) :
    PendOKI eager env c d s (InLean.pushKey b e pend) e := by
  unfold InLean.pushKey
  split
  · exact hp.self hok hw
  · exact hp

/-- Past a continuing step, the pending keys answer what the continuation
answers, read at the state after the step. -/
theorem PendOKI.cont {c : Bool} {d : Nat} {s s' : InLean.CState} {pend : List Expr} {e e' : Expr}
    (hp : PendOKI eager env c d s pend e) (ht : TabLe s s') (he : OkS s e = true)
    (hs : Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
      (TrS s e)) (.cont (TrS s' e'))) :
    PendOKI eager env c d s' pend e' := by
  intro k hk
  obtain ⟨hok, hw, hr⟩ := hp.tab ht he k hk
  refine ⟨hok, hw, fun v hv => hr v ?_⟩
  rw [TrS_of_tabLe ht he]
  exact Runs.whnfCore_of_cont hs hv

/-- The loop's continuing arm: the keys it passes on, the term joining them
where it is stored. -/
theorem PendOKI.push {b c : Bool} {d : Nat} {s s' : InLean.CState} {pend : List Expr}
    {e e' : Expr} (hp : PendOKI eager env c d s pend e) (ht : TabLe s s') (hok : OkS s e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s e))
    (hs : Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
      (TrS s e)) (.cont (TrS s' e'))) :
    PendOKI eager env c d s' (InLean.pushKey b e pend) e' :=
  (hp.pushSelf hok hw).cont ht hok hs
grind_pattern [conleche_grind] PendOKI.push =>
  PendOKI eager env c d s pend e, TabLe s s',
  Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
    (TrS s e)) (.cont (TrS s' e')),
  InLean.pushKey b e pend

/-- The loop's continuing arm, cheap keys: kept past a step the two modes
take alike, dropped past any other. -/
theorem PendOKI.pushCheap {b c : Bool} {d : Nat} {s s' : InLean.CState} {pend : List Expr}
    {e e' : Expr} (hp : PendOKI eager env true d s pend e) (ht : TabLe s s')
    (hok : OkS s e = true) (hw : ConLeche.Expr.WScoped d (TrS s e))
    (hs : Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
      (TrS s e)) (.cont (TrS s' e'))) :
    PendOKI eager env true d s'
      (InLean.pushCheapKey (InLean.whnfCoreCheapSafeC (Expr.getAppFnT e) e) b e pend) e' := by
  unfold InLean.pushCheapKey
  split
  · rename_i hsafe
    rw [← whnfCoreStepW_cheap (whnfCoreCheapSafeC_TrS hok hsafe)] at hs
    exact (hp.pushSelf hok hw).cont ht hok hs
  · exact PendOKI.nil
grind_pattern [conleche_grind] PendOKI.pushCheap =>
  PendOKI eager env true d s pend e, TabLe s s',
  Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
    (TrS s e)) (.cont (TrS s' e')),
  InLean.pushCheapKey (InLean.whnfCoreCheapSafeC (Expr.getAppFnT e) e) b e pend

/-- A memo of backed entries stays backed under inserting backed keys, one
answer for all. -/
theorem UnaryOK.foldl_insert {s : InLean.CState}
    {spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr}
    (hdi : ∀ F d₁ d₂ e, e.wscopedB d₁ = true → e.wscopedB d₂ = true → spec F d₁ e = spec F d₂ e)
    {v : Expr} (hv : OkS s v = true) (hc : (TrS s v).looseBVarsBounded 0 = true) {d : Nat} :
    ∀ {pend : List Expr} {mp : Std.HashMap EKey Expr},
      (∀ k w, mp[EKey.mk k]? = some w → UnaryOK s spec k w) →
      (∀ k ∈ pend, OkS s k = true ∧ ConLeche.Expr.WScoped d (TrS s k) ∧
        ∃ F, spec F d (TrS s k) = .ok (TrS s v)) →
      ∀ k w, (pend.foldl (fun m k => m.insert (EKey.mk k) v) mp)[EKey.mk k]? = some w →
        UnaryOK s spec k w
  | [], _, hm, _ => hm
  | k :: rest, _, hm, hp => by
    obtain ⟨hok, hw, F, hF⟩ := hp k (.head _)
    exact UnaryOK.foldl_insert hdi hv hc (pend := rest)
      (UnaryOK.insert hdi hm hok hw hv hc hF) (fun k' hk' => hp k' (.tail _ hk'))

/-- A pending key, answered by `v` at `e`, is a backed memo entry. -/
theorem PendOKI.backed {c : Bool} {d : Nat} {s : InLean.CState} {pend : List Expr} {e v : Expr}
    (hp : PendOKI eager env c d s pend e)
    (hv : Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s e)) (TrS s v)) :
    ∀ k ∈ pend, OkS s k = true ∧ ConLeche.Expr.WScoped d (TrS s k) ∧
      ∃ F, ConLeche.whnfCore .verified eager env F d (TrS s k) c = .ok (TrS s v) := by
  intro k hk
  obtain ⟨hok, hw, hr⟩ := hp k hk
  exact ⟨hok, hw, hr _ hv⟩

@[conleche_grind =] theorem TabLe_storeChain (s₀ s : InLean.CState) (pend pendC : List Expr)
    (v : Expr) : TabLe s₀ (InLean.storeChain s pend pendC v) = TabLe s₀ s := rfl

@[conleche_grind =] theorem TrS_storeChain (s : InLean.CState) (pend pendC : List Expr)
    (v e : Expr) : TrS (InLean.storeChain s pend pendC v) e = TrS s e := rfl

@[conleche_grind =] theorem OkS_storeChain (s : InLean.CState) (pend pendC : List Expr)
    (v e : Expr) : OkS (InLean.storeChain s pend pendC v) e = OkS s e := rfl

/-- A finished chain's store keeps the invariant: its full keys answer `v`
in the full mode, its cheap keys in the cheap mode (`CSOK.chainStored`'s
twin). -/
theorem CSOKI.chainStored (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat}
    {pend pendC : List Expr} {e v : Expr} (hs : CSOKI .verified eager env s)
    (hp : PendOKI eager env false d s pend e)
    (hv : Runs ((ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s e)) (TrS s v))
    (hpc : PendOKI eager env true d s pendC e)
    (hvc : Runs ((ConLeche.fueledFns .verified eager env).whnfCore true d (TrS s e)) (TrS s v))
    (hokv : OkS s v = true) (hcv : (TrS s v).looseBVarsBounded 0 = true) :
    CSOKI .verified eager env (InLean.storeChain s pend pendC v) :=
  CSOKI.ofRest (hs.keepMemos.memos _ _ s.whnfC s.inferC s.inferIOC s.defeqC s.eagerMemos)
    (UnaryOK.foldl_insert (spec := fun F d e => ConLeche.whnfCore .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnfCore_depth_inv henv F h₁ h₂) hokv hcv
      hs.whnfCoreC (hp.backed hv))
    (UnaryOK.foldl_insert (spec := fun F d e => ConLeche.whnfCore .verified eager env F d e true)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnfCore_depth_inv henv F h₁ h₂) hokv hcv
      hs.whnfCoreCheapC (hpc.backed hvc))
    hs.whnfC hs.inferC hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl

/-- A store with no cheap keys (the chain took a step the modes take
differently, or ended at a hit). -/
theorem CSOKI.chainStored_nil (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat}
    {pend : List Expr} {e v : Expr} (hs : CSOKI .verified eager env s)
    (hp : PendOKI eager env false d s pend e)
    (hv : Runs ((ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s e)) (TrS s v))
    (hokv : OkS s v = true) (hcv : (TrS s v).looseBVarsBounded 0 = true) :
    CSOKI .verified eager env (InLean.storeChain s pend [] v) :=
  CSOKI.ofRest (hs.keepMemos.memos _ _ s.whnfC s.inferC s.inferIOC s.defeqC s.eagerMemos)
    (UnaryOK.foldl_insert (spec := fun F d e => ConLeche.whnfCore .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnfCore_depth_inv henv F h₁ h₂) hokv hcv
      hs.whnfCoreC (hp.backed hv))
    hs.whnfCoreCheapC hs.whnfC hs.inferC hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl

/-- The store at a hit, its keys answered by the hit's answer, read at the
state the keys are pending at. -/
theorem CSOKI.chainStoredHit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat}
    {pend : List Expr} {e r : Expr} (hs : CSOKI .verified eager env s)
    (hp : PendOKI eager env false d s pend e)
    (hl : s.whnfCoreC[EKey.mk e]? = some r) (hok : OkS s e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s e)) :
    CSOKI .verified eager env (InLean.storeChain s pend [] r) := by
  obtain ⟨hokr, hrun, -, hcr⟩ := CSOKI.whnfCore_hit henv hs hl hok hw
  exact CSOKI.chainStored_nil henv hs hp hrun hokr hcr
grind_pattern [conleche_grind] CSOKI.chainStoredHit =>
  CSOKI .verified eager env s, PendOKI eager env false d s pend e, s.whnfCoreC[EKey.mk e]?,
  InLean.storeChain s pend [] r

/-- The store at an easy case: the term is its own answer, in both modes. -/
theorem CSOKI.chainStoredEasy (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat}
    {pend pendC : List Expr} {e : Expr} (hs : CSOKI .verified eager env s)
    (hp : PendOKI eager env false d s pend e) (hpc : PendOKI eager env true d s pendC e)
    (he : InLean.whnfCoreEasy e = true) (hok : OkS s e = true)
    (hc : (TrS s e).looseBVarsBounded 0 = true) :
    CSOKI .verified eager env (InLean.storeChain s pend pendC e) :=
  CSOKI.chainStored henv hs hp (Runs.whnfCore_easyI he hok) hpc (Runs.whnfCore_easyI he hok) hok hc
grind_pattern [conleche_grind] CSOKI.chainStoredEasy =>
  CSOKI .verified eager env s, PendOKI eager env false d s pend e,
  PendOKI eager env true d s pendC e, InLean.whnfCoreEasy e, InLean.storeChain s pend pendC e

/-- The loop's answering arm in the full mode: the chain's keys, the term
joining them where it is stored, stored with the answer, read at the state
after the step (`CSOK.chainStoredDone`'s twin). -/
theorem CSOKI.chainStoredDone (henv : ConLeche.EnvWF env) {b : Bool} {s₀ s : InLean.CState}
    {d : Nat} {pend pendC : List Expr} {e v : Expr} (hs : CSOKI .verified eager env s)
    (ht : TabLe s₀ s)
    (hp : PendOKI eager env false d s₀ pend e) (hpc : PendOKI eager env true d s₀ pendC e)
    (hok : OkS s₀ e = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ e))
    (hst : Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env
      false d (TrS s₀ e)) (.done (TrS s v)))
    (hokv : OkS s v = true) (hcv : (TrS s v).looseBVarsBounded 0 = true) :
    CSOKI .verified eager env (InLean.storeChain s (InLean.pushKey b e pend)
      (InLean.pushCheapKey (InLean.whnfCoreCheapSafeC (Expr.getAppFnT e) e) b e pendC) v) := by
  have he : TrS s e = TrS s₀ e := TrS_of_tabLe ht hok
  have hv : Runs ((ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s e))
      (TrS s v) := by rw [he]; exact Runs.whnfCore_of_done hst
  have hp' := (hp.pushSelf (b := b) hok hw).tab ht hok
  unfold InLean.pushCheapKey
  split
  · rename_i hsafe
    have hvc : Runs ((ConLeche.fueledFns .verified eager env).whnfCore true d (TrS s e))
        (TrS s v) := by
      rw [he]; exact Runs.whnfCore_of_doneCheap (whnfCoreCheapSafeC_TrS hok hsafe) hst
    exact CSOKI.chainStored henv hs hp' hv ((hpc.pushSelf (b := b) hok hw).tab ht hok) hvc hokv hcv
  · exact CSOKI.chainStored_nil henv hs hp' hv hokv hcv
grind_pattern [conleche_grind] CSOKI.chainStoredDone =>
  InLean.storeChain s (InLean.pushKey b e pend)
    (InLean.pushCheapKey (InLean.whnfCoreCheapSafeC (Expr.getAppFnT e) e) b e pendC) v,
  Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env
      false d (TrS s₀ e)) (.done (TrS s v)),
  TabLe s₀ s

/-- **The head-normalization loop** (`whnfCoreLoopC_spec`'s twin), over the
step's callee specs: it answers the chained `whnfCore` of its term, by
induction on the shared step budget; the memo is looked up at every key and
written with the chain's keys at its end. -/
theorem whnfCoreLoopI_specI (ih : KnotSpecI .verified .verified eager env fe lv)
    (happ : WhnfAppSpecI eager env fe lv) (hstuck : WhnfStuckSpecI eager env fe lv)
    (hproj : ReduceProjSpecI eager env fe lv) (henv : ConLeche.EnvWF env) {c : Bool}
    {d : Nat} (n : Nat) :
    ∀ {pend pendC : List Expr} {i : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ →
      OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
      (TrS s₀ i).looseBVarsBounded 0 = true →
      PendOKI eager env c d s₀ pend i → PendOKI eager env true d s₀ pendC i →
      ⦃fun s => s = s₀⦄ InLean.whnfCoreLoopI .verified fe eager lv c d n pend pendC i
      ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s₀ i)) (TrS s' v) ∧
        ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  induction n with
  | zero =>
    intro pend pendC i s₀ hs hok hw hc hp hpc
    sym only [conleche_grind] => vcgen [InLean.whnfCoreLoopI.eq_def] <;> finish
  | succ n ihn =>
    intro pend pendC i s₀ hs hok hw hc hp hpc
    sym only [conleche_grind, CSOKI.chainStored henv, CSOKI.chainStored_nil henv,
        CSOKI.chainStoredDone henv, CSOKI.chainStoredHit henv, CSOKI.chainStoredEasy henv,
        CSOKI.whnfCore_hit henv, CSOKI.whnfCoreCheap_hit henv] =>
      vcgen [InLean.whnfCoreLoopI.eq_def, InLean.storeChainI, InLean.whnfCoreLookupI,
        whnfCoreStepI_spec ih happ hstuck hproj, ihn] <;> finish

/-- **The head-normalization body** (`whnfCoreBodyC_spec`'s twin): the loop
with no key pending. -/
theorem whnfCoreBodyI_specI (ih : KnotSpecI .verified .verified eager env fe lv)
    (happ : WhnfAppSpecI eager env fe lv) (hstuck : WhnfStuckSpecI eager env fe lv)
    (hproj : ReduceProjSpecI eager env fe lv) (henv : ConLeche.EnvWF env) (c : Bool) :
    BodySpecI .verified eager env (InLean.whnfCoreBodyI .verified fe eager lv c)
      (fun d i => (ConLeche.fueledFns .verified eager env).whnfCore c d i) := by
  intro s₀ d i hs hok hw hc
  sym only [conleche_grind] =>
    vcgen [InLean.whnfCoreBodyI.eq_def, whnfCoreLoopI_specI ih happ hstuck hproj henv] <;> finish

end CoreLoop

/-! ## The argument loop -/

section AppLoop

variable {fe : InLean.FEnv} {lv : Nat}

/-- **The ι step's spec** (`iotaRecC_spec`'s twin), this lane's to prove
(`WalksIotaRec.lean`); the argument loop takes it as a named callee spec.  The
step reads the spine `h args[0:k]` as an array; its specification is the
ι step at the redex rebuilt as a list. -/
abbrev IotaRecSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) :
    Prop :=
  ∀ {d : Nat} {h : Expr} {args : Array Expr} {k : Nat} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → Expr.getAppFnT h = h → k ≤ args.size →
    OkS s₀ h = true → OkSL s₀ args.toList = true → AllWS d (TrSL s₀ args.toList) →
    AllClosed (TrSL s₀ args.toList) = true →
    ⦃fun s => s = s₀⦄ InLean.iotaRecI .verified fe eager lv d h args k
    ⦃fun o s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.iotaRec .verified (ConLeche.fueledFns .verified eager env) env d
        (ConLeche.Expr.mkAppN (TrS s₀ h) (TrSL s₀ (args.toList.take k)))) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄

theorem iotaNumArgs_eq : ∀ (e : Expr) (n : Nat), InLean.iotaNumArgs e n = Expr.getAppNumArgsT e + n
  | .app f _, n => by rw [InLean.iotaNumArgs, iotaNumArgs_eq f, Expr.getAppNumArgsT]; omega
  | .mdata _ e, n => by rw [InLean.iotaNumArgs, iotaNumArgs_eq e, Expr.getAppNumArgsT]
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _
  | .forallE .., _ | .letE .., _ | .lit _, _ | .proj .., _ => by
    simp [InLean.iotaNumArgs, Expr.getAppNumArgsT]

/-- The arity read is the recursor view's. -/
theorem recArity_of_recAt (n : Name) :
    fe.recArity? n = (fe.recAt? n).map fun p => (majorIdxOf p.1, p.1.levelParams.length) := by
  unfold InLean.FEnv.recArity? InLean.FEnv.recAt?
  cases fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | recInfo rv => rfl
    | quotInfo q =>
      simp only [InLean.quotRecVal]
      cases hk : q.kind <;> simp [majorIdxOf] <;> decide
    | _ => rfl

theorem getAppFnT_getAppFnT (e : Expr) : Expr.getAppFnT (Expr.getAppFnT e) = Expr.getAppFnT e := by
  induction e with
  | app f a ih _ => exact ih
  | mdata _ x ih => exact ih
  | _ => rfl

/-- Where the arity pre-check fails, the ι step has nothing to do
(`iotaRecI_of_arityOk_false`'s twin). -/
theorem iotaRecI_of_arityOk_false {d : Nat} {e : Expr} (h : InLean.iotaArityOk fe e = false) :
    InLean.iotaRecI .verified fe eager lv d (Expr.getAppFnT e) (InLean.getAppArgsArr e)
      (InLean.iotaNumArgs e 0) = pure none := by
  unfold InLean.iotaArityOk at h
  unfold InLean.iotaRecI
  cases hg : Expr.getAppFnT e with
  | const c us =>
    rw [hg] at h
    simp only [recArity_of_recAt] at h
    simp only
    cases hf : fe.recAt? c with
    | none => rfl
    | some p =>
      obtain ⟨rv, isQuot⟩ := p
      rw [hf] at h
      simp only [Option.map_some, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      simp only
      rw [ite_eq_right_iff.2 (fun hc => absurd hc ?_)]
      intro hc
      obtain ⟨hlen, -, hlvl, -⟩ := hc
      exact h.elim (fun h' => h' hlen) (fun h' => h' hlvl)
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
theorem iotaArityOk_guardI {d : Nat} {e : Expr} :
    (if InLean.iotaArityOk fe e then
        InLean.iotaRecI .verified fe eager lv d (Expr.getAppFnT e) (InLean.getAppArgsArr e)
          (InLean.iotaNumArgs e 0)
      else pure none)
      = InLean.iotaRecI .verified fe eager lv d (Expr.getAppFnT e) (InLean.getAppArgsArr e)
          (InLean.iotaNumArgs e 0) := by
  by_cases h : InLean.iotaArityOk fe e = true
  · rw [ite_eq_left_iff.2 (fun hc => absurd h hc)]
  · rw [ite_eq_right_iff.2 (fun hc => absurd hc h), iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

/-- The pure argument loop at a translated head, stepped in InLean's shape. -/
theorem whnfAppW_TrS_cons {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (s : InLean.CState) {v : Expr} (hv : OkS s v = true)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.whnfAppW mode r env d (TrS s v) (a :: rest) =
      match EO.stripTop v with
      | .lam _ _ body _ => ConLeche.betaPeelW mode r env d (TrS s body) [a] rest
      | _ => (do
        match ← ConLeche.iotaRec mode r env d (.app (TrS s v) a) with
        | some e'' => pure (.cont (ConLeche.Expr.mkAppN e'' rest))
        | none => ConLeche.whnfAppW mode r env d (.app (TrS s v) a) rest) := by
  rw [← OkS_stripTop s v] at hv
  conv => lhs; rw [← TrS_stripTop s v]
  conv => rhs; rw [← TrS_stripTop s v]
  generalize hx : EO.stripTop v = x at hv
  cases x with
  | lam n dom body bi => rw [TrS_lam, ConLeche.whnfAppW.eq_2]
  | fvar id => rw [TrS_fvar hv, ConLeche.whnfAppW.eq_def]; rfl
  | mvar _ => rw [OkS_mvar] at hv; cases hv
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rw [ConLeche.whnfAppW.eq_def]; rfl

/-- The peel loop's first binder: a well-scoped lambda opened at a
well-scoped argument (`wscoped_peel` at an empty accumulator). -/
theorem wscoped_openI {s : InLean.CState} {d : Nat} {ty : ConLeche.Expr} {body a : Expr}
    (hl : ConLeche.Expr.WScoped d (.lam ty (TrS s body)))
    (ha : ConLeche.Expr.WScoped d (TrS s a)) :
    ConLeche.Expr.WScoped d ((TrS s body).instantiateList (TrSL s [a])) := by
  rw [TrSL_cons, TrSL_nil, ConLeche.Expr.instantiateList_cons, ConLeche.Expr.instantiateList_nil]
  rw [ConLeche.Expr.WScoped] at hl
  exact ConLeche.Expr.WScoped.instantiate1_gen ha 0 hl.2
grind_pattern [conleche_grind] wscoped_openI =>
  ConLeche.Expr.WScoped d (.lam ty (TrS s body)), (TrS s body).instantiateList (TrSL s [a])

/-- The spine of one more application: its arguments have readings. -/
theorem OkSL_appArgs_app {s : InLean.CState} {v a : Expr} (hv : OkS s v = true)
    (ha : OkS s a = true) : OkSL s (appArgs (.app v a)) = true :=
  OkSL_appArgs s (by rw [OkS_app, hv, ha]; rfl)
grind_pattern [conleche_grind] OkSL_appArgs_app => OkS s v, OkS s a, appArgs (.app v a)

/-- The spine of one more application: its arguments are closed. -/
theorem allClosed_getAppArgs_app {v a : ConLeche.Expr} (hv : v.looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) : AllClosed (ConLeche.Expr.app v a).getAppArgs = true :=
  allClosed_getAppArgs (by rw [ConLeche.Expr.looseBVarsBounded, hv, ha]; rfl)
grind_pattern [conleche_grind] allClosed_getAppArgs_app =>
  v.looseBVarsBounded 0, a.looseBVarsBounded 0, (ConLeche.Expr.app v a).getAppArgs

/-- **The bulk-beta argument loop** (`whnfAppC_spec`'s twin): it discharges
`WhnfAppSpecI` given the ι step's spec, by induction on the arguments left. -/
theorem whnfAppI_specI (hiota : IotaRecSpecI eager env fe lv) : WhnfAppSpecI eager env fe lv := by
  intro d v args i
  generalize hn : args.size - i = n
  induction n generalizing v i with
  | zero =>
    intro _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.whnfAppW.eq_1,
        toList_drop_of_ge (A := args) (i := i) (by omega)] =>
      vcgen [InLean.whnfAppI.eq_def] <;> finish
  | succ n ihr =>
    intro _ hs hv _ _ _ _ _
    rw [InLean.whnfAppI.eq_def]; simp only [iotaArityOk_guardI]
    sym only [conleche_grind, toList_drop_of_lt (A := args) (i := i) (by omega),
        whnfAppW_TrS_cons _ _ _ hv, getAppFnT_getAppFnT, iotaNumArgs_length, List.take_length,
        ConLeche.Expr.mkAppN_getApp] =>
      vcgen [InLean.pollC, hiota,
        betaPeelI_specI (mode := .verified) (lv := lv) (fe := fe) n (args := args) (i := i + 1)
          (by omega),
        ihr (i := i + 1) (by omega)] <;> finish

end AppLoop




/-! ## The projection rule -/

section Proj

variable {fe : InLean.FEnv} {lv : Nat}

theorem peelPis_TrS (s : InLean.CState) : ∀ (n : Nat) (t : Expr),
    (ConLeche.Expr.peelPis n (TrS s t)).isSome = (InLean.peelPis n t).isSome
  | 0, t => by simp [ConLeche.Expr.peelPis, InLean.peelPis]
  | n + 1, .forallE _ _ b _ => by
    rw [TrS_forallE, ConLeche.Expr.peelPis, InLean.peelPis, peelPis_TrS s n b]
  | n + 1, .mdata _ e => by rw [TrS_mdata, InLean.peelPis, peelPis_TrS s (n + 1) e]
  | n + 1, .fvar id => by
    simp only [InLean.peelPis, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | n + 1, .bvar _ | n + 1, .mvar _ | n + 1, .sort _ | n + 1, .const .. | n + 1, .app ..
  | n + 1, .lam .. | n + 1, .letE .. | n + 1, .lit _ | n + 1, .proj .. => rfl

/-- The projection certificate through the views. -/
theorem projCert_TrS (hv : EnvViewI fe env) (s : InLean.CState) (k : Name) (args : List Expr) :
    ConLeche.projCert env (toName k) (TrSL s args) = InLean.projCertF fe k args := by
  unfold ConLeche.projCert InLean.projCertF
  cases hc : fe.ctorView? k with
  | none =>
    split
    · rename_i cv nP nF T hf; exact absurd hf (hv.ctorNone k hc cv nP nF T)
    · rfl
  | some p =>
    obtain ⟨cv, nP, nF, T⟩ := p
    obtain ⟨ccv, hrel, hf⟩ := hv.ctor k cv nP nF T hc
    rw [hf]
    simp only [ConLeche.teleArityOk, InLean.teleArityOk, TrSL, List.length_map]
    rw [← hrel.2.2.trS s, peelPis_TrS]

theorem ite_pos' {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem TrS_getD (s : InLean.CState) (l : List Expr) (n : Nat) :
    TrS s (l.getD n (.bvar 0)) = (TrSL s l).getD n (.bvar 0) := by
  simp only [List.getD, TrSL, List.getElem?_map]
  cases l[n]? <;> rfl

/-- **The projection rule** (`reduceProjCoreC_spec`'s twin): it discharges
`ReduceProjSpecI`. -/
theorem reduceProjCoreI_specI (ih : KnotSpecI .verified .verified eager env fe lv) (hdom : EnvDomI fe env)
    (hv : EnvViewI fe env) : ReduceProjSpecI eager env fe lv := by
  intro d sn i c s₀ hs hok hw hcl
  refine tripleI_iff_run.2 fun o s' hr => ?_
  unfold InLean.reduceProjCoreI at hr
  obtain ⟨e', s₁, he', hr⟩ := bind_run hr
  obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ :=
    tripleI_iff_run.1 (projLitToCtorI_specI ih hdom hs hok hw hcl) e' s₁ he'
  unfold ConLeche.reduceProjCore
  have hfin : CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (match env.findProj? (toName sn) i with
        | some entry =>
          match (TrS s₁ e').getAppFn with
          | .const k us =>
            if k = entry.ctor ∧ i < entry.numFields ∧
                (TrS s₁ e').getAppArgs.length = entry.numParams + entry.numFields ∧
                us.length = entry.levelParams.length then
              if ConLeche.projCertAt env ConLeche.CheckMode.verified.verifiedChecks k
                  (TrS s₁ e').getAppArgs then
                pure (some ((TrS s₁ e').getAppArgs.getD (entry.numParams + i) (.bvar 0)))
              else pure none
            else pure none
          | _ => pure none
        | none => pure none : ConLeche.FueledM (Option ConLeche.Expr)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true := by
    cases hp : fe.findProj? sn i with
    | none =>
      rw [hp] at hr
      obtain ⟨rfl, rfl⟩ := pure_run hr
      rw [hv.projNone sn i hp]
      exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
    | some entry =>
      rw [hp] at hr
      obtain ⟨ce, hce, hctor, hnF, hnP, hlps⟩ := hv.proj sn i entry hp
      rw [hce]
      simp only
      by_cases hA : ∃ k us, Expr.getAppFnT e' = .const k us
      · obtain ⟨k, us, hA⟩ := hA
        rw [TrS_getAppFn_const s₁ hA]
        rw [hA] at hr
        simp only at hr ⊢
        have hlen : (TrS s₁ e').getAppArgs.length = (appArgs e').length := by
          rw [← TrSL_appArgs, TrSL, List.length_map]
        have hcond : (toName k = ce.ctor ∧ i < ce.numFields ∧
            (TrS s₁ e').getAppArgs.length = ce.numParams + ce.numFields ∧
            (us.map trL).length = ce.levelParams.length) ↔
            ((k == entry.ctor) = true ∧ i < entry.numFields ∧
              (appArgs e').length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length) := by
          rw [hctor, hnF, hnP, hlps, hlen, toName_eq_iff, beq_iff_eq]; simp
        have hargs : OkSL s₁ (appArgs e') = true := OkSL_appArgs s₁ hok₁
        by_cases hc : (k == entry.ctor) = true ∧ i < entry.numFields ∧
            (appArgs e').length = entry.numParams + entry.numFields ∧
            us.length = entry.levelParams.length
        · rw [ite_pos' (hcond.2 hc)]
          rw [ite_pos' hc] at hr
          have hcert : ConLeche.projCertAt env ConLeche.CheckMode.verified.verifiedChecks (toName k)
              (TrS s₁ e').getAppArgs = InLean.projCertAtF fe
                InLean.CheckMode.verified.verifiedChecks k (appArgs e') := by
            simp only [ConLeche.projCertAt, InLean.projCertAtF, ConLeche.CheckMode.verifiedChecks,
              InLean.CheckMode.verifiedChecks, ↓reduceIte]
            rw [← TrSL_appArgs, projCert_TrS hv]
          rw [hcert]
          by_cases hpc : InLean.projCertAtF fe InLean.CheckMode.verified.verifiedChecks k
              (appArgs e') = true
          · rw [ite_pos' hpc]; rw [ite_pos' hpc] at hr
            obtain ⟨rfl, rfl⟩ := pure_run hr
            have hidx : entry.numParams + i < (appArgs e').length := by omega
            have hmem : (appArgs e').getD (entry.numParams + i) (.bvar 0) ∈ appArgs e' := by
              have : (appArgs e').getD (entry.numParams + i) (.bvar 0) =
                  (appArgs e')[entry.numParams + i] := by
                simp [List.getD, List.getElem?_eq_getElem hidx]
              rw [this]; exact List.getElem_mem hidx
            have htr : TrS s₁ ((appArgs e').getD (entry.numParams + i) (.bvar 0)) =
                (TrS s₁ e').getAppArgs.getD (ce.numParams + i) (.bvar 0) := by
              rw [TrS_getD, TrSL_appArgs, hnP]
            have hmemT : TrS s₁ ((appArgs e').getD (entry.numParams + i) (.bvar 0)) ∈
                (TrS s₁ e').getAppArgs := by
              rw [← TrSL_appArgs]; exact List.mem_map_of_mem hmem
            refine ⟨hs₁, ht₁, ?_, ?_, ?_, ?_⟩
            · rw [OkO_some]
              simp only [OkSL, List.all_eq_true] at hargs; exact hargs _ hmem
            · rw [TrO_some, htr, hnP]; exact Runs.pure _
            · exact allWS_getAppArgs hw₁ _ hmemT
            · rw [TrO_some, OptClosed_some]
              have := allClosed_getAppArgs hc₁
              simp only [AllClosed, List.all_eq_true] at this; exact this _ hmemT
          · rw [ite_neg' hpc]; rw [ite_neg' hpc] at hr
            obtain ⟨rfl, rfl⟩ := pure_run hr
            exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
        · rw [ite_neg' (fun h => hc (hcond.1 h))]
          rw [ite_neg' hc] at hr
          obtain ⟨rfl, rfl⟩ := pure_run hr
          exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
      · have hA' : ∀ k us, Expr.getAppFnT e' ≠ .const k us := fun k us h => hA ⟨k, us, h⟩
        have hT := TrS_getAppFn_notConst s₁ hA'
        have hr' : (pure none : InLean.CheckCM (Option Expr)) s₁ = .ok (o, s') := by
          rw [← hr]
          generalize hx : Expr.getAppFnT e' = x at hA'
          cases x with
          | const k us => exact absurd rfl (hA' k us)
          | _ => rfl
        obtain ⟨rfl, rfl⟩ := pure_run hr'
        refine ⟨hs₁, ht₁, rfl, ?_, trivial, rfl⟩
        generalize hx : (TrS s₁ e').getAppFn = x at hT
        cases x with
        | const k us => exact absurd rfl (hT k us)
        | _ => exact Runs.pure _
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfin
  exact ⟨h1, h2, h3, Runs.bind hrun₁ h4, h5, h6⟩

end Proj

end InLeanProof
