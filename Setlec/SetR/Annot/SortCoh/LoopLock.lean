import Setlec.SetR.Annot.SortCoh.CoreLock

/-!
# Run-level sort coherence — the loop-level lockstep tier

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-! ### The loop-level lockstep tier (loopLock's statement kit)

The whnf-loop lockstep the proj/iota discharges ride (the mapped
arc): the carrier `LoopReaches` (loop steps compose the nine landed
preservers — no new species), the out-shapes (`LoopLockOut`:
pack ∨ re-based seam ∨ nat split — the nat tier is wholesale
Θ-family, deferred as raw data with a PROGRESS MARKER so the
disjunct cannot be satisfied vacuously), the recursion bar
`LoopBelow` (knot-sum then loop-budget-sum; `fc` fixed — the loop
tier never descends cert fuel), and the two routed step Props
(`LoopIotaStep`/`LoopProjStep`, each discharged at its own seal —
coreLock's recHead/projHead seams are UNPACKED through them, since
no sort premise exists at scrutinee/major level). -/

/-- `Q` survives a projection fire (scrutinee whnf'd, field
extracted, spine kept; at `FrameQ` this is the model's projection
law on the whnf'd constructor form — the models-public-interface
theorems — composed with the claims' whnf preservation). -/
def QPreserveProjFireF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' c : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    Q d (Setlec.Expr.mkAppN (.proj sn i e) as) c →
    Q d (Setlec.Expr.mkAppN h' as) c

/-- The subject package survives a projection fire (supplier: the
whnf/core preservation family, `EnvWF`-backed, own seal). -/
def InvPreserveProjFireF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e) as) →
    SubjInv d (Setlec.Expr.mkAppN h' as)

/-- Cross-pairing survives a projection fire (left slot; supplier:
the whnf/core leaf-subset family). -/
def PairedPreserveProjFireF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' c : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e) as) c →
    PairedLeaves (Setlec.Expr.mkAppN h' as) c

/-- **The loop-level carrier**: reachability by whole-subject loop
steps (full core runs, δ, nat) and embedded contraction traces. -/
inductive LoopReaches (μ : CheckMode) (env : Env) (d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : LoopReaches μ env d e e
  | core (g : Nat) {s s' w : Expr}
      (h : whnfCore μ env g d s = .ok s')
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | delta {s s' w : Expr}
      (h : Setlec.unfoldDefinition env s = some s')
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | nat (g : Nat) {s s' w : Expr}
      (h : Setlec.reduceNat (Setlec.pureFns μ env g) env d s
        = .ok (some s'))
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | contract {s t w : Expr} (h : Contracts μ env d s t)
      (rest : LoopReaches μ env d t w) : LoopReaches μ env d s w
  | projFire (sn : Name) (i g : Nat) (e w e₃ h' : Expr)
      (entry : Setlec.ProjEntry) (us : List Level)
      (as : List Expr) {t : Expr}
      (hw : whnf μ env g d e = .ok w)
      (hlit : Setlec.projLitToCtorP μ env g d w = .ok e₃)
      (hfn : e₃.getAppFn = .const entry.ctor us)
      (hf : env.findProj? sn i = some entry)
      (hnat : entry.native = true)
      (hi : i < entry.numFields)
      (hlen : e₃.getAppArgs.length
        = entry.numParams + entry.numFields)
      (hfield : whnfCore μ env g d
        (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
        = .ok h')
      (rest : LoopReaches μ env d (Setlec.Expr.mkAppN h' as) t) :
      LoopReaches μ env d
        (Setlec.Expr.mkAppN (.proj sn i e) as) t

/-- Reachability composes. -/
theorem LoopReaches.trans {μ : CheckMode} {env : Env} {d : Nat}
    {u w x : Expr} (h₁ : LoopReaches μ env d u w)
    (h₂ : LoopReaches μ env d w x) : LoopReaches μ env d u x := by
  induction h₁ with
  | refl e => exact h₂
  | core g h rest ih => exact .core g h (ih h₂)
  | delta h rest ih => exact .delta h (ih h₂)
  | nat g h rest ih => exact .nat g h (ih h₂)
  | contract h rest ih => exact .contract h (ih h₂)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact .projFire sn i g e w e₃ h' entry us as hw hlit hfn hf
      hnat hi hlen hfield (ih h₂)

/-- Q rides the loop carrier (the nine step preservers). -/
theorem LoopReaches.q_transport {μ : CheckMode} {env : Env} {d : Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hQP : QPreserveProjFireF μ env Q)
    {u w c : Expr} (h : LoopReaches μ env d u w) :
    Q d u c → Q d w c := by
  induction h with
  | refl e => exact id
  | core g h rest ih => exact fun hq => ih (hQC h hq)
  | delta h rest ih => exact fun hq => ih (hQD h hq)
  | nat g h rest ih => exact fun hq => ih (hQN h hq)
  | contract h rest ih =>
    exact fun hq => ih (h.q_transport hQB hQZ hQH hq)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact fun hq => ih (hQP hw hlit hfn hf hnat hi hlen hfield hq)

/-- `SubjInv` rides the loop carrier. -/
theorem LoopReaches.subjInv {μ : CheckMode} {env : Env} {d : Nat}
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hLS : LeavesSubCoreF μ env)
    (hIP : InvPreserveProjFireF μ env)
    {u w : Expr} (h : LoopReaches μ env d u w)
    (hI : SubjInv d u) : SubjInv d w := by
  induction h with
  | refl e => exact hI
  | core g h rest ih => exact ih (hIC h hI)
  | delta h rest ih => exact ih (hID h hI)
  | nat g h rest ih => exact ih (hIN h hI)
  | contract h rest ih => exact ih (h.subjInv hIC hLS hI)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact ih (hIP hw hlit hfn hf hnat hi hlen hfield hI)

/-- Cross-pairing rides the carrier one side at a time (left-slot
species; the embedded contraction uses a refl other-trace). -/
theorem LoopReaches.pairing_left {μ : CheckMode} {env : Env}
    {d : Nat}
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env) (hLS : LeavesSubCoreF μ env)
    (hLP : PairedPreserveProjFireF μ env)
    {u w c : Expr} (h : LoopReaches μ env d u w) :
    PairedLeaves u c → PairedLeaves w c := by
  induction h with
  | refl e => exact id
  | core g h rest ih => exact fun hp => ih (hLC h hp)
  | delta h rest ih => exact fun hp => ih (hLD h hp)
  | nat g h rest ih => exact fun hp => ih (hLN h hp)
  | contract h rest ih =>
    exact fun hp => ih (Contracts.pairing hLS h (.refl c) hp)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact fun hp => ih (hLP hw hlit hfn hf hnat hi hlen hfield hp)

/-- **The loop-tier seam set** (the audit fact IN THE TYPE): the
walk never ships a projHead seam — coreLock's projHead seams are
unpacked through the routed step Prop — so the loop-tier seam type
has exactly four constructors, and top consumers never face their
own shape. -/
inductive LoopSeam (μ : CheckMode) (env : Env) (fc d : Nat) :
    Expr → Expr → Prop
  | certHead (F₁ F₂ : Expr) (as bs : List Expr)
      (hba : F₁.looseBVarsBounded 0 = true)
      (hbb : F₂.looseBVarsBounded 0 = true)
      (hc : isDefEqCore μ env fc d F₁ F₂ = .ok true)
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      LoopSeam μ env fc d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs)
  | recHead (n : Name) (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rules : List Setlec.RecRule) (us us' : List Level)
      (as bs : List Expr)
      (hf : env.find? n = some (.recInfo cv mI rP rules))
      (hev : ∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ'))
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      LoopSeam μ env fc d (Setlec.Expr.mkAppN (.const n us) as)
        (Setlec.Expr.mkAppN (.const n us') bs)
  | deadL (u v u' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
      (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, u' ≠ .lam n ty body m)
      (hns : ∀ ℓ, u' ≠ .sort ℓ) :
      LoopSeam μ env fc d u v
  | deadR (u v v' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d v = .ok v')
      (hnc : ∀ p q, v'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, v' ≠ .lam n ty body m)
      (hns : ∀ ℓ, v' ≠ .sort ℓ) :
      LoopSeam μ env fc d u v

def LoopSeamOut (μ : CheckMode) (env : Env) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ l₁ l₂ : Nat) : Prop :=
  ∃ w₁ w₂ c₁ c₂ lc₁ lc₂, c₁ ≤ f₁ ∧ c₂ ≤ f₂ ∧
    lc₁ ≤ l₁ ∧ lc₂ ≤ l₂ ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d lc₁ w₁
      = .ok u' ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d lc₂ w₂
      = .ok v' ∧
    LoopReaches μ env d u w₁ ∧ LoopReaches μ env d v w₂ ∧
    LoopSeam μ env fc d w₁ w₂

/-- **The nat split** (the Θ-family deferral, PROGRESS-MARKED): a
last-synced zipped pair whose next core outputs carry at least one
`reduceNat` fire — value divergence between zipped sides traces to
buried certs, so the loop tier hands the raw data to the consumers
(sort-premised tops kill the fired side by `NatStepNoSort`;
scrutinee/major consumers route through their own cert's Θ-funnel).
The `isSome` marker is what keeps this disjunct from absorbing the
whole theorem vacuously. -/
def NatSplitOut (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ l₁ l₂ : Nat) : Prop :=
  ∃ p₁ p₂ t₁ t₂ g₁ g₂ gn₁ gn₂ o₁ o₂ c₁ c₂ lc₁ lc₂,
    c₁ ≤ f₁ ∧ c₂ ≤ f₂ ∧ lc₁ ≤ l₁ ∧ lc₂ ≤ l₂ ∧
    LoopReaches μ env d u p₁ ∧ LoopReaches μ env d v p₂ ∧
    CertZip μ env fc d t₁ t₂ ∧ SubjInv d t₁ ∧ SubjInv d t₂ ∧
    PairedLeaves t₁ t₂ ∧ Q d t₁ t₂ ∧
    whnfCore μ env g₁ d p₁ = .ok t₁ ∧
    whnfCore μ env g₂ d p₂ = .ok t₂ ∧
    Setlec.reduceNat (Setlec.pureFns μ env gn₁) env d t₁
      = .ok o₁ ∧
    Setlec.reduceNat (Setlec.pureFns μ env gn₂) env d t₂
      = .ok o₂ ∧
    (o₁.isSome = true ∨ o₂.isSome = true) ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d lc₁ p₁
      = .ok u' ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d lc₂ p₂
      = .ok v'

/-- **loopLock's conclusion** (the ratified self-similar shape): a
strictly-positive inductive — outputs zipped with the invariants, a
re-based seam, the nat split, or the proj split whose midsection
NESTS the scrutinee-level out (the discharge forwards whatever the
scrutinee analysis produced; the Θ-arc consumes it whole).  The
dual-fire marker keeps the proj split progress-marked. -/
inductive LoopLockOut (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc d : Nat) :
    Expr → Expr → Expr → Expr → Nat → Nat → Nat → Nat → Prop
  | pack {u v u' v' : Expr} {f₁ f₂ l₁ l₂ : Nat}
      (hz : CertZip μ env fc d u' v') (hI₁ : SubjInv d u')
      (hI₂ : SubjInv d v') (hp : PairedLeaves u' v')
      (hq : Q d u' v') :
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂
  | seam {u v u' v' : Expr} {f₁ f₂ l₁ l₂ : Nat}
      (h : LoopSeamOut μ env fc d u v u' v' f₁ f₂ l₁ l₂) :
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂
  | natSplit {u v u' v' : Expr} {f₁ f₂ l₁ l₂ : Nat}
      (h : NatSplitOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂) :
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂
  | projSplit {u v u' v' : Expr} {f₁ f₂ l₁ l₂ : Nat}
      (sn : Name) (i : Nat) (e₁ e₂ w₁ w₂ e₃₁ e₃₂ : Expr)
      (as bs : List Expr)
      (g₁ g₂ gp₁ gp₂ gl₁ gl₂ c₁ c₂ lc₁ lc₂ : Nat)
      (hb₁ : c₁ ≤ f₁) (hb₂ : c₂ ≤ f₂)
      (hlb₁ : lc₁ ≤ l₁) (hlb₂ : lc₂ ≤ l₂)
      (hg₁ : g₁ ≤ f₁) (hg₂ : g₂ ≤ f₂)
      (hgp₁ : gp₁ ≤ f₁) (hgp₂ : gp₂ ≤ f₂)
      (hr₁ : LoopReaches μ env d u
        (Setlec.Expr.mkAppN (.proj sn i e₁) as))
      (hr₂ : LoopReaches μ env d v
        (Setlec.Expr.mkAppN (.proj sn i e₂) bs))
      (hze : CertZip μ env fc d e₁ e₂)
      (hlen : as.length = bs.length)
      (hargs : ∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
        CertZip μ env fc d as[j] bs[j])
      (hw₁ : whnf μ env g₁ d e₁ = .ok w₁)
      (hw₂ : whnf μ env g₂ d e₂ = .ok w₂)
      (hnested : LoopLockOut μ env Q fc d e₁ e₂ w₁ w₂ gp₁ gp₂
        gl₁ gl₂)
      (hlit₁ : Setlec.projLitToCtorP μ env g₁ d w₁ = .ok e₃₁)
      (hlit₂ : Setlec.projLitToCtorP μ env g₂ d w₂ = .ok e₃₂)
      (hfire₁ : ∃ us₁ entry₁,
        e₃₁.getAppFn = Setlec.Expr.const entry₁.ctor us₁ ∧
        env.findProj? sn i = some entry₁ ∧ entry₁.native = true)
      (hfire₂ : ∃ us₂ entry₂,
        e₃₂.getAppFn = Setlec.Expr.const entry₂.ctor us₂ ∧
        env.findProj? sn i = some entry₂ ∧ entry₂.native = true)
      (hrun₁ : Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d lc₁
        (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok u')
      (hrun₂ : Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d lc₂
        (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok v') :
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂

/-- **The loop recursion bar**: knot-fuel sum strictly below, or
equal with the loop-budget sum strictly below.  `fc` is fixed —
the loop tier never descends cert fuel (Θ-funnels exit as seams). -/
def LoopBelow (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc N R : Nat) : Prop :=
  ∀ {f₁ f₂ l₁ l₂ d : Nat} {u v u' v' : Expr},
    (f₁ + f₂ < N ∨ (f₁ + f₂ = N ∧ l₁ + l₂ < R)) →
    CertZip μ env fc d u v → SubjInv d u → SubjInv d v →
    PairedLeaves u v → Q d u v →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁ u
      = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂ v
      = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂

/-- **Routed: the loop-level iota step** (unpacking coreLock's
recHead seams — no sort premise exists at major level, so rec-spine
pairs must actually sync: zipped majors recurse through `LoopBelow`
at knot minus one, fires match by ctor-name determinism, the K/eta
rescue rows scope their infer-lockstep lemmas leg-locally at the
discharge; divergence exits Θ-seams or the nat split).  Premises:
the shaped pair with its core runs, reachability from the loop
subjects, and the suffix loop runs. -/
def LoopIotaStep (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc N R f₁ f₂ l₁ l₂ d mI rP : Nat} {n : Name}
    {cv : Setlec.ConstantVal} {rules : List Setlec.RecRule}
    {us us' : List Level} {as bs : List Expr}
    {u v u' v' : Expr},
    LoopBelow μ env Q fc N R →
    f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
    env.find? n = some (.recInfo cv mI rP rules) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    LoopReaches μ env d u (Setlec.Expr.mkAppN (.const n us) as) →
    LoopReaches μ env d v (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁
      (Setlec.Expr.mkAppN (.const n us) as) = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂

/-- **Routed: the loop-level proj step** (unpacking coreLock's
projHead seams: the scrutinees' whnfs run at knot minus one —
`whnf_proj_inv` pins it — so the zipped scrutinees recurse through
`LoopBelow`; fire sync by table+ctor determinism, stuck sides
rebuild, divergence exits Θ-seams or the nat split). -/
def LoopProjStep (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc N R f₁ f₂ l₁ l₂ d i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {as bs : List Expr} {u v u' v' : Expr},
    LoopBelow μ env Q fc N R →
    f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
    CertZip μ env fc d e₁ e₂ →
    as.length = bs.length →
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Q d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    LoopReaches μ env d u (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    LoopReaches μ env d v (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂

/-- Budget slots weaken upward (bounds compose; the pack and the
nested out are untouched). -/
theorem LoopLockOut.mono_budget {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop} {fc d : Nat}
    {u v u' v' : Expr} {f₁ f₂ l₁ l₂ l₁' l₂' : Nat}
    (h₁ : l₁ ≤ l₁') (h₂ : l₂ ≤ l₂')
    (h : LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂) :
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁' l₂' := by
  cases h with
  | pack hz hI₁ hI₂ hp hq => exact .pack hz hI₁ hI₂ hp hq
  | seam h =>
    obtain ⟨w₁, w₂, c₁, c₂, lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂,
      hrn₁, hrn₂, ht₁, ht₂, hsm⟩ := h
    exact .seam ⟨w₁, w₂, c₁, c₂, lc₁, lc₂, hb₁, hb₂,
      Nat.le_trans hlb₁ h₁, Nat.le_trans hlb₂ h₂,
      hrn₁, hrn₂, ht₁, ht₂, hsm⟩
  | natSplit h =>
    obtain ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂, c₁, c₂,
      lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂, hrest⟩ := h
    exact .natSplit ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂,
      c₁, c₂, lc₁, lc₂, hb₁, hb₂, Nat.le_trans hlb₁ h₁,
      Nat.le_trans hlb₂ h₂, hrest⟩
  | projSplit sn i e₁ e₂ w₁ w₂ e₃₁ e₃₂ as bs g₁ g₂ gp₁ gp₂ gl₁ gl₂
      c₁ c₂ lc₁ lc₂ hb₁ hb₂ hlb₁ hlb₂ hg₁ hg₂ hgp₁ hgp₂ hr₁' hr₂'
      hze hlen hargs hw₁ hw₂ hnested hlit₁ hlit₂ hfire₁ hfire₂
      hrn₁ hrn₂ =>
    exact .projSplit sn i e₁ e₂ w₁ w₂ e₃₁ e₃₂ as bs g₁ g₂ gp₁ gp₂
      gl₁ gl₂ c₁ c₂ lc₁ lc₂ hb₁ hb₂ (Nat.le_trans hlb₁ h₁)
      (Nat.le_trans hlb₂ h₂) hg₁ hg₂ hgp₁ hgp₂ hr₁' hr₂' hze hlen
      hargs hw₁ hw₂ hnested hlit₁ hlit₂ hfire₁ hfire₂ hrn₁ hrn₂

/-- `LoopLockOut` re-bases along reachability prefixes (the pack is
output-only; the seam and splits compose their traces; the proj
split's NESTED out is scrutinee-level and untouched). -/
theorem LoopLockOut.prepend {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop} {fc d : Nat}
    {u v x₁ x₂ u' v' : Expr} {f₁ f₂ l₁ l₂ : Nat}
    (r₁ : LoopReaches μ env d u x₁) (r₂ : LoopReaches μ env d v x₂)
    (h : LoopLockOut μ env Q fc d x₁ x₂ u' v' f₁ f₂ l₁ l₂) :
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂ := by
  cases h with
  | pack hz hI₁ hI₂ hp hq => exact .pack hz hI₁ hI₂ hp hq
  | seam h =>
    obtain ⟨w₁, w₂, c₁, c₂, lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂,
      hrn₁, hrn₂, ht₁, ht₂, hsm⟩ := h
    exact .seam ⟨w₁, w₂, c₁, c₂, lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂,
      hrn₁, hrn₂, r₁.trans ht₁, r₂.trans ht₂, hsm⟩
  | natSplit h =>
    obtain ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂, c₁, c₂,
      lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂, hp₁, hp₂, hrest⟩ := h
    exact .natSplit ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂,
      c₁, c₂, lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂, r₁.trans hp₁,
      r₂.trans hp₂, hrest⟩
  | projSplit sn i e₁ e₂ w₁ w₂ e₃₁ e₃₂ as bs g₁ g₂ gp₁ gp₂ gl₁ gl₂
      c₁ c₂ lc₁ lc₂ hb₁ hb₂ hlb₁ hlb₂ hg₁ hg₂ hgp₁ hgp₂ hr₁' hr₂'
      hze hlen hargs hw₁ hw₂ hnested hlit₁ hlit₂ hfire₁ hfire₂
      hrn₁ hrn₂ =>
    exact .projSplit sn i e₁ e₂ w₁ w₂ e₃₁ e₃₂ as bs g₁ g₂ gp₁ gp₂
      gl₁ gl₂ c₁ c₂ lc₁ lc₂ hb₁ hb₂ hlb₁ hlb₂ hg₁ hg₂ hgp₁ hgp₂
      (r₁.trans hr₁') (r₂.trans hr₂') hze hlen hargs hw₁ hw₂
      hnested hlit₁ hlit₂ hfire₁ hfire₂ hrn₁ hrn₂

/-- A whnfCore output either re-cores to itself at the producing
fuel, or is dead-stuck (non-const-headed, non-λ, non-sort) — the
R-a family packaged for the loop walk's stuck sides. -/
theorem whnfCore_self_or_dead {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {f d : Nat} {p t : Expr}
    (h : whnfCore μ env f d p = .ok t) :
    whnfCore μ env f d t = .ok t ∨
    ((∀ p' q', t.getAppFn ≠ .const p' q') ∧
      (∀ n ty b m, t ≠ .lam n ty b m) ∧ (∀ ℓ, t ≠ .sort ℓ)) := by
  by_cases hc : ∃ n us, t.getAppFn = Setlec.Expr.const n us
  · obtain ⟨n, us, hhd⟩ := hc
    exact .inl (whnfCore_reidem_const hm h hhd)
  · have hpos : 1 ≤ f := whnfCore_pos h
    cases t with
    | sort ℓ => exact .inl (whnfCore_sort_run hpos)
    | lam n ty b m => exact .inl (whnfCore_lam_run hpos)
    | fvar i n ty => exact .inl (whnfCore_fvar_run hpos)
    | forallE n ty b m => exact .inl (whnfCore_forallE_run hpos)
    | lit l => exact .inl (whnfCore_lit_run hpos)
    | const n us => exact absurd ⟨n, us, rfl⟩ hc
    | bvar i =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | letE n ty v b =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | proj sn i pe =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | app pf pa =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩

/-- An unfolding spine's non-app head is a constant (subject-first
argument order so the head resolves before the shape lambda). -/
theorem unfold_some_head_of_spine {env : Env} {H x : Expr}
    {cs : List Expr}
    (h : Setlec.unfoldDefinition env (Setlec.Expr.mkAppN H cs)
      = some x)
    (hne : ∀ p q, H ≠ .app p q) :
    ∃ n us, H = Setlec.Expr.const n us := by
  obtain ⟨n, us, hfn⟩ := unfoldDefinition_some_head h
  rw [Setlec.Expr.getAppFn_mkAppN, getAppFn_of_not_app hne] at hfn
  exact ⟨n, us, hfn⟩

set_option maxHeartbeats 1600000 in
/-- **The whnf-loop lockstep** (the frozen statement): a zipped
pair's loop runs land zipped, or exit at a re-based seam, or split
at the nat tier.  Double strong induction (knot-fuel sum, then
loop-budget sum); per step: decompose both sides, coreLock on the
core parts, recHead/projHead seams unpacked through the routed step
Props, δ synced by name-determinism or exited at cert layers, nat
to the progress-marked split. -/
theorem loopLock {μ : CheckMode} (hgOff : μ.betaGate = false) {env : Env}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env) (hIDl : InvPreserveDeltaF env)
    (hLC : PairedPreserveCoreF μ env)
    (hLD : PairedPreserveDeltaF env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hIo : LoopIotaStep μ env Q) (hPr : LoopProjStep μ env Q) :
    ∀ (N R : Nat) {f₁ f₂ l₁ l₂ fc d : Nat} {u v u' v' : Expr},
      f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
      CertZip μ env fc d u v →
      SubjInv d u → SubjInv d v → PairedLeaves u v → Q d u v →
      Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁ u
        = .ok u' →
      Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂ v
        = .ok v' →
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ l₁ l₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IHN =>
  intro R
  induction R using Nat.strongRecOn with
  | ind R IHR =>
  intro f₁ f₂ l₁ l₂ fc d u v u' v' hN hR hz hIu hIv hP hQ h₁ h₂
  have below : LoopBelow μ env Q fc N R := by
    intro f₁' f₂' l₁' l₂' d' u₀ v₀ u₀' v₀' hrel hz' hI₁' hI₂'
      hp' hq' ha' hb'
    rcases hrel with hlt | ⟨heq, hlt⟩
    · exact IHN (f₁' + f₂') hlt (l₁' + l₂') (Nat.le_refl _)
        (Nat.le_refl _) hz' hI₁' hI₂' hp' hq' ha' hb'
    · exact IHR (l₁' + l₂') hlt (heq ▸ Nat.le_refl _)
        (Nat.le_refl _) hz' hI₁' hI₂' hp' hq' ha' hb'
  cases l₁ with
  | zero => exact nomatch h₁
  | succ l₁' =>
  cases l₂ with
  | zero => exact nomatch h₂
  | succ l₂' =>
  have haD := h₁
  rw [whnfLoop_succ] at haD
  obtain ⟨t₁, hwc₁, triA⟩ := whnfStep_decompose haD
  have hbD := h₂
  rw [whnfLoop_succ] at hbD
  obtain ⟨t₂, hwc₂, triB⟩ := whnfStep_decompose hbD
  have hwc₁' : whnfCore μ env f₁ d u = .ok t₁ := hwc₁
  have hwc₂' : whnfCore μ env f₂ d v = .ok t₂ := hwc₂
  have stepA : ∀ {W : Expr},
      whnfCore μ env f₁ d W = .ok t₁ →
      Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d (l₁' + 1) W
        = .ok u' := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triA with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have stepB : ∀ {W : Expr},
      whnfCore μ env f₂ d W = .ok t₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d (l₂' + 1) W
        = .ok v' := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triB with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  rcases @coreLock μ hgOff env Q hm hIC hLC hQC hQB hQZ hQH hLS
      (fun {d'} {a b} h => hQs h)
      (fun {d'} {P} {y} {Rz} {z} h => hQA h)
      (f₁ + f₂) f₁ f₂ fc d u v t₁ t₂
      (Nat.le_refl _) hz hIu hIv hP hQ hwc₁' hwc₂' with
    ⟨hzT, hIt₁, hIt₂, hPt, hQt⟩ |
    ⟨w₁, w₂, c₁, c₂, hcb₁, hcb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
  · -- pack: the tri matrix
    have natOut : ∀ (o₁ o₂ : Option Expr),
        Setlec.reduceNat (Setlec.pureFns μ env f₁) env d t₁
          = .ok o₁ →
        Setlec.reduceNat (Setlec.pureFns μ env f₂) env d t₂
          = .ok o₂ →
        (o₁.isSome = true ∨ o₂.isSome = true) →
        LoopLockOut μ env Q fc d u v u' v' f₁ f₂
          (l₁' + 1) (l₂' + 1) :=
      fun o₁ o₂ hn₁ hn₂ hmark =>
        .natSplit ⟨u, v, t₁, t₂, f₁, f₂, f₁, f₂, o₁, o₂,
          f₁, f₂, l₁' + 1, l₂' + 1, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
          .refl _, .refl _, hzT, hIt₁, hIt₂, hPt, hQt,
          hwc₁', hwc₂', hn₁, hn₂, hmark, h₁, h₂⟩
    rcases triA with ⟨x₁, hrn₁, hk₁⟩ | ⟨hrnn₁, x₁, hux₁, hk₁⟩ |
      ⟨hrnn₁, hud₁, hstop₁⟩
    · -- A nat fire
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, -, -, -⟩ |
        ⟨hrnn₂, -, -⟩
      · exact natOut _ _ hrn₁ hrn₂ (.inl rfl)
      · exact natOut _ _ hrn₁ hrnn₂ (.inl rfl)
      · exact natOut _ _ hrn₁ hrnn₂ (.inl rfl)
    · -- A δ
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, x₂, hux₂, hk₂⟩ |
        ⟨hrnn₂, hud₂, hstop₂⟩
      · exact natOut _ _ hrnn₁ hrn₂ (.inr rfl)
      · -- δδ: classify the zipped pair by the spine view
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v u' v' f₁ f₂
              (l₁' + 1) (l₂' + 1) := by
          intro hba hbb hc
          obtain ⟨n₁, us₁, hhd₁⟩ := unfoldDefinition_some_head hux₁
          obtain ⟨n₂', us₂', hhd₂⟩ := unfoldDefinition_some_head hux₂
          refine LoopLockOut.seam ⟨Setlec.Expr.mkAppN H₁ cs,
            Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
            Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
            stepA (whnfCore_reidem_const hm hwc₁' hhd₁),
            stepB (whnfCore_reidem_const hm hwc₂' hhd₂),
            .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
            LoopSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv hargsv⟩
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaConst : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v u' v' f₁ f₂
              (l₁' + 1) (l₂' + 1) := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us.length = us'.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this
            obtain ⟨cv, value, hxeq, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us') (bs := ds)
                hlen' hux₁
            subst hxeq
            have hx₂ := Option.some.inj (hux₂.symm.trans huy')
            subst hx₂
            have hzX : CertZip μ env fc d
                (Setlec.Expr.mkAppN
                  (Setlec.Expr.instantiateLevelParams
                    cv.levelParams us value) cs)
                (Setlec.Expr.mkAppN
                  (Setlec.Expr.instantiateLevelParams
                    cv.levelParams us' value) ds) :=
              certZip_mkAppN_zips (certZip_instantiate hev value)
                hlenv hargsv
            have hIx₁ := hIDl hux₁ hIt₁
            have hIx₂ := hIDl hux₂ hIt₂
            have hpX := (hLD hux₂ ((hLD hux₁ hPt).symm)).symm
            have hQX := hQs (hQD hux₂ (hQs (hQD hux₁ hQt)))
            have hout := below (by omega) hzX hIx₁ hIx₂ hpX hQX
              hk₁ hk₂
            exact LoopLockOut.mono_budget (Nat.le_succ _)
              (Nat.le_succ _) (LoopLockOut.prepend
                (.core f₁ hwc₁' (.delta hux₁ (.refl _)))
                (.core f₂ hwc₂' (.delta hux₂ (.refl _))) hout)
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaConst rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaConst rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
      · -- A δ, B stuck: dead or seam by B's re-core
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        subst hstop₂
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v u'
              (Setlec.Expr.mkAppN H₂ ds) f₁ f₂
              (l₁' + 1) (l₂' + 1) := by
          intro hba hbb hc
          obtain ⟨n₁, us₁, hhd₁⟩ := unfoldDefinition_some_head hux₁
          rcases whnfCore_self_or_dead hm hwc₂' with hS₂ |
            ⟨hnc, hnl, hns⟩
          · exact LoopLockOut.seam ⟨Setlec.Expr.mkAppN H₁ cs,
              Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
              stepA (whnfCore_reidem_const hm hwc₁' hhd₁),
              stepB hS₂,
              .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
              LoopSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv
                hargsv⟩
          · exact LoopLockOut.seam ⟨u, v, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h₁, h₂,
              .refl _, .refl _,
              LoopSeam.deadR u v (Setlec.Expr.mkAppN H₂ ds) f₂
                (fun g hg => hm.2.2.1 hg hwc₂') hnc hnl hns⟩
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaBoth : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v u'
                (Setlec.Expr.mkAppN H₂ ds) f₁ f₂
                (l₁' + 1) (l₂' + 1) := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us.length = us'.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this
            obtain ⟨cv, value, -, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us') (bs := ds)
                hlen' hux₁
            rw [huy'] at hud₂
            exact nomatch hud₂
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaBoth rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaBoth rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
    · -- A stuck
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, x₂, hux₂, hk₂⟩ |
        ⟨hrnn₂, hud₂, hstop₂⟩
      · exact natOut _ _ hrnn₁ hrn₂ (.inr rfl)
      · -- A stuck, B δ (mirror)
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        subst hstop₁
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v
              (Setlec.Expr.mkAppN H₁ cs) v' f₁ f₂
              (l₁' + 1) (l₂' + 1) := by
          intro hba hbb hc
          obtain ⟨n₂', us₂', hhd₂⟩ := unfoldDefinition_some_head hux₂
          rcases whnfCore_self_or_dead hm hwc₁' with hS₁ |
            ⟨hnc, hnl, hns⟩
          · exact LoopLockOut.seam ⟨Setlec.Expr.mkAppN H₁ cs,
              Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
              stepA hS₁,
              stepB (whnfCore_reidem_const hm hwc₂' hhd₂),
              .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
              LoopSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv
                hargsv⟩
          · exact LoopLockOut.seam ⟨u, v, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h₁, h₂,
              .refl _, .refl _,
              LoopSeam.deadL u v (Setlec.Expr.mkAppN H₁ cs) f₁
                (fun g hg => hm.2.2.1 hg hwc₁') hnc hnl hns⟩
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaBoth : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v
                (Setlec.Expr.mkAppN H₁ cs) v' f₁ f₂
                (l₁' + 1) (l₂' + 1) := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us'.length = us.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this.symm
            obtain ⟨cv, value, -, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us) (bs := cs)
                hlen' hux₂
            rw [huy'] at hud₁
            exact nomatch hud₁
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaBoth rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaBoth rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
      · -- both stuck: pack out
        subst hstop₁
        subst hstop₂
        exact .pack hzT hIt₁ hIt₂ hPt hQt
  · -- seam from the core step
    have hIw₁ : SubjInv d w₁ := ht₁.subjInv hIC hLS hIu
    have hIw₂ : SubjInv d w₂ := ht₂.subjInv hIC hLS hIv
    have hpw : PairedLeaves w₁ w₂ :=
      Contracts.pairing hLS ht₁ ht₂ hP
    have hQw : Q d w₁ w₂ :=
      hQs (ht₂.q_transport hQB hQZ hQH
        (hQs (ht₁.q_transport hQB hQZ hQH hQ)))
    have runA := stepA (hm.2.2.1 hcb₁ hr₁)
    have runB := stepB (hm.2.2.1 hcb₂ hr₂)
    cases hsm with
    | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
      exact LoopLockOut.seam ⟨Setlec.Expr.mkAppN F₁ as,
        Setlec.Expr.mkAppN F₂ bs, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        LoopSeam.certHead F₁ F₂ as bs hba hbb hc hlen hargs⟩
    | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
      exact hIo below hN hR hf hev hlen hargs hIw₁ hIw₂ hpw hQw
        (.contract ht₁ (.refl _)) (.contract ht₂ (.refl _))
        runA runB
    | projHead sn i pe₁ pe₂ as bs he hlen hargs =>
      exact hPr below hN hR he hlen hargs hIw₁ hIw₂ hpw hQw
        (.contract ht₁ (.refl _)) (.contract ht₂ (.refl _))
        runA runB
    | deadL _ _ u'd bnd hrun hnc hnl hns =>
      exact LoopLockOut.seam ⟨w₁, w₂, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        LoopSeam.deadL w₁ w₂ u'd bnd hrun hnc hnl hns⟩
    | deadR _ _ v'd bnd hrun hnc hnl hns =>
      exact LoopLockOut.seam ⟨w₁, w₂, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        LoopSeam.deadR w₁ w₂ v'd bnd hrun hnc hnl hns⟩

/-- A spine over a non-λ head is never a λ. -/
theorem mkAppN_ne_lam {H : Expr}
    (hH : ∀ n ty b m, H ≠ .lam n ty b m) :
    ∀ {cs : List Expr} (n : Name) (ty b : Expr)
      (m : Setlec.BinderMeta),
      Setlec.Expr.mkAppN H cs ≠ .lam n ty b m := by
  intro cs
  cases cs with
  | nil => exact hH
  | cons a as =>
    intro n ty b m h
    obtain ⟨p, q, hpq⟩ := mkAppN_cons_app (F := H) (a := a) (as := as)
    rw [hpq] at h
    exact nomatch h

/-- `Q` descends through a proj-node pair (the descent family's
second member; at `FrameQ` the frame is per-side structural — a
defined projection has a defined scrutinee). -/
def QDescendProjF (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d i i' : Nat} {sn sn' : Name} {a b : Expr},
    Q d (.proj sn i a) (.proj sn' i' b) → Q d a b

/-- **The proj-spine inversion** (reverse-spine induction): a core
run on a projection-headed spine factors through the scrutinee's
whnf and the projection decision — stuck (the rebuilt spine), or
fired with the field's run and a residual that is a run, the empty
spine, or a dead shape (the nil/dead disjuncts dodge every
idempotence, per the map). -/
theorem whnfCore_proj_spine_inv {μ : CheckMode} (hgOff : μ.betaGate = false) {env : Env}
    (hm : KnotFuelMono μ env) :
    ∀ {as : List Expr} {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) as)
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) as ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((as = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' as)
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) := by
  suffices H : ∀ (n : Nat) (as : List Expr), as.length ≤ n →
      ∀ {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) as)
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) as ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((as = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' as)
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) by
    exact fun {as} => H as.length as (Nat.le_refl _)
  have nilCase : ∀ {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) [])
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) [] ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((([] : List Expr) = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' [])
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) := by
    intro f d i sn e t h
    cases f with
    | zero => exact nomatch h
    | succ f' =>
    obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
    refine ⟨f', e₂, e₃, Nat.le_refl _, he, hlit, ?_⟩
    rcases hcase with rfl |
      ⟨us, entry, hfn, hf, hnat, hi, hlen, hus, hred, -⟩
    · exact .inl rfl
    · exact .inr ⟨us, entry, t, hfn, hf, hnat, hi, hlen, hred,
        .inl ⟨rfl, rfl⟩⟩
  intro n
  induction n with
  | zero =>
    intro as hlen0 f d i sn e t h
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp hlen0)
    exact nilCase h
  | succ n ihn =>
    intro as hlenn f d i sn e t h
    rcases List.eq_nil_or_concat as with rfl | ⟨as₀, b, rfl⟩
    · exact nilCase h
    · rw [List.concat_eq_append] at h hlenn ⊢
      have hlen₀ : as₀.length ≤ n := by
        rw [List.length_append] at hlenn
        simpa using Nat.le_of_succ_le_succ hlenn
      have ih := fun {f d i sn e t} h => ihn as₀ hlen₀
        (f := f) (d := d) (i := i) (sn := sn) (e := e) (t := t) h
      rw [show Setlec.Expr.mkAppN (.proj sn i e) (as₀ ++ [b])
          = Expr.app (Setlec.Expr.mkAppN (.proj sn i e) as₀) b
        from mkAppN_append_one] at h
      cases f with
      | zero => exact nomatch h
      | succ f' =>
      obtain ⟨P', hhead, legs⟩ := whnfCore_app_decompose hgOff h
      obtain ⟨g, e₂, e₃, hg, he, hlit, hcase⟩ := ih hhead
      refine ⟨g, e₂, e₃, by omega, he, hlit, ?_⟩
      rcases hcase with rfl |
        ⟨us, entry, h', hfn, hf, hnat, hi, hlen, hred, hres⟩
      · -- head stuck: the layer must be iota-none
        rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
          ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.proj sn i e₃)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.proj sn i e₃)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
          · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
            rw [show (Expr.app
                  (Setlec.Expr.mkAppN (.proj sn i e₃) as₀) b).getAppFn
                = (Setlec.Expr.mkAppN (.proj sn i e₃) as₀).getAppFn
              from rfl, Setlec.Expr.getAppFn_mkAppN] at hh
            exact nomatch hh
          · exact .inl mkAppN_append_one.symm
      · -- head fired: compose the residual through the layer
        refine .inr ⟨us, entry, h', hfn, hf, hnat, hi, hlen, hred, ?_⟩
        rcases hres with ⟨rfl, rfl⟩ | ⟨c, hc, hresrun⟩ |
          ⟨hnc, hnl2, hns⟩
        · -- empty head spine: the head output IS the field output
          rcases whnfCore_self_or_dead hm hred with hS |
            ⟨hnc, hnl2, hns⟩
          · refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
            rw [show Setlec.Expr.mkAppN P' ([] ++ [b])
                = Expr.app (Setlec.Expr.mkAppN P' []) b
              from mkAppN_append_one]
            exact whnfCore_app_assemble (hg := hgOff) (g := f') (gl := f') hm
              (hm.2.2.1 (by omega) hS) legs
          · rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
              ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
              · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
                exact absurd hh (hnc nn uu)
              · refine .inr (.inr ⟨?_, ?_, ?_⟩)
                · exact fun p' q' hh => hnc p' q' hh
                · exact fun _ _ _ _ hh => nomatch hh
                · exact fun _ hh => nomatch hh
        · -- run residual: assemble one more layer
          refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
          rw [show Setlec.Expr.mkAppN h' (as₀ ++ [b])
              = Expr.app (Setlec.Expr.mkAppN h' as₀) b
            from mkAppN_append_one]
          exact whnfCore_app_assemble (hg := hgOff) (g := f') (gl := f') hm
            (hm.2.2.1 (Nat.le_trans hc (by omega)) hresrun) legs
        · -- dead residual: the layer stays dead
          rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
            ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
            · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
              exact absurd hh (hnc nn uu)
            · refine .inr (.inr ⟨?_, ?_, ?_⟩)
              · exact fun p' q' hh => hnc p' q' hh
              · exact fun _ _ _ _ hh => nomatch hh
              · exact fun _ hh => nomatch hh

/-- `Q` descends a spine to its head (repeated app descent over
equal-length argument lists). -/
theorem qDescend_mkAppN {Q : Nat → Expr → Expr → Prop}
    (hQA : QDescendAppF Q) :
    ∀ (n : Nat) {as bs : List Expr} {d : Nat} {P R : Expr},
      as.length ≤ n → as.length = bs.length →
      Q d (Setlec.Expr.mkAppN P as) (Setlec.Expr.mkAppN R bs) →
      Q d P R := by
  intro n
  induction n with
  | zero =>
    intro as bs d P R hlen0 hlen hq
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp hlen0)
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact hq
  | succ n ihn =>
    intro as bs d P R hlenn hlen hq
    rcases List.eq_nil_or_concat as with rfl | ⟨as₀, a, rfl⟩
    · obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      exact hq
    · rcases List.eq_nil_or_concat bs with rfl | ⟨bs₀, b, rfl⟩
      · rw [List.concat_eq_append] at hlen
        simp at hlen
      · simp only [List.concat_eq_append] at hlenn hlen hq
        rw [show Setlec.Expr.mkAppN P (as₀ ++ [a])
            = Expr.app (Setlec.Expr.mkAppN P as₀) a
          from mkAppN_append_one,
          show Setlec.Expr.mkAppN R (bs₀ ++ [b])
            = Expr.app (Setlec.Expr.mkAppN R bs₀) b
          from mkAppN_append_one] at hq
        have hlen' : as₀.length = bs₀.length := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hlen
          omega
        have hlen₀ : as₀.length ≤ n := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hlenn
          omega
        exact ihn hlen₀ hlen' (hQA hq)

/-- The subject package descends a spine to its head. -/
theorem subjInv_spine_head {d : Nat} {H : Expr} {as : List Expr}
    (h : SubjInv d (Setlec.Expr.mkAppN H as)) : SubjInv d H := by
  obtain ⟨hw, hb, hL, hp⟩ := h
  obtain ⟨hwH, -⟩ := wScoped_mkAppN_parts hw
  obtain ⟨hbH, -⟩ := looseBVarsBounded_mkAppN_parts hb
  exact ⟨hwH, hbH,
    fun l hl => hL l (mem_fvarLeaves_mkAppN_head hl),
    pairedLeaves_mono (fun l hl => mem_fvarLeaves_mkAppN_head hl)
      (fun l hl => mem_fvarLeaves_mkAppN_head hl) hp⟩

/-- A scrutinee leaf is a proj leaf. -/
theorem mem_fvarLeaves_proj {sn : Name} {i : Nat} {e : Expr} :
    ∀ l ∈ e.fvarLeaves, l ∈ (Expr.proj sn i e).fvarLeaves := by
  intro l hl
  simpa [Setlec.Expr.fvarLeaves] using hl

/-- The subject package descends through a proj node. -/
theorem subjInv_proj {d : Nat} {sn : Name} {i : Nat} {e : Expr}
    (h : SubjInv d (.proj sn i e)) : SubjInv d e := by
  obtain ⟨hw, hb, hL, hp⟩ := h
  simp only [Setlec.Expr.WScoped] at hw
  simp only [Setlec.Expr.looseBVarsBounded] at hb
  exact ⟨hw, hb, fun l hl => hL l (mem_fvarLeaves_proj l hl),
    pairedLeaves_mono mem_fvarLeaves_proj mem_fvarLeaves_proj hp⟩

/-- **The loop-level proj step DISCHARGED** (the minimal discharge
on the self-similar shape): a stuck or dead-residual side exits a
dead seam at the raw subjects; both-fire recurses on the zipped
scrutinees at knot minus one and FORWARDS the analysis' out inside
the proj split — the split is the interface, and the sync work
belongs to its sort-premised consumers, which hold strictly more
facts. -/
theorem loopProjStep_of {μ : CheckMode} (hgOff : μ.betaGate = false) {env : Env}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hQA : QDescendAppF Q) (hQPd : QDescendProjF Q) :
    LoopProjStep μ env Q := by
  intro fc N R f₁ f₂ l₁ l₂ d i sn e₁ e₂ as bs u v u' v' below hN hR
    hze hlen hargs hI₁ hI₂ hp hQ hre₁ hre₂ h₁ h₂
  cases l₁ with
  | zero => exact nomatch h₁
  | succ l₁' =>
  cases l₂ with
  | zero => exact nomatch h₂
  | succ l₂' =>
  have haD := h₁
  rw [whnfLoop_succ] at haD
  obtain ⟨t₁, hwc₁, triA⟩ := whnfStep_decompose haD
  have hbD := h₂
  rw [whnfLoop_succ] at hbD
  obtain ⟨t₂, hwc₂, triB⟩ := whnfStep_decompose hbD
  have hwc₁' : whnfCore μ env f₁ d
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok t₁ := hwc₁
  have hwc₂' : whnfCore μ env f₂ d
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok t₂ := hwc₂
  -- dead exits, shared
  have deadLExit : (∀ p' q', t₁.getAppFn ≠ Setlec.Expr.const p' q') →
      (∀ n' ty' b' m', t₁ ≠ .lam n' ty' b' m') →
      (∀ ℓ, t₁ ≠ .sort ℓ) →
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂
        (l₁' + 1) (l₂' + 1) := by
    intro hnc hnl hns
    exact .seam ⟨Setlec.Expr.mkAppN (.proj sn i e₁) as,
      Setlec.Expr.mkAppN (.proj sn i e₂) bs, f₁, f₂,
      l₁' + 1, l₂' + 1, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h₁, h₂,
      hre₁, hre₂,
      LoopSeam.deadL _ _ t₁ f₁ (fun g hg => hm.2.2.1 hg hwc₁')
        hnc hnl hns⟩
  have deadRExit : (∀ p' q', t₂.getAppFn ≠ Setlec.Expr.const p' q') →
      (∀ n' ty' b' m', t₂ ≠ .lam n' ty' b' m') →
      (∀ ℓ, t₂ ≠ .sort ℓ) →
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂
        (l₁' + 1) (l₂' + 1) := by
    intro hnc hnl hns
    exact .seam ⟨Setlec.Expr.mkAppN (.proj sn i e₁) as,
      Setlec.Expr.mkAppN (.proj sn i e₂) bs, f₁, f₂,
      l₁' + 1, l₂' + 1, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h₁, h₂,
      hre₁, hre₂,
      LoopSeam.deadR _ _ t₂ f₂ (fun g hg => hm.2.2.1 hg hwc₂')
        hnc hnl hns⟩
  obtain ⟨g₁, w₁, e₃₁, hg₁, hw₁, hlit₁, hcase₁⟩ :=
    whnfCore_proj_spine_inv (hgOff := hgOff) hm hwc₁'
  obtain ⟨g₂, w₂, e₃₂, hg₂, hw₂, hlit₂, hcase₂⟩ :=
    whnfCore_proj_spine_inv (hgOff := hgOff) hm hwc₂'
  rcases hcase₁ with rfl |
    ⟨us₁, entry₁, h₁', hfn₁, hf₁, hnat₁, hi₁, hlen₁, hred₁, hres₁⟩
  · -- side 1 stuck: dead-shaped output
    exact deadLExit
      (mkAppN_fn_ne_const (not_const_getAppFn_of_shape
        (e := Expr.proj sn i e₃₁)
        (fun _ _ hh => nomatch hh) (fun _ _ hh => nomatch hh)))
      (mkAppN_ne_lam (H := Expr.proj sn i e₃₁)
        (fun _ _ _ _ hh => nomatch hh))
      (mkAppN_ne_sort (H := Expr.proj sn i e₃₁)
        (fun _ hh => nomatch hh))
  · rcases hres₁ with ⟨-, -⟩ | ⟨-, -, -⟩ | ⟨hnc₁, hnl₁, hns₁⟩
    case inr.inr => exact deadLExit hnc₁ hnl₁ hns₁
    all_goals
    rcases hcase₂ with rfl |
      ⟨us₂, entry₂, h₂', hfn₂, hf₂, hnat₂, hi₂, hlen₂, hred₂, hres₂⟩
    case inl =>
      exact deadRExit
        (mkAppN_fn_ne_const (not_const_getAppFn_of_shape
          (e := Expr.proj sn i e₃₂)
          (fun _ _ hh => nomatch hh) (fun _ _ hh => nomatch hh)))
        (mkAppN_ne_lam (H := Expr.proj sn i e₃₂)
          (fun _ _ _ _ hh => nomatch hh))
        (mkAppN_ne_sort (H := Expr.proj sn i e₃₂)
          (fun _ hh => nomatch hh))
    all_goals
    rcases hres₂ with ⟨-, -⟩ | ⟨-, -, -⟩ | ⟨hnc₂, hnl₂, hns₂⟩
    case inr.inr => exact deadRExit hnc₂ hnl₂ hns₂
    all_goals (
    -- both fired: recurse on the scrutinees and forward
    first
    | (have hIe₁ : SubjInv d e₁ := subjInv_proj (subjInv_spine_head hI₁)
       have hIe₂ : SubjInv d e₂ := subjInv_proj (subjInv_spine_head hI₂)
       have hpe : PairedLeaves e₁ e₂ :=
         pairedLeaves_mono
           (fun l hl => mem_fvarLeaves_mkAppN_head
             (mem_fvarLeaves_proj l hl))
           (fun l hl => mem_fvarLeaves_mkAppN_head
             (mem_fvarLeaves_proj l hl)) hp
       have hQe : Q d e₁ e₂ :=
         hQPd (qDescend_mkAppN (Q := Q) hQA as.length
           (Nat.le_refl _) hlen hQ)
       cases g₁ with
       | zero => exact nomatch hw₁
       | succ gA =>
       cases g₂ with
       | zero => exact nomatch hw₂
       | succ gB =>
       have hl₁ : Setlec.whnfLoop (Setlec.pureFns μ env gA) env d
           Setlec.whnfLoopFuel e₁ = .ok w₁ := hw₁
       have hl₂ : Setlec.whnfLoop (Setlec.pureFns μ env gB) env d
           Setlec.whnfLoopFuel e₂ = .ok w₂ := hw₂
       have hout := below (Or.inl (by omega)) hze hIe₁ hIe₂ hpe hQe
         hl₁ hl₂
       exact .projSplit sn i e₁ e₂ w₁ w₂ e₃₁ e₃₂ as bs
         (gA + 1) (gB + 1) gA gB Setlec.whnfLoopFuel
         Setlec.whnfLoopFuel f₁ f₂ (l₁' + 1) (l₂' + 1)
         (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
         (Nat.le_refl _) (by omega) (by omega)
         (by omega) (by omega) hre₁ hre₂ hze hlen hargs hw₁ hw₂
         hout hlit₁ hlit₂ ⟨us₁, entry₁, hfn₁, hf₁, hnat₁⟩
         ⟨us₂, entry₂, hfn₂, hf₂, hnat₂⟩ h₁ h₂))

/-- **The loop-level iota step DISCHARGED** (the map's dissolution
finding): the routed premises are EXACTLY `LoopSeam.recHead`'s
payload, so the honest loop-tier answer is the seam itself — legal,
terminal, and non-circular, because the seam's consumer is the
SORT-PREMISED top (`ZipIotaCase`'s own discharge), a different
Prop with strictly more facts: deadness for mixed fire, `below` at
the loop decrease for synced fire, and the Θ-arc for cert-swallowed
majors.  No iota split channel exists because none is needed —
rec-spine pairs carry a rich seam where proj-stuck pairs were
dead-shaped-poor; the channels are not parallel because the seams
are not. -/
theorem loopIotaStep_of {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop} :
    LoopIotaStep μ env Q := by
  intro fc N R f₁ f₂ l₁ l₂ d mI rP n cv rules us us' as bs
    u v u' v' below hN hR hf hev hlen hargs hIs hIt hp hQ
    hre₁ hre₂ h₁ h₂
  exact .seam ⟨Setlec.Expr.mkAppN (.const n us) as,
    Setlec.Expr.mkAppN (.const n us') bs, f₁, f₂, l₁, l₂,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h₁, h₂, hre₁, hre₂,
    LoopSeam.recHead n cv mI rP rules us us' as bs hf hev
      hlen hargs⟩

/-- The recursion bar weakens to smaller measures (the budget
surgery's payoff: shipped bounds license the translation). -/
theorem ZipBelow.weaken {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    {fc g r g' r' : Nat}
    (h : ZipBelow μ env φ Q fc g r) (hg : g' ≤ g) (hr : r' ≤ r) :
    ZipBelow μ env φ Q fc g' r' :=
  fun hrel hz hIs hIt hp hq hla hlb =>
    h (by omega) hz hIs hIt hp hq hla hlb

/-- **Routed: the proj-split conversion** (the Θ-family's second
docket item): the split's full payload at sort-landing suffix runs,
the bar in hand — concluding the claim.  Discharged at Θ's arc. -/
def ProjSplitSortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name}
    {u v e₁ e₂ w₁ w₂ e₃₁ e₃₂ : Expr} {as bs : List Expr}
    {g₁ g₂ gp₁ gp₂ gl₁ gl₂ c₁ c₂ lc₁ lc₂ : Nat} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    SubjInv d u → SubjInv d v → PairedLeaves u v → Q d u v →
    c₁ ≤ ga → c₂ ≤ gb → lc₁ ≤ la → lc₂ ≤ lb →
    g₁ ≤ ga → g₂ ≤ gb → gp₁ ≤ ga → gp₂ ≤ gb →
    LoopReaches μ env d u
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    LoopReaches μ env d v
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    CertZip μ env fc d e₁ e₂ →
    as.length = bs.length →
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) →
    whnf μ env g₁ d e₁ = .ok w₁ → whnf μ env g₂ d e₂ = .ok w₂ →
    LoopLockOut μ env Q fc d e₁ e₂ w₁ w₂ gp₁ gp₂ gl₁ gl₂ →
    Setlec.projLitToCtorP μ env g₁ d w₁ = .ok e₃₁ →
    Setlec.projLitToCtorP μ env g₂ d w₂ = .ok e₃₂ →
    (∃ us₁ entry₁,
      e₃₁.getAppFn = Setlec.Expr.const entry₁.ctor us₁ ∧
      env.findProj? sn i = some entry₁ ∧ entry₁.native = true) →
    (∃ us₂ entry₂,
      e₃₂.getAppFn = Setlec.Expr.const entry₂.ctor us₂ ∧
      env.findProj? sn i = some entry₂ ∧ entry₂.native = true) →
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d lc₁
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d lc₂
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

set_option maxHeartbeats 800000 in
/-- **The proj-head top case DISCHARGED** (the frozen map): loopLock
on the subject pair, then per-disjunct conversion under the sort
premises — pack via `certZip_sorts_eval`, certHead to Θ with the
carrier-transported invariants, recHead to the routed
`ZipIotaCase` at the weakened bar (the budget surgery's payoff),
dead seams by `loop_dead_exit`, the nat split by `NatStepNoSort`
(its fields are the exact premises), the proj split to the routed
Θ-family conversion. -/
theorem zipProjHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop} (hgOff : μ.betaGate = false)
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hIDl : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hIPf : InvPreserveProjFireF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hLPf : PairedPreserveProjFireF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hQPf : QPreserveProjFireF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q) (hQPd : QDescendProjF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hIota : ZipIotaCase μ env φ Q)
    (hPS : ProjSplitSortAgree μ env φ Q) :
    ZipProjHeadCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb i sn e₁ e₂ as bs ℓa ℓb below hze hlen
    hargs hIs hIt hp hQ ha hb
  have hzS : CertZip μ env fc d
      (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) :=
    certZip_mkAppN_zips (.proj sn i e₁ e₂ hze) hlen hargs
  have hout := loopLock (μ := μ) (env := env) (Q := Q) (hgOff := hgOff) hm hIC hIDl
    hLC hLD hQC hQD hQB hQZ hQH hLS
    (fun {d'} {a b} h => hQs h)
    (fun {d'} {P} {y} {Rz} {z} h => hQA h)
    (loopIotaStep_of (μ := μ) (env := env) (Q := Q))
    (loopProjStep_of (μ := μ) (env := env) (Q := Q) (hgOff := hgOff) hm
      (fun {d'} {P} {y} {Rz} {z} h => hQA h)
      (fun {d'} {ia} {ib} {sna} {snb} {a} {b} h =>
        hQPd (d := d') (i := ia) (i' := ib) (sn := sna)
          (sn' := snb) (a := a) (b := b) h))
    (ga + gb) (la + lb) (Nat.le_refl _) (Nat.le_refl _)
    hzS hIs hIt hp hQ ha hb
  cases hout with
  | pack hz hI₁ hI₂ hp' hq' => exact certZip_sorts_eval hm hz
  | seam h =>
    obtain ⟨w₁, w₂, c₁, c₂, lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂,
      hrn₁, hrn₂, ht₁, ht₂, hsm⟩ := h
    have hIw₁ : SubjInv d w₁ :=
      ht₁.subjInv hIC hIDl hIN hLS hIPf hIs
    have hIw₂ : SubjInv d w₂ :=
      ht₂.subjInv hIC hIDl hIN hLS hIPf hIt
    have hpw : PairedLeaves w₁ w₂ :=
      (ht₂.pairing_left hLC hLD hLN hLS hLPf
        ((ht₁.pairing_left hLC hLD hLN hLS hLPf hp).symm)).symm
    have hQw : Q d w₁ w₂ :=
      hQs (ht₂.q_transport (Q := Q) hQC hQD hQN hQB hQZ hQH hQPf
        (hQs (ht₁.q_transport (Q := Q) hQC hQD hQN hQB hQZ hQH
          hQPf hQ)))
    cases hsm with
    | certHead F₁ F₂ cs ds hba hbb hc hlen' hargs' =>
      exact hΘ (fun hlt hz' hIs' hIt' hp' hq' hla hlb =>
          below (Or.inl hlt) hz' hIs' hIt' hp' hq' hla hlb)
        hba hbb hc hlen' hargs' hIw₁ hIw₂ hpw hQw hrn₁ hrn₂
    | recHead n cv mI rP rules us us' cs ds hf hev hlen' hargs' =>
      exact @hIota fc d c₁ lc₁ c₂ lc₂ mI rP n us us' cv rules
        cs ds ℓa ℓb hf
        (ZipBelow.weaken below (by omega) (by omega))
        hev hlen' hargs' hIw₁ hIw₂ hpw hQw hrn₁ hrn₂
    | deadL _ _ u'd bnd hrun hnc hnl hns =>
      cases lc₁ with
      | zero => exact nomatch hrn₁
      | succ lc₁' =>
      have hrnD := hrn₁
      rw [whnfLoop_succ] at hrnD
      obtain ⟨x₁, hxc, trix⟩ := whnfStep_decompose hrnD
      have hxc' : whnfCore μ env c₁ d w₁ = .ok x₁ := hxc
      have h1 : whnfCore μ env (max bnd c₁) d w₁ = .ok u'd :=
        hrun (max bnd c₁) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd c₁) d w₁ = .ok x₁ :=
        hm.2.2.1 (Nat.le_max_right _ _) hxc'
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hxc' hrn₁ trix hnc hns
    | deadR _ _ v'd bnd hrun hnc hnl hns =>
      cases lc₂ with
      | zero => exact nomatch hrn₂
      | succ lc₂' =>
      have hrnD := hrn₂
      rw [whnfLoop_succ] at hrnD
      obtain ⟨x₂, hxc, trix⟩ := whnfStep_decompose hrnD
      have hxc' : whnfCore μ env c₂ d w₂ = .ok x₂ := hxc
      have h1 : whnfCore μ env (max bnd c₂) d w₂ = .ok v'd :=
        hrun (max bnd c₂) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd c₂) d w₂ = .ok x₂ :=
        hm.2.2.1 (Nat.le_max_right _ _) hxc'
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hxc' hrn₂ trix hnc hns
  | natSplit h =>
    obtain ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂, c₁, c₂,
      lc₁, lc₂, hb₁, hb₂, hlb₁, hlb₂, hp₁, hp₂, hzt, hIt₁, hIt₂,
      hpt, hqt, hc₁, hc₂, hn₁, hn₂, hmark, hr₁, hr₂⟩ := h
    rcases hmark with hs₁ | hs₂
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs₁
      subst hx
      exact (hN hc₁ hn₁ hr₁).elim
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs₂
      subst hx
      exact (hN hc₂ hn₂ hr₂).elim
  | projSplit sn' i' e₁' e₂' w₁ w₂ e₃₁ e₃₂ as' bs' g₁ g₂ gp₁ gp₂
      gl₁ gl₂ c₁ c₂ lc₁ lc₂ hb₁ hb₂ hlb₁ hlb₂ hg₁ hg₂ hgp₁ hgp₂
      hr₁ hr₂ hze' hlen' hargs' hw₁ hw₂ hnested hlit₁ hlit₂
      hfire₁ hfire₂ hrn₁ hrn₂ =>
    exact hPS below hIs hIt hp hQ hb₁ hb₂ hlb₁ hlb₂ hg₁ hg₂
      hgp₁ hgp₂ hr₁ hr₂ hze' hlen' hargs' hw₁ hw₂ hnested
      hlit₁ hlit₂ hfire₁ hfire₂ hrn₁ hrn₂

/-- Recursor heads never unfold (`recInfo` stores no value). -/
theorem unfoldDefinition_none_of_recInfo {env : Env} {e : Expr}
    {n : Name} {us : List Level} {cv : Setlec.ConstantVal}
    {mI rP : Nat} {rules : List Setlec.RecRule}
    (hfn : e.getAppFn = .const n us)
    (hf : env.find? n = some (.recInfo cv mI rP rules)) :
    Setlec.unfoldDefinition env e = none := by
  unfold Setlec.unfoldDefinition
  rw [hfn]
  simp only []
  rw [hf]

/-- **The rec-spine inversion** (parallel to the proj one): a core
run on a recursor-headed spine is stuck (the spine — under-applied
or iota-none at the arity layer) or fired at some prefix, with the
continuation's run and the run/nil/dead residual. -/
theorem whnfCore_rec_spine_inv {μ : CheckMode} (hgOff : μ.betaGate = false) {env : Env}
    (hm : KnotFuelMono μ env) :
    ∀ {as : List Expr} {f d : Nat} {n : Name} {us : List Level}
      {t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.const n us) as)
        = .ok t →
      t = Setlec.Expr.mkAppN (.const n us) as ∨
      ∃ (pre post : List Expr) (g : Nat) (e'' h' : Expr),
        as = pre ++ post ∧ g + 1 ≤ f ∧
        Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
          (Setlec.Expr.mkAppN (.const n us) pre)
          = .ok (some e'') ∧
        whnfCore μ env g d e'' = .ok h' ∧
        ((post = [] ∧ t = h') ∨
         (∃ c, c ≤ f ∧
           whnfCore μ env c d (Setlec.Expr.mkAppN h' post)
             = .ok t) ∨
         ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
           (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
           (∀ ℓ, t ≠ .sort ℓ))) := by
  suffices H : ∀ (m : Nat) (as : List Expr), as.length ≤ m →
      ∀ {f d : Nat} {n : Name} {us : List Level} {t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.const n us) as)
        = .ok t →
      t = Setlec.Expr.mkAppN (.const n us) as ∨
      ∃ (pre post : List Expr) (g : Nat) (e'' h' : Expr),
        as = pre ++ post ∧ g + 1 ≤ f ∧
        Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
          (Setlec.Expr.mkAppN (.const n us) pre)
          = .ok (some e'') ∧
        whnfCore μ env g d e'' = .ok h' ∧
        ((post = [] ∧ t = h') ∨
         (∃ c, c ≤ f ∧
           whnfCore μ env c d (Setlec.Expr.mkAppN h' post)
             = .ok t) ∨
         ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
           (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
           (∀ ℓ, t ≠ .sort ℓ))) by
    exact fun {as} => H as.length as (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro as hlen0 f d n us t h
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp hlen0)
    exact .inl (whnfCore_inert (fun _ _ hh => nomatch hh)
      (fun _ _ _ _ hh => nomatch hh) (fun _ _ _ hh => nomatch hh)
      h)
  | succ m ihm =>
    intro as hlenn f d n us t h
    rcases List.eq_nil_or_concat as with rfl | ⟨as₀, b, rfl⟩
    · exact .inl ((whnfCore_inert (fun _ _ hh => nomatch hh)
        (fun _ _ _ _ hh => nomatch hh)
        (fun _ _ _ hh => nomatch hh) h))
    · rw [List.concat_eq_append] at h hlenn ⊢
      have hlen₀ : as₀.length ≤ m := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hlenn
        omega
      rw [show Setlec.Expr.mkAppN (.const n us) (as₀ ++ [b])
          = Expr.app (Setlec.Expr.mkAppN (.const n us) as₀) b
        from mkAppN_append_one] at h
      cases f with
      | zero => exact nomatch h
      | succ f' =>
      obtain ⟨P', hhead, legs⟩ := whnfCore_app_decompose hgOff h
      rcases ihm as₀ hlen₀ hhead with rfl |
        ⟨pre, post, g, e'', h', heq, hg, hio, hcont, hres⟩
      · -- head stuck: fire here or stay stuck
        rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
          ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.const n us)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.const n us)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
          · refine .inr ⟨as₀ ++ [b], [], f', e'', t,
              (List.append_nil _).symm, Nat.le_refl _, ?_, hrun,
              .inl ⟨rfl, rfl⟩⟩
            rw [show Setlec.Expr.mkAppN (.const n us) (as₀ ++ [b])
                = Expr.app
                  (Setlec.Expr.mkAppN (.const n us) as₀) b
              from mkAppN_append_one]
            exact hio
          · exact .inl mkAppN_append_one.symm
      · -- head fired: compose the residual through the layer
        subst heq
        refine .inr ⟨pre, post ++ [b], g, e'', h',
          List.append_assoc _ _ _, by omega, hio, hcont, ?_⟩
        rcases hres with ⟨rfl, rfl⟩ | ⟨c, hc, hresrun⟩ |
          ⟨hnc, hnl2, hns⟩
        · -- empty inner post: the head output is the continuation's
          rcases whnfCore_self_or_dead hm hcont with hS |
            ⟨hnc, hnl2, hns⟩
          · refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
            rw [show Setlec.Expr.mkAppN P' ([] ++ [b])
                = Expr.app (Setlec.Expr.mkAppN P' []) b
              from mkAppN_append_one]
            exact whnfCore_app_assemble (hg := hgOff) (g := f') (gl := f') hm
              (hm.2.2.1 (by omega) hS) legs
          · rcases legs with
              ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
              ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ |
              ⟨hnl, hio'⟩
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · rcases hio' with ⟨e₂'', hio', hrun'⟩ | ⟨hio', rfl⟩
              · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio'
                exact absurd hh (hnc nn uu)
              · refine .inr (.inr ⟨?_, ?_, ?_⟩)
                · exact fun p' q' hh => hnc p' q' hh
                · exact fun _ _ _ _ hh => nomatch hh
                · exact fun _ hh => nomatch hh
        · -- run residual: assemble one more layer
          refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
          rw [show Setlec.Expr.mkAppN h' (post ++ [b])
              = Expr.app (Setlec.Expr.mkAppN h' post) b
            from mkAppN_append_one]
          exact whnfCore_app_assemble (hg := hgOff) (g := f') (gl := f') hm
            (hm.2.2.1 (Nat.le_trans hc (by omega)) hresrun) legs
        · -- dead residual: the layer stays dead
          rcases legs with
            ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
            ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio'⟩
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · rcases hio' with ⟨e₂'', hio', hrun'⟩ | ⟨hio', rfl⟩
            · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio'
              exact absurd hh (hnc nn uu)
            · refine .inr (.inr ⟨?_, ?_, ?_⟩)
              · exact fun p' q' hh => hnc p' q' hh
              · exact fun _ _ _ _ hh => nomatch hh
              · exact fun _ hh => nomatch hh

/-- **Routed: the iota-major conversion** (the Θ-family's third
docket item, the self-similar interface a third time): the shared
recursor's data, both fires as runs (consumers invert), the zipped
majors' whnfs with the major-level out VERBATIM, the subject spine
zips and invariants, and the sort runs — concluding the claim.
Discharged at Θ's arc. -/
def IotaMajorSortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb g₁ g₂ gm₁ gm₂ gp₁ gp₂ gl₁ gl₂ mI rP : Nat}
    {n : Name} {cv : Setlec.ConstantVal}
    {rules : List Setlec.RecRule} {us us' : List Level}
    {pre₁ pre₂ post₁ post₂ : List Expr}
    {e₁'' e₂'' w₁ w₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    env.find? n = some (.recInfo cv mI rP rules) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    pre₁.length = pre₂.length →
    (∀ i (h₁ : i < pre₁.length) (h₂ : i < pre₂.length),
      CertZip μ env fc d pre₁[i] pre₂[i]) →
    post₁.length = post₂.length →
    (∀ i (h₁ : i < post₁.length) (h₂ : i < post₂.length),
      CertZip μ env fc d post₁[i] post₂[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) (pre₁ ++ post₁)) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') (pre₂ ++ post₂)) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) (pre₁ ++ post₁))
      (Setlec.Expr.mkAppN (.const n us') (pre₂ ++ post₂)) →
    Q d (Setlec.Expr.mkAppN (.const n us) (pre₁ ++ post₁))
      (Setlec.Expr.mkAppN (.const n us') (pre₂ ++ post₂)) →
    g₁ ≤ ga → g₂ ≤ gb →
    Setlec.iotaRec μ (Setlec.pureFns μ env g₁) env d
      (Setlec.Expr.mkAppN (.const n us) pre₁) = .ok (some e₁'') →
    Setlec.iotaRec μ (Setlec.pureFns μ env g₂) env d
      (Setlec.Expr.mkAppN (.const n us') pre₂) = .ok (some e₂'') →
    gm₁ ≤ ga → gm₂ ≤ gb →
    whnf μ env gm₁ d (pre₁.getD mI (.bvar 0)) = .ok w₁ →
    whnf μ env gm₂ d (pre₂.getD mI (.bvar 0)) = .ok w₂ →
    LoopLockOut μ env Q fc d (pre₁.getD mI (.bvar 0))
      (pre₂.getD mI (.bvar 0)) w₁ w₂ gp₁ gp₂ gl₁ gl₂ →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) (pre₁ ++ post₁))
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') (pre₂ ++ post₂))
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the eta-rescue conversion** (the ONE row carrying the
deferred infer-lockstep; the K row needs none — its `cnF = 0` gate
kills the field-dependence, so K-reducts depend only on zipped
spine args, and the single-rule gate pins the rule on both sides).
Premises: both sides' rescue data as runs (`whnf (infer major)`
included — the infer-lockstep enters here and nowhere else), the
subject payload, the sort runs. -/
def EtaRescueSortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb g₁ g₂ mI rP : Nat} {n : Name}
    {cv : Setlec.ConstantVal} {rules : List Setlec.RecRule}
    {us us' : List Level} {pre₁ pre₂ post₁ post₂ : List Expr}
    {maj₁ maj₂ tmaj₁ tmaj₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    env.find? n = some (.recInfo cv mI rP rules) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    pre₁.length = pre₂.length →
    (∀ i (h₁ : i < pre₁.length) (h₂ : i < pre₂.length),
      CertZip μ env fc d pre₁[i] pre₂[i]) →
    post₁.length = post₂.length →
    (∀ i (h₁ : i < post₁.length) (h₂ : i < post₂.length),
      CertZip μ env fc d post₁[i] post₂[i]) →
    CertZip μ env fc d maj₁ maj₂ →
    g₁ ≤ ga → g₂ ≤ gb →
    inferTypeCore μ env g₁ d maj₁ = .ok tmaj₁ →
    inferTypeCore μ env g₂ d maj₂ = .ok tmaj₂ →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) (pre₁ ++ post₁))
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') (pre₂ ++ post₂))
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- `getD` at an in-bounds index is `getElem`. -/
theorem getD_eq_getElem' {α : Type _} {l : List α} {i : Nat}
    {dflt : α} (h : i < l.length) : l.getD i dflt = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

/-- Spines compose over list append. -/
theorem mkAppN_append {F : Expr} : ∀ (xs ys : List Expr),
    Setlec.Expr.mkAppN F (xs ++ ys)
      = Setlec.Expr.mkAppN (Setlec.Expr.mkAppN F xs) ys := by
  intro xs
  induction xs generalizing F with
  | nil => intro ys; rfl
  | cons x xs ih =>
    intro ys
    exact ih (F := .app F x) ys

/-- `Q` descends to an app-node pair's arguments (the descent
family's third member; `FrameQ` per-side structural). -/
def QDescendArgF (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {P y R z : Expr},
    Q d (.app P y) (.app R z) → Q d y z

/-- The subject package descends to a spine argument. -/
theorem subjInv_spine_arg {d : Nat} {H a : Expr} {as : List Expr}
    (h : SubjInv d (Setlec.Expr.mkAppN H as)) (ha : a ∈ as) :
    SubjInv d a := by
  obtain ⟨hw, hb, hL, hp⟩ := h
  obtain ⟨-, hwargs⟩ := wScoped_mkAppN_parts hw
  obtain ⟨-, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
  exact ⟨hwargs a ha, hbargs a ha,
    fun l hl => hL l (mem_fvarLeaves_mkAppN_arg ha hl),
    pairedLeaves_mono (fun l hl => mem_fvarLeaves_mkAppN_arg ha hl)
      (fun l hl => mem_fvarLeaves_mkAppN_arg ha hl) hp⟩

set_option maxHeartbeats 800000 in
/-- **The iota top case DISCHARGED** (the minimal discharge, the
proj pattern): stuck sides die by their own tri; both-fired
supplies the majors' loopLock analysis and FORWARDS everything to
the routed `IotaMajorSortAgree` — the sync algebra lives at Θ's
arc, which holds the same data plus the claim-level facts. -/
theorem zipIotaCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop} (hgOff : μ.betaGate = false)
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hIDl : InvPreserveDeltaF env)
    (hLC : PairedPreserveCoreF μ env)
    (hLD : PairedPreserveDeltaF env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q) (hQPd : QDescendProjF Q)
    (hQAr : QDescendArgF Q)
    (hIM : IotaMajorSortAgree μ env φ Q) :
    ZipIotaCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb mI rP n us us' cv rules as bs ℓa ℓb hf
    below hev hlen hargs hIs hIt hp hQ ha hb
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨t₁, hwc₁, triA⟩ := whnfStep_decompose haD
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨t₂, hwc₂, triB⟩ := whnfStep_decompose hbD
  have hwc₁' : whnfCore μ env ga d
      (Setlec.Expr.mkAppN (.const n us) as) = .ok t₁ := hwc₁
  have hwc₂' : whnfCore μ env gb d
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok t₂ := hwc₂
  have stuckKill₁ : t₁ = Setlec.Expr.mkAppN (.const n us) as →
      Level.eval φ ℓa = Level.eval φ ℓb := by
    intro heq
    subst heq
    rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
    · exact (hN hwc₁' hrx ha).elim
    · rw [unfoldDefinition_none_of_recInfo
        (show (Setlec.Expr.mkAppN (.const n us) as).getAppFn
            = Setlec.Expr.const n us by
          rw [Setlec.Expr.getAppFn_mkAppN]; rfl) hf] at hud
      exact nomatch hud
    · cases as with
      | nil => exact nomatch hstop
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.const n us) (a := a) (as := as')
        rw [hpq] at hstop
        exact nomatch hstop
  have stuckKill₂ : t₂ = Setlec.Expr.mkAppN (.const n us') bs →
      Level.eval φ ℓa = Level.eval φ ℓb := by
    intro heq
    subst heq
    rcases triB with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
    · exact (hN hwc₂' hrx hb).elim
    · rw [unfoldDefinition_none_of_recInfo
        (show (Setlec.Expr.mkAppN (.const n us') bs).getAppFn
            = Setlec.Expr.const n us' by
          rw [Setlec.Expr.getAppFn_mkAppN]; rfl) hf] at hud
      exact nomatch hud
    · cases bs with
      | nil => exact nomatch hstop
      | cons b bs' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.const n us') (a := b) (as := bs')
        rw [hpq] at hstop
        exact nomatch hstop
  rcases whnfCore_rec_spine_inv (hgOff := hgOff) hm hwc₁' with heq₁ |
    ⟨pre₁, post₁, g₁, e₁'', h₁', heq₁, hg₁, hio₁, hcont₁, hres₁⟩
  · exact stuckKill₁ heq₁
  rcases whnfCore_rec_spine_inv (hgOff := hgOff) hm hwc₂' with heq₂ |
    ⟨pre₂, post₂, g₂, e₂'', h₂', heq₂, hg₂, hio₂, hcont₂, hres₂⟩
  · exact stuckKill₂ heq₂
  subst heq₁
  subst heq₂
  -- invert the fires for lengths and majors
  obtain ⟨c₁, us₁, cv₁, mI₁, rP₁, rules₁, major₀₁, major₁₁, major₁,
    cj₁, usj₁, cvj₁, cnP₁, cnF₁, r₁, -, -, -, -, -, hfn₁, hfc₁,
    hlenp₁, -, hmaj₁, -⟩ := iotaRec_inv (show Setlec.iotaRecP μ env g₁ d
      (Setlec.Expr.mkAppN (.const n us) pre₁) = .ok (some e₁'')
      from hio₁)
  obtain ⟨c₂, us₂, cv₂, mI₂, rP₂, rules₂, major₀₂, major₁₂, major₂,
    cj₂, usj₂, cvj₂, cnP₂, cnF₂, r₂, -, -, -, -, -, hfn₂, hfc₂,
    hlenp₂, -, hmaj₂, -⟩ := iotaRec_inv (show Setlec.iotaRecP μ env g₂ d
      (Setlec.Expr.mkAppN (.const n us') pre₂) = .ok (some e₂'')
      from hio₂)
  -- identify the recursor
  rw [Setlec.Expr.getAppFn_mkAppN,
    show (Expr.const n us).getAppFn = Expr.const n us from rfl]
    at hfn₁
  rw [Setlec.Expr.getAppFn_mkAppN,
    show (Expr.const n us').getAppFn = Expr.const n us' from rfl]
    at hfn₂
  have hcn₁ : c₁ = n := by cases hfn₁; rfl
  have hcn₂ : c₂ = n := by cases hfn₂; rfl
  rw [hcn₁, hf] at hfc₁
  rw [hcn₂, hf] at hfc₂
  have hmI₁e : mI₁ = mI := by cases hfc₁; rfl
  have hmI₂e : mI₂ = mI := by cases hfc₂; rfl
  rw [hmI₁e] at hlenp₁ hmaj₁
  rw [hmI₂e] at hlenp₂ hmaj₂
  -- prefix lengths
  rw [Setlec.Expr.getAppArgs_mkAppN,
    show (Expr.const n us).getAppArgs = ([] : List Expr) from rfl,
    List.nil_append] at hlenp₁ hmaj₁
  rw [Setlec.Expr.getAppArgs_mkAppN,
    show (Expr.const n us').getAppArgs = ([] : List Expr) from rfl,
    List.nil_append] at hlenp₂ hmaj₂
  have hlenpre : pre₁.length = pre₂.length := by
    rw [hlenp₁, hlenp₂]
  have hlenas : (pre₁ ++ post₁).length = (pre₂ ++ post₂).length :=
    hlen
  have hlenpost : post₁.length = post₂.length := by
    simp only [List.length_append] at hlenas
    omega
  -- component zips
  have hzpre : ∀ i (h₁ : i < pre₁.length) (h₂ : i < pre₂.length),
      CertZip μ env fc d pre₁[i] pre₂[i] := by
    intro i h₁ h₂
    have hi₁ : i < (pre₁ ++ post₁).length := by
      simp only [List.length_append]; omega
    have hi₂ : i < (pre₂ ++ post₂).length := by
      simp only [List.length_append]; omega
    have e1 := List.getElem_append_left (bs := post₁) h₁
      (h' := hi₁)
    have e2 := List.getElem_append_left (bs := post₂) h₂
      (h' := hi₂)
    rw [← e1, ← e2]
    exact hargs i hi₁ hi₂
  have hzpost : ∀ i (h₁ : i < post₁.length)
      (h₂ : i < post₂.length),
      CertZip μ env fc d post₁[i] post₂[i] := by
    intro i h₁ h₂
    have hi₁ : pre₁.length + i < (pre₁ ++ post₁).length := by
      simp only [List.length_append]; omega
    have hi₂ : pre₁.length + i < (pre₂ ++ post₂).length := by
      simp only [List.length_append]; omega
    have h := hargs (pre₁.length + i) hi₁ hi₂
    rw [List.getElem_append_right (Nat.le_add_right _ _)] at h
    rw [List.getElem_append_right (by omega)] at h
    simpa [Nat.add_sub_cancel_left, hlenpre] using h
  -- the majors
  have hmIlt₁ : mI < pre₁.length := by omega
  have hmIlt₂ : mI < pre₂.length := by omega
  have hmemmaj₁ : pre₁.getD mI (.bvar 0) ∈ pre₁ ++ post₁ := by
    rw [getD_eq_getElem' hmIlt₁]
    exact List.mem_append_left _ (List.getElem_mem _)
  have hmemmaj₂ : pre₂.getD mI (.bvar 0) ∈ pre₂ ++ post₂ := by
    rw [getD_eq_getElem' hmIlt₂]
    exact List.mem_append_left _ (List.getElem_mem _)
  have hImaj₁ : SubjInv d (pre₁.getD mI (.bvar 0)) :=
    subjInv_spine_arg hIs hmemmaj₁
  have hImaj₂ : SubjInv d (pre₂.getD mI (.bvar 0)) :=
    subjInv_spine_arg hIt hmemmaj₂
  have hpmaj : PairedLeaves (pre₁.getD mI (.bvar 0))
      (pre₂.getD mI (.bvar 0)) :=
    pairedLeaves_mono
      (fun l hl => mem_fvarLeaves_mkAppN_arg hmemmaj₁ hl)
      (fun l hl => mem_fvarLeaves_mkAppN_arg hmemmaj₂ hl) hp
  have hzmaj : CertZip μ env fc d (pre₁.getD mI (.bvar 0))
      (pre₂.getD mI (.bvar 0)) := by
    rw [getD_eq_getElem' hmIlt₁, getD_eq_getElem' hmIlt₂]
    exact hzpre mI hmIlt₁ hmIlt₂
  -- Q at the majors: strip the posts, then the last-arg descent
  have hQmaj : Q d (pre₁.getD mI (.bvar 0))
      (pre₂.getD mI (.bvar 0)) := by
    have hQpre : Q d (Setlec.Expr.mkAppN (.const n us) pre₁)
        (Setlec.Expr.mkAppN (.const n us') pre₂) := by
      have h1 := hQ
      rw [mkAppN_append (F := Expr.const n us) pre₁ post₁,
        mkAppN_append (F := Expr.const n us') pre₂ post₂] at h1
      exact qDescend_mkAppN (Q := Q) hQA post₁.length
        (Nat.le_refl _) hlenpost h1
    obtain ⟨pre₁', m₁, hpre₁⟩ : ∃ l x, pre₁ = l ++ [x] := by
      rcases List.eq_nil_or_concat pre₁ with rfl | ⟨l, x, hx⟩
      · exact absurd hmIlt₁ (by simp)
      · exact ⟨l, x, by rw [hx, List.concat_eq_append]⟩
    obtain ⟨pre₂', m₂, hpre₂⟩ : ∃ l x, pre₂ = l ++ [x] := by
      rcases List.eq_nil_or_concat pre₂ with rfl | ⟨l, x, hx⟩
      · exact absurd hmIlt₂ (by simp)
      · exact ⟨l, x, by rw [hx, List.concat_eq_append]⟩
    have hm₁ : pre₁.getD mI (.bvar 0) = m₁ := by
      rw [getD_eq_getElem' hmIlt₁]
      subst hpre₁
      have : mI = pre₁'.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hlenp₁
        omega
      subst this
      exact getElem_append_last _ _
    have hm₂ : pre₂.getD mI (.bvar 0) = m₂ := by
      rw [getD_eq_getElem' hmIlt₂]
      subst hpre₂
      have : mI = pre₂'.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hlenp₂
        omega
      subst this
      exact getElem_append_last _ _
    rw [hm₁, hm₂]
    rw [hpre₁, hpre₂] at hQpre
    rw [show Setlec.Expr.mkAppN (.const n us) (pre₁' ++ [m₁])
        = Expr.app (Setlec.Expr.mkAppN (.const n us) pre₁') m₁
      from mkAppN_append_one,
      show Setlec.Expr.mkAppN (.const n us') (pre₂' ++ [m₂])
        = Expr.app (Setlec.Expr.mkAppN (.const n us') pre₂') m₂
      from mkAppN_append_one] at hQpre
    exact hQAr hQpre
  -- the majors' loop analysis
  cases hg₁' : g₁ with
  | zero => rw [hg₁'] at hmaj₁; exact nomatch hmaj₁
  | succ gA =>
  cases hg₂' : g₂ with
  | zero => rw [hg₂'] at hmaj₂; exact nomatch hmaj₂
  | succ gB =>
  subst hg₁'
  subst hg₂'
  have hl₁ : Setlec.whnfLoop (Setlec.pureFns μ env gA) env d
      Setlec.whnfLoopFuel (pre₁.getD mI (.bvar 0))
      = .ok major₀₁ := hmaj₁
  have hl₂ : Setlec.whnfLoop (Setlec.pureFns μ env gB) env d
      Setlec.whnfLoopFuel (pre₂.getD mI (.bvar 0))
      = .ok major₀₂ := hmaj₂
  have hout := loopLock (μ := μ) (env := env) (Q := Q) (hgOff := hgOff) hm hIC hIDl
    hLC hLD hQC hQD hQB hQZ hQH hLS
    (fun {d'} {a b} h => hQs h)
    (fun {d'} {P} {y} {Rz} {z} h => hQA h)
    (loopIotaStep_of (μ := μ) (env := env) (Q := Q))
    (loopProjStep_of (μ := μ) (env := env) (Q := Q) (hgOff := hgOff) hm
      (fun {d'} {P} {y} {Rz} {z} h => hQA h)
      (fun {d'} {ia} {ib} {sna} {snb} {a} {b} h =>
        hQPd (d := d') (i := ia) (i' := ib) (sn := sna)
          (sn' := snb) (a := a) (b := b) h))
    (gA + gB) (Setlec.whnfLoopFuel + Setlec.whnfLoopFuel)
    (Nat.le_refl _) (Nat.le_refl _)
    hzmaj hImaj₁ hImaj₂ hpmaj hQmaj hl₁ hl₂
  exact hIM below hf hev hlenpre hzpre hlenpost hzpost hIs hIt
    hp hQ (by omega) (by omega) hio₁ hio₂ (by omega) (by omega)
    hmaj₁ hmaj₂ hout ha hb

end Discharge

end Setlec.SetR.Interp2
