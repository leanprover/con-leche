import Setlec.SetR.Sound.Struct
import Setlec.SetR.Sound.Irrel
import Setlec.SetR.Sound.Stuck
import Setlec.SetR.Sound.Proj
import Setlec.SetR.Sound.Iota
import Setlec.SetR.Sound.NatOpsWf

/-!
# The soundness theorems (task #148, T4 — assembly)

The five mutual soundness theorems, each one term-mode application of
its recursor to the 46 case lemmas (the `Weaken.lean` pattern; the
motives are the `*S` forms of `Sound/Motives.lean`).  This is the
campaign's SOUNDNESS half: a derivation in the relation family yields
collapse-interpretation facts, under the environment-hypothesis bundle
`EnvSHyp` (T5's `EnvS` discharges it by projection).

The statement shapes (recorded in `Setlec/SetR/DESIGN.md`'s T4
architecture section, binding):

* `DefEq.sound` — **unconditional** interpretation equality under
  `Sat`;
* `Red.sound` — unconditional equality plus forward `AnnotOkV`
  transport;
* `Infer.sound` — the subject's truthfulness and its membership in
  its type's interpretation;
* `Tele.sound` — the spine fit (`TeleFitV`), argument truthfulness,
  and residual-truthfulness transport;
* `DefEqL.sound` — pointwise interpretation equality (map form).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Main

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- **Soundness for `Red`**: reduction preserves the interpretation
and transports truthfulness forward. -/
theorem Red.sound (henv : EnvSHyp V env cval φ) {Γ : List VExpr}
    {v w : VExpr} (h : Red μ env cval φ Γ v w) : RedS V Γ v w :=
  Red.rec
    (motive_1 := fun Δ v w _ => RedS V Δ v w)
    (motive_2 := fun Δ v T _ => InfS V Δ v T)
    (motive_3 := fun Δ a b _ => DeqS V Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleS V Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLS V Δ as bs)
    sndRedRefl sndRedTrans sndRedAppFn sndRedBeta sndRedZeta
    (sndRedProjRed henv) sndRedStrLitCtor (sndRedNatSucc henv)
    (sndRedNatOp1 henv) (sndRedNatOp2 henv) (sndRedIota henv)
    (sndRedRescueK henv) (sndRedRescueEta henv) (sndRedRescueUnit0 henv)
    sndRedProjArg
    sndInfSort sndInfBvar (sndInfConst henv) (sndInfLitNat henv)
    (sndInfLitStr henv) sndInfPi sndInfLam sndInfApp (sndInfProj henv)
    sndInfLetE
    sndDeqRefl sndDeqSymm sndDeqTrans sndDeqOfRed sndDeqPiCong
    sndDeqLamCong sndDeqAppCong sndDeqIrrelProp (sndDeqIrrelUnit henv)
    (sndDeqStructEta henv) (sndDeqStructUnit henv) (sndDeqPairEta henv)
    sndDeqEta sndDeqLitSuccApp sndDeqProjCong
    sndTeleNil sndTeleCons sndDeqLNil sndDeqLCons
    h

/-- **Soundness for `Infer`**: the subject is truthful and inhabits
its type's interpretation. -/
theorem Infer.sound (henv : EnvSHyp V env cval φ) {Γ : List VExpr}
    {v T : VExpr} (h : Infer μ env cval φ Γ v T) : InfS V Γ v T :=
  Infer.rec
    (motive_1 := fun Δ v w _ => RedS V Δ v w)
    (motive_2 := fun Δ v T _ => InfS V Δ v T)
    (motive_3 := fun Δ a b _ => DeqS V Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleS V Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLS V Δ as bs)
    sndRedRefl sndRedTrans sndRedAppFn sndRedBeta sndRedZeta
    (sndRedProjRed henv) sndRedStrLitCtor (sndRedNatSucc henv)
    (sndRedNatOp1 henv) (sndRedNatOp2 henv) (sndRedIota henv)
    (sndRedRescueK henv) (sndRedRescueEta henv) (sndRedRescueUnit0 henv)
    sndRedProjArg
    sndInfSort sndInfBvar (sndInfConst henv) (sndInfLitNat henv)
    (sndInfLitStr henv) sndInfPi sndInfLam sndInfApp (sndInfProj henv)
    sndInfLetE
    sndDeqRefl sndDeqSymm sndDeqTrans sndDeqOfRed sndDeqPiCong
    sndDeqLamCong sndDeqAppCong sndDeqIrrelProp (sndDeqIrrelUnit henv)
    (sndDeqStructEta henv) (sndDeqStructUnit henv) (sndDeqPairEta henv)
    sndDeqEta sndDeqLitSuccApp sndDeqProjCong
    sndTeleNil sndTeleCons sndDeqLNil sndDeqLCons
    h

/-- **Soundness for `DefEq`**: derivable definitional equalities are
interpretation equalities — unconditionally. -/
theorem DefEq.sound (henv : EnvSHyp V env cval φ) {Γ : List VExpr}
    {a b : VExpr} (h : DefEq μ env cval φ Γ a b) : DeqS V Γ a b :=
  DefEq.rec
    (motive_1 := fun Δ v w _ => RedS V Δ v w)
    (motive_2 := fun Δ v T _ => InfS V Δ v T)
    (motive_3 := fun Δ a b _ => DeqS V Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleS V Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLS V Δ as bs)
    sndRedRefl sndRedTrans sndRedAppFn sndRedBeta sndRedZeta
    (sndRedProjRed henv) sndRedStrLitCtor (sndRedNatSucc henv)
    (sndRedNatOp1 henv) (sndRedNatOp2 henv) (sndRedIota henv)
    (sndRedRescueK henv) (sndRedRescueEta henv) (sndRedRescueUnit0 henv)
    sndRedProjArg
    sndInfSort sndInfBvar (sndInfConst henv) (sndInfLitNat henv)
    (sndInfLitStr henv) sndInfPi sndInfLam sndInfApp (sndInfProj henv)
    sndInfLetE
    sndDeqRefl sndDeqSymm sndDeqTrans sndDeqOfRed sndDeqPiCong
    sndDeqLamCong sndDeqAppCong sndDeqIrrelProp (sndDeqIrrelUnit henv)
    (sndDeqStructEta henv) (sndDeqStructUnit henv) (sndDeqPairEta henv)
    sndDeqEta sndDeqLitSuccApp sndDeqProjCong
    sndTeleNil sndTeleCons sndDeqLNil sndDeqLCons
    h

/-- **Soundness for `Tele`**: the certified spine fits its telescope's
interpretation. -/
theorem Tele.sound (henv : EnvSHyp V env cval φ) {Γ : List VExpr}
    {T : VExpr} {as : List VExpr} {rest : VExpr}
    (h : Tele μ env cval φ Γ T as rest) : TeleS V Γ T as rest :=
  Tele.rec
    (motive_1 := fun Δ v w _ => RedS V Δ v w)
    (motive_2 := fun Δ v T _ => InfS V Δ v T)
    (motive_3 := fun Δ a b _ => DeqS V Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleS V Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLS V Δ as bs)
    sndRedRefl sndRedTrans sndRedAppFn sndRedBeta sndRedZeta
    (sndRedProjRed henv) sndRedStrLitCtor (sndRedNatSucc henv)
    (sndRedNatOp1 henv) (sndRedNatOp2 henv) (sndRedIota henv)
    (sndRedRescueK henv) (sndRedRescueEta henv) (sndRedRescueUnit0 henv)
    sndRedProjArg
    sndInfSort sndInfBvar (sndInfConst henv) (sndInfLitNat henv)
    (sndInfLitStr henv) sndInfPi sndInfLam sndInfApp (sndInfProj henv)
    sndInfLetE
    sndDeqRefl sndDeqSymm sndDeqTrans sndDeqOfRed sndDeqPiCong
    sndDeqLamCong sndDeqAppCong sndDeqIrrelProp (sndDeqIrrelUnit henv)
    (sndDeqStructEta henv) (sndDeqStructUnit henv) (sndDeqPairEta henv)
    sndDeqEta sndDeqLitSuccApp sndDeqProjCong
    sndTeleNil sndTeleCons sndDeqLNil sndDeqLCons
    h

/-- **Soundness for `DefEqL`**: certified spine comparisons are
pointwise interpretation equalities. -/
theorem DefEqL.sound (henv : EnvSHyp V env cval φ) {Γ : List VExpr}
    {as bs : List VExpr} (h : DefEqL μ env cval φ Γ as bs) :
    DeqLS V Γ as bs :=
  DefEqL.rec
    (motive_1 := fun Δ v w _ => RedS V Δ v w)
    (motive_2 := fun Δ v T _ => InfS V Δ v T)
    (motive_3 := fun Δ a b _ => DeqS V Δ a b)
    (motive_4 := fun Δ T as rest _ => TeleS V Δ T as rest)
    (motive_5 := fun Δ as bs _ => DeqLS V Δ as bs)
    sndRedRefl sndRedTrans sndRedAppFn sndRedBeta sndRedZeta
    (sndRedProjRed henv) sndRedStrLitCtor (sndRedNatSucc henv)
    (sndRedNatOp1 henv) (sndRedNatOp2 henv) (sndRedIota henv)
    (sndRedRescueK henv) (sndRedRescueEta henv) (sndRedRescueUnit0 henv)
    sndRedProjArg
    sndInfSort sndInfBvar (sndInfConst henv) (sndInfLitNat henv)
    (sndInfLitStr henv) sndInfPi sndInfLam sndInfApp (sndInfProj henv)
    sndInfLetE
    sndDeqRefl sndDeqSymm sndDeqTrans sndDeqOfRed sndDeqPiCong
    sndDeqLamCong sndDeqAppCong sndDeqIrrelProp (sndDeqIrrelUnit henv)
    (sndDeqStructEta henv) (sndDeqStructUnit henv) (sndDeqPairEta henv)
    sndDeqEta sndDeqLitSuccApp sndDeqProjCong
    sndTeleNil sndTeleCons sndDeqLNil sndDeqLCons
    h

end Main

end Setlec.SetR
