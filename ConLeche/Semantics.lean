module

public import ConLeche.Semantics.Syntax
public import ConLeche.Semantics.Interp
public import ConLeche.Semantics.Kit
public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.DefEqList
public import ConLeche.Semantics.EqTower
public import ConLeche.Semantics.EraseInv
public import ConLeche.Semantics.DivModEval
public import ConLeche.Semantics.Frame
public import ConLeche.Semantics.LitParams
public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.DefEqStep
public import ConLeche.Semantics.Canon
public import ConLeche.Semantics.LitStep
public import ConLeche.Semantics.DenoteClosed
public import ConLeche.Semantics.Install
public import ConLeche.Semantics.ConstsBound
public import ConLeche.Semantics.BasisType
public import ConLeche.Semantics.Univ
public import ConLeche.Semantics.BasisOk
public import ConLeche.Semantics.Skeleton
public import ConLeche.Semantics.Hoist
public import ConLeche.Semantics.Decl
public import ConLeche.Semantics.DeclEta
public import ConLeche.Semantics.DeclRun
public import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Verify.Inductives.TargetAuxFire
public import ConLeche.Verify.Inductives.BlockPartsInv
public import ConLeche.Verify.Inductives.BlockWF
public import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Semantics.Inductives.HoleApp
public import ConLeche.Semantics.SubstAV
public import ConLeche.Semantics.Inductives.HoleMono
public import ConLeche.Semantics.Inductives.HoleAcc
public import ConLeche.Semantics.Inductives.TeleAcc
public import ConLeche.Semantics.Inductives.HoleAppGrade
public import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Semantics.EnvFacts
public import ConLeche.Semantics.BasisRules
public import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Semantics.Tower.SumTower
public import ConLeche.Semantics.Tower.FixTower
public import ConLeche.Semantics.Tower.BlockTower
public import ConLeche.Semantics.Tower.BlockRecTower
public import ConLeche.Semantics.Bridge.Decl
public import ConLeche.Semantics.Bridge.DeclRun
public import ConLeche.Semantics.Bridge.Sound

@[expose] public section

/-!
# `ConLeche.Semantics` — the Expr-facing semantic tier

What is pure — the two-regime product and abstraction
(`piR`/`lamR`), the built-in constants' value towers and the
unit-terminated tuple tower — is `ConLeche/SetModel/*` and mentions
neither `Expr` nor the annotated syntax.  Everything that reads a term
lives here: the annotated syntax `AnnotTerm` and its two-regime
interpretation `interp`, the membership kit, `WellDenoted`, the
per-declaration run records and the run bridge (`Bridge/*`), the
inductive-block facts (`Inductives/*`) and the tower introduction
machinery that reads annotated field domains (`Tower/*`).
`ConLeche/{Kernel,Cached,Frontend}/*` and `Main.lean` never import this
tier; `ConLeche/Model/*` stands on it.
-/
