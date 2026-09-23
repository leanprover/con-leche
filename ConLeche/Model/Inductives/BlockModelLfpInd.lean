module

public import ConLeche.Model.Inductives.BlockRecPreRun
public section

/-!
# The IND regime's induction, from the RECORDED lfp clause (lane ENVLFP)

The consumer of the environment invariant's lfp clause
(`EnvModelM.lfpBlocks`/`lfp_ok`, `Model/Annot/BlockLfp.lean`).

Regime IND's induction principle is `blockIndPt`
(`BlockRecPreRun.lean` §17): the recursor's conclusion is inhabited at
every fitting spine, by `lfpTuple_induction` on the block's
representation.  It reads the representation `BlockModelAt` at exactly
two clauses — `functor` (monotone, closed tuple) and `leaf` (the major
lies in the carrier) — which are the lfp clause's.  So the induction
is a consequence of the RECORDED clause alone:

* `blockIndPt_lfp` — `blockIndPt` with `BlockModelAt` replaced by the
  lfp clause of the block's datum `d.toLfp`;
* `blockIndPt_of_env` — the same, with the clause read off an
  environment carrier that records the block (`d.toLfp ∈
  mp.lfpBlocks`).  `declBlock` records every uniform block this way at
  its constructors' environment (`EnvModelM.addLfp`), which is the
  carrier the recursor stage is handed.

The regime itself is not rewired: the graph route (DESIGN, ruling of
2026-09-23) replaces it, and its `ind` is `LfpClause.kitInd`. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

section BlockIndLfp

variable {env : Env} {mo : EnvModel V env} {d : BlockData V}

/-- **`blockIndPt` from the lfp clause**: the conclusion at every
fitting spine, by the block's own induction, reading only the clause's
`functor` and `leaf`. -/
theorem blockIndPt_lfp (hL : LfpClause mo.acval d.toLfp) {ψ : Name → Nat} {ρ : Nat → V}
    {K : Nat} {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm}
    (hmemK : ∀ c, c < K → mem c < d.k)
    (hshape : BlockRecTyShape V mo d ψ K rP mem rds ρ)
    (hsplit : BlockRecSplitAt V mo d ψ K rP mem rds ρ)
    (hstep : ∀ as : List V, SpineFit ρ (d.params ψ) as →
      ∀ m, m < d.N → ∀ i, i ∈ˢ d.idx ψ (consList as ρ) m → ∀ x,
        x ∈ˢ app (d.Φ ψ (consList as ρ)
            (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
              (blockIndP d ψ ρ K rP mem rds concl as)) m) i →
        blockIndP d ψ ρ K rP mem rds concl as m i x) :
    ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (pt : V) ∈ˢ interp V (consList ys ρ) (concl c) := by
  intro c hc ys hfit
  obtain ⟨-, hys2, hpar, hidx, hmaj⟩ := hsplit c hc ys hfit
  have hsat := d.satOfSpine hpar
  obtain ⟨hmono, -, hcl⟩ := hL.functor ψ (consList ((prefOf (rP c) ys).take d.nP) ρ) hsat
  have hmemN : mem c < d.N := Nat.lt_of_lt_of_le (hmemK c hc) (Nat.le_add_right _ _)
  have hi : d.tup ψ (mem c) (idxOf (rP c) ys)
      ∈ˢ d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ) (mem c) := tupW_mem hidx
  -- the LEAF, read off the clause: the major lies in the carrier
  have hleaf : ((prefOf (rP c) ys).take d.nP ++ idxOf (rP c) ys).foldl app
        (interp V ρ (mo.acval (d.memberName (mem c)) ψ))
      = app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
          (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)) (mem c))
          (d.tup ψ (mem c) (idxOf (rP c) ys)) :=
    hL.leaf (mem c) (hmemK c hc) ψ ρ _ _ hpar hidx
  have hmajC : majOf ys ∈ˢ
      app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ((prefOf (rP c) ys).take d.nP) ρ))
        (d.Φ ψ (consList ((prefOf (rP c) ys).take d.nP) ρ)) (mem c))
        (d.tup ψ (mem c) (idxOf (rP c) ys)) := by
    rw [← hleaf]
    exact hmaj
  obtain ⟨hnP, hlenL, -, -, -⟩ := hshape c hc
  have hmid := spineFit_dropAt (spineFit_take_le (rP c) hfit) (n := d.nP)
    (by rw [List.length_take, List.length_map] at *; omega)
  rw [List.drop_take] at hmid
  have hrebuild : (prefOf (rP c) ys).take d.nP ++ (prefOf (rP c) ys).drop d.nP
      ++ idxOf (rP c) ys ++ [majOf ys] = ys := by
    rw [List.append_assoc, List.take_append_drop]
    exact hys2.symm
  have hgoal := lfpTuple_induction hcl hmono
    (blockIndP d ψ ρ K rP mem rds concl ((prefOf (rP c) ys).take d.nP))
    (hstep ((prefOf (rP c) ys).take d.nP) hpar) (mem c) hmemN _ hi _ hmajC c hc rfl
    ((prefOf (rP c) ys).drop d.nP) (idxOf (rP c) ys) hmid hidx rfl
  rwa [hrebuild] at hgoal

end BlockIndLfp

/-- **Regime IND's induction, from the environment invariant**: at a
carrier that RECORDS the block (`d.toLfp ∈ mp.lfpBlocks` — what
`declBlock` establishes at the constructors' environment), the
conclusion at every fitting spine follows from the recorded clause;
no `BlockModelAt` is consulted. -/
theorem blockIndPt_of_env {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env)
    {d : BlockData V} (hD : d.toLfp ∈ mp.lfpBlocks) {ψ : Name → Nat} {ρ : Nat → V}
    {K : Nat} {rP mem : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm}
    (hmemK : ∀ c, c < K → mem c < d.k)
    (hshape : BlockRecTyShape V mp.base2 d ψ K rP mem rds ρ)
    (hsplit : BlockRecSplitAt V mp.base2 d ψ K rP mem rds ρ)
    (hstep : ∀ as : List V, SpineFit ρ (d.params ψ) as →
      ∀ m, m < d.N → ∀ i, i ∈ˢ d.idx ψ (consList as ρ) m → ∀ x,
        x ∈ˢ app (d.Φ ψ (consList as ρ)
            (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
              (blockIndP d ψ ρ K rP mem rds concl as)) m) i →
        blockIndP d ψ ρ K rP mem rds concl as m i x) :
    ∀ c, c < K → ∀ ys : List V, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (pt : V) ∈ˢ interp V (consList ys ρ) (concl c) :=
  blockIndPt_lfp (mp.lfpClause_of_mem hD) hmemK hshape hsplit hstep

end ConLeche.Model
