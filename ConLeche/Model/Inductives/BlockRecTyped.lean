module

public import ConLeche.Model.Inductives.BlockRecKit
public import ConLeche.Model.Inductives.BlockRec
public import ConLeche.Model.Inductives.MutualRuleRead
public section

/-!
# The candidate typed at the readings; the equations at the candidate (task #315, M3)

`blockRecs` (`BlockRec.lean`) names four facts; this file discharges
`hcand` (the candidate tuple's components are typed at the `k`-motive
recursor types' readings) and `hceq` (the rules' equations hold at the
candidate) at the CONCRETE readings M4 assembles: member `mm`'s
recursor type reads to `mkPisAV (mutualRecDataAV m ψ Ls nP nIdxs elimL
pps ipss cds mots tgts mm) (mutualConcAV k n nIdx mm)`
(`denoteMeta_mutualRecTy`), and `BlockReadings` says those readings are
the datum's — the leaves are the members', the index counts and
telescopes the members', the constructor data list is the members'
constructor data in block order, the minors' members and targets the
datum's.

`hcand`: a fitting spine of the recursor type decomposes into the
parameters, the `k` motives, the `n` minors, the member's indices and
the major (`spineFit_recData_inv`); the candidate's leaf there is the
union recursor at the frame's data (`blockLeafV_at`), typed by the
kit at `w ≠ 0` (`blockRecAt_mem_B`); at a `Prop`-valued block
(`w = 0`, hence `ℓ = 0` — the run fact) the candidate is the point and
the recursor type is inhabited by the induction (`inhab_all`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The readings are the datum's -/

/-- **The `k`-motive recursor types' readings are the datum's** — what
M4's assembly supplies from `FormerReadsM`/`MutualCtorReadsM` and the
datum's construction: the leaves, index counts and telescopes are the
members', the parameter data's domains are the block's, the
constructor data list is the members' constructor data in block order
(`minorIdx`), the minors' members and targets are the datum's, and
the readings' domains are closed at their depths (`MutualRecData.below`). -/
structure BlockReadings (m : EnvModel V env) (d : BlockRepData V) (ψ : Name → Nat) (elimL : Level)
    (Ls : List AnnotTerm) (nIdxs : List Nat) (pps : List (Nat × Nat × AnnotTerm))
    (ipss : List (List (Nat × Nat × AnnotTerm))) (cds : List CtorDatumR) (mots : Nat → Nat)
    (tgts : Nat → Nat → Nat) : Prop where
  lsLen : Ls.length = d.k
  leafAt : ∀ t, t < d.k → Ls.getD t default = m.acval (d.memberName t) ψ
  nIdxAt : ∀ t, t < d.k → nIdxs.getD t 0 = d.nIdxAt t
  ppsDom : pps.map (·.2.2) = d.params ψ
  ipsAt : ∀ t, t < d.k → ipss.getD t [] = (d.ppsM t ψ).drop d.nP
  cdsLen : cds.length = d.nCtors
  cdsAt : ∀ c j cA, c < d.k → (d.ctorsM c)[j]? = some cA →
    cds[d.minorIdx c j]? = some (cA.1.name, cA.2, d.dsF c j ψ, d.esF c j ψ,
      ConLeche.recIdxOf (d.ksF c j), d.eissF c j ψ, d.tssF c j ψ)
  motsAt : ∀ c j, c < d.k → j < (d.ctorsM c).length → mots (d.minorIdx c j) = c
  tgtsAt : ∀ c j, c < d.k → j < (d.ctorsM c).length → tgts (d.minorIdx c j) = d.tgts c j
  below : ∀ mm, mm < d.k →
    DomsBelow 0 (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)

/-! ## Spines of the readings -/

theorem map_dom_getD {l : List (Nat × Nat × AnnotTerm)} {J : Nat} {e : Nat × Nat × AnnotTerm}
    (h : l[J]? = some e) : (l.map (·.2.2)).getD J default = e.2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]; rfl

/-- The prefix of the readings: the parameters, the `k` motives and
the `n` minors. -/
@[expose] def recPrefixAV {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (Ls : List AnnotTerm)
    (nP : Nat) (nIdxs : List Nat) (elimL : Level) (pps : List (Nat × Nat × AnnotTerm))
    (ipss : List (List (Nat × Nat × AnnotTerm))) (cds : List CtorDatumR) (mots : Nat → Nat)
    (tgts : Nat → Nat → Nat) : List (Nat × Nat × AnnotTerm) :=
  rebit (pwBit ψ (Level.zeronessOf elimL)) pps ++
    motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0) (fun t => ipss.getD t [])
      ψ nP elimL (pwBit ψ (Level.zeronessOf elimL)) Ls.length 0 ++
    fixMinorsDataM mots tgts m ψ nP (pwBit ψ (Level.zeronessOf elimL)) cds Ls.length

theorem mutualRecDataAV_eq_prefix {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP : Nat} {nIdxs : List Nat} {elimL : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {mm : Nat} :
    mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mots tgts mm
      = recPrefixAV m ψ Ls nP nIdxs elimL pps ipss cds mots tgts ++
        (rebit (pwBit ψ (Level.zeronessOf elimL))
          (liftDoms (Ls.length + cds.length) 0 (ipss.getD mm [])) ++
        [(0, pwBit ψ (Level.zeronessOf elimL),
          majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) Ls.length cds.length)]) := by
  unfold mutualRecDataAV recPrefixAV
  simp only [List.append_assoc]

theorem mutualRuleDataAV_eq_prefix {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP : Nat} {nIdxs : List Nat} {elimL : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} :
    (mutualRuleDataAV m ψ Ls nP nIdxs elimL pps ipss cds mots tgts ds).map (·.2)
      = (recPrefixAV m ψ Ls nP nIdxs elimL pps ipss cds mots tgts ++
          rebit (pwBit ψ (Level.zeronessOf elimL))
            (liftDoms (Ls.length + cds.length) 0 (ds.drop nP))).map (·.2.2) := by
  unfold mutualRuleDataAV recPrefixAV
  simp only [List.map_map, List.append_assoc]
  rfl

/-- **The frame of the readings' prefix**: a fit of the parameters,
motives and minors, decomposed with the pieces' typings in the
datum's spellings. -/
structure PrefixFrame (m : EnvModel V env) (d : BlockRepData V) (ψ : Name → Nat) (elimL : Level)
    (ρ : Nat → V) (ps Msl msl : List V) : Prop where
  params : SpineFit ρ (d.params ψ) ps
  mslLen : Msl.length = d.k
  motives : ∀ c, c < d.k → Msl.getD c pt ∈ˢ interp V (consList ps ρ)
    (motiveAVIL (m.acval (d.memberName c) ψ) ψ d.nP (d.nIdxAt c) elimL ((d.ppsM c ψ).drop d.nP))
  minsLen : msl.length = d.nCtors
  minors : ∀ c j cA, c < d.k → (d.ctorsM c)[j]? = some cA →
    msl.getD (d.minorIdx c j) pt
      ∈ˢ interp V (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ)))
        (minorAVAtRM c (d.tgts c j) m cA.1.name ψ d.nP cA.2 (pwBit ψ (Level.zeronessOf elimL))
          (d.k + d.minorIdx c j) (d.dsF c j ψ) (d.esF c j ψ) (ConLeche.recIdxOf (d.ksF c j))
          (d.tssF c j ψ) (d.eissF c j ψ))

/-- A fit of the readings' prefix decomposes. -/
theorem spineFit_prefix_inv {m : EnvModel V env} {d : BlockRepData V} {ψ : Name → Nat}
    {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    {ρ : Nat → V} {xs : List V}
    (hsp : SpineFit ρ ((recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts).map (·.2.2)) xs) :
    ∃ ps Msl msl, xs = ps ++ Msl ++ msl ∧ PrefixFrame m d ψ elimL ρ ps Msl msl := by
  unfold recPrefixAV at hsp
  rw [List.map_append, List.map_append] at hsp
  obtain ⟨xs₁, msl, rfl, hsp₁, hmsl⟩ := spineFit_append_inv hsp
  obtain ⟨ps, Msl, rfl, hps, hMsl⟩ := spineFit_append_inv hsp₁
  rw [rebit_map_dom, hR.ppsDom] at hps
  have hlenM : Msl.length = d.k := by
    rw [hMsl.length_eq, List.length_map, motivesDataGo_length, hR.lsLen]
  have hlenm : msl.length = d.nCtors := by
    rw [hmsl.length_eq, List.length_map, fixMinorsDataM_length, hR.cdsLen]
  rw [consList_append] at hmsl
  refine ⟨ps, Msl, msl, rfl, hps, hlenM, fun c hc => ?_, hlenm, fun c j cA hc hj => ?_⟩
  · have hck : c < Ls.length := by rw [hR.lsLen]; exact hc
    have := FixKI.spineFit_getD_mem' hMsl (l := c)
      (by rw [List.length_map, motivesDataGo_length]; exact hck)
    rw [map_dom_getD (motivesDataGo_getElem? _ _ _ ψ d.nP elimL _ Ls.length 0 c hck)] at this
    have hlen : (Msl.take c).length = 0 + c := by
      rw [List.length_take, hlenM, Nat.zero_add]; exact Nat.min_eq_left (Nat.le_of_lt hc)
    rw [← hlen, interp_liftN_consList, hR.leafAt c hc, hR.nIdxAt c hc, hR.ipsAt c hc] at this
    exact this
  · have hj' : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
    have hJ := d.minorIdx_lt hc hj'
    have hJc : d.minorIdx c j < cds.length := by rw [hR.cdsLen]; exact hJ
    have := FixKI.spineFit_getD_mem' hmsl (l := d.minorIdx c j)
      (by rw [List.length_map, fixMinorsDataM_length]; exact hJc)
    rw [map_dom_getD (by rw [fixMinorsDataM_getElem?, hR.cdsAt c j cA hc hj]; rfl)] at this
    rw [hR.motsAt c j hc hj', hR.tgtsAt c j hc hj', hR.lsLen] at this
    exact this

/-- The readings' bits are the elimination level's. -/
theorem recPrefixAV_bits {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm} {nP : Nat}
    {nIdxs : List Nat} {elimL : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {d' : Nat × Nat × AnnotTerm}
    (hd : d' ∈ recPrefixAV m ψ Ls nP nIdxs elimL pps ipss cds mots tgts) :
    d'.2.1 = pwBit ψ (Level.zeronessOf elimL) := by
  unfold recPrefixAV at hd
  simp only [List.mem_append] at hd
  rcases hd with (h | h) | h
  · exact mem_rebit h
  · exact mem_motivesDataGo h
  · exact mem_fixMinorsDataM h

/-- **A fitting spine of member `mm`'s recursor type decomposes**: the
prefix frame, a fitting index spine of the member and a major in the
carrier's fibre at its tuple. -/
theorem BlockReps.spineFit_recData_inv {m : EnvModel V env} {d : BlockRepData V}
    (hreps : BlockReps m d) {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm}
    {nIdxs : List Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts)
    {mm : Nat} (hmm : mm < d.k) {ρ : Nat → V} {xs : List V}
    (hsp : SpineFit ρ ((mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm).map (·.2.2))
      xs) :
    ∃ ps Msl msl is t, xs = ps ++ Msl ++ msl ++ is ++ [t] ∧
      PrefixFrame m d ψ elimL ρ ps Msl msl ∧
      SpineFit (consList ps ρ) (d.IdsM mm ψ) is ∧
      t ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)) mm)
        (d.tup ψ mm is) := by
  rw [mutualRecDataAV_eq_prefix, List.map_append, List.map_append] at hsp
  obtain ⟨xs₁, xs₂, rfl, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  obtain ⟨ps, Msl, msl, rfl, hF⟩ := spineFit_prefix_inv hR hsp₁
  obtain ⟨is, ts, rfl, his, ht⟩ := spineFit_append_inv hsp₂
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mm hmm
  have hpl := hreps.params_length (by omega) ψ
  have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
  -- the index spine
  rw [rebit_map_dom, spineFit_liftDoms, consList_append, consList_append, ← consList_append Msl msl,
    show Ls.length + cds.length = (Msl ++ msl).length from by
      rw [List.length_append, hR.lsLen, hR.cdsLen, hF.mslLen, hF.minsLen],
    shiftE_consList, hR.ipsAt mm hmm] at his
  have his' : SpineFit (consList ps ρ) (d.IdsM mm ψ) is := his
  -- the major
  obtain ⟨t, rfl, htm⟩ := spineFit_singleton ht
  refine ⟨ps, Msl, msl, is, t, by simp only [List.append_assoc], hF, his', ?_⟩
  have htm' : t ∈ˢ interp V (consList is (consList (ps ++ Msl ++ msl) ρ))
      (majorAVAtK (Ls.getD mm default) d.nP (nIdxs.getD mm 0) Ls.length cds.length) := htm
  unfold majorAVAtK at htm'
  rw [hR.leafAt mm hmm, hR.nIdxAt mm hmm, hR.lsLen, hR.cdsLen, consList_append, consList_append,
    ← consList_append Msl msl, show d.nP + d.k + d.nCtors + d.nIdxAt mm
      = d.nP + ((Msl ++ msl).length + d.nIdxAt mm) from by
        rw [List.length_append, hF.mslLen, hF.minsLen]; omega,
    h.leaf_app hpl hρp his' (Msl ++ msl)] at htm'
  exact htm'

/-- **The candidate's leaf at a frame of its recursor type** is the
union recursor at the frame's data. -/
theorem BlockRepData.blockLeafV_at (d : BlockRepData V) (ψ : Name → Nat) (ℓ mm : Nat)
    (ρ : Nat → V) {ps Msl msl is : List V} (t : V) (hMsl : Msl.length = d.k)
    (hmsl : msl.length = d.nCtors) (his : is.length = d.nIdxAt mm) :
    d.blockLeafV ψ ℓ mm (consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ)
      = d.blockRecAt ψ (consList ps ρ) ℓ (fun c => if c < d.k then Msl.getD c pt else pt)
          (fun J => if J < d.nCtors then msl.getD J pt else pt) mm (d.tup ψ mm is) t := by
  unfold BlockRepData.blockLeafV
  have hfr : consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ
      = cons t (consList is (consList msl (consList Msl (consList ps ρ)))) := by
    simp only [consList_append, consList_cons, consList_nil]
  rw [hfr]
  have hsh : shiftE (1 + d.nIdxAt mm + d.nCtors + d.k) 0
      (cons t (consList is (consList msl (consList Msl (consList ps ρ))))) = consList ps ρ := by
    rw [show cons t (consList is (consList msl (consList Msl (consList ps ρ))))
        = consList (Msl ++ msl ++ is ++ [t]) (consList ps ρ) from by
          simp only [consList_append, consList_cons, consList_nil],
      show 1 + d.nIdxAt mm + d.nCtors + d.k = (Msl ++ msl ++ is ++ [t]).length from by
        simp only [List.length_append, List.length_singleton, hMsl, hmsl, his]; omega,
      shiftE_consList]
  have hsh1 : shiftE 1 0 (cons t (consList is (consList msl (consList Msl (consList ps ρ)))))
      = consList is (consList msl (consList Msl (consList ps ρ))) := by
    rw [show cons t (consList is (consList msl (consList Msl (consList ps ρ))))
        = consList [t] (consList is (consList msl (consList Msl (consList ps ρ)))) from rfl,
      show (1 : Nat) = [t].length from rfl, shiftE_consList]
  rw [hsh, hsh1, ← his, frameIdx_consList', his]
  congr 1
  · funext c
    split
    · next hc =>
      rw [show 1 + d.nIdxAt mm + d.nCtors + (d.k - 1 - c) = (((d.k - 1 - c) + msl.length) + is.length) + 1
          from by rw [hmsl, his]; omega]
      show consList [t] (consList is (consList msl (consList Msl (consList ps ρ))))
        ((((d.k - 1 - c) + msl.length) + is.length) + [t].length) = _
      rw [consList_apply_add, consList_apply_add, consList_apply_add,
        consList_apply_lt' _ _ (by omega), hMsl,
        show d.k - 1 - (d.k - 1 - c) = c from by omega]
    · rfl
  · funext J
    split
    · next hJ =>
      rw [show 1 + d.nIdxAt mm + d.nCtors - 1 - J = ((d.nCtors - 1 - J) + is.length) + 1
          from by rw [his]; omega]
      show consList [t] (consList is (consList msl (consList Msl (consList ps ρ))))
        (((d.nCtors - 1 - J) + is.length) + [t].length) = _
      rw [consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega), hmsl,
        show d.nCtors - 1 - (d.nCtors - 1 - J) = J from by omega]
    · rfl

/-- The conclusion of member `mm`'s recursor type at a frame: motive
`mm` at the index spine and the major. -/
theorem interp_mutualConcAV_at (d : BlockRepData V) (ρ : Nat → V) {ps Msl msl is : List V}
    (t : V) (hMsl : Msl.length = d.k) (hmsl : msl.length = d.nCtors) {mm : Nat} (hmm : mm < d.k)
    (his : is.length = d.nIdxAt mm) :
    interp V (consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ)
        (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)
      = SetTheory.app (is.foldl SetTheory.app (Msl.getD mm pt)) t := by
  have hfr : consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ
      = cons t (consList is (consList msl (consList Msl (consList ps ρ)))) := by
    simp only [consList_append, consList_cons, consList_nil]
  rw [hfr]
  unfold mutualConcAV
  rw [interp_app, interp_mkAppN, interp_bvar, interp_bvar, cons_zero,
    ← List.foldl_map (f := interp V (cons t (consList is (consList msl (consList Msl (consList ps ρ))))))
      (g := SetTheory.app),
    map_idxVarsAV_interp (ρ₀ := consList is (consList msl (consList Msl (consList ps ρ))))
      (by unfold RecFrameS; rw [show cons t (consList is (consList msl (consList Msl (consList ps ρ))))
          = consList [t] (consList is (consList msl (consList Msl (consList ps ρ)))) from rfl,
        show (1 : Nat) = [t].length from rfl, shiftE_consList]),
    ← his, frameIdx_consList', his]
  congr 2
  rw [show 1 + d.nIdxAt mm + d.nCtors + d.k - 1 - mm = (((d.k - 1 - mm) + msl.length) + is.length) + 1
      from by rw [hmsl, his]; omega]
  show consList [t] (consList is (consList msl (consList Msl (consList ps ρ))))
    ((((d.k - 1 - mm) + msl.length) + is.length) + [t].length) = _
  rw [consList_apply_add, consList_apply_add, consList_apply_add,
    consList_apply_lt' _ _ (by omega), hMsl, show d.k - 1 - (d.k - 1 - mm) = mm from by omega]

/-- The tower's walk premise from the leaf's facts at every fitting
spine. -/
theorem towerWalk_of {mm : Nat} {C : AnnotTerm} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ xs, SpineFit ρ (ds.map (·.2.2)) xs →
        g (consList xs ρ) ∈ˢ interp V (consList xs ρ) C ∧
        (mm = 0 → interp V (consList xs ρ) C ∈ˢ (univZero : V))) →
      TowerWalk mm C g ρ ds
  | [], ρ, h => by
    have := h [] trivial
    rw [consList_nil] at this
    exact this
  | d :: ds, ρ, h => fun a ha => towerWalk_of fun xs hxs => by
    have := h (a :: xs) ⟨ha, hxs⟩
    rwa [consList_cons] at this

/-! ## `hcand` -/

/-- **The candidate is typed at the readings** (`blockRecs`'s `hcand`):
at every frame, member `mm`'s candidate lies in the reading of its
recursor type.  At `w ≠ 0` the leaf is the union recursor, in the
bound (`blockRecAt_mem_B`); at `w = 0` (hence `ℓ = 0`, the run fact
`hwℓ`) the candidate is the point and the type is inhabited at every
fitting spine by the induction (`inhab_all`). -/
theorem BlockReps.blockCand_mem {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {elimL : Level}
    (hwℓ : d.w ψ = 0 → elimL.eval ψ = 0) {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts) (ρ : Nat → V) {mm : Nat}
    (hmm : mm < d.k) :
    d.blockCand ψ (elimL.eval ψ) (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
        mm ρ
      ∈ˢ interp V ρ (mkPisAV (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm)
          (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) := by
  have hbits : ∀ d' ∈ mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm,
      (elimL.eval ψ = 0 ↔ d'.2.1 = 0) := by
    intro d' hd'
    rw [mem_mutualRecDataAV hd', pwBit_zeronessOf]
  have hb : pwBit ψ (Level.zeronessOf elimL) = 0 ↔ elimL.eval ψ = 0 := pwBit_zeronessOf ψ elimL
  -- the leaf's facts at every fitting spine
  have hleaf : ∀ xs, SpineFit ρ
      ((mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm).map (·.2.2)) xs →
      (d.w ψ ≠ 0 →
        d.blockLeafV ψ (elimL.eval ψ) mm (consList xs ρ)
          ∈ˢ interp V (consList xs ρ) (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) ∧
      (∃ y, y ∈ˢ interp V (consList xs ρ) (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)) ∧
      interp V (consList xs ρ) (mutualConcAV d.k d.nCtors (d.nIdxAt mm) mm)
        ∈ˢ (univ (elimL.eval ψ) : V) := by
    intro xs hxs
    obtain ⟨ps, Msl, msl, is, t, rfl, hF, his, ht⟩ := hreps.spineFit_recData_inv hR hmm hxs
    obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps mm hmm
    have hpl := hreps.params_length (by omega) ψ
    have hρp : Sat V (d.params ψ).reverse (consList ps ρ) := d.satOfSpine hF.params
    have hlenI : is.length = d.nIdxAt mm := by rw [his.length_eq, h.IdsM_length]
    have hMseq : ∀ c, c < d.k → (fun c => if c < d.k then Msl.getD c pt else pt) c = Msl.getD c pt :=
      fun c hc => if_pos hc
    have hMs : ∀ c, c < d.k → (fun c => if c < d.k then Msl.getD c pt else pt) c ∈ˢ
        interp V (consList ps ρ) (motiveAVIL (m.acval (d.memberName c) ψ) ψ d.nP (d.nIdxAt c) elimL
          ((d.ppsM c ψ).drop d.nP)) := fun c hc => by
      rw [hMseq c hc]; exact hF.motives c hc
    have hms : ∀ c j cA, c < d.k → (d.ctorsM c)[j]? = some cA →
        (fun J => if J < d.nCtors then msl.getD J pt else pt) (d.minorIdx c j)
          ∈ˢ interp V (consList (msl.take (d.minorIdx c j)) (consList Msl (consList ps ρ)))
            (minorAVAtRM c (d.tgts c j) m cA.1.name ψ d.nP cA.2 (pwBit ψ (Level.zeronessOf elimL))
              (d.k + d.minorIdx c j) (d.dsF c j ψ) (d.esF c j ψ) (ConLeche.recIdxOf (d.ksF c j))
              (d.tssF c j ψ) (d.eissF c j ψ)) := fun c j cA hc hj => by
      show (if d.minorIdx c j < d.nCtors then msl.getD (d.minorIdx c j) pt else pt) ∈ˢ _
      rw [if_pos (d.minorIdx_lt hc (List.getElem?_eq_some_iff.mp hj).1)]
      exact hF.minors c j cA hc hj
    rw [interp_mutualConcAV_at d ρ t hF.mslLen hF.minsLen hmm hlenI,
      d.blockLeafV_at ψ (elimL.eval ψ) mm ρ t hF.mslLen hF.minsLen hlenI]
    have huniv : SetTheory.app (is.foldl SetTheory.app (Msl.getD mm pt)) t ∈ˢ (univ (elimL.eval ψ) : V) :=
      h.motive_app_mem hpl hρp (hF.motives mm hmm) his ht
    refine ⟨fun hw => ?_, ?_, huniv⟩
    · have := hreps.blockRecAt_mem_B hfT hρp hw hF.mslLen hMseq hMs hb hF.minsLen
        (ms := fun J => if J < d.nCtors then msl.getD J pt else pt) hms hmm (tupW_mem his) ht
      rw [BlockRepData.kitB_tagged, ← h.IdsM_length ψ, isOfW_tupW (h.idxOk ψ (consList ps ρ) hρp mm hmm) his,
        if_pos hmm] at this
      exact this
    · rcases Classical.em (d.w ψ = 0) with hw0 | hw
      · have := hreps.inhab_all hfT hρp (hwℓ hw0) hF.mslLen hF.motives hb hF.minsLen
          (ms := fun J => msl.getD J pt) hF.minors mm hmm _ (tupW_mem his) t ht
        rw [← h.IdsM_length ψ, isOfW_tupW (h.idxOk ψ (consList ps ρ) hρp mm hmm) his] at this
        exact this
      · have := hreps.blockRecAt_mem_B hfT hρp hw hF.mslLen hMseq hMs hb hF.minsLen
          (ms := fun J => if J < d.nCtors then msl.getD J pt else pt) hms hmm (tupW_mem his) ht
        rw [BlockRepData.kitB_tagged, ← h.IdsM_length ψ, isOfW_tupW (h.idxOk ψ (consList ps ρ) hρp mm hmm) his,
          if_pos hmm] at this
        exact ⟨_, this⟩
  rcases Classical.em (d.w ψ = 0) with hw0 | hw
  · -- the `Prop`-valued block: the candidate is the point, the type inhabited
    have hℓ := hwℓ hw0
    have hne : mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      rw [mutualRecDataAV_length (by rw [← List.length_map, hR.ppsDom]; exact hreps.params_length (by omega) ψ)] at this
      simp at this
    have hpt : d.blockCand ψ (elimL.eval ψ)
        (mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm) mm ρ = pt := by
      unfold BlockRepData.blockCand
      cases hd : mutualRecDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts mm with
      | nil => exact absurd hd hne
      | cons d' ds' =>
        show lamR (elimL.eval ψ) _ _ = pt
        rw [hℓ]; exact lamR_zero
    rw [hpt]
    exact pt_mem_mkPisAV_zero_of hne (fun d' hd' => (hbits d' hd').mp hℓ)
      fun xs hxs => (hleaf xs hxs).2.1
  · unfold BlockRepData.blockCand
    exact lamTower_mem hbits (towerWalk_of fun xs hxs =>
      ⟨(hleaf xs hxs).1 hw, fun h0 => by rw [← univ_zero, ← h0]; exact (hleaf xs hxs).2.2⟩)

end ConLeche.Model
