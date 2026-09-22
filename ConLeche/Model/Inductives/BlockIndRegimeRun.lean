module

public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The IND regime, at the run (task #315, M5M-rule)

`blockIndRegime_run` (`BlockRecPreRun.lean`) is the dispatch's
`ℓ = 0` arm: it turns the block's own induction, the rules'
certificates and the regime's two chain-frame premises into
`IndRegimeAt`.  Until this file it was never APPLIED — and it is the
hinge of the whole arm's `ℓ = 0` half, so twelve landed theorems
across two lanes had no consumer for want of it.

Two pieces:

* **§1 the CROSSING.**  `hihOpen` is stated in the BLOCK datum's
  currency (`d.Fss`, `d.tlss`, `d.Eiss`, `d.IdsM`, `mem c`, `rP c`)
  and the run produces it in the rule FRAME's
  (`fr.nF`, `fr.teleOf`, `fr.idxOf`, `fr.ihKeys`, the callee's stored
  type).  `blockIhOpen_key_of` is that crossing, at one key: half A's
  three block facts (`BlockRecTyShapeRun.lean`) decide what the KEY
  says, and `blockIhOpenerDom_run`'s fused reading supplies the peel,
  the tower and the domain equation.  Every identification it needs is
  a premise, because each one is a different lane's fact;
* **§2 the COMPOSITION.**  `blockIndRegime_of_run` applies
  `blockIndRegime_run` with everything the run already produces
  discharged: the recursor type's shape (`blockRecTyShape_run`), the
  binder bits (`blockRecOneElimLevel`), the Π-tower identification and
  the conclusion's boundedness (`checkBlockRecK_tyPis`,
  `checkBlockRecK_tyBounds`), and `hihOpen` through §1.

**Two premises stay open and are NOT invented here.**  `hjoinC`
(`BlockRecTyJoin`) is the certificate lane's — nothing in the run ties
the recursor's index binders to the member's telescope, and that lane
is restating `blockIndP` around it; and the four `univZero` facts
(`hTStep`, `hCaE`, `hihReg`, `hTReg`) are that lane's current session
(§40.14's note: `hT`, `hTStep`, `hTReg` and the `ih` opener's `h0` are
four premises of ONE missing producer — a peel of a block recursor
type at a fitting spine lands in `univZero` when the elimination level
is zero).  They are taken here in the shape those lanes deliver.

No `w` hypothesis: every statement below is a READING, a peel or a
key's own filter fact, never a membership in the block's carrier
(the settled criterion, and the `w ≠ 0` ruling's own blast radius).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)
open ConLeche (BlockFieldKind blockIhKeys blockTgtsOf)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. THE CROSSING — `hihOpen` at ONE key

`blockIndRegime_run`'s `hihOpen` quantifies over `(c, j, r)` and
produces eight existential witnesses and thirteen conjuncts.  Eleven
of the thirteen are the KEY's own (half A, `BlockRecTyShapeRun.lean`
§7) or are `rfl` at the witnesses this theorem chooses; the two that
carry content are the callee's peel and the opener's domain, and both
come out of the ONE fused reading `blockIhOpenerDom_run`.

The premises are grouped by who owns them:

* the block datum's tables at this constructor (`hcj`, `hcf`, `hmr`,
  `hksF`, `hksLen`, `hFssLen`, `htgtsF`, `hrecTgtsLen`, `hrecTgts`,
  `hmemK`) — the install's;
* the frame's widths and the callees' prefixes (`hnF`, `hrPs`, `hb`)
  — the recursor stage's;
* the callee recursor types' readings (`hRecTy`) — §21's;
* the openers' slot and their fused reading (`hfvsIh`, `hslot`,
  `hdom`) — this lane's, `readOpenedDoms_reads` and
  `blockIhOpenerDom_run`.

`hb` is the generated tower's binder BIT (`pwBit ψ fr.pw`), which
`hihOpen` asks at `0`: the `ih` binders of a recursor whose motive
lives at level `0` are `Prop` binders.  It is a premise because the
datum is the CHECK's (`BlockRuleFrame.pw`) and the identification
`pwBit ψ fr.pw = 0` at the IND regime is the stage's, not this
module's. -/
theorem blockIhOpen_key_of {envT envC : Env} {mT : EnvModel V envT} {mo : EnvModel V envC}
    {ψ : Name → Nat} {d : BlockData V} {lps : List Name}
    {q : ConLeche.BlockShape} {cvTas : List ConstantVal}
    {K c j nF b : Nat} {mem rP : Nat → Nat}
    {rPs recTgts : List Nat} {ks : List BlockFieldKind} {cA : ConstantVal × Nat}
    {RecTy : Nat → AnnotTerm} {recTyOf : Nat → Expr}
    {ihdoms : List AnnotTerm} {fvsIh : List Expr}
    -- the block datum's tables at this constructor
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mo d lps (mem c) j cA)
    (hmr : BlockMembersRun mo d q cvTas)
    (hksF : d.ksF (mem c) j = ks.map BlockFieldKind.toRec)
    (hksLen : ks.length = cA.2)
    (hFssLen : ((d.Fss (mem c) ψ).getD j []).length = cA.2)
    (htgtsF : ∀ l, d.tgts (mem c) j l = (blockTgtsOf ks).getD l 0)
    (hrecTgtsLen : recTgts.length = K)
    (hrecTgts : ∀ e, e < K → recTgts.getD e K = mem e)
    (hmemK : ∀ e, e < K → mem e < d.k)
    -- the frame's widths and the callees' prefixes
    (hnF : cA.2 = nF) (hrPs : ∀ e, e < K → rPs.getD e 0 = rP e) (hb : b = 0)
    -- the callee recursors' stored types read to `RecTy`
    (hRecTy : ∀ e, e < K → denoteMeta mT.acval envT ψ 0 (recTyOf e) = some (RecTy e))
    -- the openers' slot, and their FUSED reading
    (hfvsIh : ∀ r, r < (blockIhKeys (rP c) rPs recTgts ks).length → ∃ x, fvsIh[r]? = some x)
    (hslot : ∀ (r : Nat) (x : Expr), fvsIh[r]? = some x →
      denoteMeta mT.acval envT ψ (rP c + nF + r) (Expr.fvarTypeD x)
        = some (ihdoms.getD r default))
    (hdom : ∀ (i c' r : Nat) (x : Expr),
      (blockIhKeys (rP c) rPs recTgts ks)[r]? = some (i, c') → fvsIh[r]? = some x →
      ∃ TVa CihR : AnnotTerm,
        denoteMeta mT.acval envT ψ 0 (recTyOf c') = some TVa ∧
        ConLeche.Model.AnnotTerm.peelPis TVa
            (paramBvarsAt (rP c)
                (rP c + nF + (((d.tlss (mem c) ψ).getD j []).getD i []).length) ++
              (((d.Eiss (mem c) ψ).getD j []).getD i []).map
                (ihIdxAtM nF (rP c - d.nP) i 0
                  (((d.tlss (mem c) ψ).getD j []).getD i []).length) ++
              [AnnotTerm.mkAppN
                (.bvar (nF - 1 - i + 0 + (((d.tlss (mem c) ψ).getD j []).getD i []).length))
                (teleVarsAV (((d.tlss (mem c) ψ).getD j []).getD i []).length)])
          = some CihR ∧
        denoteMeta mT.acval envT ψ (rP c + nF + r) (Expr.fvarTypeD x)
          = some ((mkPisAV (ihTeleAtR nF (rP c - d.nP) i 0
              (rebit b (((d.tlss (mem c) ψ).getD j []).getD i []))) CihR).liftN r 0)) :
    ∀ r, r < (blockIhKeys (rP c) rPs recTgts ks).length →
      ∃ (i c' nF' nIdx m : Nat) (eisA : List AnnotTerm) (fapA CihR : AnnotTerm),
        ((blockIhKeys (rP c) rPs recTgts ks).getD r (0, 0)).1 = i ∧
        ((blockIhKeys (rP c) rPs recTgts ks).getD r (0, 0)).2 = c' ∧
        c' < K ∧
        i < ((d.Fss (mem c) ψ).getD j []).length ∧
        ((d.rss (mem c)).getD j []).getD i false = true ∧
        d.tgts (mem c) j i = mem c' ∧
        ((d.Fss (mem c) ψ).getD j []).length = nF' ∧
        (((d.tlss (mem c) ψ).getD j []).getD i []).length = m ∧
        (((d.Eiss (mem c) ψ).getD j []).getD i []).length = nIdx ∧
        (d.IdsM (mem c') ψ).length = nIdx ∧
        eisA = (((d.Eiss (mem c) ψ).getD j []).getD i []).map
            (ihIdxAtM nF' (rP c - d.nP) i 0 m) ∧
        fapA = AnnotTerm.mkAppN (.bvar (nF' - 1 - i + m)) (teleVarsAV m) ∧
        BlockRuleConclAt (rP c') nF' m (RecTy c') eisA fapA CihR ∧
        ihdoms.getD r default
          = (mkPisAV (ihTeleAtR nF' (rP c - d.nP) i 0
              (rebit 0 (((d.tlss (mem c) ψ).getD j []).getD i []))) CihR).liftN r 0 := by
  subst hb
  subst hnF
  intro r hr
  obtain ⟨x, hx⟩ := hfvsIh r hr
  obtain ⟨i, c', hkey⟩ : ∃ i c', (blockIhKeys (rP c) rPs recTgts ks).getD r (0, 0) = (i, c') :=
    ⟨_, _, rfl⟩
  have hkeyE : (blockIhKeys (rP c) rPs recTgts ks)[r]? = some (i, c') := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at hkey
    rw [List.getElem?_eq_getElem hr, hkey]
  obtain ⟨hc'K, hiF, hrec, htgt, hrPsv, hkind⟩ :=
    blockIhKey_block_facts hcj hksF hksLen hFssLen htgtsF hrecTgtsLen hrecTgts hkey hr
  obtain ⟨-, hEl⟩ := blockIhKey_block_lengths (V := V) ψ hcj hcf (hFssLen ▸ hiF) hkind
  have hIds := blockMembers_IdsM_length (V := V) hmr (hmemK c' hc'K) ψ
  obtain ⟨TVa, CihR, hTVa, hpeel, hread⟩ := hdom i c' r x hkeyE hx
  obtain rfl : TVa = RecTy c' := Option.some.inj (hTVa.symm.trans (hRecTy c' hc'K))
  -- the callee's rule prefix IS this rule's, which is what the key's filter decides
  have hrPc' : rP c' = rP c := by rw [← hrPs c' hc'K, hrPsv]
  rw [Nat.add_zero] at hpeel
  refine ⟨i, c', cA.2, d.nIdxAt (mem c'), (((d.tlss (mem c) ψ).getD j []).getD i []).length,
    (((d.Eiss (mem c) ψ).getD j []).getD i []).map
      (ihIdxAtM cA.2 (rP c - d.nP) i 0 (((d.tlss (mem c) ψ).getD j []).getD i []).length),
    AnnotTerm.mkAppN
      (.bvar (cA.2 - 1 - i + (((d.tlss (mem c) ψ).getD j []).getD i []).length))
      (teleVarsAV (((d.tlss (mem c) ψ).getD j []).getD i []).length),
    CihR, by rw [hkey], by rw [hkey], hc'K, hiF, hrec, htgt, hFssLen, rfl,
    by rw [hEl, htgt], hIds, rfl, rfl, ?_, ?_⟩
  · rw [hrPc']
    exact hpeel
  · exact Option.some.inj ((hslot r x hx).symm.trans hread)

/-! ### 1b. `hihOpen` ASSEMBLED — the same crossing at every key

`blockIndRegime_run`'s `hihOpen` quantifies over the rule `c`, the
constructor `j` and the opener position `r`; §1 is its body at one
key.  The per-`(c, j)` data the crossing needs is EXISTENTIAL at the
run — each rule's frame is produced by that rule's own run, and the
field kinds, the constructor, the `ih` openers and the tower's bit
come out of it together — so it is one premise, `hframe`, and not
thirteen indexed families.  `hmr`, `hrecTgts`, `hmemK`, `hrPs` and
`hRecTy` are BLOCK-wide and stay outside it.

The `ihKeys` identification is inside `hframe` too: the regime reads
its keys off a POSITION in its own `ihKeys c j`, and what the check
generates is `blockIhKeys` at the rule's prefix, the block's prefixes
and targets and the constructor's kinds. -/
theorem blockIhOpen_of {envT envC : Env} {mT : EnvModel V envT} {mo : EnvModel V envC}
    {ψ : Name → Nat} {d : BlockData V} {lps : List Name}
    {q : ConLeche.BlockShape} {cvTas : List ConstantVal}
    {K : Nat} {mem nCt rP : Nat → Nat} {rPs recTgts : List Nat}
    {RecTy : Nat → AnnotTerm} {recTyOf : Nat → Expr}
    {ihKeys : Nat → Nat → List (Nat × Nat)} {ihdoms : Nat → Nat → List AnnotTerm}
    (hmr : BlockMembersRun mo d q cvTas)
    (hrecTgtsLen : recTgts.length = K)
    (hrecTgts : ∀ e, e < K → recTgts.getD e K = mem e)
    (hmemK : ∀ e, e < K → mem e < d.k)
    (hrPs : ∀ e, e < K → rPs.getD e 0 = rP e)
    (hRecTy : ∀ e, e < K → denoteMeta mT.acval envT ψ 0 (recTyOf e) = some (RecTy e))
    (hframe : ∀ c, c < K → ∀ j, j < nCt c →
      ∃ (ks : List BlockFieldKind) (cA : ConstantVal × Nat) (fvsIh : List Expr) (nF b : Nat),
        ihKeys c j = blockIhKeys (rP c) rPs recTgts ks ∧
        (d.ctorsM (mem c))[j]? = some cA ∧
        BlockCtorFacts mo d lps (mem c) j cA ∧
        d.ksF (mem c) j = ks.map BlockFieldKind.toRec ∧
        ks.length = cA.2 ∧
        ((d.Fss (mem c) ψ).getD j []).length = cA.2 ∧
        (∀ l, d.tgts (mem c) j l = (blockTgtsOf ks).getD l 0) ∧
        cA.2 = nF ∧ b = 0 ∧
        (∀ r, r < (ihKeys c j).length → ∃ x, fvsIh[r]? = some x) ∧
        (∀ (r : Nat) (x : Expr), fvsIh[r]? = some x →
          denoteMeta mT.acval envT ψ (rP c + nF + r) (Expr.fvarTypeD x)
            = some ((ihdoms c j).getD r default)) ∧
        (∀ (i c' r : Nat) (x : Expr), (ihKeys c j)[r]? = some (i, c') → fvsIh[r]? = some x →
          ∃ TVa CihR : AnnotTerm,
            denoteMeta mT.acval envT ψ 0 (recTyOf c') = some TVa ∧
            ConLeche.Model.AnnotTerm.peelPis TVa
                (paramBvarsAt (rP c)
                    (rP c + nF + (((d.tlss (mem c) ψ).getD j []).getD i []).length) ++
                  (((d.Eiss (mem c) ψ).getD j []).getD i []).map
                    (ihIdxAtM nF (rP c - d.nP) i 0
                      (((d.tlss (mem c) ψ).getD j []).getD i []).length) ++
                  [AnnotTerm.mkAppN
                    (.bvar (nF - 1 - i + 0
                      + (((d.tlss (mem c) ψ).getD j []).getD i []).length))
                    (teleVarsAV (((d.tlss (mem c) ψ).getD j []).getD i []).length)])
              = some CihR ∧
            denoteMeta mT.acval envT ψ (rP c + nF + r) (Expr.fvarTypeD x)
              = some ((mkPisAV (ihTeleAtR nF (rP c - d.nP) i 0
                  (rebit b (((d.tlss (mem c) ψ).getD j []).getD i []))) CihR).liftN r 0))) :
    ∀ c, c < K → ∀ j, j < nCt c → ∀ r, r < (ihKeys c j).length →
      ∃ (i c' nF nIdx m : Nat) (eisA : List AnnotTerm) (fapA CihR : AnnotTerm),
        ((ihKeys c j).getD r (0, 0)).1 = i ∧
        ((ihKeys c j).getD r (0, 0)).2 = c' ∧
        c' < K ∧
        i < ((d.Fss (mem c) ψ).getD j []).length ∧
        ((d.rss (mem c)).getD j []).getD i false = true ∧
        d.tgts (mem c) j i = mem c' ∧
        ((d.Fss (mem c) ψ).getD j []).length = nF ∧
        (((d.tlss (mem c) ψ).getD j []).getD i []).length = m ∧
        (((d.Eiss (mem c) ψ).getD j []).getD i []).length = nIdx ∧
        (d.IdsM (mem c') ψ).length = nIdx ∧
        eisA = (((d.Eiss (mem c) ψ).getD j []).getD i []).map
            (ihIdxAtM nF (rP c - d.nP) i 0 m) ∧
        fapA = AnnotTerm.mkAppN (.bvar (nF - 1 - i + m)) (teleVarsAV m) ∧
        BlockRuleConclAt (rP c') nF m (RecTy c') eisA fapA CihR ∧
        (ihdoms c j).getD r default
          = (mkPisAV (ihTeleAtR nF (rP c - d.nP) i 0
              (rebit 0 (((d.tlss (mem c) ψ).getD j []).getD i []))) CihR).liftN r 0 := by
  intro c hc j hj r hr
  obtain ⟨ks, cA, fvsIh, nF, b, hkeys, hcj, hcf, hksF, hksLen, hFssLen, htgtsF, hnF, hb,
    hfvsIh, hslot, hdom⟩ := hframe c hc j hj
  rw [hkeys] at hr hfvsIh hdom ⊢
  exact blockIhOpen_key_of hcj hcf hmr hksF hksLen hFssLen htgtsF hrecTgtsLen hrecTgts hmemK
    hnF hrPs hb hRecTy hfvsIh hslot hdom r hr
