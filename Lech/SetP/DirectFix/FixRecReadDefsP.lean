import Lech.SetP.DirectSum.SumRecReadP
import Lech.SetP.DirectFix.FixDataP

/-!
# The generated recursive recursor's readings: the targets (task #188)

The binder data the generated recursor type `directRecTyR`
(`Lech/Kernel/Direct/RecParts.lean`) reads to, and the rules' λ-data
and cores — the indexed sum route's (`SumRecReadP.lean`) with the
**inductive-hypothesis binders** in the minors (`ihPisAV`: for each
recursive field `i`, at ih position `l`, `motive e⃗_i f_i` with the
field's index readings moved to the binder's frame, `ihIdxAt`) and
the ih applications in the rules (`ihAppAV`: the recursor's leaf at
the block's variables, the field's index readings and the field).  The
reading theorems (`FixRecReadP.lean`) prove the kernel's generators
read to exactly these.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The ih binders -/

/-- Field `i`'s index expression (read at the field's own frame: the
parameters, the `i` earlier fields) moved under all `nF` fields, `l`
ih binders below them and `o` extras between the parameters and the
fields — `directIdxAt`'s reading. -/
def ihIdxAt (nF o i l : Nat) (E : AVExpr) : AVExpr :=
  (E.liftN (nF - i + l) 0).liftN o (nF + l)

/-- The ih binder's domain for recursive field `i` at ih position `l`:
the motive at the field's index readings and the field. -/
def ihDomAV (nF o i l : Nat) (Eis : List AVExpr) : AVExpr :=
  AVExpr.mkAppN (.bvar (nF + o - 1 + l))
    (Eis.map (ihIdxAt nF o i l) ++ [.bvar (nF - 1 - i + l)])

/-- The ih binders' Π-tower over the recursive positions. -/
def ihPisAV (nF o b : Nat) (Eiss : List (List AVExpr)) : List Nat → Nat → AVExpr → AVExpr
  | [], _, body => body
  | i :: is, l, body =>
    .pi 0 b (ihDomAV nF o i l (Eiss.getD i [])) (ihPisAV nF o b Eiss is (l + 1) body)

/-- The minor premise's domain reading at a recursive block: the
constructor's field data lifted `o` under (bits reset to `b`), the ih
binders, the motive at the constructor's index readings and spine
lifted above the ih binders. -/
def minorAVAtR {env : Env} (m : EnvS2Core V env) (C : Name) (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AVExpr)) (Es : List AVExpr) (recIdx : List Nat)
    (Eiss : List (List AVExpr)) : AVExpr :=
  mkPisAV (rebit b (liftDoms o 0 (ds.drop nP)))
    (ihPisAV nF o b Eiss recIdx 0
      ((AVExpr.mkAppN (.bvar (nF + o - 1))
        ((Es.map fun E => E.liftN o nF) ++
          [AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)])).liftN
        recIdx.length 0))

/-- A recursive constructor datum: name, field count, field data,
index readings, recursive positions, per-field index-expression
readings. -/
abbrev CtorDatumR :=
  Name × Nat × List (Nat × Nat × AVExpr) × List AVExpr × List Nat × List (List AVExpr)

/-- The minor entries, one per constructor datum, from offset `o`. -/
def fixMinorsData {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (nP b : Nat) :
    List CtorDatumR → Nat → List (Nat × Nat × AVExpr)
  | [], _ => []
  | (C, nF, ds, Es, recIdx, Eiss) :: cs, o =>
    (0, b, minorAVAtR m C ψ nP nF b o ds Es recIdx Eiss) :: fixMinorsData m ψ nP b cs (o + 1)

theorem fixMinorsData_length {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List CtorDatumR) (o : Nat), (fixMinorsData m ψ nP b cds o).length = cds.length
  | [], _ => rfl
  | (_, _, _, _, _, _) :: cs, o => by simp [fixMinorsData, fixMinorsData_length cs (o + 1)]

theorem mem_fixMinorsData {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ {cds : List CtorDatumR} {o : Nat} {d : Nat × Nat × AVExpr},
      d ∈ fixMinorsData m ψ nP b cds o → d.2.1 = b
  | [], _, _, h => nomatch h
  | (_, _, _, _, _, _) :: cs, o, d, h => by
    simp only [fixMinorsData, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_fixMinorsData h

theorem fixMinorsData_getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List CtorDatumR) (o j : Nat),
      (fixMinorsData m ψ nP b cds o)[j]?
        = (cds[j]?).map fun cd => (0, b, minorAVAtR m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1
            cd.2.2.2.2.1 cd.2.2.2.2.2)
  | [], _, _ => rfl
  | (C, nF, ds, Es, recIdx, Eiss) :: cs, o, 0 => by simp [fixMinorsData]
  | (C, nF, ds, Es, recIdx, Eiss) :: cs, o, j + 1 => by
    simp only [fixMinorsData, List.getElem?_cons_succ]
    rw [fixMinorsData_getElem? cs (o + 1) j]
    congr 2
    funext cd
    rw [show o + 1 + j = o + (j + 1) from by omega]

/-- **The generated recursive recursor type's binder data**: parameters,
motive, minors (with the ih binders), the index telescope lifted under
the motive and the minors, major. -/
def fixRecDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AVExpr))
    (cds : List CtorDatumR) : List (Nat × Nat × AVExpr) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
    fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips) ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), majorAVAt m T ψ nP nIdx cds.length)]

theorem mem_fixRecDataAV {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AVExpr)} {cds : List CtorDatumR}
    {d : Nat × Nat × AVExpr}
    (hd : d ∈ fixRecDataAV m T ψ nP nIdx ℓ pps ips cds) : d.2.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  simp only [fixRecDataAV, List.mem_append, List.mem_singleton] at hd
  rcases hd with (((h | rfl) | h) | h) | rfl
  · exact mem_rebit h
  · rfl
  · exact mem_fixMinorsData h
  · exact mem_rebit h
  · rfl

theorem fixRecDataAV_length {m : EnvS2Core V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AVExpr)} {cds : List CtorDatumR}
    (hp : pps.length = nP) (hi : ips.length = nIdx) :
    (fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).length = nP + cds.length + nIdx + 2 := by
  simp only [fixRecDataAV, List.length_append, rebit_length, hp, hi, List.length_singleton,
    fixMinorsData_length, liftDoms_length]
  omega

/-! ## The rules -/

/-- The recursor's leading spine `p⃗ motive m⃗` read under the `nF`
fields of a rule (`directRecPrefixAt nP n nF 0`'s reading). -/
def recPrefixBvars (nP n nF : Nat) : List AVExpr :=
  paramBvarsAt nP (nF + n + 1) ++ [.bvar (nF + n)] ++
    (List.range n).map fun l => AVExpr.bvar (nF + n - 1 - l)

/-- The ih application in a rule for recursive field `i`: the recursor's
leaf `R` at the block's variables, the field's index readings moved
under the fields (with the motive and `n` minors as the extras) and the
field. -/
def ihAppAV (R : AVExpr) (nP n nF i : Nat) (Eis : List AVExpr) : AVExpr :=
  AVExpr.mkAppN R (recPrefixBvars nP n nF ++ Eis.map (ihIdxAt nF (n + 1) i 0) ++
    [.bvar (nF - 1 - i)])

/-- Rule `j`'s core at a recursive block: minor `j` at the field
variables and the ih applications. -/
def fixRuleCoreAV (R : AVExpr) (nP nF n j : Nat) (recIdx : List Nat) (Eiss : List (List AVExpr)) :
    AVExpr :=
  AVExpr.mkAppN (.bvar (nF + n - 1 - j))
    (fieldBvars nF ++ recIdx.map fun i => ihAppAV R nP n nF i (Eiss.getD i []))

/-- **Rule `j`'s binder data** at a recursive block: the recursor's
parameter, motive and minor entries, then constructor `j`'s field data
lifted `n + 1` under. -/
def fixRuleDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AVExpr))
    (cds : List CtorDatumR) (ds : List (Nat × Nat × AVExpr)) :
    List (Nat × AVExpr) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
    fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2)

/-! ## The per-constructor reading premise -/

/-- What the readings need of one constructor `(C, nF, cty, recIdx)`
and its datum `(C, nF, ds, Es, recIdx, Eiss)`: the sum route's
(`CtorRead`) and, per recursive position `i`, the reading of the
field's index expressions at the field's own depth (`Eiss.getD i`, as
many as the indices) with the field's entry the family at the
parameter variables and those readings. -/
structure CtorReadR {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (c : Name × Nat × Expr × List Nat) (cd : CtorDatumR) :
    Prop where
  name : cd.1 = c.1
  nF : cd.2.1 = c.2.1
  find : ∃ ci : ConstantInfo, env.find? c.1 = some ci ∧ ci.toConstantVal.levelParams = lps
  hasFvar : c.2.2.1.hasFvar = false
  bounded : c.2.2.1.looseBVarsBounded 0 = true
  resid : ∃ (cbs : List (Name × Expr × BinderMeta)) (es : List Expr),
    c.2.2.1.stripPis (nP + c.2.1)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt c.2.1 nP ++ es)) ∧
    es.length = nIdx
  read : denoteP m.acval env ψ 0 c.2.2.1
    = some (mkPisAV cd.2.2.1 (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP c.2.1 ++ cd.2.2.2.1)))
  len : cd.2.2.1.length = nP + c.2.1
  lenE : cd.2.2.2.1.length = nIdx
  recIdx : cd.2.2.2.2.1 = c.2.2.2
  recIdxBnd : ∀ i ∈ c.2.2.2, i < c.2.1
  /-- the recursive positions are strictly increasing (`recIdxOf`) -/
  recIdxSorted : c.2.2.2.Pairwise (· < ·)
  eissLen : cd.2.2.2.2.2.length = c.2.1
  eisLen : ∀ i ∈ c.2.2.2, (cd.2.2.2.2.2.getD i []).length = nIdx
  /-- a recursive field's index expressions, read at the field's own
  depth `nP + i` with the parameters and the earlier fields as
  variables, in an opening of the constructor's telescope -/
  eisRead : ∀ i ∈ c.2.2.2, ∀ (fvs : List Expr) (o : Expr),
    openPisAtFvars (nP + c.2.1) c.2.2.1 0 = some (fvs, o) →
    DenoteSpineP m.acval env ψ (nP + i)
      ((Lech.directFieldIdxOf c.2.2.1 nP c.2.1 i).map
        (Expr.instSeq (fvs.take (nP + i)) (nP + i - 1)))
      (cd.2.2.2.2.2.getD i [])
  recEntry : ∀ i ∈ c.2.2.2,
    (cd.2.2.1.getD (nP + i) default).2.2
      = AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + i) ++ cd.2.2.2.2.2.getD i [])

/-- The constructors' reading premises, positionally. -/
inductive CtorReadsR {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) :
    List (Name × Nat × Expr × List Nat) → List CtorDatumR → Prop
  | nil : CtorReadsR m ψ T lps nP nIdx [] []
  | cons {c cd cs cds} : CtorReadR m ψ T lps nP nIdx c cd → CtorReadsR m ψ T lps nP nIdx cs cds →
      CtorReadsR m ψ T lps nP nIdx (c :: cs) (cd :: cds)

theorem CtorReadsR.length_eq {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      CtorReadsR m ψ T lps nP nIdx ctors cds → cds.length = ctors.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CtorReadsR.length_eq h]

theorem CtorReadsR.getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      ∀ {i : Nat} {c : Name × Nat × Expr × List Nat}, ctors[i]? = some c →
        ∃ cd, cds[i]? = some cd ∧ CtorReadR m ψ T lps nP nIdx c cd
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hr htl, i, c, h => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hr⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨cd, hcd, hR⟩ := CtorReadsR.getElem? htl h
      exact ⟨cd, by simpa using hcd, hR⟩

end Lech.SetP
