module

public import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Annot.Bit
public import ConLeche.Semantics.Tower.IhSpell
import ConLeche.Model.Annot.BitInst
public section

/-!
# The recursor spellings, below the representation clause (task #279 M-A′)

The binder data and cores the generated recursors and rules READ TO —
the fixpoint route's (`fixRecDataAV`, `fixRuleDataAV`, `fixRuleCoreAV`,
task #188) and the `k`-motive mutual block's (`mutualRecDataAV`,
`mutualRuleDataAV`, `mutualRuleCoreAV`, task #278), with the pieces
they are spelled from (the motive `motiveAVIL`, the major `majorAVAtK`,
the minors `fixMinorsDataM` with their ih binders `ihPisAVM`, the ih
applications `ihAppAVK`, and the bookkeeping `rebit`, `liftDoms`,
`fieldBvars`).  They used to live with their reading theorems
(`StructRecRead`, `StructRecSpine`, `SumRecRead`, `FixRecReadDefs`,
`MutualRecRead`, `MutualRuleRead`); the representation clause
(`ConLeche/Model/IndRep.lean`) now STATES that a stored recursor's type
and rules read to these towers (`recRead`, `rulesRead`), so the
definitions moved here verbatim, below the clause, and those modules
re-export this one.  No statement changed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Bits reset -/

/-- Binder data with every codomain bit reset to `b`. -/
@[expose] def rebit (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ds.map fun d => (d.1, b, d.2.2)

@[simp] theorem rebit_nil (b : Nat) : rebit b [] = [] := rfl

@[simp] theorem rebit_cons (b : Nat) (d : Nat × Nat × AnnotTerm) (ds : List (Nat × Nat × AnnotTerm)) :
    rebit b (d :: ds) = (d.1, b, d.2.2) :: rebit b ds := rfl

@[simp] theorem rebit_length (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).length = ds.length := by simp [rebit]

@[simp] theorem rebit_map_dom (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).map (·.2.2) = ds.map (·.2.2) := by simp [rebit]

theorem rebit_getD (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) (j : Nat) (hj : j < ds.length) :
    (rebit b ds).getD j default = ((ds.getD j default).1, b, (ds.getD j default).2.2) := by
  simp only [rebit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

theorem mem_rebit {b : Nat} {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm}
    (h : d ∈ rebit b ds) : d.2.1 = b := by
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp h
  rfl

/-! ## The field variables -/

/-- The field variables' spine at the minor's core. -/
@[expose] def fieldBvars (nF : Nat) : List AnnotTerm :=
  (List.range nF).map fun k => AnnotTerm.bvar (nF - 1 - k)

/-! ## Lifted Π-towers -/

/-- The binder data of a lifted Π-tower: each domain lifted at its own
depth. -/
@[expose] def liftDoms (n : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: ds => (d.1, d.2.1, d.2.2.liftN n k) :: liftDoms n (k + 1) ds

theorem liftDoms_length (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat), (liftDoms n k ds).length = ds.length
  | [], _ => rfl
  | _ :: ds, k => by simp [liftDoms, liftDoms_length n ds (k + 1)]

theorem liftDoms_getElem? (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k i : Nat),
      (liftDoms n k ds)[i]? = ds[i]?.map fun d => (d.1, d.2.1, d.2.2.liftN n (k + i))
  | [], _, _ => rfl
  | _ :: ds, k, 0 => by simp [liftDoms]
  | _ :: ds, k, i + 1 => by
    simp only [liftDoms, List.getElem?_cons_succ, liftDoms_getElem? n ds (k + 1) i]
    rw [show k + 1 + i = k + (i + 1) from by omega]

/-! ## The motive and the major -/

/-- The motive's domain reading `∀ ı⃗ (t : L p⃗ ı⃗), Sort ℓ` at the
parameters' frame, over the former's index data `ips`, spelled at an
**explicit type-former leaf** `L` (task #278: the mutual block's
former is not a stored constant's leaf). -/
@[expose] def motiveAVIL (L : AnnotTerm) (ψ : Name → Nat) (nP nIdx : Nat)
    (ℓ : Level) (ips : List (Nat × Nat × AnnotTerm)) : AnnotTerm :=
  mkPisAV (rebit (pwBit ψ PropWhen.never) ips)
    (.pi 0 (pwBit ψ PropWhen.never)
      (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx))
      (.sort (ℓ.eval ψ)))

/-- The major premise's domain reading under the motive, `n` minors
and the index variables, at an explicit former leaf `L`: the family at
the parameters and the index variables. -/
@[expose] def majorAVAtL (L : AnnotTerm) (nP nIdx n : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN L (paramBvarsAt nP (nP + 1 + n + nIdx) ++ fieldBvars nIdx)

/-- The motive's domain reading at a **stored** former: `motiveAVIL` at
the constant's leaf. -/
@[expose] def motiveAVI {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat) (nP nIdx : Nat)
    (ℓ : Level) (ips : List (Nat × Nat × AnnotTerm)) : AnnotTerm :=
  motiveAVIL (m.acval T ψ) ψ nP nIdx ℓ ips

/-- The major premise's domain reading at a **stored** former:
`majorAVAtL` at the constant's leaf. -/
@[expose] def majorAVAt {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat) (nP nIdx n : Nat) :
    AnnotTerm :=
  majorAVAtL (m.acval T ψ) nP nIdx n

/-! ## The ih binders -/

/-- The ih binder's domain for recursive field `i` at ih position `l`:
under the field's telescope, the motive at the field's index readings
and the field applied to the telescope's variables (a finitary field:
the motive at the readings and the field).  The motive named is the
one `mot` binders ABOVE the innermost motive (task #278: in a mutual
block the ih of a field targeting member `mot` names member `mot`'s
motive; the fixpoint route's single motive is `mot = 0`). -/
@[expose] def ihDomAVM (mot nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    AnnotTerm :=
  mkPisAV (ihTeleAtR nF o i l tl)
    (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + tl.length - mot))
      (Eis.map (ihIdxAtM nF o i l tl.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + tl.length)) (teleVarsAV tl.length)]))

/-- The ih binder's domain at the fixpoint route's single motive. -/
@[expose] def ihDomAV (nF o i l : Nat) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    AnnotTerm :=
  ihDomAVM 0 nF o i l tl Eis

/-- The ih binders' Π-tower over the recursive positions (the moved
telescopes re-bit to the elimination bit `b`, task #202 A2), field `i`
naming the motive `moti i` binders above the innermost one. -/
@[expose] def ihPisAVM (moti : Nat → Nat) (nF o b : Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eiss : List (List AnnotTerm)) :
    List Nat → Nat → AnnotTerm → AnnotTerm
  | [], _, body => body
  | i :: is, l, body =>
    .pi 0 b (ihDomAVM (moti i) nF o i l (rebit b (tls.getD i [])) (Eiss.getD i []))
      (ihPisAVM moti nF o b tls Eiss is (l + 1) body)

/-- The minor premise's domain reading at a recursive block: the
constructor's field data lifted `o` under (bits reset to `b`), the ih
binders, the motive at the constructor's index readings and spine
lifted above the ih binders.  The conclusion names the motive `mot`
binders above the innermost one (the constructor's own member) and ih
`i` the motive `moti i` (the field's target member). -/
@[expose] def minorAVAtRM {env : Env} (mot : Nat) (moti : Nat → Nat) (m : EnvModel V env) (C : Name)
    (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  mkPisAV (rebit b (liftDoms o 0 (ds.drop nP)))
    (ihPisAVM moti nF o b tls Eiss recIdx 0
      ((AnnotTerm.mkAppN (.bvar (nF + o - 1 - mot))
        ((Es.map fun E => E.liftN o nF) ++
          [AnnotTerm.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)])).liftN
        recIdx.length 0))

/-- The minor premise's domain reading at the fixpoint route's single
motive. -/
@[expose] def minorAVAtR {env : Env} (m : EnvModel V env) (C : Name) (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  minorAVAtRM 0 (fun _ => 0) m C ψ nP nF b o ds Es recIdx tls Eiss

/-- The minor entries, one per constructor datum, from offset `o`; the
datum at position `J` names the motive `mots J` (its own member) and
its ih `i` the motive `tgts J i` (the field's target member). -/
@[expose] def fixMinorsDataM {env : Env} (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (m : EnvModel V env) (ψ : Name → Nat) (nP b : Nat) :
    List CtorDatumR → Nat → List (Nat × Nat × AnnotTerm)
  | [], _ => []
  | (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o =>
    (0, b, minorAVAtRM (mots 0) (tgts 0) m C ψ nP nF b o ds Es recIdx tls Eiss) ::
      fixMinorsDataM (fun J => mots (J + 1)) (fun J => tgts (J + 1)) m ψ nP b cs (o + 1)

/-- The minor entries at the fixpoint route's single motive. -/
@[expose] def fixMinorsData {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (nP b : Nat)
    (cds : List CtorDatumR) (o : Nat) : List (Nat × Nat × AnnotTerm) :=
  fixMinorsDataM (fun _ => 0) (fun _ _ => 0) m ψ nP b cds o

theorem fixMinorsDataM_length {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (o : Nat),
      (fixMinorsDataM mots tgts m ψ nP b cds o).length = cds.length
  | _, _, [], _ => rfl
  | mots, tgts, (_, _, _, _, _, _, _) :: cs, o => by
    simp [fixMinorsDataM, fixMinorsDataM_length (fun J => mots (J + 1)) (fun J => tgts (J + 1)) cs (o + 1)]

theorem fixMinorsData_length {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat}
    (cds : List CtorDatumR) (o : Nat) : (fixMinorsData m ψ nP b cds o).length = cds.length :=
  fixMinorsDataM_length _ _ cds o

theorem mem_fixMinorsDataM {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {cds : List CtorDatumR} {o : Nat}
      {d : Nat × Nat × AnnotTerm},
      d ∈ fixMinorsDataM mots tgts m ψ nP b cds o → d.2.1 = b
  | _, _, [], _, _, h => nomatch h
  | _, _, (_, _, _, _, _, _, _) :: cs, o, d, h => by
    simp only [fixMinorsDataM, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_fixMinorsDataM h

theorem mem_fixMinorsData {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat}
    {cds : List CtorDatumR} {o : Nat} {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ fixMinorsData m ψ nP b cds o) : d.2.1 = b :=
  mem_fixMinorsDataM hd

theorem fixMinorsDataM_getElem? {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (o j : Nat),
      (fixMinorsDataM mots tgts m ψ nP b cds o)[j]?
        = (cds[j]?).map fun cd => (0, b, minorAVAtRM (mots j) (tgts j) m cd.1 ψ nP cd.2.1 b (o + j)
            cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
  | _, _, [], _, _ => rfl
  | mots, tgts, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, 0 => by simp [fixMinorsDataM]
  | mots, tgts, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, j + 1 => by
    simp only [fixMinorsDataM, List.getElem?_cons_succ]
    rw [fixMinorsDataM_getElem? (fun J => mots (J + 1)) (fun J => tgts (J + 1)) cs (o + 1) j]
    congr 2
    funext cd
    rw [show o + 1 + j = o + (j + 1) from by omega]

theorem fixMinorsData_getElem? {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat}
    (cds : List CtorDatumR) (o j : Nat) :
      (fixMinorsData m ψ nP b cds o)[j]?
        = (cds[j]?).map fun cd => (0, b, minorAVAtR m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1
            cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1) :=
  fixMinorsDataM_getElem? _ _ cds o j

/-- **The generated recursive recursor type's binder data** at an
**explicit type-former leaf** `L` (task #278): parameters, motive,
minors (with the ih binders), the index telescope lifted under the
motive and the minors, major.  Only the former's two occurrences (the
motive's and the major's domains) are generic; the minors keep the
constructors' stored leaves. -/
@[expose] def fixRecDataAVL {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (L : AnnotTerm)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AnnotTerm))
    (cds : List CtorDatumR) : List (Nat × Nat × AnnotTerm) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVIL L ψ nP nIdx ℓ ips)] ++
    fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips) ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), majorAVAtL L nP nIdx cds.length)]

/-- The generated recursor type's binder data at a **stored** former:
`fixRecDataAVL` at the constant's leaf. -/
@[expose] def fixRecDataAV {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AnnotTerm))
    (cds : List CtorDatumR) : List (Nat × Nat × AnnotTerm) :=
  fixRecDataAVL m ψ (m.acval T ψ) nP nIdx ℓ pps ips cds

theorem mem_fixRecDataAVL {m : EnvModel V env} {ψ : Name → Nat} {L : AnnotTerm} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ fixRecDataAVL m ψ L nP nIdx ℓ pps ips cds) :
    d.2.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  simp only [fixRecDataAVL, List.mem_append, List.mem_singleton] at hd
  rcases hd with (((h | rfl) | h) | h) | rfl
  · exact mem_rebit h
  · rfl
  · exact mem_fixMinorsData h
  · exact mem_rebit h
  · rfl

theorem mem_fixRecDataAV {m : EnvModel V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ fixRecDataAV m T ψ nP nIdx ℓ pps ips cds) : d.2.1 = pwBit ψ (Level.zeronessOf ℓ) :=
  mem_fixRecDataAVL hd

theorem fixRecDataAVL_length {m : EnvModel V env} {ψ : Name → Nat} {L : AnnotTerm} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    (hp : pps.length = nP) (hi : ips.length = nIdx) :
    (fixRecDataAVL m ψ L nP nIdx ℓ pps ips cds).length = nP + cds.length + nIdx + 2 := by
  simp only [fixRecDataAVL, List.length_append, rebit_length, hp, hi, List.length_singleton,
    fixMinorsData_length, liftDoms_length]
  omega

theorem fixRecDataAV_length {m : EnvModel V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    (hp : pps.length = nP) (hi : ips.length = nIdx) :
    (fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).length = nP + cds.length + nIdx + 2 :=
  fixRecDataAVL_length hp hi

/-! ## The rules -/

/-- The recursor's leading spine under `m` more binders
(`structRecPrefixAt nP n nF m`'s reading). -/
@[expose] def recPrefixBvarsM (nP n nF m : Nat) : List AnnotTerm :=
  paramBvarsAt nP (nP + nF + n + 1 + m) ++ [.bvar (nF + n + m)] ++
    (List.range n).map fun l => AnnotTerm.bvar (nF + n - 1 - l + m)

/-- The ih application in a rule for recursive field `i`: under the
field's telescope (a λ-tower with the telescope's own bits), the
recursor's leaf `R` at the block's variables, the field's index
readings moved under the fields (with the motive and `n` minors as the
extras) and the field applied to the telescope's variables (a finitary
field: no telescope). -/
@[expose] def ihAppAV (R : AnnotTerm) (nP n nF i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) :
    AnnotTerm :=
  mkLamsAV ((ihTeleAtR nF (n + 1) i 0 tl).map fun d => (d.2.1, d.2.2))
    (AnnotTerm.mkAppN R (recPrefixBvarsM nP n nF tl.length ++
      Eis.map (ihIdxAtM nF (n + 1) i 0 tl.length) ++
      [AnnotTerm.mkAppN (.bvar (nF - 1 - i + tl.length)) (teleVarsAV tl.length)]))

/-- Rule `j`'s core at a recursive block: minor `j` at the field
variables and the ih applications (their telescopes re-bit to the
elimination bit `b`, task #202 A2). -/
@[expose] def fixRuleCoreAV (b : Nat) (R : AnnotTerm) (nP nF n j : Nat) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nF + n - 1 - j))
    (fieldBvars nF ++ recIdx.map fun i =>
      ihAppAV R nP n nF i (rebit b (tls.getD i [])) (Eiss.getD i []))

/-! ### The `k`-motive spellings (task #278)

A mutual block's recursors have `k` motives where the fixpoint route
has one; the spellings below are the fixpoint route's with that count
generic, and the fixpoint route's are their `k = 1` instances
(definitionally, `*_eq_*` below). -/

/-- The recursor's leading spine `p⃗ M⃗ S⃗` of a `k`-motive block, read
under `m` more binders (`ConLeche.mutualRecPrefixAt nP k n nF m`'s
reading): the parameters sit `nF + n + k + m` binders above the fields,
motive `t` at `bvar (nF + n + k - 1 - t + m)` and minor `l` at
`bvar (nF + n - 1 - l + m)`. -/
@[expose] def recPrefixBvarsMK (nP k n nF m : Nat) : List AnnotTerm :=
  paramBvarsAt nP (nP + nF + n + k + m) ++
    ((List.range k).map fun t => AnnotTerm.bvar (nF + n + k - 1 - t + m)) ++
    ((List.range n).map fun l => AnnotTerm.bvar (nF + n - 1 - l + m))

/-- The ih application in a `k`-motive rule for recursive field `i`,
with the TARGET member's recursor leaf `R`: under the field's
telescope, `R` at the block's variables, the field's index readings
(the `n + k` extras between the parameters and the fields) and the
field applied to the telescope's variables. -/
@[expose] def ihAppAVK (R : AnnotTerm) (nP k n nF i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) : AnnotTerm :=
  mkLamsAV ((ihTeleAtR nF (n + k) i 0 tl).map fun d => (d.2.1, d.2.2))
    (AnnotTerm.mkAppN R (recPrefixBvarsMK nP k n nF tl.length ++
      Eis.map (ihIdxAtM nF (n + k) i 0 tl.length) ++
      [AnnotTerm.mkAppN (.bvar (nF - 1 - i + tl.length)) (teleVarsAV tl.length)]))

/-- **Rule `j`'s core at a mutual block**: minor `j` (its GLOBAL index)
at the field variables and the ih applications, the ih of recursive
field `i` firing the recursor of the member `tgts i` the field targets
(`Rof t` is member `t`'s recursor leaf). -/
@[expose] def mutualRuleCoreAV (b : Nat) (Rof : Nat → AnnotTerm) (tgts : Nat → Nat)
    (nP k n nF j : Nat) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN (.bvar (nF + n - 1 - j))
    (fieldBvars nF ++ recIdx.map fun i =>
      ihAppAVK (Rof (tgts i)) nP k n nF i (rebit b (tls.getD i [])) (Eiss.getD i []))

/-- **Rule `j`'s binder data** at a recursive block: the recursor's
parameter, motive and minor entries, then constructor `j`'s field data
lifted `n + 1` under. -/
@[expose] def fixRuleDataAV {env : Env} (m : EnvModel V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AnnotTerm))
    (cds : List CtorDatumR) (ds : List (Nat × Nat × AnnotTerm)) :
    List (Nat × AnnotTerm) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
    fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AnnotTerm => (d.2.1, d.2.2)

/-- Every rule binder carries the elimination level's bit. -/
theorem mem_fixRuleDataAV {m : EnvModel V env} {T : Name} {ψ : Name → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × AnnotTerm}
    (hd : d ∈ fixRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds) :
    d.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_append, List.mem_singleton] at hd'
  rcases hd' with ((h | rfl) | h) | h
  · exact mem_rebit h
  · rfl
  · exact mem_fixMinorsData h
  · exact mem_rebit h

/-! ## The `k`-motive binder data (task #278) -/

/-- The major premise's domain reading under `k` motives, `n` minors
and the index variables, at an explicit former leaf: the family at the
parameters and the index variables (`majorAVAtL` with `k` motives). -/
@[expose] def majorAVAtK (L : AnnotTerm) (nP nIdx k n : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN L (paramBvarsAt nP (nP + k + n + nIdx) ++ fieldBvars nIdx)

/-- **The motive entries** of a mutual block, from offset `i`: motive
`t` is the fixpoint route's motive at member `t`'s leaf, index count
and index data, lifted `i + t` under — it sits that many binders below
the parameters. -/
@[expose] def motivesDataGo (Lof : Nat → AnnotTerm) (nIdxOf : Nat → Nat)
    (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat) (ℓ : Level)
    (b : Nat) : Nat → Nat → List (Nat × Nat × AnnotTerm)
  | 0, _ => []
  | k + 1, i =>
    (0, b, (motiveAVIL (Lof 0) ψ nP (nIdxOf 0) ℓ (ipsOf 0)).liftN i 0) ::
      motivesDataGo (fun t => Lof (t + 1)) (fun t => nIdxOf (t + 1)) (fun t => ipsOf (t + 1))
        ψ nP ℓ b k (i + 1)

omit [SetTheory V] in
theorem motivesDataGo_length (Lof : Nat → AnnotTerm) (nIdxOf : Nat → Nat)
    (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat) (ℓ : Level) (b : Nat) :
    ∀ (k i : Nat), (motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ b k i).length = k
  | 0, _ => rfl
  | k + 1, i => by
    simp [motivesDataGo,
      motivesDataGo_length (fun t => Lof (t + 1)) (fun t => nIdxOf (t + 1))
        (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1)]

omit [SetTheory V] in
theorem mem_motivesDataGo {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
    {ipsOf : Nat → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat} {nP : Nat} {ℓ : Level} {b : Nat} :
    ∀ {k i : Nat} {d : Nat × Nat × AnnotTerm},
      d ∈ motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ b k i → d.2.1 = b
  | 0, _, _, h => nomatch h
  | k + 1, i, d, h => by
    simp only [motivesDataGo, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_motivesDataGo h

omit [SetTheory V] in
/-- The motive entries, positionally. -/
theorem motivesDataGo_getElem? (Lof : Nat → AnnotTerm) (nIdxOf : Nat → Nat)
    (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat) (ℓ : Level) (b : Nat) :
    ∀ (k i t : Nat), t < k →
      (motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ b k i)[t]?
        = some (0, b, (motiveAVIL (Lof t) ψ nP (nIdxOf t) ℓ (ipsOf t)).liftN (i + t) 0)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, 0, _ => by simp [motivesDataGo]
  | k + 1, i, t + 1, h => by
    simp only [motivesDataGo, List.getElem?_cons_succ]
    rw [motivesDataGo_getElem? (fun t => Lof (t + 1)) (fun t => nIdxOf (t + 1))
      (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1) t (by omega),
      show i + 1 + t = i + (t + 1) from by omega]

omit [SetTheory V] in
/-- The motive entries depend on the members' data only below `k`. -/
theorem motivesDataGo_congr {Lof Lof' : Nat → AnnotTerm} {nIdxOf nIdxOf' : Nat → Nat}
    {ipsOf ipsOf' : Nat → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat} {nP : Nat} {ℓ : Level}
    {b : Nat} :
    ∀ (k i : Nat),
      (∀ t, t < k → Lof t = Lof' t ∧ nIdxOf t = nIdxOf' t ∧ ipsOf t = ipsOf' t) →
      motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ b k i
        = motivesDataGo Lof' nIdxOf' ipsOf' ψ nP ℓ b k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    obtain ⟨h1, h2, h3⟩ := h 0 (by omega)
    simp only [motivesDataGo, h1, h2, h3]
    rw [motivesDataGo_congr (Lof := fun t => Lof (t + 1)) (Lof' := fun t => Lof' (t + 1)) k (i + 1)
      fun t ht => h (t + 1) (by omega)]

/-- **The generated `k`-motive recursor type's binder data** for member
`mm`: the parameters, the `k` motives (motive `m'` lifted `m'` under),
the `n` minors (`mots J` is constructor `J`'s own member, `tgts J i`
the member field `i` targets), member `mm`'s index telescope lifted
under the motives and the minors, and its major. -/
@[expose] def mutualRecDataAV {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (Ls : List AnnotTerm) (nP : Nat) (nIdxs : List Nat) (ℓ : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (ipss : List (List (Nat × Nat × AnnotTerm)))
    (cds : List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (mm : Nat) :
    List (Nat × Nat × AnnotTerm) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0) (fun t => ipss.getD t [])
      ψ nP ℓ (pwBit ψ (Level.zeronessOf ℓ)) Ls.length 0 ++
    fixMinorsDataM mots tgts m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds Ls.length ++
    rebit (pwBit ψ (Level.zeronessOf ℓ))
      (liftDoms (Ls.length + cds.length) 0 (ipss.getD mm [])) ++
    [(0, pwBit ψ (Level.zeronessOf ℓ),
      majorAVAtK (Ls.getD mm default) nP (nIdxs.getD mm 0) Ls.length cds.length)]

/-- **The conclusion** of member `mm`'s generated recursor type:
motive `mm` at the index variables and the major (`recConcAV` with `k`
motives). -/
@[expose] def mutualConcAV (k n nIdx mm : Nat) : AnnotTerm :=
  .app (AnnotTerm.mkAppN (.bvar (1 + nIdx + n + k - 1 - mm)) (idxVarsAV nIdx 1)) (.bvar 0)

theorem mem_mutualRecDataAV {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP : Nat} {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {mm : Nat} {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ mutualRecDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts mm) :
    d.2.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  simp only [mutualRecDataAV, List.mem_append, List.mem_singleton] at hd
  rcases hd with (((h | h) | h) | h) | rfl
  · exact mem_rebit h
  · exact mem_motivesDataGo h
  · exact mem_fixMinorsDataM h
  · exact mem_rebit h
  · rfl

theorem mutualRecDataAV_length {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP : Nat} {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {mm : Nat} (hp : pps.length = nP) :
    (mutualRecDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts mm).length
      = nP + Ls.length + cds.length + (ipss.getD mm []).length + 1 := by
  simp only [mutualRecDataAV, List.length_append, rebit_length, hp, List.length_singleton,
    fixMinorsDataM_length, liftDoms_length, motivesDataGo_length]

/-! ## The `k`-motive rule binder data (task #278) -/

/-- **Rule `J`'s binder data** at a mutual block: the recursor's
parameter, motive and minor entries (`mutualRecDataAV` without the
index telescope and the major) and then constructor `J`'s field data
lifted `k + n` under. -/
@[expose] def mutualRuleDataAV {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (Ls : List AnnotTerm) (nP : Nat) (nIdxs : List Nat) (ℓ : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (ipss : List (List (Nat × Nat × AnnotTerm)))
    (cds : List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × AnnotTerm) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0) (fun t => ipss.getD t [])
      ψ nP ℓ (pwBit ψ (Level.zeronessOf ℓ)) Ls.length 0 ++
    fixMinorsDataM mots tgts m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds Ls.length ++
    rebit (pwBit ψ (Level.zeronessOf ℓ))
      (liftDoms (Ls.length + cds.length) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AnnotTerm => (d.2.1, d.2.2)

/-- Every rule binder carries the elimination level's bit. -/
theorem mem_mutualRuleDataAV {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP : Nat} {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × AnnotTerm}
    (hd : d ∈ mutualRuleDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds) :
    d.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_append] at hd'
  rcases hd' with ((h | h) | h) | h
  · exact mem_rebit h
  · exact mem_motivesDataGo h
  · exact mem_fixMinorsDataM h
  · exact mem_rebit h

theorem mutualRuleDataAV_length {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {nP nF : Nat} {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} (hp : pps.length = nP)
    (hd : ds.length = nP + nF) :
    (mutualRuleDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds).length
      = nP + Ls.length + cds.length + nF := by
  simp only [mutualRuleDataAV, List.length_map, List.length_append, rebit_length, hp,
    fixMinorsDataM_length, liftDoms_length, motivesDataGo_length, List.length_drop, hd]
  omega

/-! ## The pinned spellings (task #279 M-A′)

A stored recursor's block may have COPY members — a nested block's
`numNested` copies of containers at pins — whose family is not "the
member's leaf at the parameter variables" but the container's leaf at
the pins.  The spellings below take, per member, the pins at the
parameter frame (`pins`, at depth `nP`: an entry mentions only
`bvar j < nP`) in place of the parameter variables, and are the
originals at `pins = paramBvarsAt nP nP` (`*_params`). -/

/-- The family of a member at depth `D ≥ nP` below the parameters: its
leaf `L` at its pins lifted `D - nP`, then `nIdx` index variables. -/
@[expose] def famAppAV (L : AnnotTerm) (pins : List AnnotTerm) (nP D nIdx : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN L (pins.map (·.liftN (D - nP) 0) ++ fieldBvars nIdx)

omit [SetTheory V] in
/-- The parameter variables at the parameter frame, lifted to depth `D`. -/
theorem map_liftN_paramBvarsAt (nP D : Nat) (h : nP ≤ D) :
    (paramBvarsAt nP nP).map (·.liftN (D - nP) 0) = paramBvarsAt nP D := by
  simp only [paramBvarsAt, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < nP := List.mem_range.mp hk
  simp only [Function.comp_def, AnnotTerm.liftN_bvar, Nat.not_lt_zero, if_false]
  congr 1
  omega

omit [SetTheory V] in
theorem famAppAV_params (L : AnnotTerm) (nP D nIdx : Nat) (h : nP ≤ D) :
    famAppAV L (paramBvarsAt nP nP) nP D nIdx
      = AnnotTerm.mkAppN L (paramBvarsAt nP D ++ fieldBvars nIdx) := by
  unfold famAppAV
  rw [map_liftN_paramBvarsAt nP D h]

/-- `motiveAVIL` at pins. -/
@[expose] def motiveAVP (L : AnnotTerm) (pins : List AnnotTerm) (ψ : Name → Nat) (nP nIdx : Nat)
    (ℓ : Level) (ips : List (Nat × Nat × AnnotTerm)) : AnnotTerm :=
  mkPisAV (rebit (pwBit ψ PropWhen.never) ips)
    (.pi 0 (pwBit ψ PropWhen.never) (famAppAV L pins nP (nP + nIdx) nIdx) (.sort (ℓ.eval ψ)))

omit [SetTheory V] in
theorem motiveAVP_params (L : AnnotTerm) (ψ : Name → Nat) (nP nIdx : Nat) (ℓ : Level)
    (ips : List (Nat × Nat × AnnotTerm)) :
    motiveAVP L (paramBvarsAt nP nP) ψ nP nIdx ℓ ips = motiveAVIL L ψ nP nIdx ℓ ips := by
  unfold motiveAVP motiveAVIL
  rw [famAppAV_params _ _ _ _ (Nat.le_add_right _ _)]

/-- `majorAVAtK` at pins. -/
@[expose] def majorAVP (L : AnnotTerm) (pins : List AnnotTerm) (nP nIdx k n : Nat) : AnnotTerm :=
  famAppAV L pins nP (nP + k + n + nIdx) nIdx

omit [SetTheory V] in
theorem majorAVP_params (L : AnnotTerm) (nP nIdx k n : Nat) :
    majorAVP L (paramBvarsAt nP nP) nP nIdx k n = majorAVAtK L nP nIdx k n := by
  unfold majorAVP majorAVAtK
  exact famAppAV_params _ _ _ _ (by omega)

/-- `motivesDataGo` at pins (`pinsOf t` member `t`'s). -/
@[expose] def motivesDataGoP (Lof : Nat → AnnotTerm) (pinsOf : Nat → List AnnotTerm)
    (nIdxOf : Nat → Nat) (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat)
    (ℓ : Level) (b : Nat) : Nat → Nat → List (Nat × Nat × AnnotTerm)
  | 0, _ => []
  | k + 1, i =>
    (0, b, (motiveAVP (Lof 0) (pinsOf 0) ψ nP (nIdxOf 0) ℓ (ipsOf 0)).liftN i 0) ::
      motivesDataGoP (fun t => Lof (t + 1)) (fun t => pinsOf (t + 1)) (fun t => nIdxOf (t + 1))
        (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1)

omit [SetTheory V] in
theorem motivesDataGoP_params (Lof : Nat → AnnotTerm) (nIdxOf : Nat → Nat)
    (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat) (ℓ : Level) (b : Nat) :
    ∀ (k i : Nat), motivesDataGoP Lof (fun _ => paramBvarsAt nP nP) nIdxOf ipsOf ψ nP ℓ b k i
      = motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ b k i
  | 0, _ => rfl
  | k + 1, i => by
    simp only [motivesDataGoP, motivesDataGo, motiveAVP_params]
    rw [motivesDataGoP_params (fun t => Lof (t + 1)) (fun t => nIdxOf (t + 1))
      (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1)]

omit [SetTheory V] in
theorem motivesDataGoP_length (Lof : Nat → AnnotTerm) (pinsOf : Nat → List AnnotTerm)
    (nIdxOf : Nat → Nat) (ipsOf : Nat → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) (nP : Nat)
    (ℓ : Level) (b : Nat) :
    ∀ (k i : Nat), (motivesDataGoP Lof pinsOf nIdxOf ipsOf ψ nP ℓ b k i).length = k
  | 0, _ => rfl
  | k + 1, i => by
    simp [motivesDataGoP, motivesDataGoP_length (fun t => Lof (t + 1)) (fun t => pinsOf (t + 1))
      (fun t => nIdxOf (t + 1)) (fun t => ipsOf (t + 1)) ψ nP ℓ b k (i + 1)]

omit [SetTheory V] in
theorem mem_motivesDataGoP {Lof : Nat → AnnotTerm} {pinsOf : Nat → List AnnotTerm}
    {nIdxOf : Nat → Nat} {ipsOf : Nat → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat} {nP : Nat}
    {ℓ : Level} {b : Nat} :
    ∀ {k i : Nat} {d : Nat × Nat × AnnotTerm},
      d ∈ motivesDataGoP Lof pinsOf nIdxOf ipsOf ψ nP ℓ b k i → d.2.1 = b
  | 0, _, _, h => nomatch h
  | k + 1, i, d, h => by
    simp only [motivesDataGoP, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_motivesDataGoP h

/-- `minorAVAtRM` with the constructor's member at its pins `pinsC`. -/
@[expose] def minorAVAtRMP {env : Env} (mot : Nat) (moti : Nat → Nat) (m : EnvModel V env) (C : Name)
    (pinsC : List AnnotTerm) (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) : AnnotTerm :=
  mkPisAV (rebit b (liftDoms o 0 (ds.drop nP)))
    (ihPisAVM moti nF o b tls Eiss recIdx 0
      ((AnnotTerm.mkAppN (.bvar (nF + o - 1 - mot))
        ((Es.map fun E => E.liftN o nF) ++
          [famAppAV (m.acval C ψ) pinsC nP (nP + o + nF) nF])).liftN recIdx.length 0))

theorem minorAVAtRMP_params {m : EnvModel V env} {mot : Nat} {moti : Nat → Nat} {C : Name}
    {ψ : Name → Nat} {nP nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdx : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} :
    minorAVAtRMP mot moti m C (paramBvarsAt nP nP) ψ nP nF b o ds Es recIdx tls Eiss
      = minorAVAtRM mot moti m C ψ nP nF b o ds Es recIdx tls Eiss := by
  unfold minorAVAtRMP minorAVAtRM
  rw [famAppAV_params _ _ _ _ (by omega)]

/-- `fixMinorsDataM` at pins (`pinsOf J` constructor `J`'s member's). -/
@[expose] def fixMinorsDataMP {env : Env} (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (pinsOf : Nat → List AnnotTerm) (m : EnvModel V env) (ψ : Name → Nat) (nP b : Nat) :
    List CtorDatumR → Nat → List (Nat × Nat × AnnotTerm)
  | [], _ => []
  | (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o =>
    (0, b, minorAVAtRMP (mots 0) (tgts 0) m C (pinsOf 0) ψ nP nF b o ds Es recIdx tls Eiss) ::
      fixMinorsDataMP (fun J => mots (J + 1)) (fun J => tgts (J + 1)) (fun J => pinsOf (J + 1))
        m ψ nP b cs (o + 1)

theorem fixMinorsDataMP_params {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (o : Nat),
      fixMinorsDataMP mots tgts (fun _ => paramBvarsAt nP nP) m ψ nP b cds o
        = fixMinorsDataM mots tgts m ψ nP b cds o
  | _, _, [], _ => rfl
  | mots, tgts, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o => by
    simp only [fixMinorsDataMP, fixMinorsDataM, minorAVAtRMP_params]
    rw [fixMinorsDataMP_params (fun J => mots (J + 1)) (fun J => tgts (J + 1)) cs (o + 1)]

theorem fixMinorsDataMP_length {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (pinsOf : Nat → List AnnotTerm)
      (cds : List CtorDatumR) (o : Nat),
      (fixMinorsDataMP mots tgts pinsOf m ψ nP b cds o).length = cds.length
  | _, _, _, [], _ => rfl
  | mots, tgts, pinsOf, (_, _, _, _, _, _, _) :: cs, o => by
    simp [fixMinorsDataMP, fixMinorsDataMP_length (fun J => mots (J + 1)) (fun J => tgts (J + 1))
      (fun J => pinsOf (J + 1)) cs (o + 1)]

theorem mem_fixMinorsDataMP {m : EnvModel V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {pinsOf : Nat → List AnnotTerm}
      {cds : List CtorDatumR} {o : Nat} {d : Nat × Nat × AnnotTerm},
      d ∈ fixMinorsDataMP mots tgts pinsOf m ψ nP b cds o → d.2.1 = b
  | _, _, _, [], _, _, h => nomatch h
  | _, _, _, (_, _, _, _, _, _, _) :: cs, o, d, h => by
    simp only [fixMinorsDataMP, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_fixMinorsDataMP h

/-- **`mutualRecDataAV` at pins**: the `k`-motive recursor type's binder
data with every member's family spelled at that member's pins. -/
@[expose] def recDataAVP {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (Ls : List AnnotTerm) (pinsOf : Nat → List AnnotTerm) (nP : Nat) (nIdxs : List Nat) (ℓ : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (ipss : List (List (Nat × Nat × AnnotTerm)))
    (cds : List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (mm : Nat) :
    List (Nat × Nat × AnnotTerm) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    motivesDataGoP (fun t => Ls.getD t default) pinsOf (fun t => nIdxs.getD t 0)
      (fun t => ipss.getD t []) ψ nP ℓ (pwBit ψ (Level.zeronessOf ℓ)) Ls.length 0 ++
    fixMinorsDataMP mots tgts (fun J => pinsOf (mots J)) m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds
      Ls.length ++
    rebit (pwBit ψ (Level.zeronessOf ℓ))
      (liftDoms (Ls.length + cds.length) 0 (ipss.getD mm [])) ++
    [(0, pwBit ψ (Level.zeronessOf ℓ),
      majorAVP (Ls.getD mm default) (pinsOf mm) nP (nIdxs.getD mm 0) Ls.length cds.length)]

theorem recDataAVP_params {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm} {nP : Nat}
    {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {mm : Nat} :
    recDataAVP m ψ Ls (fun _ => paramBvarsAt nP nP) nP nIdxs ℓ pps ipss cds mots tgts mm
      = mutualRecDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts mm := by
  unfold recDataAVP mutualRecDataAV
  rw [motivesDataGoP_params, majorAVP_params]
  simp only [fixMinorsDataMP_params]

theorem mem_recDataAVP {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {pinsOf : Nat → List AnnotTerm} {nP : Nat} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {mm : Nat}
    {d : Nat × Nat × AnnotTerm}
    (hd : d ∈ recDataAVP m ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts mm) :
    d.2.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  simp only [recDataAVP, List.mem_append, List.mem_singleton] at hd
  rcases hd with (((h | h) | h) | h) | rfl
  · exact mem_rebit h
  · exact mem_motivesDataGoP h
  · exact mem_fixMinorsDataMP h
  · exact mem_rebit h
  · rfl

theorem recDataAVP_length {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {pinsOf : Nat → List AnnotTerm} {nP : Nat} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat} {mm : Nat}
    (hp : pps.length = nP) :
    (recDataAVP m ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts mm).length
      = nP + Ls.length + cds.length + (ipss.getD mm []).length + 1 := by
  simp only [recDataAVP, List.length_append, rebit_length, hp, List.length_singleton,
    fixMinorsDataMP_length, liftDoms_length, motivesDataGoP_length]

/-- **`mutualRuleDataAV` at pins.** -/
@[expose] def ruleDataAVP {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (Ls : List AnnotTerm) (pinsOf : Nat → List AnnotTerm) (nP : Nat) (nIdxs : List Nat) (ℓ : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (ipss : List (List (Nat × Nat × AnnotTerm)))
    (cds : List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × AnnotTerm) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    motivesDataGoP (fun t => Ls.getD t default) pinsOf (fun t => nIdxs.getD t 0)
      (fun t => ipss.getD t []) ψ nP ℓ (pwBit ψ (Level.zeronessOf ℓ)) Ls.length 0 ++
    fixMinorsDataMP mots tgts (fun J => pinsOf (mots J)) m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds
      Ls.length ++
    rebit (pwBit ψ (Level.zeronessOf ℓ))
      (liftDoms (Ls.length + cds.length) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AnnotTerm => (d.2.1, d.2.2)

theorem ruleDataAVP_params {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm} {nP : Nat}
    {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} :
    ruleDataAVP m ψ Ls (fun _ => paramBvarsAt nP nP) nP nIdxs ℓ pps ipss cds mots tgts ds
      = mutualRuleDataAV m ψ Ls nP nIdxs ℓ pps ipss cds mots tgts ds := by
  unfold ruleDataAVP mutualRuleDataAV
  rw [motivesDataGoP_params]
  simp only [fixMinorsDataMP_params]

theorem mem_ruleDataAVP {m : EnvModel V env} {ψ : Name → Nat} {Ls : List AnnotTerm}
    {pinsOf : Nat → List AnnotTerm} {nP : Nat} {nIdxs : List Nat} {ℓ : Level}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × AnnotTerm}
    (hd : d ∈ ruleDataAVP m ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts ds) :
    d.1 = pwBit ψ (Level.zeronessOf ℓ) := by
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_append] at hd'
  rcases hd' with ((h | h) | h) | h
  · exact mem_rebit h
  · exact mem_motivesDataGoP h
  · exact mem_fixMinorsDataMP h
  · exact mem_rebit h

/-! ## The fixpoint route's spellings as the `k = 1` instances -/

omit [SetTheory V] in
theorem recPrefixBvarsMK_one (nP n nF m : Nat) :
    recPrefixBvarsMK nP 1 n nF m = recPrefixBvarsM nP n nF m := by
  unfold recPrefixBvarsMK recPrefixBvarsM
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    show nF + n + 1 - 1 - 0 + m = nF + n + m from by omega]

omit [SetTheory V] in
theorem ihAppAVK_one (R : AnnotTerm) (nP n nF i : Nat) (tl : List (Nat × Nat × AnnotTerm))
    (Eis : List AnnotTerm) : ihAppAVK R nP 1 n nF i tl Eis = ihAppAV R nP n nF i tl Eis := by
  unfold ihAppAVK ihAppAV
  rw [recPrefixBvarsMK_one]

omit [SetTheory V] in
theorem mutualRuleCoreAV_congr_Rof {b : Nat} {Rof Rof' : Nat → AnnotTerm} {tgts : Nat → Nat}
    {nP k n nF j : Nat} {recIdx : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (h : ∀ i ∈ recIdx, Rof (tgts i) = Rof' (tgts i)) :
    mutualRuleCoreAV b Rof tgts nP k n nF j recIdx tls Eiss
      = mutualRuleCoreAV b Rof' tgts nP k n nF j recIdx tls Eiss := by
  unfold mutualRuleCoreAV
  congr 2
  exact List.map_congr_left fun i hi => by rw [h i hi]

omit [SetTheory V] in
theorem mutualRuleCoreAV_one (b : Nat) (R : AnnotTerm) (nP nF n j : Nat) (recIdx : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eiss : List (List AnnotTerm)) :
    mutualRuleCoreAV b (fun _ => R) (fun _ => 0) nP 1 n nF j recIdx tls Eiss
      = fixRuleCoreAV b R nP nF n j recIdx tls Eiss := by
  unfold mutualRuleCoreAV fixRuleCoreAV
  simp only [ihAppAVK_one]

omit [SetTheory V] in
theorem mutualConcAV_one (n nIdx : Nat) : mutualConcAV 1 n nIdx 0 = recConcAV n nIdx := by
  unfold mutualConcAV recConcAV motAppAV
  rw [show 1 + nIdx + n + 1 - 1 - 0 = 1 + nIdx + n from by omega]

theorem mutualRecDataAV_one {m : EnvModel V env} {ψ : Name → Nat} (L : AnnotTerm) (nP nIdx : Nat)
    (ℓ : Level) (pps ips : List (Nat × Nat × AnnotTerm)) (cds : List CtorDatumR) :
    mutualRecDataAV m ψ [L] nP [nIdx] ℓ pps [ips] cds (fun _ => 0) (fun _ _ => 0) 0
      = fixRecDataAVL m ψ L nP nIdx ℓ pps ips cds := by
  unfold mutualRecDataAV fixRecDataAVL fixMinorsData majorAVAtK majorAVAtL
  simp only [List.length_singleton, List.getD_cons_zero, motivesDataGo, AnnotTerm.liftN_zero,
    Nat.add_comm 1 cds.length]

theorem mutualRuleDataAV_one {m : EnvModel V env} {ψ : Name → Nat} (T : Name) (nP nIdx : Nat)
    (ℓ : Level) (pps ips : List (Nat × Nat × AnnotTerm)) (cds : List CtorDatumR)
    (ds : List (Nat × Nat × AnnotTerm)) :
    mutualRuleDataAV m ψ [m.acval T ψ] nP [nIdx] ℓ pps [ips] cds (fun _ => 0) (fun _ _ => 0) ds
      = fixRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds := by
  unfold mutualRuleDataAV fixRuleDataAV fixMinorsData motiveAVI
  simp only [List.length_singleton, List.getD_cons_zero, motivesDataGo, AnnotTerm.liftN_zero,
    Nat.add_comm 1 cds.length]

/-! ## Insensitivity of the pinned spellings to the valuation -/

theorem minorAVAtRMP_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {mot : Nat} {moti : Nat → Nat} {C : Name} {pinsC : List AnnotTerm}
    {nP nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm}
    {recIdx : List Nat} {Eiss : List (List AnnotTerm)} {tls : List (List (Nat × Nat × AnnotTerm))}
    (hC : m₁.acval C ψ = m₂.acval C ψ) :
    minorAVAtRMP mot moti m₁ C pinsC ψ nP nF b o ds Es recIdx tls Eiss
      = minorAVAtRMP mot moti m₂ C pinsC ψ nP nF b o ds Es recIdx tls Eiss := by
  unfold minorAVAtRMP famAppAV
  rw [hC]

theorem fixMinorsDataMP_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {nP b : Nat} :
    ∀ (mots : Nat → Nat) (tgts : Nat → Nat → Nat) (pinsOf : Nat → List AnnotTerm)
      (cds : List CtorDatumR) (o : Nat),
      (∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) →
      fixMinorsDataMP mots tgts pinsOf m₁ ψ nP b cds o
        = fixMinorsDataMP mots tgts pinsOf m₂ ψ nP b cds o
  | _, _, _, [], _, _ => rfl
  | mots, tgts, pinsOf, (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, h => by
    simp only [fixMinorsDataMP]
    rw [minorAVAtRMP_congr (h _ List.mem_cons_self),
      fixMinorsDataMP_congr (fun J => mots (J + 1)) (fun J => tgts (J + 1))
        (fun J => pinsOf (J + 1)) cs (o + 1) fun cd hcd => h cd (List.mem_cons_of_mem _ hcd)]

theorem recDataAVP_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {Ls : List AnnotTerm} {pinsOf : Nat → List AnnotTerm} {nP : Nat}
    {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {mm : Nat}
    (hC : ∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    recDataAVP m₁ ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts mm
      = recDataAVP m₂ ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts mm := by
  unfold recDataAVP
  rw [fixMinorsDataMP_congr _ _ _ cds _ hC]

theorem ruleDataAVP_congr {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {ψ : Name → Nat} {Ls : List AnnotTerm} {pinsOf : Nat → List AnnotTerm} {nP : Nat}
    {nIdxs : List Nat} {ℓ : Level} {pps : List (Nat × Nat × AnnotTerm)}
    {ipss : List (List (Nat × Nat × AnnotTerm))} {cds : List CtorDatumR} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)}
    (hC : ∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    ruleDataAVP m₁ ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts ds
      = ruleDataAVP m₂ ψ Ls pinsOf nP nIdxs ℓ pps ipss cds mots tgts ds := by
  unfold ruleDataAVP
  rw [fixMinorsDataMP_congr _ _ _ cds _ hC]

end ConLeche.Model
