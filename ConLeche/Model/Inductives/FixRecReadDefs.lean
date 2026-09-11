module

import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.SumRecRead
public import ConLeche.Model.Inductives.FixData
public import ConLeche.Semantics.Tower.FixRecI
public section

/-!
# The generated recursive recursor's readings: the targets (task #188)

The binder data the generated recursor type `structRecTyR`
(`ConLeche/Kernel/Inductives/NativeParts.lean`) reads to, and the rules' λ-data
and cores — the indexed sum route's (`SumRecReadP.lean`) with the
**inductive-hypothesis binders** in the minors (`ihPisAV`: for each
recursive field `i`, at ih position `l`, `motive e⃗_i f_i` with the
field's index readings moved to the binder's frame, `ihIdxAt`) and
the ih applications in the rules (`ihAppAV`: the recursor's leaf at
the block's variables, the field's index readings and the field).  The
reading theorems (`FixRecReadP.lean`) prove the kernel's generators
read to exactly these.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

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

/-- The ih binders' Π-tower at the fixpoint route's single motive. -/
@[expose] def ihPisAV (nF o b : Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eiss : List (List AnnotTerm)) (is : List Nat) (l : Nat) (body : AnnotTerm) : AnnotTerm :=
  ihPisAVM (fun _ => 0) nF o b tls Eiss is l body

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

/-- The recursor's leading spine `p⃗ motive m⃗` read under the `nF`
fields of a rule (`structRecPrefixAt nP n nF 0`'s reading: the
parameters sit `nF + n + 1` binders above the fields). -/
@[expose] def recPrefixBvars (nP n nF : Nat) : List AnnotTerm :=
  paramBvarsAt nP (nP + nF + n + 1) ++ [.bvar (nF + n)] ++
    (List.range n).map fun l => AnnotTerm.bvar (nF + n - 1 - l)

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

/-! ## The per-constructor reading premise -/

/-- What the readings need of one constructor `(C, nF, cty, recIdx)`
and its datum `(C, nF, ds, Es, recIdx, Eiss)`: the sum route's
(`CtorRead`) and, per recursive position `i`, the reading of the
field's index expressions at the field's own depth (`Eiss.getD i`, as
many as the indices) with the field's entry the family at the
parameter variables and those readings. -/
structure CtorReadR {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (c : Name × Nat × Expr × List Nat) (cd : CtorDatumR) :
    Prop where
  name : cd.1 = c.1
  nF : cd.2.1 = c.2.1
  find : ∃ ci : ConstantInfo, env.find? c.1 = some ci ∧ ci.toConstantVal.levelParams = lps
  hasFvar : c.2.2.1.hasFvar = false
  bounded : c.2.2.1.looseBVarsBounded 0 = true
  resid : ∃ (cbs : List (Expr × BinderMeta)) (es : List Expr),
    c.2.2.1.stripPis (nP + c.2.1)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (ConLeche.structPsAt c.2.1 nP ++ es)) ∧
    es.length = nIdx
  read : denoteMeta m.acval env ψ 0 c.2.2.1
    = some (mkPisAV cd.2.2.1 (AnnotTerm.mkAppN (m.acval T ψ) (paramBvars nP c.2.1 ++ cd.2.2.2.1)))
  len : cd.2.2.1.length = nP + c.2.1
  lenE : cd.2.2.2.1.length = nIdx
  recIdx : cd.2.2.2.2.1 = c.2.2.2
  recIdxBnd : ∀ i ∈ c.2.2.2, i < c.2.1
  /-- the recursive positions are strictly increasing (`recIdxOf`) -/
  recIdxSorted : c.2.2.2.Pairwise (· < ·)
  eissLen : cd.2.2.2.2.2.1.length = c.2.1
  eisLen : ∀ i ∈ c.2.2.2, (cd.2.2.2.2.2.1.getD i []).length = nIdx
  tlsLen : cd.2.2.2.2.2.2.length = c.2.1
  /-- a recursive field's telescope has as many binders as the raw
  type's (`structFieldTeleOf`; none at a finitary field) -/
  teleLen : ∀ i ∈ c.2.2.2,
    (ConLeche.structFieldTeleOf c.2.2.1 nP c.2.1 i).length = (cd.2.2.2.2.2.2.getD i []).length
  /-- a recursive field's domain, at the field's own depth `nP + i`
  with the parameters and the earlier fields as variables (an opening
  of the constructor's telescope), reads to its entry -/
  fieldRead : ∀ i ∈ c.2.2.2, ∀ (fvs : List Expr) (o : Expr),
    openPisAtFvars (nP + c.2.1) c.2.2.1 0 = some (fvs, o) →
    ∀ x, fvs[nP + i]? = some x →
      denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some (cd.2.2.1.getD (nP + i) default).2.2
  /-- a recursive field's domain, under its own telescope, is an
  application of `nP + nIdx` arguments — the parameters and the index
  expressions `structFieldIdxOf` (task #202: without the arity the
  field's readings cannot be separated from the family's leaf, which
  may itself be an application) -/
  fieldArity : ∀ i ∈ c.2.2.2, ∀ (cbs : List (Expr × BinderMeta)) (body : Expr),
    c.2.2.1.stripPis (nP + c.2.1) = some (cbs, body) →
    (((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs).length = nP + nIdx
  /-- a recursive field's entry: the Π-tower over its telescope of the
  family at the parameter variables and the field's index readings
  (task #202; a finitary field: the family at the readings) -/
  recEntry : ∀ i ∈ c.2.2.2,
    (cd.2.2.1.getD (nP + i) default).2.2
      = mkPisAV (cd.2.2.2.2.2.2.getD i [])
          (AnnotTerm.mkAppN (m.acval T ψ)
            (paramBvarsAt nP (nP + i + (cd.2.2.2.2.2.2.getD i []).length) ++
              cd.2.2.2.2.2.1.getD i []))

/-- The constructors' reading premises, positionally. -/
inductive CtorReadsR {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) :
    List (Name × Nat × Expr × List Nat) → List CtorDatumR → Prop
  | nil : CtorReadsR m ψ T lps nP nIdx [] []
  | cons {c cd cs cds} : CtorReadR m ψ T lps nP nIdx c cd → CtorReadsR m ψ T lps nP nIdx cs cds →
      CtorReadsR m ψ T lps nP nIdx (c :: cs) (cd :: cds)

theorem CtorReadsR.length_eq {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      CtorReadsR m ψ T lps nP nIdx ctors cds → cds.length = ctors.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CtorReadsR.length_eq h]

/-! ## The telescope toolkit (task #202)

The kernel spells a reflexive field's own telescope with
`Expr.piBinders` (`structFieldTeleOf`); the readings need its
elementary laws — the round trip, its stability under the frame's
instantiation (whose arguments are free variables), and the openers'
count. -/

@[simp] theorem Expr.piBinders_forallE (ty b : Expr) (mt : BinderMeta) :
    (Expr.forallE ty b mt).piBinders = ((ty, mt) :: (b.piBinders).1, (b.piBinders).2) := rfl

/-- **A Π-tower is its own binders over its own body.** -/
theorem Expr.mkPisOf_piBinders : ∀ e : Expr, Expr.mkPisOf (e.piBinders).1 (e.piBinders).2 = e
  | .forallE ty b mt => by
    rw [Expr.piBinders_forallE]
    show Expr.forallE ty (Expr.mkPisOf (b.piBinders).1 (b.piBinders).2) mt = _
    rw [Expr.mkPisOf_piBinders b]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- Substituting a free variable moves a Π-tower's body but not its
binder count. -/
theorem Expr.piBinders_instantiate1_fvar {i : Nat} {tya : Expr} (e : Expr) :
    ∀ k : Nat,
      ((e.instantiate1 (.fvar i tya) k).piBinders).1.length = (e.piBinders).1.length ∧
      ((e.instantiate1 (.fvar i tya) k).piBinders).2
        = ((e.piBinders).2).instantiate1 (.fvar i tya) (k + (e.piBinders).1.length) := by
  induction e with
  | forallE ty b mt _ ihb =>
    intro k
    obtain ⟨hl, hb⟩ := ihb (k + 1)
    show (((Expr.forallE (ty.instantiate1 _ k) (b.instantiate1 _ (k + 1)) mt)).piBinders).1.length
        = _ ∧ _
    rw [Expr.piBinders_forallE, Expr.piBinders_forallE]
    refine ⟨by simp only [List.length_cons, hl], ?_⟩
    show ((b.instantiate1 (.fvar i tya) (k + 1)).piBinders).2 = _
    rw [hb]
    congr 1
    simp only [List.length_cons]
    omega
  | bvar j =>
    intro k
    show (((Expr.bvar j).instantiate1 (.fvar i tya) k).piBinders).1.length = ([] : List _).length ∧
      (((Expr.bvar j).instantiate1 (.fvar i tya) k).piBinders).2
        = (Expr.bvar j).instantiate1 (.fvar i tya) (k + ([] : List _).length)
    simp only [List.length_nil, Nat.add_zero, Expr.instantiate1]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  | _ => intro k; exact ⟨rfl, rfl⟩

/-- The frame's instantiation moves a Π-tower's body but not its
binder count (the frame's entries are free variables). -/
theorem Expr.piBinders_instSeq :
    ∀ (L : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ L, ∃ (i : Nat) (ty : Expr), a = Expr.fvar i ty) →
      L.length ≤ t + 1 →
      ((Expr.instSeq L t e).piBinders).1.length = (e.piBinders).1.length ∧
      ((Expr.instSeq L t e).piBinders).2
        = Expr.instSeq L (t + (e.piBinders).1.length) ((e.piBinders).2)
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | a :: L, t, e, hfv, hlen => by
    obtain ⟨i, tya, rfl⟩ := hfv a List.mem_cons_self
    obtain ⟨hl1, hb1⟩ := Expr.piBinders_instantiate1_fvar (i := i) (tya := tya) e t
    have hfv' : ∀ x ∈ L, ∃ (i : Nat) (ty : Expr), x = Expr.fvar i ty :=
      fun x hx => hfv x (List.mem_cons_of_mem _ hx)
    have hlen' : L.length ≤ t - 1 + 1 := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hl2, hb2⟩ := Expr.piBinders_instSeq L (t - 1) (e.instantiate1 (.fvar i tya) t)
      hfv' hlen'
    have hstep : Expr.instSeq (Expr.fvar i tya :: L) t e
        = Expr.instSeq L (t - 1) (e.instantiate1 (Expr.fvar i tya) t) := rfl
    have hstep2 : Expr.instSeq (Expr.fvar i tya :: L) (t + (e.piBinders).1.length)
          ((e.piBinders).2)
        = Expr.instSeq L (t + (e.piBinders).1.length - 1)
            (((e.piBinders).2).instantiate1 (Expr.fvar i tya)
              (t + (e.piBinders).1.length)) := rfl
    refine ⟨by rw [hstep, hl2, hl1], ?_⟩
    rw [hstep, hstep2, hb2, hb1, hl1]
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · have : L = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst this
      rfl
    · rw [show t - 1 + (e.piBinders).1.length = t + (e.piBinders).1.length - 1 from by omega]

/-- A Π-tower strips exactly its own binders. -/
theorem Expr.stripPis_piBinders : ∀ e : Expr, e.stripPis (e.piBinders).1.length = some e.piBinders
  | .forallE ty b mt => by
    rw [Expr.piBinders_forallE]
    simp only [List.length_cons, Expr.stripPis]
    rw [Expr.stripPis_piBinders b]
    rfl
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- A binder-free Π-tower is its own body. -/
theorem Expr.piBinders_nil_body : ∀ {e : Expr}, (e.piBinders).1 = [] → (e.piBinders).2 = e
  | .forallE _ _ _, h => by rw [Expr.piBinders_forallE] at h; exact nomatch h
  | .bvar _, _ | .fvar .., _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _
  | .letE .., _ | .lit _, _ | .proj .., _ => rfl

/-- An application spine has no leading `∀`. -/
theorem Expr.piBinders_nil_of_getAppFn_const {e : Expr} {c : Name} {us : List Level}
    (h : e.getAppFn = .const c us) : (e.piBinders).1 = [] := by
  match e with
  | .forallE _ _ _ => exact nomatch h
  | .bvar _ | .fvar .. | .sort _ | .const .. | .app .. | .lam .. | .letE .. | .lit _
  | .proj .. => rfl

/-- **An opened variable's type is its binder's domain instantiated at
the earlier variables.** -/
theorem openPisAtFvars_fvarTypeD :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
      {bs : List (Expr × BinderMeta)} {body : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      e.stripPis n = some (bs, body) →
      ∀ (i : Nat) (b : Expr × BinderMeta) (x : Expr),
        bs[i]? = some b → fvs[i]? = some x →
        x.fvarTypeD = Expr.instSeq (fvs.take i) (i - 1) b.1
  | 0, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    rw [← hst.1] at hb
    exact nomatch hb
  | n + 1, e, d, fvs, o, bs, body, hop, hst, i, b, x, hb, hx => by
    match e, hop, hst with
    | .forallE dom bd mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hx
          subst hb; subst hx
          rfl
        | succ i =>
          simp only [List.getElem?_cons_succ] at hb hx
          obtain ⟨bs'', hst'', hdoms⟩ :=
            ConLeche.stripPis_instantiate1_full (v := .fvar d dom) n 0 hst'
          have hb'' := hdoms i b hb
          rw [Nat.zero_add] at hb''
          have ih := openPisAtFvars_fvarTypeD n h₁ hst'' i _ x hb'' hx
          rw [ih, List.take_succ_cons]
          rfl
      · exact nomatch hop

theorem CtorReadsR.getElem? {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
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

end ConLeche.Model
