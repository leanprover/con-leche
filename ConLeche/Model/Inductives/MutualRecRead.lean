module

public import ConLeche.Model.Inductives.FixRecRead
public section

/-!
# The mutual block's generated recursor type, read (task #278)

`ConLeche/Model/Inductives/FixRecRead.lean` with `k` motives: member
`mm`'s generated recursor type (`ConLeche.mutualRecTy`,
`ConLeche/Kernel/Inductives/MutualParts.lean`) reads to the Π-tower over
`mutualRecDataAV` — the parameters, the `k` motives (motive `m'`
sitting `m'` binders below them, so its reading is the fixpoint
route's lifted), the `n` minors (each over its own member's motive,
its inductive hypotheses over their fields' target members), member
`mm`'s index telescope and its major — with the core
`mutualConcAV`, `motive_mm ı⃗ t`.

The minors are the `M`-spellings of `FixRecReadDefs.lean`
(`fixMinorsDataM`, read by `denoteMeta_minorAtRM`); what is new here is
the motive block (`motivesDataGo`, read by `denoteMeta_mutualMotiveTy`
— the fixpoint route's motive reading `i` binders below the
parameters) and the assembly.
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

/-! ## The binder data -/

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

/-! ## The motive entry, lifted -/

omit [SetTheory V] in
theorem liftDoms_rebit (n b : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat),
      liftDoms n k (rebit b ds) = rebit b (liftDoms n k ds)
  | [], _ => rfl
  | d :: ds, k => by
    simp only [rebit_cons, liftDoms, liftDoms_rebit n b ds (k + 1)]

omit [SetTheory V] in
theorem map_paramBvarsAt_liftN (nP D n k : Nat) (hD : nP ≤ D) (h : k ≤ D - nP) :
    (paramBvarsAt nP D).map (fun a => AnnotTerm.liftN n a k) = paramBvarsAt nP (D + n) := by
  unfold paramBvarsAt
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' : t < nP := List.mem_range.mp ht
  simp only [Function.comp_def, AnnotTerm.liftN_bvar]
  rw [if_neg (by omega)]
  congr 1
  omega

omit [SetTheory V] in
theorem map_fieldBvars_liftN (nIdx n : Nat) :
    (fieldBvars nIdx).map (fun a => AnnotTerm.liftN n a nIdx) = fieldBvars nIdx := by
  unfold fieldBvars
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' : t < nIdx := List.mem_range.mp ht
  simp only [Function.comp_def, AnnotTerm.liftN_bvar]
  rw [if_pos (by omega)]

/-- **Motive `i`'s entry**: the fixpoint route's motive reading lifted
`i` under is the motive at the parameters `i` binders further up. -/
theorem motiveAVIL_liftN {L : AnnotTerm} (hL : ∀ n k, AnnotTerm.liftN n L k = L)
    (ψ : Name → Nat) (nP nIdx : Nat) (ℓ : Level) (ips : List (Nat × Nat × AnnotTerm))
    (hlenI : ips.length = nIdx) (i : Nat) :
    (motiveAVIL L ψ nP nIdx ℓ ips).liftN i 0
      = mkPisAV (rebit (pwBit ψ PropWhen.never) (liftDoms i 0 ips))
          (.pi 0 (pwBit ψ PropWhen.never)
            (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + i + nIdx) ++ fieldBvars nIdx))
            (.sort (ℓ.eval ψ))) := by
  unfold motiveAVIL
  rw [liftN_mkPisAV, liftDoms_rebit, rebit_length, hlenI, Nat.zero_add,
    AnnotTerm.liftN_pi, AnnotTerm.liftN_sort, liftN_mkAppN, hL, List.map_append,
    map_paramBvarsAt_liftN nP (nP + nIdx) i nIdx (by omega) (by omega), map_fieldBvars_liftN,
    show nP + nIdx + i = nP + i + nIdx from by omega]

/-! ## The generators, unfolded -/

theorem mutualMotivesPis_nil {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} {i : Nat}
    {body mots : Expr} (h : ConLeche.mutualMotivesPis lps nP ℓ pw [] i body = some mots) :
    mots = body := by
  simp only [ConLeche.mutualMotivesPis, Option.some.injEq] at h
  exact h.symm

theorem mutualMotivesPis_cons {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {f : ConLeche.MutualFormer} {fs : List ConLeche.MutualFormer} {i : Nat} {body mots : Expr}
    (h : ConLeche.mutualMotivesPis lps nP ℓ pw (f :: fs) i body = some mots) :
    ∃ mty rest, ConLeche.mutualMotiveTy lps nP ℓ i f = some mty ∧
      ConLeche.mutualMotivesPis lps nP ℓ pw fs (i + 1) body = some rest ∧
      mots = .forallE mty rest ⟨pw⟩ := by
  unfold ConLeche.mutualMotivesPis at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmots⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmots.symm⟩

theorem mutualMinorsPis_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : ConLeche.mutualMinorsPis lps nP pw [] o body = some mins) :
    mins = body := by
  simp only [ConLeche.mutualMinorsPis, Option.some.injEq] at h
  exact h.symm

theorem mutualMinorsPis_cons {lps : List Name} {nP : Nat} {pw : PropWhen}
    {c : ConLeche.MutualCtor4} {cs : List ConLeche.MutualCtor4} {o : Nat} {body mins : Expr}
    (h : ConLeche.mutualMinorsPis lps nP pw (c :: cs) o body = some mins) :
    ∃ mty rest, ConLeche.mutualMinorTy lps nP o pw c = some mty ∧
      ConLeche.mutualMinorsPis lps nP pw cs (o + 1) body = some rest ∧
      mins = .forallE mty rest ⟨pw⟩ := by
  unfold ConLeche.mutualMinorsPis at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmins⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmins.symm⟩

/-- `mutualRecTy`, unfolded to its five steps (`structRecTyR_unfold`'s
`k`-motive twin). -/
theorem mutualRecTy_unfold {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List ConLeche.MutualFormer} {ctors : List ConLeche.MutualCtor4} {recTy : Expr}
    (h : ConLeche.mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f f₀ : ConLeche.MutualFormer) (tbs : List (Expr × BinderMeta))
      (itele major minors motives : Expr),
      formers[mm]? = some f ∧ formers[0]? = some f₀ ∧
      f.tty.stripPis nP = some (tbs, itele) ∧
      Expr.replacePisPw (Level.zeronessOf (ConLeche.structElimLevel elim large)) f.nIdx
        (itele.liftLooseBVars (formers.length + ctors.length) 0)
        (.forallE (ConLeche.structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0)
          (Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
            (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0]))
          ⟨Level.zeronessOf (ConLeche.structElimLevel elim large)⟩) = some major ∧
      ConLeche.mutualMinorsPis lps nP (Level.zeronessOf (ConLeche.structElimLevel elim large))
        ctors formers.length major = some minors ∧
      ConLeche.mutualMotivesPis lps nP (ConLeche.structElimLevel elim large)
        (Level.zeronessOf (ConLeche.structElimLevel elim large)) formers 0 minors = some motives ∧
      Expr.replacePisPw (Level.zeronessOf (ConLeche.structElimLevel elim large)) nP f₀.tty motives
        = some recTy := by
  unfold ConLeche.mutualRecTy at h
  split at h
  · next f f₀ hf hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    exact ⟨f, f₀, q.1, q.2, major, minors, motives, hf, hf₀, hq, hmaj, hmin, hmot, hr⟩
  · exact nomatch h

/-! ## The motive premise, read -/

/-- **What the readings need of one member's former**: its constant,
its type's shape and its reading — the fixpoint route's premises of
`denoteMeta_structRecTyR`, per member, with the member's leaf `L`,
index count and index data named. -/
structure FormerReadM {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (lps : List Name)
    (nP : Nat) (f : ConLeche.MutualFormer) (L : AnnotTerm) (nIdx : Nat)
    (pps ips : List (Nat × Nat × AnnotTerm)) : Prop where
  find : ∃ ci : ConstantInfo, env.find? f.name = some ci ∧ ci.toConstantVal.levelParams = lps
  leaf : L = m.acval f.name ψ
  idxCount : nIdx = f.nIdx
  hasFvar : f.tty.hasFvar = false
  bounded : f.tty.looseBVarsBounded 0 = true
  stripP : ∃ (tbs : List (Expr × BinderMeta)) (itele : Expr),
    f.tty.stripPis nP = some (tbs, itele)
  strip : (f.tty.stripPis (nP + f.nIdx)).isSome = true
  read : ∃ (ppsAll : List (Nat × Nat × AnnotTerm)) (w : Nat),
    denoteMeta m.acval env ψ 0 f.tty = some (mkPisAV ppsAll (.sort w)) ∧
    ppsAll.length = nP + f.nIdx ∧ pps = ppsAll.take nP ∧ ips = ppsAll.drop nP

/-- The members' reading premises, positionally. -/
@[expose] def FormerReadsM {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (lps : List Name)
    (nP : Nat) (Lof : Nat → AnnotTerm) (nIdxOf : Nat → Nat)
    (ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm))
    (formers : List ConLeche.MutualFormer) : Prop :=
  ∀ t, t < formers.length →
    FormerReadM m ψ lps nP (formers.getD t default) (Lof t) (nIdxOf t) (ppsOf t) (ipsOf t)

theorem FormerReadsM.head {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat}
    {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
    {ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm)}
    {f : ConLeche.MutualFormer} {fs : List ConLeche.MutualFormer}
    (h : FormerReadsM m ψ lps nP Lof nIdxOf ppsOf ipsOf (f :: fs)) :
    FormerReadM m ψ lps nP f (Lof 0) (nIdxOf 0) (ppsOf 0) (ipsOf 0) := h 0 (by simp)

theorem FormerReadsM.tail {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat}
    {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
    {ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm)}
    {f : ConLeche.MutualFormer} {fs : List ConLeche.MutualFormer}
    (h : FormerReadsM m ψ lps nP Lof nIdxOf ppsOf ipsOf (f :: fs)) :
    FormerReadsM m ψ lps nP (fun t => Lof (t + 1)) (fun t => nIdxOf (t + 1))
      (fun t => ppsOf (t + 1)) (fun t => ipsOf (t + 1)) fs :=
  fun t ht => h (t + 1) (by simp; omega)

set_option maxHeartbeats 1600000 in
/-- **Motive `i`'s premise**, instantiated at the parameters and the
`i` earlier motives, reads to the fixpoint route's motive reading
lifted `i` under. -/
theorem denoteMeta_mutualMotiveTy {m : EnvModel V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx i : Nat} {ℓ : Level} {tty itele motiveTy : Expr} {tbs : List (Expr × BinderMeta)}
    (hsT : tty.stripPis nP = some (tbs, itele))
    (hmot : ConLeche.mutualMotiveTy lps nP ℓ i ⟨T, nIdx, tty⟩ = some motiveTy)
    (hTf : tty.hasFvar = false) (hTb : tty.looseBVarsBounded 0 = true)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {ppsAll : List (Nat × Nat × AnnotTerm)} {w : Nat}
    (hTread : denoteMeta m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (q : Nat) (a : Expr), tfvs[q]? = some a → Expr.WScoped (0 + q + 1) a)
    {extras : List Expr} (hlenE : extras.length = i)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) :
    denoteMeta m.acval env ψ (nP + i) (Expr.instSeq (tfvs ++ extras) (nP + i - 1) motiveTy)
      = some ((motiveAVI m T ψ nP nIdx ℓ (ppsAll.drop nP)).liftN i 0) := by
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxE q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE a h
  have hlenTE : (tfvs ++ extras).length = nP + i := by
    rw [List.length_append, hlenT, hlenE]
  -- the generator, instantiated at the frame
  have hmotP : Expr.replacePisPw .never nIdx (itele.liftLooseBVars i 0)
      (.forallE (ConLeche.structFamI T lps nP nIdx i 0) (.sort ℓ) ⟨.never⟩) = some motiveTy := by
    unfold ConLeche.mutualMotiveTy at hmot
    simp only [Option.bind_eq_some_iff] at hmot
    obtain ⟨q, hq, h⟩ := hmot
    rw [hsT] at hq
    obtain rfl := (Option.some.inj hq).symm
    exact h
  clear hmot
  have htb0 : itele.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsT hTb
    rwa [Nat.zero_add] at this
  have hmot' := ConLeche.replacePisPw_instSeq (tfvs ++ extras) (nP + i - 1)
    (by rw [hlenTE]; omega) hmotP
  have hres := ConLeche.instSeq_minorTele tfvs extras hlenT hclT htb0
  rw [hlenE] at hres
  rw [hres] at hmot'
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx (nP + i) htstrip
  have htreadN := ctorResidual_read_lift htread htw hlenP i
  rw [AnnotTerm.liftN_sort] at htreadN
  have hstI : stripPisAV nIdx (mkPisAV (liftDoms i 0 (ppsAll.drop nP)) (.sort w))
      = some (liftDoms i 0 (ppsAll.drop nP), .sort w) := by
    have := stripPisAV_mkPisAV (liftDoms i 0 (ppsAll.drop nP)) (AnnotTerm.sort w)
    rwa [liftDoms_length, List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmotR := denoteMeta_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmot' hopI
    htreadN hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the body, instantiated
  have hnilE : (tfvs ++ extras) = [] ∨ nP + i - 1 + nIdx = 0 + i + nIdx + nP - 1 := by
    rcases Nat.eq_zero_or_pos (nP + i) with h0 | hpos
    · left
      exact List.eq_nil_of_length_eq_zero (by rw [hlenTE, h0])
    · right; omega
  have hdom1 : Expr.instSeq (tfvs ++ extras) (nP + i - 1 + nIdx)
      (ConLeche.structFamI T lps nP nIdx i 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold ConLeche.structFamI
    rw [instSeq_idx_congr (sp := tfvs ++ extras) (t := nP + i - 1 + nIdx)
        (t' := 0 + i + nIdx + nP - 1) _ hnilE,
      Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      ConLeche.map_instSeq_structPsAt (tfvs ++ extras) (0 + i + nIdx) nP hclTE
        (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      structPsAt_zero, ConLeche.map_instSeq_fieldBvars_above (tfvs ++ extras) _ nIdx
        (by rw [hlenTE]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      ConLeche.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq (tfvs ++ extras) (nP + i - 1 + nIdx)
      (.forallE (ConLeche.structFamI T lps nP nIdx i 0) (.sort ℓ) ⟨.never⟩))
      = .forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs)) (.sort ℓ) ⟨.never⟩ := by
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + i - 1 + nIdx) _ _ _ (by rw [hlenTE]; omega),
      hdom1, Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ (by omega), hdom2,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl]
  rw [hbody] at hmotR
  -- the body's reading
  have hspine := denoteMeta_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := i) hlenT hlenI hidxT
    hidxI
  have hpi : denoteMeta m.acval env ψ (nP + i + nIdx)
      (.forallE (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs)) (.sort ℓ) ⟨.never⟩)
      = some (.pi 0 (pwBit ψ PropWhen.never)
          (AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + i + nIdx) ++ fieldBvars nIdx))
          (.sort (ℓ.eval ψ))) := by
    rw [denoteMeta_forallE, hspine,
      show (Expr.sort ℓ).instantiate1 (Expr.fvar (nP + i + nIdx)
          (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))) 0 = Expr.sort ℓ from rfl,
      denoteMeta_sort]
    rfl
  rw [hpi, Option.map_some] at hmotR
  rw [hmotR, motiveAVI_eq_L,
    motiveAVIL_liftN (liftN_eq_self_of_one (m.acval_closed T ψ)) ψ nP nIdx ℓ (ppsAll.drop nP)
      (by rw [List.length_drop, hlenP]; omega) i]

set_option maxHeartbeats 1600000 in
/-- **The motives' `∀`-telescope** reads to the Π-tower over
`motivesDataGo`, the body read under all `k` of them. -/
theorem denoteMeta_mutualMotivesPis {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {ℓ : Level} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (q : Nat) (a : Expr), tfvs[q]? = some a → Expr.WScoped (0 + q + 1) a) :
    ∀ {formers : List ConLeche.MutualFormer} {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
      {ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm)} {body mots : Expr} {extras : List Expr},
      FormerReadsM m ψ lps nP Lof nIdxOf ppsOf ipsOf formers →
      ConLeche.mutualMotivesPis lps nP ℓ pw formers extras.length body = some mots →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = formers.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mots)
          = (denoteMeta m.acval env ψ (nP + extras.length + formers.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + formers.length - 1) body)).map
              (mkPisAV (motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ (pwBit ψ pw) formers.length
                extras.length))
  | [], Lof, nIdxOf, ppsOf, ipsOf, body, mots, extras, _, hmot, hidxE => by
    rw [mutualMotivesPis_nil hmot]
    refine ⟨extras, by simp, hidxE, ?_⟩
    simp only [List.length_nil, Nat.add_zero, motivesDataGo, mkPisAV]
    cases denoteMeta m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | f :: fs, Lof, nIdxOf, ppsOf, ipsOf, body, mots, extras, hfr, hmot, hidxE => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMotivesPis_cons hmot
    obtain ⟨ci, hfT, hlpsT⟩ := hfr.head.find
    obtain ⟨tbs, itele, hsT⟩ := hfr.head.stripP
    obtain ⟨ppsAll, w, hTread, hlenP, -, hips⟩ := hfr.head.read
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    have hnil : (tfvs ++ extras) = [] ∨ nP + extras.length - 1 + 1 = nP + extras.length := by
      rcases Nat.eq_zero_or_pos (nP + extras.length) with h0 | hpos
      · left; exact List.eq_nil_of_length_eq_zero (by rw [hlenTE, h0])
      · right; omega
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _
        (by rw [hlenTE]; omega),
      instSeq_idx_congr (sp := tfvs ++ extras) (t := nP + extras.length - 1 + 1)
        (t' := nP + extras.length) rest hnil,
      denoteMeta_forallE,
      denoteMeta_mutualMotiveTy hfT hlpsT hsT hmty hfr.head.hasFvar hfr.head.bounded
        hfr.head.strip hTread hlenP hlenT hidxT hspW rfl hidxE]
    generalize hmk : Expr.fvar (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + k) ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : ConLeche.mutualMotivesPis lps nP ℓ pw fs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_mutualMotivesPis hlenT hidxT hspW hfr.tail hrest' hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + fs.length
        = nP + extras.length + (fs.length + 1) := by omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith,
      motivesDataGo, mkPisAV, hfr.head.leaf, hfr.head.idxCount, hips, motiveAVI_eq_L]
    cases denoteMeta m.acval env ψ (nP + extras.length + (fs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (fs.length + 1) - 1) body) <;> rfl

/-! ## The minor premises, read -/

/-- **The per-constructor reading premise with PER-FIELD TARGETS**:
`CtorReadR` (`FixRecReadDefs.lean`) at a block whose recursive fields
need not target the constructor's own member.  The constructor's own
residual is still its own member `T`'s (`resid`, `read`, `lenE`);
what moves to the field's target is the field's entry (`recEntry` —
the TARGET's leaf `Tt i`), the number of index readings it carries
(`eisLen`) and its domain's argument count (`fieldArity`), each at the
target's index count `nIt i`.  The fixpoint route is the constant
instance `Tt := fun _ => T`, `nIt := fun _ => nIdx` (`CtorReadR.toT`). -/
structure CtorReadRT {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (T : Name)
    (Tt : Nat → Name) (lps : List Name) (nP nIdx : Nat) (nIt : Nat → Nat)
    (c : Name × Nat × Expr × List Nat) (cd : CtorDatumR) : Prop where
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
  /-- a recursive field carries the TARGET member's index readings -/
  eisLen : ∀ i ∈ c.2.2.2, (cd.2.2.2.2.2.1.getD i []).length = nIt i
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
  application of `nP + nIt i` arguments — the parameters and the TARGET
  member's index expressions -/
  fieldArity : ∀ i ∈ c.2.2.2, ∀ (cbs : List (Expr × BinderMeta)) (body : Expr),
    c.2.2.1.stripPis (nP + c.2.1) = some (cbs, body) →
    (((cbs.getD (nP + i) default).1.piBinders).2.getAppArgs).length = nP + nIt i
  /-- a recursive field's entry: the Π-tower over its telescope of the
  TARGET member's leaf at the parameter variables and the field's index
  readings -/
  recEntry : ∀ i ∈ c.2.2.2,
    (cd.2.2.1.getD (nP + i) default).2.2
      = mkPisAV (cd.2.2.2.2.2.2.getD i [])
          (AnnotTerm.mkAppN (m.acval (Tt i) ψ)
            (paramBvarsAt nP (nP + i + (cd.2.2.2.2.2.2.getD i []).length) ++
              cd.2.2.2.2.2.1.getD i []))

/-- A recursive field's readings, off the target-aware premise
(`fieldReadAt_ofE` at the field's TARGET leaf and index count). -/
theorem fieldReadAtT_of {m : EnvModel V env} {ψ : Name → Nat} {T : Name} {Tt : Nat → Name}
    {lps : List Name} {nP nIdx : Nat} {nIt : Nat → Nat} {c : Name × Nat × Expr × List Nat}
    {cd : CtorDatumR}
    (hc : CtorReadRT m ψ T Tt lps nP nIdx nIt c cd) {i : Nat} (hi : i ∈ c.2.2.2)
    {fvs0 : List Expr} {crest : Expr}
    (hop0 : openPisAtFvars (nP + c.2.1) c.2.2.1 0 = some (fvs0, crest)) :
    FieldReadAt m ψ nP c.2.1 i c.2.2.1 fvs0 (cd.2.2.2.2.2.2.getD i [])
      (cd.2.2.2.2.2.1.getD i []) :=
  fieldReadAt_ofE hc.hasFvar
    (by obtain ⟨cbs, es, hst, -⟩ := hc.resid; exact ⟨cbs, _, hst⟩)
    (hc.recIdxBnd i hi) (hc.fieldRead i hi) (hc.teleLen i hi) (hc.fieldArity i hi)
    (hc.eisLen i hi) (hc.recEntry i hi) hop0

/-- **What the readings need of one constructor of a mutual block**:
the target-aware premise at its own member's former, plus its
member (`mot`) and its recursive fields' target members (`moti`). -/
structure MutualCtorRead {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (lps : List Name)
    (nP : Nat) (Tname : Nat → Name) (nIdxOf : Nat → Nat) (mot : Nat) (moti : Nat → Nat)
    (c : ConLeche.MutualCtor4) (cd : CtorDatumR) : Prop where
  member : c.member = mot
  fields : c.recFields = cd.2.2.2.2.1.map fun i => (i, moti i)
  base : CtorReadRT m ψ (Tname mot) (fun i => Tname (moti i)) lps nP (nIdxOf mot)
    (fun i => nIdxOf (moti i)) (c.name, c.nF, c.cty, cd.2.2.2.2.1) cd

/-- The constructors' reading premises, positionally. -/
@[expose] def MutualCtorReadsM {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    (lps : List Name) (nP : Nat) (Tname : Nat → Name) (nIdxOf : Nat → Nat) (mots : Nat → Nat)
    (tgts : Nat → Nat → Nat) (ctors : List ConLeche.MutualCtor4) (cds : List CtorDatumR) : Prop :=
  cds.length = ctors.length ∧
  ∀ J, J < ctors.length →
    MutualCtorRead m ψ lps nP Tname nIdxOf (mots J) (tgts J) (ctors.getD J default)
      (cds.getD J default)

theorem MutualCtorReadsM.head {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat}
    {Tname : Nat → Name} {nIdxOf : Nat → Nat} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {c : ConLeche.MutualCtor4} {cs : List ConLeche.MutualCtor4} {cd : CtorDatumR}
    {cds : List CtorDatumR}
    (h : MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts (c :: cs) (cd :: cds)) :
    MutualCtorRead m ψ lps nP Tname nIdxOf (mots 0) (tgts 0) c cd := h.2 0 (by simp)

theorem MutualCtorReadsM.tail {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name} {nP : Nat}
    {Tname : Nat → Name} {nIdxOf : Nat → Nat} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {c : ConLeche.MutualCtor4} {cs : List ConLeche.MutualCtor4} {cd : CtorDatumR}
    {cds : List CtorDatumR}
    (h : MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts (c :: cs) (cd :: cds)) :
    MutualCtorReadsM m ψ lps nP Tname nIdxOf (fun J => mots (J + 1)) (fun J => tgts (J + 1))
      cs cds :=
  ⟨by have := h.1; simp only [List.length_cons] at this; omega,
    fun J hJ => h.2 (J + 1) (by simp only [List.length_cons]; omega)⟩

theorem MutualCtorReadsM.length_eq {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {Tname : Nat → Name} {nIdxOf : Nat → Nat} {mots : Nat → Nat}
    {tgts : Nat → Nat → Nat} {ctors : List ConLeche.MutualCtor4} {cds : List CtorDatumR}
    (h : MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts ctors cds) :
    cds.length = ctors.length := h.1

set_option maxHeartbeats 1600000 in
/-- **The minors' `∀`-telescope** of a mutual block reads to the
Π-tower over `fixMinorsDataM`, the body read under the `k` motives and
all the minors. -/
theorem denoteMeta_mutualMinorsPis {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {Tname : Nat → Name} {nIdxOf : Nat → Nat}
    (hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      env.find? (Tname q) = some ci ∧ ci.toConstantVal.levelParams = lps)
    {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (q : Nat) (a : Expr), tfvs[q]? = some a → Expr.WScoped (0 + q + 1) a) :
    ∀ {ctors : List ConLeche.MutualCtor4} {cds : List CtorDatumR} {mots : Nat → Nat}
      {tgts : Nat → Nat → Nat} {body mins : Expr} {extras : List Expr},
      MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts ctors cds →
      ConLeche.mutualMinorsPis lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ J, J < ctors.length → mots J < extras.length) →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteMeta m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkPisAV (fixMinorsDataM mots tgts m ψ nP (pwBit ψ pw) cds extras.length))
  | [], cds, mots, tgts, body, mins, extras, hcr, hmin, _, _, hidxE => by
    obtain rfl : cds = [] := List.eq_nil_of_length_eq_zero hcr.length_eq
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [mutualMinorsPis_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsDataM, mkPisAV]
    cases denoteMeta m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | c :: cs, cds, mots, tgts, body, mins, extras, hcr, hmin, ho, hmots, hidxE => by
    obtain ⟨cd, cds', rfl⟩ : ∃ cd cds', cds = cd :: cds' := by
      cases cds with
      | nil => have := hcr.length_eq; simp at this
      | cons cd cds' => exact ⟨cd, cds', rfl⟩
    have hc := hcr.head
    obtain ⟨C', nF', ds, Es, recIdx, Eiss, tls⟩ := cd
    have hC' : c.name = C' := hc.base.name.symm
    have hnF' : c.nF = nF' := hc.base.nF.symm
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMinorsPis_cons hmin
    obtain ⟨ciT, hfTc, hlpsTc⟩ := hfT (mots 0)
    obtain ⟨ciC, hfC, hlpsC⟩ := hc.base.find
    have hmty' : ConLeche.mutualMinorTy lps nP extras.length pw
        ⟨c.name, c.nF, c.cty, mots 0, recIdx.map fun i => (i, tgts 0 i)⟩ = some mty := by
      rw [← hc.member, ← hc.fields]
      exact hmty
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteMeta_forallE,
      denoteMeta_minorAtRM hfTc hlpsTc hfC hlpsC hmty' hc.base.hasFvar hc.base.bounded
        hc.base.resid hc.base.read hc.base.len hc.base.lenE hc.base.recIdxBnd
        (fun i hi fvs rest hop => fieldReadAtT_of hc.base hi hop) hlenT hidxT hspW ho
        (hmots 0 (by simp)) hidxE]
    generalize hmk : Expr.fvar (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ ty, x = Expr.fvar (nP + k) ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          rcases Nat.lt_or_ge (k - extras.length) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by simp; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : ConLeche.mutualMinorsPis lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_mutualMinorsPis hfT hlenT hidxT hspW hcr.tail hrest' (by simp)
        (fun J hJ => by
          have := hmots (J + 1) (by simp only [List.length_cons]; omega)
          simp only [List.length_append, List.length_singleton]
          omega)
        hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith,
      fixMinorsDataM, mkPisAV, ← hC', ← hnF']
    cases denoteMeta m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

/-! ## The generated type -/

omit [SetTheory V] in
theorem getD_range_map {α : Type} (g : Nat → α) (k t : Nat) (h : t < k) (d : α) :
    ((List.range k).map g).getD t d = g t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show t < (List.range k).length from by simpa using h),
    List.getElem_range]
  rfl

set_option maxHeartbeats 3200000 in
/-- **The generated `k`-motive recursor type of member `mm` reads to
the Π-tower over `mutualRecDataAV`** with the core `motive_mm ı⃗ t`. -/
theorem denoteMeta_mutualRecTy {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {elim : Name} {large : Bool} {nP mm : Nat}
    {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
    {ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm)}
    {Tname : Nat → Name} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    {formers : List ConLeche.MutualFormer} {ctors : List ConLeche.MutualCtor4}
    {cds : List CtorDatumR}
    (hformers : FormerReadsM m ψ lps nP Lof nIdxOf ppsOf ipsOf formers)
    (hctors : MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts ctors cds)
    (hmots : ∀ J, J < ctors.length → mots J < formers.length)
    (hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      env.find? (Tname q) = some ci ∧ ci.toConstantVal.levelParams = lps)
    {recTy : Expr}
    (hgen : ConLeche.mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    denoteMeta m.acval env ψ 0 recTy
      = some (mkPisAV
          (mutualRecDataAV m ψ ((List.range formers.length).map Lof) nP
            ((List.range formers.length).map nIdxOf) (ConLeche.structElimLevel elim large)
            (ppsOf 0) ((List.range formers.length).map ipsOf) cds mots tgts mm)
          (mutualConcAV formers.length ctors.length (nIdxOf mm) mm)) := by
  obtain ⟨f, f₀, tbs, itele, major, minors, motives, hfmm, hf0, hsT, hmaj, hmin, hmotives, hrec⟩ :=
    mutualRecTy_unfold hgen
  have hmmlt : mm < formers.length := (List.getElem?_eq_some_iff.mp hfmm).1
  have h0lt : 0 < formers.length := by omega
  have hfmmD : formers.getD mm default = f := by
    rw [List.getD_eq_getElem?_getD, hfmm]; rfl
  have hf0D : formers.getD 0 default = f₀ := by
    rw [List.getD_eq_getElem?_getD, hf0]; rfl
  have hfr0 := hformers 0 h0lt
  have hfrmm := hformers mm hmmlt
  rw [hf0D] at hfr0
  rw [hfmmD] at hfrmm
  obtain ⟨tbs0, itele0, hsT0⟩ := hfr0.stripP
  obtain ⟨ppsAll0, w0, hTread0, hlenP0, hpps0, hips0⟩ := hfr0.read
  obtain ⟨ciM, hfMfind, hlpsM⟩ := hfrmm.find
  obtain ⟨ppsAllM, wM, hTreadM, hlenPM, hppsM, hipsM⟩ := hfrmm.read
  obtain ⟨tfvs, trest, hopT⟩ :=
    openPisAtFvars_of_stripPis_isSome nP 0 (show (f₀.tty.stripPis nP).isSome = true by rw [hsT0]; rfl)
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hfr0.hasFvar
  have hlenC : cds.length = ctors.length := hctors.length_eq
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV ppsAll0 (.sort w0))
      = some (ppsAll0.take nP, mkPisAV (ppsAll0.drop nP) (.sort w0)) :=
    stripPisAV_mkPisAV_take nP ppsAll0 _ (by omega)
  rw [denoteMeta_replacePisPw nP hrec hopT hTread0 hst, Nat.zero_add]
  -- the motives, at the parameters
  obtain ⟨extras1, hlen1, hidx1, hread1⟩ :=
    denoteMeta_mutualMotivesPis (pw := Level.zeronessOf (ConLeche.structElimLevel elim large))
      (extras := []) hlenT hidxT hspW hformers hmotives (by intro k x hx; simp at hx)
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hlen1 hread1
  rw [hread1]
  -- the minors, at the motives
  obtain ⟨extras2, hlen2, hidx2, hread2⟩ :=
    denoteMeta_mutualMinorsPis hfT hlenT hidxT hspW (extras := extras1) hctors
      (by rw [hlen1]; exact hmin) (by rw [hlen1]; omega)
      (fun J hJ => by rw [hlen1]; exact hmots J hJ) hidx1
  rw [hlen1] at hread2 hlen2
  have hlen2' : extras2.length = formers.length + ctors.length := by rw [hlen2]; omega
  rw [hread2]
  -- the index telescope and the major, under the motives and the minors
  have hclE2 : ∀ a ∈ extras2, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidx2 q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras2, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE2 a h
  have hlenTE : (tfvs ++ extras2).length = nP + formers.length + ctors.length := by
    rw [List.length_append, hlenT, hlen2]; omega
  obtain ⟨mfv, hhead⟩ : ∃ x, extras2[mm]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen2]; omega)⟩
  obtain ⟨tyM, rfl⟩ := hidx2 mm mfv hhead
  have htb0 : itele.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsT hfrmm.bounded
    rwa [Nat.zero_add] at this
  have hmaj' := ConLeche.replacePisPw_instSeq (tfvs ++ extras2)
    (nP + formers.length + ctors.length - 1) (by rw [hlenTE]; omega) hmaj
  have hres := ConLeche.instSeq_minorTele tfvs extras2 hlenT hclT htb0
  rw [hlen2', show nP + (formers.length + ctors.length) - 1
    = nP + formers.length + ctors.length - 1 from by omega] at hres
  rw [hres] at hmaj'
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hfrmm.hasFvar hTreadM hlenPM hsT hfrmm.strip hlenT
    hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome f.nIdx
    (nP + formers.length + ctors.length) htstrip
  have htreadN := ctorResidual_read_lift htread htw hlenPM (formers.length + ctors.length)
  rw [show nP + (formers.length + ctors.length) = nP + formers.length + ctors.length from by omega,
    AnnotTerm.liftN_sort] at htreadN
  have hstI : stripPisAV f.nIdx
      (mkPisAV (liftDoms (formers.length + ctors.length) 0 (ppsAllM.drop nP)) (.sort wM))
      = some (liftDoms (formers.length + ctors.length) 0 (ppsAllM.drop nP), .sort wM) := by
    have := stripPisAV_mkPisAV
      (liftDoms (formers.length + ctors.length) 0 (ppsAllM.drop nP)) (AnnotTerm.sort wM)
    rwa [liftDoms_length, List.length_drop, hlenPM, Nat.add_sub_cancel_left] at this
  have hmajR := denoteMeta_replacePisPw (acval := m.acval) (env := env) (φ := ψ) f.nIdx hmaj' hopI
    htreadN hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the major's domain and the conclusion, instantiated
  have hnilI : ifvs = [] ∨ f.nIdx - 1 + 1 = f.nIdx := by
    rcases Nat.eq_zero_or_pos f.nIdx with h0 | hpos
    · left; rw [h0] at hlenI; exact List.eq_nil_of_length_eq_zero hlenI
    · right; omega
  have hdom1 : Expr.instSeq (tfvs ++ extras2)
      (nP + formers.length + ctors.length - 1 + f.nIdx)
      (ConLeche.structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0)
      = Expr.mkAppN (.const f.name (lps.map .param))
          (tfvs ++ (List.range f.nIdx).map fun k => Expr.bvar (f.nIdx - 1 - k)) := by
    unfold ConLeche.structFamI
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const f.name (lps.map .param)) rfl,
      show nP + formers.length + ctors.length - 1 + f.nIdx
        = (0 + (formers.length + ctors.length) + f.nIdx) + nP - 1 from by omega,
      ConLeche.map_instSeq_structPsAt (tfvs ++ extras2)
        (0 + (formers.length + ctors.length) + f.nIdx) nP hclTE (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      structPsAt_zero, ConLeche.map_instSeq_fieldBvars_above (tfvs ++ extras2) _ f.nIdx
        (by rw [hlenTE]; omega)]
  have hcod1 : Expr.instSeq (tfvs ++ extras2)
      (nP + formers.length + ctors.length - 1 + f.nIdx + 1)
      (Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
        (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar (nP + mm) tyM) (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0]) := by
    have hhead' : Expr.instSeq (tfvs ++ extras2)
        (nP + formers.length + ctors.length - 1 + f.nIdx + 1)
        (.bvar (f.nIdx + ctors.length + formers.length - mm)) = Expr.fvar (nP + mm) tyM := by
      have := Expr.instSeq_bvar (tfvs ++ extras2)
        (nP + formers.length + ctors.length - 1 + f.nIdx + 1)
        (f.nIdx + ctors.length + formers.length - mm) hclTE (by omega) (by rw [hlenTE]; omega)
      rw [show nP + formers.length + ctors.length - 1 + f.nIdx + 1
          - (f.nIdx + ctors.length + formers.length - mm) = nP + mm from by omega,
        List.getElem?_append_right (by omega), hlenT,
        show nP + mm - nP = mm from by omega, hhead] at this
      exact (Option.some.inj this).symm
    rw [Expr.instSeq_mkAppN, hhead', List.map_append]
    congr 2
    · refine (List.map_congr_left ?_).trans (List.map_id _)
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact ConLeche.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)
    · simp only [List.map_cons, List.map_nil]
      rw [ConLeche.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)]
  have hdom2 : Expr.instSeq ifvs (f.nIdx - 1) (Expr.mkAppN (.const f.name (lps.map .param))
      (tfvs ++ (List.range f.nIdx).map fun k => Expr.bvar (f.nIdx - 1 - k)))
      = Expr.mkAppN (.const f.name (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const f.name (lps.map .param)) rfl,
      map_instSeq_closed ifvs (f.nIdx - 1) hclT,
      ConLeche.map_instSeq_fieldBvars ifvs f.nIdx hclI hlenI]
  have hcod2 : Expr.instSeq ifvs (f.nIdx - 1 + 1)
      (Expr.mkAppN (.fvar (nP + mm) tyM) (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar (nP + mm) tyM) (ifvs ++ [.bvar 0]) := by
    rw [instSeq_idx_congr (sp := ifvs) (t := f.nIdx - 1 + 1) (t' := f.nIdx) _ hnilI,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.fvar (nP + mm) tyM) rfl,
      List.map_append, map_instSeq_structPsAt_one ifvs f.nIdx hclI hlenI]
    simp only [List.map_cons, List.map_nil]
    rw [ConLeche.instSeq_bvar_lt ifvs _ 0 (by omega)]
  have hbody : Expr.instSeq ifvs (f.nIdx - 1) (Expr.instSeq (tfvs ++ extras2)
      (nP + formers.length + ctors.length - 1 + f.nIdx)
      (.forallE (ConLeche.structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0)
        (Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
          (ConLeche.structPsAt 1 f.nIdx ++ [.bvar 0]))
        ⟨Level.zeronessOf (ConLeche.structElimLevel elim large)⟩))
      = .forallE (Expr.mkAppN (.const f.name (lps.map .param)) (tfvs ++ ifvs))
          (Expr.mkAppN (.fvar (nP + mm) tyM) (ifvs ++ [.bvar 0]))
          ⟨Level.zeronessOf (ConLeche.structElimLevel elim large)⟩ := by
    rw [Expr.instSeq_forallE (tfvs ++ extras2) (nP + formers.length + ctors.length - 1 + f.nIdx)
        _ _ _ (by rw [hlenTE]; omega), hdom1, hcod1,
      Expr.instSeq_forallE ifvs (f.nIdx - 1) _ _ _ (by omega), hdom2, hcod2]
  rw [hbody] at hmajR
  -- the major's reading and the conclusion
  have hidxI' : ∀ (k : Nat) (x : Expr), ifvs[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + (formers.length + ctors.length) + k) ty := by
    intro k x hx
    rw [show nP + (formers.length + ctors.length) + k
      = nP + formers.length + ctors.length + k from by omega]
    exact hidxI k x hx
  have hspine := denoteMeta_famSpine_at (m := m) (ψ := ψ) hfMfind hlpsM
    (o := formers.length + ctors.length) hlenT hlenI hidxT hidxI'
  rw [show nP + (formers.length + ctors.length) + f.nIdx
    = nP + formers.length + ctors.length + f.nIdx from by omega] at hspine
  have hconc : denoteMeta m.acval env ψ (nP + formers.length + ctors.length + f.nIdx + 1)
      ((Expr.mkAppN (.fvar (nP + mm) tyM) (ifvs ++ [.bvar 0])).instantiate1
        (.fvar (nP + formers.length + ctors.length + f.nIdx)
          (Expr.mkAppN (.const f.name (lps.map .param)) (tfvs ++ ifvs))) 0)
      = some (mutualConcAV formers.length ctors.length f.nIdx mm) := by
    rw [Expr.mkAppN_instantiate1, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instantiate1_eq_self (e := Expr.fvar (nP + mm) tyM) rfl,
      map_instantiate1_closed hclI]
    simp +decide only [Expr.instantiate1, ↓reduceIte]
    have hspI : DenoteMetaSpine m.acval env ψ
        (nP + formers.length + ctors.length + f.nIdx + 1) ifvs (idxVarsAV f.nIdx 1) := by
      have := denoteMetaSpine_fvars (acval := m.acval) (env := env) (φ := ψ)
        (nP + formers.length + ctors.length + f.nIdx + 1) ifvs
        (nP + formers.length + ctors.length) hidxI
      rw [hlenI] at this
      have he : ((List.range f.nIdx).map fun k =>
          AnnotTerm.bvar (nP + formers.length + ctors.length + f.nIdx + 1 - 1
            - (nP + formers.length + ctors.length + k))) = idxVarsAV f.nIdx 1 := by
        unfold idxVarsAV
        apply List.map_congr_left
        intro k _
        congr 1
        omega
      rwa [he] at this
    rw [denoteMeta_mkAppN (hspI.append (.cons (denoteMeta_fvar _ _ _ _) .nil))
        (denoteMeta_fvar _ _ _ _),
      show nP + formers.length + ctors.length + f.nIdx + 1 - 1 - (nP + mm)
        = 1 + f.nIdx + ctors.length + formers.length - 1 - mm from by omega,
      show nP + formers.length + ctors.length + f.nIdx + 1 - 1
        - (nP + formers.length + ctors.length + f.nIdx) = 0 from by omega,
      AnnotTerm.mkAppN_append_one]
    rfl
  have hpi : denoteMeta m.acval env ψ (nP + formers.length + ctors.length + f.nIdx)
      (.forallE (Expr.mkAppN (.const f.name (lps.map .param)) (tfvs ++ ifvs))
        (Expr.mkAppN (.fvar (nP + mm) tyM) (ifvs ++ [.bvar 0]))
        ⟨Level.zeronessOf (ConLeche.structElimLevel elim large)⟩)
      = some (.pi 0 (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel elim large)))
          (majorAVAtK (m.acval f.name ψ) nP f.nIdx formers.length ctors.length)
          (mutualConcAV formers.length ctors.length f.nIdx mm)) := by
    rw [denoteMeta_forallE, hspine, hconc]
    rfl
  rw [hpi, Option.map_some] at hmajR
  rw [hmajR]
  -- assembly
  have hLmm : ((List.range formers.length).map Lof).getD mm default = m.acval f.name ψ := by
    rw [getD_range_map _ _ _ hmmlt, hfrmm.leaf]
  have hNmm : ((List.range formers.length).map nIdxOf).getD mm 0 = f.nIdx := by
    rw [getD_range_map _ _ _ hmmlt, hfrmm.idxCount]
  have hImm : ((List.range formers.length).map ipsOf).getD mm [] = ppsAllM.drop nP := by
    rw [getD_range_map _ _ _ hmmlt, hipsM]
  have hlenLs : ((List.range formers.length).map Lof).length = formers.length := by simp
  have hmotD : motivesDataGo (fun t => ((List.range formers.length).map Lof).getD t default)
      (fun t => ((List.range formers.length).map nIdxOf).getD t 0)
      (fun t => ((List.range formers.length).map ipsOf).getD t []) ψ nP
      (ConLeche.structElimLevel elim large)
      (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel elim large))) formers.length 0
      = motivesDataGo Lof nIdxOf ipsOf ψ nP (ConLeche.structElimLevel elim large)
        (pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel elim large))) formers.length 0 :=
    motivesDataGo_congr _ _ fun t ht =>
      ⟨getD_range_map _ _ _ ht _, getD_range_map _ _ _ ht _, getD_range_map _ _ _ ht _⟩
  unfold mutualRecDataAV
  rw [hlenLs, hLmm, hNmm, hImm, hmotD, hpps0, hfrmm.idxCount,
    mkPisAV_append, mkPisAV_append, mkPisAV_append, mkPisAV_append, hlenC]
  rfl

end ConLeche.Model
