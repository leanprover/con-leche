module

public import ConLeche.Model.Inductives.MutualRecRead
public section

/-!
# The mutual block's generated rules, read (task #278, M2.2c)

`ConLeche/Model/Inductives/FixRecRead.lean`'s `denoteMeta_structRecRhsR`
with `k` motives: rule `J` of a mutual block (`ConLeche.mutualRecRhs`,
`ConLeche/Kernel/Inductives/MutualParts.lean`; `J` is the constructor's
GLOBAL index and member `m_J`'s recursor fires it) reads to the λ-tower
over `mutualRuleDataAV` — the parameters, the `k` motives, the `n`
minors and constructor `J`'s field data lifted under them — with the
core `mutualRuleCoreAV`: minor `J` at the fields and at the inductive
hypotheses, hypothesis `i` firing the recursor of the member its field
targets.

The pieces are the fixpoint route's: the λ-twins of
`denoteMeta_mutualMotivesPis`/`denoteMeta_mutualMinorsPis` here, and
the core's reading (`denoteMeta_mutualRuleBody`) already generalised
in place in `FixRecRead.lean`.
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

/-! ## The rule's binder data -/

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

/-! ## The generators, unfolded -/

theorem mutualMotivesLams_nil {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} {i : Nat}
    {body mots : Expr} (h : ConLeche.mutualMotivesLams lps nP ℓ pw [] i body = some mots) :
    mots = body := by
  simp only [ConLeche.mutualMotivesLams, Option.some.injEq] at h
  exact h.symm

theorem mutualMotivesLams_cons {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {f : ConLeche.MutualFormer} {fs : List ConLeche.MutualFormer} {i : Nat} {body mots : Expr}
    (h : ConLeche.mutualMotivesLams lps nP ℓ pw (f :: fs) i body = some mots) :
    ∃ mty rest, ConLeche.mutualMotiveTy lps nP ℓ i f = some mty ∧
      ConLeche.mutualMotivesLams lps nP ℓ pw fs (i + 1) body = some rest ∧
      mots = .lam mty rest ⟨pw⟩ := by
  unfold ConLeche.mutualMotivesLams at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmots⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmots.symm⟩

theorem mutualMinorsLams_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body mins : Expr} (h : ConLeche.mutualMinorsLams lps nP pw [] o body = some mins) :
    mins = body := by
  simp only [ConLeche.mutualMinorsLams, Option.some.injEq] at h
  exact h.symm

theorem mutualMinorsLams_cons {lps : List Name} {nP : Nat} {pw : PropWhen}
    {c : ConLeche.MutualCtor4} {cs : List ConLeche.MutualCtor4} {o : Nat} {body mins : Expr}
    (h : ConLeche.mutualMinorsLams lps nP pw (c :: cs) o body = some mins) :
    ∃ mty rest, ConLeche.mutualMinorTy lps nP o pw c = some mty ∧
      ConLeche.mutualMinorsLams lps nP pw cs (o + 1) body = some rest ∧
      mins = .lam mty rest ⟨pw⟩ := by
  unfold ConLeche.mutualMinorsLams at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mty, hmty, rest, hrest, hmins⟩ := h
  exact ⟨mty, rest, hmty, hrest, hmins.symm⟩

/-- `mutualRecRhs` at rule `J`, unfolded to its five steps
(`structRecRhsR_unfold`'s `k`-motive twin). -/
theorem mutualRecRhs_unfold {lps : List Name} {elim : Name} {large : Bool} {nP J : Nat}
    {formers : List ConLeche.MutualFormer} {ctors : List ConLeche.MutualCtor4}
    {recOf : Nat → Name} {rlvls : List Level} {rhs : Expr}
    (h : ConLeche.mutualRecRhs lps elim large nP formers ctors recOf rlvls J = some rhs) :
    ∃ (c : ConLeche.MutualCtor4) (f₀ : ConLeche.MutualFormer)
      (cbs : List (Expr × BinderMeta)) (crest0 inner minors motives : Expr),
      ctors[J]? = some c ∧ formers[0]? = some f₀ ∧
      c.cty.stripPis nP = some (cbs, crest0) ∧
      Expr.pisToLamsPw (Level.zeronessOf (ConLeche.structElimLevel elim large)) c.nF
          (crest0.liftLooseBVars (formers.length + ctors.length) 0)
          (ConLeche.mutualRuleBody recOf rlvls
            (Level.zeronessOf (ConLeche.structElimLevel elim large)) nP formers.length
            ctors.length c.nF J c.recFields (ConLeche.structFieldTeleOf c.cty nP c.nF)
            (ConLeche.structFieldIdxOf c.cty nP c.nF))
        = some inner ∧
      ConLeche.mutualMinorsLams lps nP (Level.zeronessOf (ConLeche.structElimLevel elim large))
          ctors formers.length inner = some minors ∧
      ConLeche.mutualMotivesLams lps nP (ConLeche.structElimLevel elim large)
          (Level.zeronessOf (ConLeche.structElimLevel elim large)) formers 0 minors
        = some motives ∧
      Expr.pisToLamsPw (Level.zeronessOf (ConLeche.structElimLevel elim large)) nP f₀.tty motives
        = some rhs := by
  unfold ConLeche.mutualRecRhs at h
  split at h
  · next c f₀ hc hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, inner, hinner, minors, hmin, motives, hmot, hr⟩ := h
    exact ⟨c, f₀, q.1, q.2, inner, minors, motives, hc, hf₀, hq, hinner, hmin, hmot, hr⟩
  · exact nomatch h

/-! ## The motives' λ-telescope -/

set_option maxHeartbeats 1600000 in
/-- **The motives' `λ`-telescope** reads to the λ-tower over
`motivesDataGo`'s domains, the body read under all `k` of them
(`denoteMeta_mutualMotivesPis`'s twin). -/
theorem denoteMeta_mutualMotivesLams {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {ℓ : Level} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (q : Nat) (a : Expr), tfvs[q]? = some a → Expr.WScoped (0 + q + 1) a) :
    ∀ {formers : List ConLeche.MutualFormer} {Lof : Nat → AnnotTerm} {nIdxOf : Nat → Nat}
      {ppsOf ipsOf : Nat → List (Nat × Nat × AnnotTerm)} {body mots : Expr} {extras : List Expr},
      FormerReadsM m ψ lps nP Lof nIdxOf ppsOf ipsOf formers →
      ConLeche.mutualMotivesLams lps nP ℓ pw formers extras.length body = some mots →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = formers.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mots)
          = (denoteMeta m.acval env ψ (nP + extras.length + formers.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + formers.length - 1) body)).map
              (mkLamsAV ((motivesDataGo Lof nIdxOf ipsOf ψ nP ℓ (pwBit ψ pw) formers.length
                extras.length).map fun d => (d.2.1, d.2.2)))
  | [], Lof, nIdxOf, ppsOf, ipsOf, body, mots, extras, _, hmot, hidxE => by
    rw [mutualMotivesLams_nil hmot]
    refine ⟨extras, by simp, hidxE, ?_⟩
    simp only [List.length_nil, Nat.add_zero, motivesDataGo, List.map_nil, mkLamsAV]
    cases denoteMeta m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | f :: fs, Lof, nIdxOf, ppsOf, ipsOf, body, mots, extras, hfr, hmot, hidxE => by
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMotivesLams_cons hmot
    obtain ⟨ci, hfT, hlpsT⟩ := hfr.head.find
    obtain ⟨tbs, itele, hsT⟩ := hfr.head.stripP
    obtain ⟨ppsAll, w, hTread, hlenP, -, hips⟩ := hfr.head.read
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    have hnil : (tfvs ++ extras) = [] ∨ nP + extras.length - 1 + 1 = nP + extras.length := by
      rcases Nat.eq_zero_or_pos (nP + extras.length) with h0 | hpos
      · left; exact List.eq_nil_of_length_eq_zero (by rw [hlenTE, h0])
      · right; omega
    rw [ConLeche.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _
        (by rw [hlenTE]; omega),
      instSeq_idx_congr (sp := tfvs ++ extras) (t := nP + extras.length - 1 + 1)
        (t' := nP + extras.length) rest hnil,
      denoteMeta_lam,
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
    have hrest' : ConLeche.mutualMotivesLams lps nP ℓ pw fs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_mutualMotivesLams hlenT hidxT hspW hfr.tail hrest' hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + fs.length
        = nP + extras.length + (fs.length + 1) := by omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith,
      motivesDataGo, List.map_cons, mkLamsAV, hfr.head.leaf, hfr.head.idxCount, hips, motiveAVI]
    cases denoteMeta m.acval env ψ (nP + extras.length + (fs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (fs.length + 1) - 1) body) <;> rfl

/-! ## The minors' λ-telescope -/

set_option maxHeartbeats 1600000 in
/-- **The minors' `λ`-telescope** of a mutual block reads to the
λ-tower over `fixMinorsDataM`'s domains, the body read under the `k`
motives and all the minors (`denoteMeta_mutualMinorsPis`'s twin). -/
theorem denoteMeta_mutualMinorsLams {m : EnvModel V env} {ψ : Name → Nat} {lps : List Name}
    {nP : Nat} {Tname : Nat → Name} {nIdxOf : Nat → Nat}
    (hfT : ∀ q : Nat, ∃ ci : ConstantInfo,
      env.find? (Tname q) = some ci ∧ ci.toConstantVal.levelParams = lps)
    {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hspW : ∀ (q : Nat) (a : Expr), tfvs[q]? = some a → Expr.WScoped (0 + q + 1) a) :
    ∀ {ctors : List ConLeche.MutualCtor4} {cds : List CtorDatumR} {mots : Nat → Nat}
      {tgts : Nat → Nat → Nat} {body mins : Expr} {extras : List Expr},
      MutualCtorReadsM m ψ lps nP Tname nIdxOf mots tgts ctors cds →
      ConLeche.mutualMinorsLams lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ J, J < ctors.length → mots J < extras.length) →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty) ∧
        denoteMeta m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteMeta m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkLamsAV ((fixMinorsDataM mots tgts m ψ nP (pwBit ψ pw) cds extras.length).map
                fun d => (d.2.1, d.2.2)))
  | [], cds, mots, tgts, body, mins, extras, hcr, hmin, _, _, hidxE => by
    obtain rfl : cds = [] := List.eq_nil_of_length_eq_zero hcr.length_eq
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [mutualMinorsLams_nil hmin]
    simp only [List.length_nil, Nat.add_zero, fixMinorsDataM, List.map_nil, mkLamsAV]
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
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := mutualMinorsLams_cons hmin
    obtain ⟨ciT, hfTc, hlpsTc⟩ := hfT (mots 0)
    obtain ⟨ciC, hfC, hlpsC⟩ := hc.base.find
    have hmty' : ConLeche.mutualMinorTy lps nP extras.length pw
        ⟨c.name, c.nF, c.cty, mots 0, recIdx.map fun i => (i, tgts 0 i)⟩ = some mty := by
      rw [← hc.member, ← hc.fields]
      exact hmty
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [ConLeche.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteMeta_lam,
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
    have hrest' : ConLeche.mutualMinorsLams lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteMeta_mutualMinorsLams hfT hlenT hidxT hspW hcr.tail hrest' (by simp)
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
      fixMinorsDataM, List.map_cons, mkLamsAV, ← hC', ← hnF']
    cases denoteMeta m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

end ConLeche.Model
