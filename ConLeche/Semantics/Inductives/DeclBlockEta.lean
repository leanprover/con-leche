module

import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Verify.EnvGuards
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.ExceptBind
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Verify.Inductives.BlockWF

@[expose] public section

/-!
# The uniform install keeps the η-families closed

The stage lemmas of the declaration fold's η half at the `.indDecl`
dispatch (`declBlockRun_etaClosed`, `DeclBlockEtaRun.lean`): every store
is a **fresh cons**, so `EtaFamiliesClosed.cons_nonind` applies at
every step that stores no η-claiming former.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  fueledOps checkConstantVal
  checkStructProjTable projTableName EtaFamiliesClosed ProjEntry)

/-! ## The stage shapes, with their freshness guards -/

/-- The table stage's run: the tower table consed at a fresh table
name. -/
theorem checkStructProjTable_shape {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env' : Env}
    (h : checkStructProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env') :
    ∃ tbl : ConLeche.ProjTable, env.find? (projTableName T) = none ∧
      tbl.structName = T ∧ env' = ⟨.projInfo tbl :: env.consts⟩ := by
  obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv h
  exact ⟨_, hfresh, rfl, rfl⟩

/-! ## The table stage -/

/-- The table stage keeps the η-families closed: a fresh cons of a
table. -/
theorem checkStructProjTable_etaClosed {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env₂ : Env}
    (h : checkStructProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env₂)
    (hE : EtaFamiliesClosed env) : EtaFamiliesClosed env₂ := by
  obtain ⟨tbl, hfresh, hsn, rfl⟩ := checkStructProjTable_shape h
  refine EtaFamiliesClosed.cons_nonind hE ?_ (fun _ _ heq => nomatch heq)
  show env.find? (projTableName tbl.structName) = none
  rw [hsn]; exact hfresh


/-! ## Lookups through the constructors' conses -/


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape fueledOps checkSumCtors
   consSumCtors sumRules EtaFamiliesClosed)

/-- A name none of the consed constructors carries looks up below the
conses. -/
theorem consSumCtors_find?_of_not_mem {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      n ∉ ctorsA.map (·.1.name) → (consSumCtors nP ctorsA env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, hn => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [consSumCtors_find?_of_not_mem hn.2, ConLeche.Env.find?_cons, if_neg (fun h => hn.1 h.symm)]


/-!
## The uniform install keeps the η-families closed, at k members

At the run `DeclBlockRun`, MODEL-FREE: the fold threads `EtaFamiliesClosed` next
to the model, so its η half must follow from the run record alone.

The install is four cons phases, and each is read at the environment
BELOW it:
* the `k` formers (`consBlockInds`) and the constructors
  (`consBlockCtors`) are consed at names that were fresh BEFORE the
  phase (`checkConstantVal`'s guard at `env`, resp. at `env₁`), so a
  family stored before the block, and its η constructor, read through
  unchanged — no distinctness is needed for that;
* a member of the block that claims η has ONE constructor
  (`blockCapsAt`), which the constructors' phase stores at the record's
  arities; the block's constructor names are distinct (`DeclBlockRun`'s
  conjunct 0), so no later constructor cons shadows it;
* the recursors (`consBlockRecsT`) are fresh at the constructors'
  environment (`recStage_cvFacts`) and store no former (`ExtEta`);
* every projection table is a fresh cons (`checkStructProjTable_etaClosed`).
-/


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo IndCaps
  BlockParts BlockShape MemberShape fueledOps EtaFamiliesClosed ExtEta exceptBind_ok
  consBlockInds consBlockCtors consSumCtors consBlockRecs checkBlockTables
  checkBlockCtors checkSumCtors blockCapsAt)

/-! ## Lookups through the formers' and the constructors' conses -/

/-- A name none of the consed formers carries reads through the
formers' conses unchanged. -/
theorem consBlockInds_find?_of_ne {p₁ : BlockShape} {isRec : Bool} {n : Name} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env},
      (∀ cv ∈ cvTas, cv.name ≠ n) →
      (consBlockInds p₁ isRec cvTas i env).find? n = env.find? n
  | [], _, _, _ => rfl
  | cv :: rest, i, env, hne => by
    simp only [consBlockInds]
    rw [consBlockInds_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      ConLeche.Env.find?_cons]
    exact if_neg (hne cv List.mem_cons_self)

/-- A name none of the consed constructors carries reads through the
constructors' conses unchanged. -/
theorem consBlockCtors_find?_of_ne {nP : Nat} {n : Name} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      (∀ ctorsA ∈ ctorsAs, n ∉ ctorsA.map (·.1.name)) →
      (consBlockCtors nP ctorsAs env).find? n = env.find? n
  | [], _, _ => rfl
  | ctorsA :: rest, env, hne => by
    simp only [consBlockCtors]
    rw [consBlockCtors_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      consSumCtors_find?_of_not_mem (hne ctorsA List.mem_cons_self)]

/-- The constructors' conses store no former: a `.indInfo` found above
them was found below them. -/
theorem consSumCtors_find?_indInfo {nP : Nat} {n : Name} {cv : ConstantVal} {caps : IndCaps} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP ctorsA env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps)
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consSumCtors] at h
    have h' := consSumCtors_find?_indInfo h
    rw [ConLeche.Env.find?_cons] at h'
    split at h'
    · exact nomatch Option.some.inj h'
    · exact h'

theorem consBlockCtors_find?_indInfo {nP : Nat} {n : Name} {cv : ConstantVal} {caps : IndCaps} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      (consBlockCtors nP ctorsAs env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps)
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consBlockCtors] at h
    exact consSumCtors_find?_indInfo (consBlockCtors_find?_indInfo h)

/-- **A consed constructor is found at its own record**, when the
member's constructor names are distinct. -/
theorem consSumCtors_find?_mem {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env} {cA : ConstantVal × Nat},
      (ctorsA.map (·.1.name)).Nodup → cA ∈ ctorsA →
      (consSumCtors nP ctorsA env).find? cA.1.name = some (.ctorInfo cA.1 nP cA.2)
  | [], _, _, _, hc => nomatch hc
  | c :: cs, env, cA, hnd, hc => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [consSumCtors_find?_of_not_mem hnd.1]
      exact ConLeche.Env.find?_cons_self _ _
    · exact consSumCtors_find?_mem hnd.2 hc'

/-- **A consed constructor is found at its own record** after all the
members' conses, when the block's constructor names are distinct. -/
theorem consBlockCtors_find?_mem {nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env} {ctorsA : List (ConstantVal × Nat)}
      {cA : ConstantVal × Nat},
      ((ctorsAs.map (·.map (·.1.name))).flatten).Nodup → ctorsA ∈ ctorsAs → cA ∈ ctorsA →
      (consBlockCtors nP ctorsAs env).find? cA.1.name = some (.ctorInfo cA.1 nP cA.2)
  | [], _, _, _, _, hl, _ => nomatch hl
  | A :: rest, env, ctorsA, cA, hnd, hl, hc => by
    simp only [consBlockCtors]
    simp only [List.map_cons, List.flatten_cons] at hnd
    obtain ⟨hndA, hndR, hcross⟩ := List.nodup_append.mp hnd
    rcases List.mem_cons.mp hl with rfl | hl'
    · rw [consBlockCtors_find?_of_ne]
      · exact consSumCtors_find?_mem hndA hc
      · intro B hB hmem
        exact hcross _ (List.mem_map_of_mem hc) _
          (List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hB, hmem⟩) rfl
    · exact consBlockCtors_find?_mem hndR hl' hc

/-! ## The constructors' stage: names, arities, freshness -/

/-- **One member's constructor loop, read at the names**: the stored
constructors carry the member's constructor names and field counts, in
order, each fresh at the environment the loop checks at. -/
theorem checkSumCtors_names {mode : CheckMode} {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat}
    {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (h : ConLeche.checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvTa cs = .ok (ctorsA, sortss)) :
    ctorsA.map (fun cA => (cA.1.name, cA.2)) = cs.map (fun c => (c.1.name, c.2)) ∧
    ∀ cA ∈ ctorsA, env.find? cA.1.name = none := by
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv h
  have hpos : ∀ (j : Nat) (hj : j < ctorsA.length),
      ctorsA[j].1.name = (cs[j]'(hlen ▸ hj)).1.name ∧ ctorsA[j].2 = (cs[j]'(hlen ▸ hj)).2 ∧
      env.find? ctorsA[j].1.name = none := by
    intro j hj
    obtain ⟨hnF, _, -, hrun⟩ := hall j (cs[j]'(hlen ▸ hj)) (ctorsA[j])
      (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem hj)
    obtain ⟨⟨_, hccv⟩, -, -⟩ := ConLeche.checkSumCtor_shape hrun
    obtain ⟨hfC, -, -, -, -, -, _, _, _, -, -, -, -, -, hCeq⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hn : ctorsA[j].1.name = (cs[j]'(hlen ▸ hj)).1.name := by rw [hCeq]
    exact ⟨hn, hnF, by rw [hn]; exact hfC⟩
  refine ⟨?_, fun cA hcA => ?_⟩
  · apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    simp only [List.getElem_map]
    have hj : j < ctorsA.length := by simpa using h1
    obtain ⟨e1, e2, -⟩ := hpos j hj
    rw [e1, e2]
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
    exact (hpos j hj).2.2

/-- **The members' constructor loops, read at the names**: member by
member, the stored constructors carry the members' constructor names
and field counts, each fresh at the environment the loops check at. -/
theorem checkBlockCtors_names {mode : CheckMode} {env₀ env : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss) →
      ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
        = l.map (fun mc => mc.1.ctors.map (fun c => (c.1.name, c.2))) ∧
      ∀ ctorsA ∈ ctorsAs, ∀ cA ∈ ctorsA, env.find? cA.1.name = none
  | [], ctorsAs, sortsss, h => by
    simp only [checkBlockCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ h => nomatch h⟩
  | (ms, cvTa) :: rest, ctorsAs, sortsss, h => by
    unfold checkBlockCtors at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, sortss⟩ := r
    try simp only at h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    obtain ⟨restC, restS⟩ := r'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn1, hf1⟩ := checkSumCtors_names hr
    obtain ⟨hn2, hf2⟩ := checkBlockCtors_names hr'
    refine ⟨by simp only [List.map_cons, hn1, hn2], ?_⟩
    intro A hA cA hcA
    rcases List.mem_cons.mp hA with rfl | hA'
    · exact hf1 cA hcA
    · exact hf2 A hA' cA hcA

/-! ## The formers' stage: freshness -/

/-- **The k formers are consed at names fresh before the block.** -/
theorem checkBlockInds_fresh {mode : CheckMode} {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    ∀ cv ∈ cvTas, env.find? cv.name = none := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, rfl, -, -, h0, hcvs, -⟩ := ConLeche.checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {cv : ConstantVal} {s : Level},
      ConLeche.checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cv, s) →
      env.find? cv.name = none := by
    intro ms cv s hh
    obtain ⟨cvT, -, -, hcv, -⟩ := ConLeche.checkBlockTele_shape hh
    obtain ⟨hf, -, -, -, -, -, _, _, _, -, -, -, -, -, heq⟩ := ConLeche.checkConstantVal_inv hcv
    rw [heq]; exact hf
  intro cv hcv
  rcases List.mem_cons.mp hcv with rfl | hcv'
  · exact hone h0
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    obtain ⟨hlen, hall⟩ := ConLeche.checkBlockTeles_inv hcvs
    have hil : i < rest.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨q', hq', hrun⟩ := hall i (rest[i]) (List.getElem?_eq_getElem hil)
    obtain rfl := Option.some.inj (hi.symm.trans hq')
    exact hone hrun


/-! ## The recursors' and the tables' phases -/

/-- **One cons at a name fresh at the BASE** extends `ExtEta` from the
base: it shadows no name the base finds and stores no former. -/
theorem extEta_snoc {env env' : Env} {c₀ : ConstantInfo} (hx : ExtEta env env')
    (hfresh : env.find? c₀.name = none) (hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps) :
    ExtEta env ⟨c₀ :: env'.consts⟩ := by
  refine ⟨fun n ci hf hnr => ?_, fun T cvT caps hf => ?_⟩
  · have hne : c₀.name ≠ n := fun hh => by rw [hh, hf] at hfresh; exact nomatch hfresh
    rw [ConLeche.Env.find?_cons, if_neg hne]
    exact hx.1 n ci hf hnr
  · rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · exact absurd (Option.some.inj hf) (hnotind cvT caps)
    · exact hx.2 T cvT caps hf


/-- **The recursors' conses at their MAJORS are an `ExtEta` extension**
(`consBlockRecsT`, the family the install conses), when every
recursor name is fresh at the constructors' environment. -/
theorem consBlockRecsT_extEta {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} {envC : Env} :
    ∀ {m : Nat} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env : Env},
      ExtEta envC env → (∀ r ∈ ConLeche.tgtRs out, envC.find? r.1.name = none) →
      ExtEta envC (ConLeche.consBlockRecsT find? res q m out env)
  | _, [], _, hx, _ => hx
  | m, (cv, M, rhss) :: rest, env, hx, hfr => by
    simp only [ConLeche.consBlockRecsT]
    have hfr' : ∀ r ∈ ConLeche.tgtRs ((cv, M, rhss) :: rest), envC.find? r.1.name = none := hfr
    simp only [ConLeche.tgtRs, List.map_cons, List.forall_mem_cons] at hfr'
    exact consBlockRecsT_extEta (extEta_snoc hx hfr'.1 (fun _ _ heq => nomatch heq))
      (fun r hr => hfr'.2 r hr)

/-- **The tables' phase keeps the η-families closed**: at every
structure-like member one fresh table cons, nothing at any other. -/
theorem checkBlockTables_etaClosed {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))}
      {env env₂ : Env},
      EtaFamiliesClosed env → checkBlockTables (m := ConLeche.CheckM) q l env = .ok env₂ →
      EtaFamiliesClosed env₂
  | [], env, env₂, hE, h => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hE
  | (ms, ctorsA, sortss) :: rest, env, env₂, hE, h => by
    unfold checkBlockTables at h
    obtain ⟨env', henv', h⟩ := exceptBind_ok h
    refine checkBlockTables_etaClosed ?_ h
    revert henv'
    split
    · split
      · intro hh; exact checkStructProjTable_etaClosed hh hE
      · intro hh
        simp only [pure, Except.pure, Except.ok.injEq] at hh
        exact hh ▸ hE
    · intro hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      exact hh ▸ hE

end ConLeche.Semantics
