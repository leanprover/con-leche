module

public import ConLeche.Verify.EnvGuards
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Verify.Extend.Inversions
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.GenRecRun

@[expose] public section

/-!
# The uniform install keeps the η-families closed

The declaration fold's η half at the `.indDecl` dispatch
(`declBlockRun_etaClosed`), with the stage lemmas it uses: every store
is a **fresh cons**, so `EtaFamiliesClosed.cons_nonind` applies at
every step that stores no η-claiming former.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  fueledOps checkConstantVal
  EtaFamiliesClosed ProjEntry)

/-! ## Lookups through the constructors' conses -/


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape fueledOps checkSumCtors
   consSumCtors sumRules EtaFamiliesClosed)

/-- A name none of the consed constructors carries looks up below the
conses. -/
theorem consSumCtors_find?_of_not_mem {nP : Nat} {n : Name} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      n ∉ ctorList.map (·.1.name) → (consSumCtors nP ctorList env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, hn => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [consSumCtors_find?_of_not_mem hn.2, ConLeche.Env.find?_cons, ite_eq_right (fun h => hn.1 h.symm)]


/-!
## The uniform install keeps the η-families closed, at k members

At the run `DeclBlockRun`, MODEL-FREE: the fold threads `EtaFamiliesClosed` next
to the model, so its η half must follow from the run record alone.

The install is three cons phases and the tables, and each is read at the environment
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
* the projection tables store no constant.
-/


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo IndCaps
  BlockShape BlockShape MemberShape fueledOps EtaFamiliesClosed ExtEta exceptBind_ok
  consBlockInds consBlockCtors consSumCtors consBlockRecs
  checkBlockCtors checkSumCtors blockCapsAt)

/-! ## Lookups through the formers' and the constructors' conses -/

/-- A name none of the consed formers carries reads through the
formers' conses unchanged. -/
theorem consBlockInds_find?_of_ne {p₁ : BlockShape} {isRec : Bool} {n : Name} :
    ∀ {formers : List ConstantVal} {i : Nat} {env : Env},
      (∀ cv ∈ formers, cv.name ≠ n) →
      (consBlockInds p₁ isRec formers i env).find? n = env.find? n
  | [], _, _, _ => rfl
  | cv :: rest, i, env, hne => by
    simp only [consBlockInds]
    rw [consBlockInds_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      ConLeche.Env.find?_cons]
    exact ite_eq_right (hne cv List.mem_cons_self)

/-- A name none of the consed constructors carries reads through the
constructors' conses unchanged. -/
theorem consBlockCtors_find?_of_ne {nP : Nat} {n : Name} :
    ∀ {memberCtors : List (List (ConstantVal × Nat))} {env : Env},
      (∀ ctorList ∈ memberCtors, n ∉ ctorList.map (·.1.name)) →
      (consBlockCtors nP memberCtors env).find? n = env.find? n
  | [], _, _ => rfl
  | ctorList :: rest, env, hne => by
    simp only [consBlockCtors]
    rw [consBlockCtors_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      consSumCtors_find?_of_not_mem (hne ctorList List.mem_cons_self)]

/-- The constructors' conses store no former: a `.indInfo` found above
them was found below them. -/
theorem consSumCtors_find?_indInfo {nP : Nat} {n : Name} {cv : ConstantVal} {caps : IndCaps} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP ctorList env).find? n = some (.indInfo cv caps) →
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
    ∀ {memberCtors : List (List (ConstantVal × Nat))} {env : Env},
      (consBlockCtors nP memberCtors env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps)
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consBlockCtors] at h
    exact consSumCtors_find?_indInfo (consBlockCtors_find?_indInfo h)

/-- **A consed constructor is found at its own record**, when the
member's constructor names are distinct. -/
theorem consSumCtors_find?_mem {nP : Nat} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env} {ctor : ConstantVal × Nat},
      (ctorList.map (·.1.name)).Nodup → ctor ∈ ctorList →
      (consSumCtors nP ctorList env).find? ctor.1.name = some (.ctorInfo ctor.1 nP ctor.2)
  | [], _, _, _, hc => nomatch hc
  | c :: cs, env, ctor, hnd, hc => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [consSumCtors_find?_of_not_mem hnd.1]
      exact ConLeche.Env.find?_cons_self _ _
    · exact consSumCtors_find?_mem hnd.2 hc'

/-- **A consed constructor is found at its own record** after all the
members' conses, when the block's constructor names are distinct. -/
theorem consBlockCtors_find?_mem {nP : Nat} :
    ∀ {memberCtors : List (List (ConstantVal × Nat))} {env : Env} {ctorList : List (ConstantVal × Nat)}
      {ctor : ConstantVal × Nat},
      ((memberCtors.map (·.map (·.1.name))).flatten).Nodup → ctorList ∈ memberCtors → ctor ∈ ctorList →
      (consBlockCtors nP memberCtors env).find? ctor.1.name = some (.ctorInfo ctor.1 nP ctor.2)
  | [], _, _, _, _, hl, _ => nomatch hl
  | A :: rest, env, ctorList, ctor, hnd, hl, hc => by
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

/-! ## The formers' stage: freshness -/

/-- **The k formers are consed at names fresh before the block.** -/
theorem checkBlockInds_fresh {mode : CheckMode} {env envI : Env} {p : BlockShape} {isRec : Bool}
    {p₁ : BlockShape} {F : Nat}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, p₁)) :
    ∀ cv ∈ p.formers, env.find? cv.name = none := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, h0, hcvs, -⟩ := ConLeche.checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {cv : ConstantVal} {s : Level},
      ConLeche.checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cv, s) →
      env.find? cv.name = none := by
    intro ms cv s hh
    obtain ⟨cvT, -, -, heq, hcv, -⟩ := ConLeche.checkBlockTele_shape hh
    obtain ⟨hf, -, -, -, -, -, -, -, -, -, -⟩ := ConLeche.checkConstantVal_inv hcv
    rw [heq]; exact hf
  intro cv hcv
  rw [← ConLeche.checkBlockInds_teles hm h0 hcvs] at hcv
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
    ExtEta env ⟨c₀ :: env'.consts, env'.tables⟩ := by
  refine ⟨fun n ci hf hnr => ?_, fun T cvT caps hf => ?_⟩
  · have hne : c₀.name ≠ n := fun hh => by rw [hh, hf] at hfresh; exact nomatch hfresh
    rw [ConLeche.Env.find?_cons, ite_eq_right hne]
    exact hx.1 n ci hf hnr
  · rw [ConLeche.Env.find?_cons] at hf
    split at hf
    · exact absurd (Option.some.inj hf) (hnotind cvT caps)
    · exact hx.2 T cvT caps hf


/-- **The recursors' conses at their MAJORS are an `ExtEta` extension**
(`consBlockRecsT`, the family the install conses), when every
recursor name is fresh at the constructors' environment. -/
theorem consBlockRecsT_extEta {q : BlockShape} {envC : Env} :
    ∀ {m : Nat} {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {env : Env},
      ExtEta envC env → (∀ r ∈ ConLeche.tgtRs out, envC.find? r.1.name = none) →
      ExtEta envC (ConLeche.consBlockRecsT q m out env)
  | _, [], _, hx, _ => hx
  | m, (cv, M, rhss) :: rest, env, hx, hfr => by
    simp only [ConLeche.consBlockRecsT]
    have hfr' : ∀ r ∈ ConLeche.tgtRs ((cv, M, rhss) :: rest), envC.find? r.1.name = none := hfr
    simp only [ConLeche.tgtRs, List.map_cons, List.forall_mem_cons] at hfr'
    exact consBlockRecsT_extEta (extEta_snoc hx hfr'.1 (fun _ _ heq => nomatch heq))
      (fun r hr => hfr'.2 r hr)

/-! ## The whole run -/

/-- **The uniform install keeps the η-families closed, at k members**,
from the run record alone, at every setting of both gates. -/
theorem declBlockRun_etaClosed {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockShape} (hE : EtaFamiliesClosed env)
    (hdn : ∀ m ∈ p₀.members, m.cvT.name = m.declared.name)
    (h : DeclBlockRun F env block p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hndC, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds, nfs,
    pos, st, isorts, rs, hInd, hCtors, -, -, -, -, -, -, hRec, -, -, -, hfin⟩ := h
  obtain ⟨_, _, _, _, _, -, hp₁, rfl, -, -, -⟩ := ConLeche.checkBlockInds_shape hInd
  -- the three freshness facts and the constructors' names
  have hfT := checkBlockInds_fresh hInd
  have hfC : ∀ A ∈ p₁.memberCtors, ∀ ctor ∈ A,
      (consBlockInds p₁ isRec (p₀.members.map (·.declared)) 0 env).find? ctor.1.name = none :=
    ConLeche.checkBlockCtors_fresh hCtors
  generalize hctor : p₁.memberCtors = memberCtors at hfin hfC
  have hnames : memberCtors.map (·.map (fun ctor => (ctor.1.name, ctor.2)))
      = p₁.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
    rw [← hctor]
    show (p₁.members.map (·.ctors)).map _ = _
    rw [List.map_map]
    rfl
  have hndAll : ((memberCtors.map (·.map (·.1.name))).flatten).Nodup := by
    have hmap : memberCtors.map (·.map (·.1.name))
        = p₁.members.map (fun ms => ms.ctors.map (·.1.name)) := by
      have := congrArg (List.map (List.map Prod.fst)) hnames
      simpa [List.map_map, Function.comp_def] using this
    have hall : p₁.allCtors = p₀.allCtors := by
      rw [hp₁]; rfl
    rw [hmap]
    have : p₁.allCtors.map (·.1.name)
        = (p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten := by
      rw [ConLeche.BlockShape.allCtors, List.map_flatten, List.map_map]
      rfl
    rw [← this, hall]
    exact hndC
  -- ## the constructors' environment is closed
  have hEC : EtaFamiliesClosed (consBlockCtors p₁.nP memberCtors
      (consBlockInds p₁ isRec (p₀.members.map (·.declared)) 0 env)) := by
    intro T cvT caps hf he hr
    have hf₁ := consBlockCtors_find?_indInfo hf
    rcases ConLeche.find?_consBlockInds_indInfo hf₁ with ⟨j, hj, -, hcaps⟩ | hf₀
    · -- a member of the block: its one constructor is stored
      subst hcaps
      rw [Nat.zero_add] at he ⊢
      have hjl : j < p₁.members.length := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.length_map] at this
        rw [ConLeche.checkBlockInds_members hInd]
        exact this
      have hgetD : p₁.members.getD j default = p₁.members[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
      have hj' : (memberCtors.map (·.map (fun ctor => (ctor.1.name, ctor.2))))[j]?
          = some (p₁.members[j].ctors.map (fun c => (c.1.name, c.2))) := by
        rw [hnames, List.getElem?_map, List.getElem?_eq_getElem hjl]; rfl
      rw [List.getElem?_map] at hj'
      obtain ⟨ctorList, hctor, hcAeq⟩ := Option.map_eq_some_iff.mp hj'
      match hcs : p₁.members[j].ctors with
      | [c] =>
        rw [hcs] at hcAeq
        match ctorList, hcAeq with
        | [ctor], hcAeq =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
            and_true] at hcAeq
          refine ⟨ctor.1, ?_⟩
          rw [blockCapsAt, hgetD, hcs]
          show (consBlockCtors p₁.nP memberCtors (consBlockInds p₁ isRec (p₀.members.map (·.declared)) 0 env)).find? c.1.name
            = some (.ctorInfo ctor.1 p₁.nP c.2)
          rw [← hcAeq.1, ← hcAeq.2]
          exact consBlockCtors_find?_mem hndAll (List.mem_of_getElem? hctor) List.mem_cons_self
        | [], hcAeq => simp at hcAeq
        | _ :: _ :: _, hcAeq => simp at hcAeq
      | [] => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
      | _ :: _ :: _ => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
    · -- a family stored before the block: its η constructor reads through
      obtain ⟨cvC, hfC₀⟩ := hE T cvT caps hf₀ he hr
      refine ⟨cvC, ?_⟩
      have hf₁C : (consBlockInds p₁ isRec (p₀.members.map (·.declared)) 0 env).find? caps.etaCtor
          = some (.ctorInfo cvC caps.etaParams caps.etaFields) := by
        rw [consBlockInds_find?_of_ne]
        · exact hfC₀
        · intro cv hcv hh
          obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hcv
          have := hfT m.cvT (List.mem_map_of_mem hm)
          rw [hdn m hm, hh, hfC₀] at this
          exact nomatch this
      rw [consBlockCtors_find?_of_ne]
      · exact hf₁C
      · intro A hA hmem
        obtain ⟨ctor, hctor, hn⟩ := List.mem_map.mp hmem
        have := hfC A hA ctor hctor
        rw [hn, hf₁C] at this
        exact nomatch this
  -- ## the recursors (at their majors), then the tables
  have hfresh := ConLeche.genRecCheck_out_fresh hRec
  rw [hctor] at hfresh
  subst hfin
  -- the tables store no constant
  show EtaFamiliesClosed ⟨(consBlockRecsT _ _ _ _).consts, _⟩
  refine EtaFamiliesClosed.keep hEC (consBlockRecsT_extEta (ExtEta.refl _) fun r hr => ?_)
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
  obtain ⟨g, hg, hn, -⟩ := ConLeche.mem_streamRecs ho
  rw [hn]
  exact hfresh g hg

/-- **A block's run keeps the η-families closed.** -/
theorem blockRun_etaClosed {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockShape} (hE : EtaFamiliesClosed env)
    (h : BlockRun F env block p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨ms, -, hAt, -, hR⟩ := h
  exact declBlockRun_etaClosed hE (fun m hm => (hAt m hm).name) hR

end ConLeche.Semantics
