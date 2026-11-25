module

public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The graph route at the GENERATED recursor family (G1)

The generated recursor stage (`Kernel/Inductives/GenRec.lean`) GENERATES
the recursor family: per recursor `c` a type
`Π (prefix) (ı⃗ : index domains) (t : I D⃗ ı⃗), motive_c ı⃗ t` whose
prefix (parameters, motives, minors) is shared, and per constructor a
rule `λ prefix f⃗, minor f⃗ (λ a⃗, rec_t prefix e⃗ (f a⃗))…`.  The recursor
model's producer `graphRecPre_core` (`BlockRecGraph.lean`) is generic in
the family's classes (`Is`, `Cr`, `injX`, the index tuple, the decoding
`fit`, the calls) and asks rows of them.  Read off the GENERATED family,
most rows hold BY CONSTRUCTION — this file chooses the classes so:

* **the majors are the generated type's own readings**: a class's index
  set is the index-tuple set of the type's index domains
  (`genIs`), its carrier at an index tuple the major domain's reading
  (`genCr`).  So the type split (`hsplit`) and the conclusion
  (`hconcl`) are the type's reading, nothing else;
* **a decoding's fit is the rule's own binder fit** (`genFit`): the
  fields fit the rule's field domains and the index tuple is the
  constructor's index expressions' reading.  So `hspF` and `hdec`'s fit
  half are definitional;
* **the calls are the generated `ih`s' own** (`genCall`, over the
  generator's call relation `callAt`: an `ih` of callee `t` at a
  telescope spine), and the graph's `ih` values are the `ih` terms read
  at the chain valuation `genF g` — every recursor the λ-tower reading
  the graph `g` at its tagged major.  So `hchain` is the `ih` terms'
  CHAIN READING (`hihRead`: an `ih` term reads the chain only at its
  calls' spines) and the calls' typing (`hcallTy`: a call's spine fits
  its callee's type) — no K.53′, no call tie, no node landing: the
  callee is literally the class the generator used.

What is left as premises is what no construction gives:
* the CONSTRUCTOR's typing at the class (`hctorTy`: the rule's own
  spine fits the recursor type — the class side's T3′) and its
  parameter-blind reading (`hmk`: the model's constructor value);
* the rows' independence of the chain frame (`hchI`: the prefix and
  field domains, index expressions and fired spine name no recursor —
  syntactic, the generated terms mention the recursors only in the
  `ih`s);
* the index telescope's grading (`hIdx`), the family's level (`hbits`),
  and the kit's typing, uniqueness and induction rows, passed through
  (`hconclTy`; `hstep`, the step's typing — at the generated rule the
  minor premise's own type, §0; `huniq`; `hind`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

open ConLeche (CheckMode Env Expr Name Level ConstantVal)

universe w

variable {V : Type w} [SetTheory V]


/-! ## 0′. First-order encoding of `(c, j, fs)` and motive definability -/

section EncDec

/-- First-order list encoding over `V`: `[] ↦ ∅`, `a :: as ↦ ⟨pt, ⟨a, enc as⟩⟩`. -/
@[expose] noncomputable def listEnc : List V → V
  | [] => empty
  | a :: as => kpair pt (kpair a (listEnc as))

/-- Fixed-length inverse to `listEnc` via `kp1`/`kp2`. -/
@[expose] noncomputable def listDec : Nat → V → List V
  | 0, _ => []
  | n + 1, v => kp1 (kp2 v) :: listDec n (kp2 (kp2 v))

/-- First-order decoding encoding `(c, j, fs) ↦ ⟨vnat c, ⟨vnat j, listEnc fs⟩⟩`. -/
@[expose] noncomputable def decEnc (c j : Nat) (fs : List V) : V :=
  kpair (vnat c) (kpair (vnat j) (listEnc fs))

theorem listEnc_ne_empty {a : V} {as : List V} : listEnc (a :: as) ≠ empty := by
  intro h
  have h1 : (sing pt : V) ∈ˢ kpair pt (kpair a (listEnc as)) := by
    unfold kpair; exact mem_upair_left _ _
  rw [listEnc] at h
  rw [h] at h1
  exact not_mem_empty _ h1

theorem listEnc_inj : ∀ {xs ys : List V}, listEnc xs = listEnc ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h.symm listEnc_ne_empty
  | _ :: _, [], h => absurd h listEnc_ne_empty
  | x :: xs, y :: ys, h => by
    simp only [listEnc] at h
    obtain ⟨_, h2⟩ := kpair_inj h
    obtain ⟨rfl, h3⟩ := kpair_inj h2
    exact congrArg (x :: ·) (listEnc_inj h3)

theorem listDec_listEnc : ∀ fs : List V, listDec fs.length (listEnc fs) = fs
  | [] => rfl
  | a :: fs => by
    simp only [List.length_cons, listDec, listEnc, kp2_kpair, kp1_kpair]
    exact congrArg (a :: ·) (listDec_listEnc fs)

theorem listDec_length : ∀ (n : Nat) (v : V), (listDec n v).length = n
  | 0, _ => rfl
  | n + 1, v => congrArg Nat.succ (listDec_length n (kp2 (kp2 v)))

theorem decEnc_inj {c j c' j' : Nat} {fs fs' : List V}
    (h : decEnc c j fs = decEnc c' j' fs') : c = c' ∧ j = j' ∧ fs = fs' := by
  unfold decEnc at h
  obtain ⟨hc, h2⟩ := kpair_inj h
  obtain ⟨hj, hfs⟩ := kpair_inj h2
  exact ⟨vnat_inj hc, vnat_inj hj, listEnc_inj hfs⟩

theorem listDec_eq_ofFn (n : Nat) (v : V) :
    listDec n v = List.ofFn fun i : Fin n => (listDec n v).getD i.val empty := by
  apply List.ext_getElem
  · simp [listDec_length]
  · intro i h1 h2
    have hi : i < n := by simpa [listDec_length] using h1
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, Option.getD_some]

theorem defFun_listEnc : ∀ n : Nat,
    DefFun (V := V) n fun xs : Fin n → V => listEnc (List.ofFn xs)
  | 0 => DefFun.empty.congr fun xs => by rw [List.ofFn_zero]; rfl
  | n + 1 =>
    (DefFun.kpair_apply DefFun.pt
      (DefFun.kpair_apply (DefFun.proj 0)
        ((defFun_listEnc n).reIndex Fin.succ))).congr fun xs => by
      rw [List.ofFn_succ]; rfl

theorem defFun_decEnc (c j n : Nat) :
    DefFun (V := V) n fun xs : Fin n → V => decEnc c j (List.ofFn xs) :=
  DefFun.kpair_apply (DefFun.const (vnat c))
    (DefFun.kpair_apply (DefFun.const (vnat j)) (defFun_listEnc n))

theorem defFun_listDec_getD {p : Nat} : ∀ (n i : Nat) (_hi : i < n)
    {W : (Fin p → V) → V} (_hW : DefFun p W),
    DefFun p fun v => (listDec n (W v)).getD i empty
  | 0, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | _ + 1, 0, _, _, hW => (DefFun.kp1_apply (DefFun.kp2_apply hW)).congr fun _ => rfl
  | n + 1, i + 1, hi, _W, hW =>
    (defFun_listDec_getD n i (Nat.lt_of_succ_lt_succ hi)
      (DefFun.kp2_apply (DefFun.kp2_apply hW))).congr fun _ => rfl

theorem defRel_exists_lt {p : Nat} : ∀ (k : Nat)
    {P : (c : Nat) → c < k → (Fin p → V) → Prop},
    (∀ c (hc : c < k), DefRel p (P c hc)) →
    DefRel p fun env => ∃ c, ∃ hc : c < k, P c hc env
  | 0, _, _ => (DefRel.false (V := V)).congr fun _ =>
    ⟨False.elim, by rintro ⟨c, hc, _⟩; exact absurd hc (Nat.not_lt_zero c)⟩
  | k + 1, P, hP => by
    have hprev : DefRel p fun env => ∃ c, ∃ hc : c < k, P c (Nat.lt_succ_of_lt hc) env :=
      defRel_exists_lt k (fun c hc => hP c (Nat.lt_succ_of_lt hc))
    exact (hprev.or (hP k (Nat.lt_succ_self k))).congr fun env => by
      constructor
      · rintro (⟨c, hc, h⟩ | h)
        · exact ⟨c, Nat.lt_succ_of_lt hc, h⟩
        · exact ⟨k, Nat.lt_succ_self k, h⟩
      · rintro ⟨c, hc, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
        · exact Or.inl ⟨c, hc', h⟩
        · exact Or.inr h

private theorem isOfW_length (u nIdx : Nat) (t : V) :
    (isOfW u nIdx t).length = nIdx := by
  unfold isOfW; split <;> simp [projList_length]

private theorem isOfW_getElem {u nIdx : Nat} {t : V} {l : Nat} (hl : l < nIdx) :
    (isOfW u nIdx t)[l]'(by rw [isOfW_length]; exact hl) =
      if u = 0 then pt else projS l t := by
  unfold isOfW
  split
  · simp
  · exact projList_get nIdx l t hl

private theorem consList_eq_prepend_blockMot {n nIdx : Nat}
    (xsVec : Fin n → V) (is : List V) (his : is.length = nIdx) (x : V) (ρ : Nat → V) :
    consList (revList xsVec ++ (is ++ [x])) ρ =
      ConLeche.Semantics.prepend (fun k : Fin (1 + nIdx + n) =>
        if hk0 : k.val = 0 then x
        else if hk1 : k.val < 1 + nIdx then
          is[nIdx - 1 - (k.val - 1)]'(by omega)
        else xsVec ⟨k.val - (1 + nIdx), by omega⟩) ρ := by
  have his1 : (is ++ [x]).length = 1 + nIdx := by simp [his]; omega
  have hrev : (revList xsVec).length = n := by simp [revList]
  funext q
  by_cases hq0 : q = 0
  · subst hq0
    rw [consList_append, consList_append, consList_cons, consList_nil]
    simp [ConLeche.Semantics.prepend, cons]
  · by_cases hq1 : q < 1 + nIdx
    · have hlt : q < (is ++ [x]).length := by omega
      rw [consList_append, consList_getD_of_lt _ _ _ hlt]
      simp only [ConLeche.Semantics.prepend, show q < 1 + nIdx + n by omega, ↓reduceDIte, hq0, hq1]
      have hsub : (is ++ [x]).length - 1 - q = nIdx - 1 - (q - 1) := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getElem_append_left (by omega)]
      simp only [hsub]
    · by_cases hq2 : q < 1 + nIdx + n
      · have hLhs : consList (revList xsVec ++ (is ++ [x])) ρ q =
            (revList xsVec).getD ((revList xsVec).length - 1 - (q - (is ++ [x]).length)) pt := by
          rw [consList_append, show q = (q - (is ++ [x]).length) + (is ++ [x]).length by omega,
            consList_apply_add, consList_getD_of_lt _ _ _ (by omega)]
          congr 1; omega
        rw [hLhs]
        simp only [ConLeche.Semantics.prepend, hq2, ↓reduceDIte, hq0, hq1]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp only [revList, List.getElem_ofFn]
        have hiEq : n - 1 - ((revList xsVec).length - 1 - (q - (is ++ [x]).length)) =
            q - (1 + nIdx) := by
          rw [hrev, his1]; omega
        exact congrArg (fun idx : Fin n => xsVec idx) (Fin.ext hiEq)
      · have hLhs : consList (revList xsVec ++ (is ++ [x])) ρ q = ρ (q - (1 + nIdx + n)) := by
          rw [consList_append, show q = (q - (is ++ [x]).length) + (is ++ [x]).length by omega,
            consList_apply_add,
            show q - (is ++ [x]).length =
              (q - (is ++ [x]).length - (revList xsVec).length) + (revList xsVec).length by omega,
            consList_apply_add]
          congr 1; omega
        rw [hLhs]
        simp only [ConLeche.Semantics.prepend, hq2, ↓reduceDIte]

@[expose] noncomputable def blockRecMotBranch (K : Nat) (concl : Nat → Term)
    (uOf nIdxOf : Nat → Nat) (ρ : Nat → V) (xs : List V) (u : V) : Nat → V
  | 0 => interp V (consList (xs ++ (isOfW (uOf 0) (nIdxOf 0) pt ++ [pt])) ρ) (concl 0)
  | c + 1 =>
    open Classical in
    if ∃ i x, u = tagged c i x then
      interp V (consList (xs ++ (isOfW (uOf c) (nIdxOf c) (kp1 (kp2 u)) ++ [kp2 (kp2 u)])) ρ)
        (concl c)
    else blockRecMotBranch K concl uOf nIdxOf ρ xs u c

private theorem blockRecMotBranch_tagged_aux (K : Nat) (concl : Nat → Term)
    (uOf nIdxOf : Nat → Nat) (ρ : Nat → V) (xs : List V) {c : Nat} (i x : V) :
    ∀ k, c < k → k ≤ K →
      blockRecMotBranch K concl uOf nIdxOf ρ xs (tagged c i x) k =
        blockRecMot K concl uOf nIdxOf ρ xs (tagged c i x)
  | 0, hc, _ => absurd hc (Nat.not_lt_zero c)
  | c' + 1, hc, hle => by
    unfold blockRecMotBranch
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | rfl
    · have hno : ¬ ∃ i' x', tagged c i x = tagged c' i' x' := by
        rintro ⟨i', x', h⟩
        exact absurd (tagged_inj h).1 (Nat.ne_of_lt hlt)
      simp only [hno, ↓reduceIte]
      exact blockRecMotBranch_tagged_aux K concl uOf nIdxOf ρ xs i x c' hlt (by omega)
    · have htag : ∃ i' x', tagged c i x = tagged c i' x' := ⟨i, x, rfl⟩
      split
      · simp only [tagged, kp2_kpair, kp1_kpair]
        exact (blockRecMot_tagged (V := V) (K := K) (c := c) (by omega)).symm
      · contradiction

theorem blockRecMotBranch_tagged {K c : Nat} (hc : c < K) (concl : Nat → Term)
    (uOf nIdxOf : Nat → Nat) (ρ : Nat → V) (xs : List V) (i x : V) :
    blockRecMotBranch K concl uOf nIdxOf ρ xs (tagged c i x) K =
      blockRecMot K concl uOf nIdxOf ρ xs (tagged c i x) :=
  blockRecMotBranch_tagged_aux K concl uOf nIdxOf ρ xs i x K hc (Nat.le_refl K)

theorem defFun_blockRecMotBranch_param (K : Nat) (concl : Nat → Term) (uOf nIdxOf : Nat → Nat)
    (ρ : Nat → V) (n : Nat) :
    DefFun (V := V) (n + 1) fun v =>
      blockRecMotBranch K concl uOf nIdxOf ρ (revList (ftail v)) (v 0) K := by
  have branchFn : ∀ k : Nat, DefFun (V := V) (n + 1) fun v =>
      blockRecMotBranch K concl uOf nIdxOf ρ (revList (ftail v)) (v 0) k := by
    intro k
    induction k with
    | zero =>
      have h0 : DefFun (n + 1) fun v =>
          interp V (consList (revList (ftail v) ++ (isOfW (uOf 0) (nIdxOf 0) pt ++ [pt])) ρ)
            (concl 0) := by
        let Gs0 : Fin (1 + nIdxOf 0 + n) → (Fin (n + 1) → V) → V := fun k v =>
          if hk0 : k.val = 0 then pt
          else if hk1 : k.val < 1 + nIdxOf 0 then
            (isOfW (uOf 0) (nIdxOf 0) pt)[nIdxOf 0 - 1 - (k.val - 1)]'(by
              rw [isOfW_length]; omega)
          else (ftail v) ⟨k.val - (1 + nIdxOf 0), by omega⟩
        have hGs0 : ∀ k, DefFun (n + 1) (Gs0 k) := fun k => by
          dsimp only [Gs0]
          split
          · exact DefFun.pt
          · split
            · exact DefFun.const _
            · exact (DefFun.proj ⟨(k.val - (1 + nIdxOf 0)) + 1, by omega⟩).congr fun _ => rfl
        refine ((interp_defFun_prepend ρ (1 + nIdxOf 0 + n) (concl 0)).comp hGs0).congr
          fun v => ?_
        rw [consList_eq_prepend_blockMot (ftail v) (isOfW (uOf 0) (nIdxOf 0) pt)
          (isOfW_length _ _ _) pt ρ]
      exact h0
    | succ c ih =>
      have hTag : DefRel (n + 1) fun v => ∃ i x : V, v 0 = tagged c i x := by
        have hRel0 : DefRel (((n + 1) + 1) + 1) fun w =>
            w ⟨2, by omega⟩ = tagged c (w ⟨1, by omega⟩) (w ⟨0, by omega⟩) :=
          DefRel.eq_apply (V := V) (DefFun.proj (V := V) ⟨2, by omega⟩)
            (DefFun.tagged_apply (V := V) c (DefFun.proj (V := V) ⟨1, by omega⟩)
              (DefFun.proj (V := V) ⟨0, by omega⟩))
        have hRel1 : DefRel ((n + 1) + 1) fun u => ∃ x : V, u ⟨1, by omega⟩ = tagged c (u ⟨0, by omega⟩) x := by
          refine DefRel.exists_curry (R := fun x u => u ⟨1, by omega⟩ = tagged c (u ⟨0, by omega⟩) x)
            (hRel0.congr fun w => ?_)
          have hw0 : w ⟨0, by omega⟩ = w 0 := rfl
          have hw1 : w ⟨1, by omega⟩ = ftail w ⟨0, by omega⟩ := rfl
          have hw2 : w ⟨2, by omega⟩ = ftail w ⟨1, by omega⟩ := rfl
          rw [hw0, hw1, hw2]
        refine DefRel.exists_curry (R := fun i v => ∃ x : V, v 0 = tagged c i x)
          (hRel1.congr fun u => ?_)
        refine exists_congr fun x => ?_
        have hu0 : u ⟨0, by omega⟩ = u 0 := rfl
        have hu1 : u ⟨1, by omega⟩ = ftail u 0 := rfl
        rw [hu0, hu1]
      have hBody : DefFun (n + 1) fun v =>
          interp V (consList (revList (ftail v) ++
            (isOfW (uOf c) (nIdxOf c) (kp1 (kp2 (v 0))) ++ [kp2 (kp2 (v 0))])) ρ) (concl c) := by
        let GsC : Fin (1 + nIdxOf c + n) → (Fin (n + 1) → V) → V := fun k v =>
          if hk0 : k.val = 0 then kp2 (kp2 (v 0))
          else if hk1 : k.val < 1 + nIdxOf c then
            if uOf c = 0 then pt
            else projS (nIdxOf c - 1 - (k.val - 1)) (kp1 (kp2 (v 0)))
          else (ftail v) ⟨k.val - (1 + nIdxOf c), by omega⟩
        have hGsC : ∀ k, DefFun (n + 1) (GsC k) := fun k => by
          dsimp only [GsC]
          split
          · exact DefFun.kp2_apply (DefFun.kp2_apply (DefFun.proj 0))
          · split
            · split
              · exact DefFun.pt
              · exact DefFun.projS_apply _ (DefFun.kp1_apply (DefFun.kp2_apply (DefFun.proj 0)))
            · exact (DefFun.proj ⟨(k.val - (1 + nIdxOf c)) + 1, by omega⟩).congr fun _ => rfl
        refine ((interp_defFun_prepend ρ (1 + nIdxOf c + n) (concl c)).comp hGsC).congr
          fun v => ?_
        rw [consList_eq_prepend_blockMot (ftail v)
          (isOfW (uOf c) (nIdxOf c) (kp1 (kp2 (v 0)))) (isOfW_length _ _ _) (kp2 (kp2 (v 0))) ρ]
        have hpre :
            ConLeche.Semantics.prepend (fun i : Fin (1 + nIdxOf c + n) => GsC i v) ρ =
              ConLeche.Semantics.prepend (fun k : Fin (1 + nIdxOf c + n) =>
                if hk0 : k.val = 0 then kp2 (kp2 (v 0))
                else if hk1 : k.val < 1 + nIdxOf c then
                  (isOfW (uOf c) (nIdxOf c) (kp1 (kp2 (v 0))))[nIdxOf c - 1 - (k.val - 1)]'(by
                    rw [isOfW_length]; omega)
                else (ftail v) ⟨k.val - (1 + nIdxOf c), by omega⟩) ρ := by
          congr 1
          funext k
          dsimp only [GsC]
          split
          · rfl
          · split
            · exact (isOfW_getElem (by omega)).symm
            · rfl
        rw [hpre]
      exact (DefFun.ite hTag hBody ih).congr fun _ => by
        dsimp only [blockRecMotBranch]
  exact branchFn K

theorem defFun_blockRecMotBranch_const (K : Nat) (concl : Nat → Term) (uOf nIdxOf : Nat → Nat)
    (ρ : Nat → V) (xs : List V) :
    DefFun (V := V) 1 fun v => blockRecMotBranch K concl uOf nIdxOf ρ xs (v 0) K := by
  let Gs : Fin (xs.length + 1) → (Fin 1 → V) → V := fun l v =>
    if hl : l.val = 0 then v 0 else xs.reverse[l.val - 1]'(by simp; omega)
  have hGs : ∀ j, DefFun 1 (Gs j) := fun l => by
    dsimp only [Gs]
    split
    · exact DefFun.proj 0
    · exact DefFun.const _
  refine ((defFun_blockRecMotBranch_param K concl uOf nIdxOf ρ xs.length).comp hGs).congr
    fun v => ?_
  have hrev : revList (ftail (fun j : Fin (xs.length + 1) => Gs j v)) = xs := by
    have htail : ftail (fun j : Fin (xs.length + 1) => Gs j v) =
        fun i : Fin xs.length => xs.reverse[i.val] := by
      funext ⟨i, hi⟩
      simp [ftail, Gs]
    rw [htail]
    apply List.ext_getElem
    · simp [revList]
    · intro i h1 h2
      simp only [revList, List.getElem_ofFn, List.getElem_reverse]
      congr 1; omega
  have hv0 : (fun i => Gs i v) 0 = v 0 := by simp [Gs]
  rw [hrev, hv0]

/-- Finite constructor dispatcher over `j < m` for `d : V` matching `⟨vnat c, ⟨vnat j, fs⟩⟩`. -/
@[expose] noncomputable def decSwitchJ (c : Nat) (fLen : Nat → Nat)
    (body : Nat → List V → V) : Nat → V → V
  | 0, _ => empty
  | m + 1, d =>
    open Classical in
    if kp1 d = vnat c ∧ kp1 (kp2 d) = vnat m then
      body m (listDec (fLen m) (kp2 (kp2 d)))
    else decSwitchJ c fLen body m d

/-- Finite class+constructor dispatcher over `c < K`, `j < nCt c`. -/
@[expose] noncomputable def decSwitch (nCt : Nat → Nat) (fLen : Nat → Nat → Nat)
    (body : Nat → Nat → List V → V) : Nat → V → V
  | 0, _ => empty
  | c + 1, d =>
    open Classical in
    if kp1 d = vnat c then
      decSwitchJ c (fLen c) (body c) (nCt c) d
    else decSwitch nCt fLen body c d

theorem decSwitchJ_decEnc (c : Nat) (fLen : Nat → Nat) (body : Nat → List V → V)
    {j : Nat} {fs : List V} (hfs : fs.length = fLen j) :
    ∀ m, j < m → decSwitchJ c fLen body m (decEnc c j fs) = body j fs
  | 0, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, hj => by
    unfold decSwitchJ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · have hne : kp1 (kp2 (decEnc c j fs)) ≠ vnat m := by
        simp only [decEnc, kp2_kpair, kp1_kpair]
        intro h
        exact absurd (vnat_inj h) (Nat.ne_of_lt hlt)
      have hnot : ¬ (kp1 (decEnc c j fs) = vnat c ∧ kp1 (kp2 (decEnc c j fs)) = vnat m) :=
        fun h => hne h.2
      simp only [hnot, ↓reduceIte]
      exact decSwitchJ_decEnc c fLen body hfs m hlt
    · have heq : kp1 (decEnc c j fs) = vnat c ∧ kp1 (kp2 (decEnc c j fs)) = vnat j := by
        simp [decEnc, kp1_kpair, kp2_kpair]
      simp only [heq, and_self, ↓reduceIte]
      simp only [decEnc, kp2_kpair, ← hfs, listDec_listEnc]

theorem decSwitch_decEnc (nCt : Nat → Nat) (fLen : Nat → Nat → Nat)
    (body : Nat → Nat → List V → V) {c j : Nat} {fs : List V}
    (hj : j < nCt c) (hfs : fs.length = fLen c j) :
    ∀ k, c < k → decSwitch nCt fLen body k (decEnc c j fs) = body c j fs
  | 0, hc => absurd hc (Nat.not_lt_zero c)
  | k + 1, hc => by
    unfold decSwitch
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | rfl
    · have hne : kp1 (decEnc c j fs) ≠ vnat k := by
        simp only [decEnc, kp1_kpair]
        intro h
        exact absurd (vnat_inj h) (Nat.ne_of_lt hlt)
      simp only [hne, ↓reduceIte]
      exact decSwitch_decEnc nCt fLen body hj hfs k hlt
    · have heq : kp1 (decEnc c j fs) = vnat c := by simp [decEnc, kp1_kpair]
      simp only [heq, ↓reduceIte]
      exact decSwitchJ_decEnc c (fLen c) (body c) hfs (nCt c) hj

theorem defFun_decSwitchJ {p : Nat} (c : Nat) (fLen : Nat → Nat)
    (body : Nat → List V → (Fin p → V) → V)
    {D : (Fin p → V) → V} (hD : DefFun p D)
    (m : Nat)
    (hbody : ∀ j, j < m →
      DefFun p fun v => body j (listDec (fLen j) (kp2 (kp2 (D v)))) v) :
    DefFun p fun v => decSwitchJ c fLen (fun j fs => body j fs v) m (D v) := by
  induction m with
  | zero => exact DefFun.empty
  | succ m ih =>
    have hcond : DefRel p fun v => kp1 (D v) = vnat c ∧ kp1 (kp2 (D v)) = vnat m :=
      (DefRel.eq_apply (DefFun.kp1_apply hD) (DefFun.const (vnat c))).and
        (DefRel.eq_apply (DefFun.kp1_apply (DefFun.kp2_apply hD)) (DefFun.const (vnat m)))
    exact (DefFun.ite hcond (hbody m (Nat.lt_succ_self m))
      (ih fun j hj => hbody j (Nat.lt_succ_of_lt hj))).congr fun _ => by
      dsimp only [decSwitchJ]; split <;> rfl

theorem defFun_decSwitch {p : Nat} (nCt : Nat → Nat) (fLen : Nat → Nat → Nat)
    (body : Nat → Nat → List V → (Fin p → V) → V)
    {D : (Fin p → V) → V} (hD : DefFun p D)
    (k : Nat)
    (hbody : ∀ c, c < k → ∀ j, j < nCt c →
      DefFun p fun v => body c j (listDec (fLen c j) (kp2 (kp2 (D v)))) v) :
    DefFun p fun v => decSwitch nCt fLen (fun c j fs => body c j fs v) k (D v) := by
  induction k with
  | zero => exact DefFun.empty
  | succ k ih =>
    have hcond : DefRel p fun v => kp1 (D v) = vnat k :=
      DefRel.eq_apply (DefFun.kp1_apply hD) (DefFun.const (vnat k))
    exact (DefFun.ite hcond
      (defFun_decSwitchJ k (fLen k) (body k) hD (nCt k) (hbody k (Nat.lt_succ_self k)))
      (ih fun c hc => hbody c (Nat.lt_succ_of_lt hc))).congr fun _ => by
      dsimp only [decSwitch]

end EncDec

/-! ## 0. The graph producer over a STEP premise

The generated stage infers the generated rule WHOLE (`classRuleOk`).
At the generated family the step's typing is the minor premise's own
type (a minor applied to the fields and the `ih` values lands in the
motive at the constructor), so the producer (`graphRecPre_coreR`) is
stated over the kit's step fact itself (`hstep`). -/

section CoreR

variable {ℓ K : Nat} {ρ : Nat → V} {nCt rP : Nat → Nat}
  {concl : Nat → Term} {pdoms : Nat → List Term} {fdoms : Nat → Nat → List Term}
  {Rb0 : Nat → Nat → Term} {ihv : List V → Nat → Nat → List V → V → List V}
  {call : List V → Nat → Nat → List V → V → Prop}

/-- Set-encoded `graphDecG` over `c < K`, `j < nCt c`, and `fs` of length `fLen c j`. -/
@[expose] def graphDecV (Is : List V → Nat → V) (injX : Nat → Nat → List V → V)
    (nCt : Nat → Nat) (fLen : Nat → Nat → Nat) (K : Nat)
    (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V) (u d : V) : Prop :=
  ∃ c, c < K ∧ ∃ j, j < nCt c ∧ ∃ fsVec : Fin (fLen c j) → V,
    d = decEnc c j (List.ofFn fsVec) ∧
    graphDecG Is injX nCt K fit xs u (c, j, List.ofFn fsVec)

theorem graphDecV_decEnc {Is : List V → Nat → V} {injX : Nat → Nat → List V → V}
    {fLen : Nat → Nat → Nat} {fit : List V → Nat → V → Nat → List V → Prop}
    {xs : List V} {u : V} {c j : Nat} {fs : List V}
    (hfs : fs.length = fLen c j) :
    graphDecV Is injX nCt fLen K fit xs u (decEnc c j fs) ↔
      graphDecG Is injX nCt K fit xs u (c, j, fs) := by
  constructor
  · rintro ⟨c', hc', j', hj', fsVec, hd, hdec⟩
    obtain ⟨rfl, rfl, hlist⟩ := decEnc_inj hd
    rwa [hlist]
  · intro hdec
    have hc : c < K := hdec.1
    have hj : j < nCt c := hdec.2.1
    let fsVec : Fin (fLen c j) → V := fun i => fs[i.val]'(by omega)
    have hof : List.ofFn fsVec = fs := by
      apply List.ext_getElem <;> simp [fsVec, hfs]
    exact ⟨c, hc, j, hj, fsVec, by rw [hof], by rw [hof]; exact hdec⟩

/-- First-order predecessor set on encoded decodings `d : V`. -/
@[expose] noncomputable def graphPredV (Is Cr : List V → Nat → V) (K : Nat)
    (nCt : Nat → Nat) (fLen : Nat → Nat → Nat)
    (call : List V → Nat → Nat → List V → V → Prop)
    (hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs))
    (xs : List V) (d : V) : V :=
  decSwitch nCt fLen (fun c j fs => graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs)) K d

theorem graphPredV_decEnc {Is Cr : List V → Nat → V} {fLen : Nat → Nat → Nat}
    {hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs)}
    {xs : List V} {c j : Nat} (hc : c < K) (hj : j < nCt c)
    {fs : List V} (hfs : fs.length = fLen c j) :
    graphPredV Is Cr K nCt fLen call hSep xs (decEnc c j fs) =
      graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs) :=
  decSwitch_decEnc nCt fLen _ hj hfs K hc

/-- First-order step function on encoded decodings `d : V`. -/
@[expose] noncomputable def graphStV (ρ : Nat → V) (Rb0 : Nat → Nat → Term)
    (ihv : List V → Nat → Nat → List V → V → List V)
    (K : Nat) (nCt : Nat → Nat) (fLen : Nat → Nat → Nat)
    (xs : List V) (d g : V) : V :=
  decSwitch nCt fLen (fun c j fs => blockGraphStep ρ Rb0 ihv xs (c, j, fs) g) K d

theorem graphStV_decEnc {fLen : Nat → Nat → Nat}
    {xs : List V} {c j : Nat} (hc : c < K) (hj : j < nCt c)
    {fs : List V} (hfs : fs.length = fLen c j) (g : V) :
    graphStV ρ Rb0 ihv K nCt fLen xs (decEnc c j fs) g =
      blockGraphStep ρ Rb0 ihv xs (c, j, fs) g :=
  decSwitch_decEnc nCt fLen _ hj hfs K hc

private theorem defRel_graphDecV_param {Is : List V → Nat → V} {injX : Nat → Nat → List V → V}
    {fLen : Nat → Nat → Nat} {fit : List V → Nat → V → Nat → List V → Prop} {n : Nat}
    (hIs : ∀ c, c < K → DefFun n fun xsVec : Fin n → V => Is (revList xsVec) c)
    (hinj : ∀ c, c < K → ∀ j, j < nCt c → DefFun (fLen c j) fun fs => injX c j (List.ofFn fs))
    (hfit : ∀ c, c < K → ∀ j, j < nCt c →
      DefRel ((fLen c j + 1) + n) fun v =>
        fit (revList (fdrop (k := fLen c j + 1) (p := n) v)) c
          ((ftake (k := fLen c j + 1) (p := n) v) 0) j
          (List.ofFn (ftail (ftake (k := fLen c j + 1) (p := n) v)))) :
    DefRel (n + 2) fun v => graphDecV Is injX nCt fLen K fit (revList (ftail (ftail v))) (v 0) (v 1) := by
  refine (defRel_exists_lt K fun c hc => defRel_exists_lt (nCt c) fun j hj => ?_).congr fun v => by
    simp only [graphDecV]
    exact exists_congr fun c => ⟨fun ⟨hc, j, hj, h⟩ => ⟨hc, j, hj, h⟩,
      fun ⟨hc, j, hj, h⟩ => ⟨hc, j, hj, h⟩⟩
  let m := fLen c j
  have hbody : DefRel ((m + (n + 2)) + 1) fun w =>
      w 0 ∈ˢ Is (revList fun l : Fin n => w ⟨(m + 2 + l.val) + 1, by omega⟩) c ∧
      fit (revList fun l : Fin n => w ⟨(m + 2 + l.val) + 1, by omega⟩) c (w 0) j
        (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩) ∧
      w ⟨m + 2, by omega⟩ = decEnc c j (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩) ∧
      w ⟨m + 1, by omega⟩ =
        tagged c (w 0) (injX c j (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩)) := by
    let p_u : (Fin ((m + (n + 2)) + 1) → V) → V := fun w => w ⟨m + 1, by omega⟩
    let p_d : (Fin ((m + (n + 2)) + 1) → V) → V := fun w => w ⟨m + 2, by omega⟩
    let p_xs : Fin n → (Fin ((m + (n + 2)) + 1) → V) → V :=
      fun l w => w ⟨(m + 2 + l.val) + 1, by omega⟩
    let p_fs : Fin m → (Fin ((m + (n + 2)) + 1) → V) → V :=
      fun l w => w ⟨l.val + 1, by omega⟩
    have hpu : DefFun ((m + (n + 2)) + 1) p_u := DefFun.proj ⟨m + 1, by omega⟩
    have hpd : DefFun ((m + (n + 2)) + 1) p_d := DefFun.proj ⟨m + 2, by omega⟩
    have hpxs : ∀ l, DefFun ((m + (n + 2)) + 1) (p_xs l) :=
      fun l => DefFun.proj ⟨(m + 2 + l.val) + 1, by omega⟩
    have hpfs : ∀ l, DefFun ((m + (n + 2)) + 1) (p_fs l) :=
      fun l => DefFun.proj ⟨l.val + 1, by omega⟩
    have hIsW : DefFun ((m + (n + 2)) + 1) fun w =>
        Is (revList fun l : Fin n => w ⟨(m + 2 + l.val) + 1, by omega⟩) c :=
      ((hIs c hc).comp hpxs).congr fun w => rfl
    let gsFit : Fin ((m + 1) + n) → (Fin ((m + (n + 2)) + 1) → V) → V := fun l w =>
      if hl0 : l.val = 0 then w 0
      else if hl1 : l.val < m + 1 then p_fs ⟨l.val - 1, by omega⟩ w
      else p_xs ⟨l.val - (m + 1), by omega⟩ w
    have hgsFit : ∀ l, DefFun ((m + (n + 2)) + 1) (gsFit l) := fun l => by
      dsimp only [gsFit]
      split
      · exact DefFun.proj 0
      · split
        · exact hpfs _
        · exact hpxs _
    have hFitW : DefRel ((m + (n + 2)) + 1) fun w =>
        fit (revList fun l : Fin n => w ⟨(m + 2 + l.val) + 1, by omega⟩) c (w 0) j
          (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩) := by
      refine ((hfit c hc j hj).comp hgsFit).congr fun w => ?_
      have hxs : revList (fdrop (k := m + 1) (p := n) fun i => gsFit i w) =
          revList fun l : Fin n => w ⟨(m + 2 + l.val) + 1, by omega⟩ := by
        congr 1
        funext l
        dsimp only [fdrop, gsFit]
        have h1 : ¬ ((m + 1) + l.val = 0) := by omega
        have h2 : ¬ ((m + 1) + l.val < m + 1) := by omega
        simp only [h1, ↓reduceDIte, h2, p_xs]
        congr 1; ext; dsimp; omega
      have hfs : List.ofFn (ftail (ftake (k := m + 1) (p := n) fun i => gsFit i w)) =
          List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩ := by
        congr 1
        funext l
        dsimp only [ftail, ftake, gsFit, Fin.val_succ]
        have h1 : ¬ (l.val + 1 = 0) := by omega
        have h2 : l.val + 1 < m + 1 := by omega
        simp only [h1, ↓reduceDIte, h2, p_fs]
        rfl
      have h0 : ftake (k := m + 1) (p := n) (fun i => gsFit i w) 0 = w 0 := rfl
      rw [hxs, hfs, h0]
    have hEqW : DefRel ((m + (n + 2)) + 1) fun w =>
        w ⟨m + 2, by omega⟩ =
          decEnc c j (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩) :=
      (DefRel.eq_apply hpd ((defFun_decEnc c j m).comp hpfs)).congr fun _ => Iff.rfl
    have hTagW : DefRel ((m + (n + 2)) + 1) fun w =>
        w ⟨m + 1, by omega⟩ =
          tagged c (w 0) (injX c j (List.ofFn fun l : Fin m => w ⟨l.val + 1, by omega⟩)) :=
      (DefRel.eq_apply hpu
        (DefFun.tagged_apply c (DefFun.proj 0) ((hinj c hc j hj).comp hpfs))).congr fun _ => Iff.rfl
    exact (DefRel.mem_apply (DefFun.proj 0) hIsW).and (hFitW.and (hEqW.and hTagW))
  have h1 : DefRel (m + (n + 2)) fun u => ∃ i : V,
      i ∈ˢ Is (revList (ftail (ftail (fdrop (k := m) (p := n + 2) u)))) c ∧
      fit (revList (ftail (ftail (fdrop (k := m) (p := n + 2) u)))) c i j
        (List.ofFn (ftake (k := m) (p := n + 2) u)) ∧
      (fdrop (k := m) (p := n + 2) u) 1 = decEnc c j (List.ofFn (ftake (k := m) (p := n + 2) u)) ∧
      (fdrop (k := m) (p := n + 2) u) 0 =
        tagged c i (injX c j (List.ofFn (ftake (k := m) (p := n + 2) u))) := by
    refine DefRel.exists_curry (R := fun i u =>
      i ∈ˢ Is (revList (ftail (ftail (fdrop (k := m) (p := n + 2) u)))) c ∧
      fit (revList (ftail (ftail (fdrop (k := m) (p := n + 2) u)))) c i j
        (List.ofFn (ftake (k := m) (p := n + 2) u)) ∧
      (fdrop (k := m) (p := n + 2) u) 1 = decEnc c j (List.ofFn (ftake (k := m) (p := n + 2) u)) ∧
      (fdrop (k := m) (p := n + 2) u) 0 =
        tagged c i (injX c j (List.ofFn (ftake (k := m) (p := n + 2) u))))
      (hbody.congr fun w => ?_)
    have hfs : ∀ l : Fin m, w ⟨l.val + 1, by omega⟩ = ftail w ⟨l.val, by omega⟩ := fun _ => rfl
    have hxs : ∀ l : Fin n,
        w ⟨(m + 2 + l.val) + 1, by omega⟩ = ftail w ⟨m + (l.val + 2), by omega⟩ := fun l => by
      change w ⟨(m + 2 + l.val) + 1, by omega⟩ = w ⟨(m + (l.val + 2)) + 1, by omega⟩
      congr 1; ext; dsimp; omega
    have hu0 : w ⟨m + 1, by omega⟩ = ftail w ⟨m + 0, by omega⟩ := rfl
    have hd1 : w ⟨m + 2, by omega⟩ = ftail w ⟨m + 1, by omega⟩ := rfl
    simp only [hfs, hxs, hu0, hd1]
    exact Iff.rfl
  refine (DefRel.exists_fin (k := m) (p := n + 2) h1).congr fun v => ?_
  constructor
  · rintro ⟨fsVec, i, hi, hfit', hd, hu⟩
    have hft : ftake (k := m) (p := n + 2) (fappend fsVec v) = fsVec := ftake_fappend fsVec v
    have hfd : fdrop (k := m) (p := n + 2) (fappend fsVec v) = v := fdrop_fappend fsVec v
    rw [hfd] at hi hfit' hd hu
    rw [hft] at hfit' hd hu
    exact ⟨fsVec, hd, hc, hj, i, hi, hfit', hu⟩
  · rintro ⟨fsVec, hd, -, -, i, hi, hfit', hu⟩
    refine ⟨fsVec, i, ?_⟩
    have hft : ftake (k := m) (p := n + 2) (fappend fsVec v) = fsVec := ftake_fappend fsVec v
    have hfd : fdrop (k := m) (p := n + 2) (fappend fsVec v) = v := fdrop_fappend fsVec v
    rw [hfd]
    rw [hft]
    exact ⟨hi, hfit', hd, hu⟩

private theorem specialize_xs_rev {p : Nat} (xs : List V) :
    ∃ Gs : Fin (xs.length + p) → (Fin p → V) → V,
      (∀ l, DefFun p (Gs l)) ∧
      ∀ v : Fin p → V,
        (∀ l : Fin p, Gs ⟨l.val, by omega⟩ v = v l) ∧
        revList (fun l : Fin xs.length => Gs ⟨p + l.val, by omega⟩ v) = xs := by
  let Gs : Fin (xs.length + p) → (Fin p → V) → V := fun l v =>
    if hl : l.val < p then v ⟨l.val, hl⟩ else xs.reverse[l.val - p]'(by simp; omega)
  refine ⟨Gs, fun l => by dsimp only [Gs]; split; exact DefFun.proj _; exact DefFun.const _, fun v => ?_⟩
  constructor
  · intro l
    dsimp only [Gs]
    simp [l.isLt]
  · apply List.ext_getElem
    · simp [revList]
    · intro i h1 h2
      simp only [revList, List.getElem_ofFn, Gs]
      have hge : ¬ (p + (xs.length - 1 - i) < p) := by omega
      simp only [hge, ↓reduceDIte, List.getElem_reverse]
      congr 1; omega

private theorem defRel_graphDecV_const {Is : List V → Nat → V} {injX : Nat → Nat → List V → V}
    {fLen : Nat → Nat → Nat} {fit : List V → Nat → V → Nat → List V → Prop}
    (xs : List V)
    (hinj : ∀ c, c < K → ∀ j, j < nCt c → DefFun (fLen c j) fun fs => injX c j (List.ofFn fs))
    (hfit : ∀ c, c < K → ∀ j, j < nCt c →
      DefRel ((fLen c j + 1) + xs.length) fun v =>
        fit (revList (fdrop (k := fLen c j + 1) (p := xs.length) v)) c
          ((ftake (k := fLen c j + 1) (p := xs.length) v) 0) j
          (List.ofFn (ftail (ftake (k := fLen c j + 1) (p := xs.length) v)))) :
    DefRel 2 fun v => graphDecV Is injX nCt fLen K fit xs (v 0) (v 1) := by
  obtain ⟨Gs, hGs, hspec⟩ := specialize_xs_rev (p := 2) xs
  refine ((defRel_graphDecV_param (n := xs.length) (Is := fun _ c => Is xs c)
    (fun c _ => DefFun.const (Is xs c)) hinj hfit).comp hGs).congr fun v => ?_
  obtain ⟨hft, hrev⟩ := hspec v
  have hv0 : (fun i => Gs i v) 0 = v 0 := hft ⟨0, by omega⟩
  have hv1 : (fun i => Gs i v) 1 = v 1 := hft ⟨1, by omega⟩
  have htail2 : revList (ftail (ftail (fun l => Gs l v))) = xs := by
    rw [show ftail (ftail (fun l => Gs l v)) =
        fun l : Fin xs.length => Gs ⟨2 + l.val, by omega⟩ v from
      funext fun l => congrArg (fun k => Gs k v) (Fin.ext (by dsimp; omega)), hrev]
  rw [hv0, hv1, htail2]
  exact Iff.rfl

private theorem defFun_graphPredV_param {Is Cr : List V → Nat → V} {fLen : Nat → Nat → Nat}
    {hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs)} {n : Nat}
    (hIs : ∀ m, m < K → DefFun n fun xsVec : Fin n → V => Is (revList xsVec) m)
    (hCr : ∀ m, m < K → DefFun n fun xsVec : Fin n → V => Cr (revList xsVec) m)
    (hcall : ∀ c, c < K → ∀ j, j < nCt c →
      DefRel ((fLen c j + 1) + n) fun v =>
        call (revList (fdrop (k := fLen c j + 1) (p := n) v)) c j
          (List.ofFn (ftail (ftake (k := fLen c j + 1) (p := n) v)))
          ((ftake (k := fLen c j + 1) (p := n) v) 0)) :
    DefFun (n + 1) fun v =>
      graphPredV Is Cr K nCt fLen call hSep (revList (ftail v)) (v 0) := by
  unfold graphPredV
  refine defFun_decSwitch nCt fLen _ (DefFun.proj 0) K fun c hc j hj => ?_
  let m := fLen c j
  have hU : DefFun (n + 1) fun v =>
      unionSet K (Is (revList (ftail v))) (Cr (revList (ftail v))) :=
    DefFun.unionSet_apply K
      (fun m hm => ((hIs m hm).comp fun l =>
        (DefFun.proj ⟨l.val + 1, by omega⟩).congr fun _ => rfl).congr fun _ => rfl)
      (fun m hm => ((hCr m hm).comp fun l =>
        (DefFun.proj ⟨l.val + 1, by omega⟩).congr fun _ => rfl).congr fun _ => rfl)
  let gsCall : Fin ((m + 1) + n) → (Fin ((n + 1) + 1) → V) → V := fun l w =>
    if hl0 : l.val = 0 then w 0
    else if hl1 : l.val < m + 1 then
      (listDec m (kp2 (kp2 (w 1)))).getD (l.val - 1) empty
    else w ⟨(l.val - (m + 1)) + 2, by omega⟩
  have hgsCall : ∀ l, DefFun ((n + 1) + 1) (gsCall l) := fun l => by
    dsimp only [gsCall]
    split
    · exact DefFun.proj 0
    · split
      · exact defFun_listDec_getD m (l.val - 1) (by omega)
          (DefFun.kp2_apply (DefFun.kp2_apply (DefFun.proj 1)))
      · exact DefFun.proj _
  have hP : DefRel ((n + 1) + 1) fun w =>
      call (revList (ftail (ftail w))) c j
        (listDec m (kp2 (kp2 ((ftail w) 0)))) (w 0) := by
    refine ((hcall c hc j hj).comp hgsCall).congr fun w => ?_
    have hxs : revList (fdrop (k := m + 1) (p := n) fun i => gsCall i w) =
        revList (ftail (ftail w)) := by
      congr 1
      funext l
      dsimp only [fdrop, ftail, gsCall]
      have h1 : ¬ ((m + 1) + l.val = 0) := by omega
      have h2 : ¬ ((m + 1) + l.val < m + 1) := by omega
      simp only [h1, ↓reduceDIte, h2]
      congr 1; ext; dsimp; omega
    have hfs : List.ofFn (ftail (ftake (k := m + 1) (p := n) fun i => gsCall i w)) =
        listDec m (kp2 (kp2 ((ftail w) 0))) := by
      rw [listDec_eq_ofFn m]
      congr 1
      funext l
      dsimp only [ftail, ftake, gsCall, Fin.val_succ]
      have h1 : ¬ (l.val + 1 = 0) := by omega
      have h2 : l.val + 1 < m + 1 := by omega
      simp only [h1, ↓reduceDIte, h2]
      rfl
    have h0 : ftake (k := m + 1) (p := n) (fun i => gsCall i w) 0 = w 0 := rfl
    rw [hxs, hfs, h0]
  exact DefFun.sep_apply_curry hU hP

private theorem defFun_graphPredV_const {Is Cr : List V → Nat → V} {fLen : Nat → Nat → Nat}
    {hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs)}
    (xs : List V)
    (hcall : ∀ c, c < K → ∀ j, j < nCt c →
      DefRel ((fLen c j + 1) + xs.length) fun v =>
        call (revList (fdrop (k := fLen c j + 1) (p := xs.length) v)) c j
          (List.ofFn (ftail (ftake (k := fLen c j + 1) (p := xs.length) v)))
          ((ftake (k := fLen c j + 1) (p := xs.length) v) 0)) :
    DefFun 1 fun v => graphPredV Is Cr K nCt fLen call hSep xs (v 0) := by
  unfold graphPredV
  refine defFun_decSwitch nCt fLen _ (DefFun.proj 0) K fun c hc j hj => ?_
  let m := fLen c j
  have hU : DefFun 1 fun _ => unionSet K (Is xs) (Cr xs) := DefFun.const _
  let gsCall : Fin ((m + 1) + xs.length) → (Fin (1 + 1) → V) → V := fun l w =>
    if hl0 : l.val = 0 then w 0
    else if hl1 : l.val < m + 1 then
      (listDec m (kp2 (kp2 (w 1)))).getD (l.val - 1) empty
    else xs.reverse[l.val - (m + 1)]'(by simp; omega)
  have hgsCall : ∀ l, DefFun (1 + 1) (gsCall l) := fun l => by
    dsimp only [gsCall]
    split
    · exact DefFun.proj 0
    · split
      · exact defFun_listDec_getD m (l.val - 1) (by omega)
          (DefFun.kp2_apply (DefFun.kp2_apply (DefFun.proj 1)))
      · exact DefFun.const _
  have hP : DefRel (1 + 1) fun w =>
      call xs c j (listDec m (kp2 (kp2 (w 1)))) (w 0) := by
    refine ((hcall c hc j hj).comp hgsCall).congr fun w => ?_
    have hxs : revList (fdrop (k := m + 1) (p := xs.length) fun i => gsCall i w) = xs := by
      apply List.ext_getElem
      · simp [revList]
      · intro i h1 h2
        simp only [revList, fdrop, List.getElem_ofFn, gsCall]
        have h1' : ¬ ((m + 1) + (xs.length - 1 - i) = 0) := by omega
        have h2' : ¬ ((m + 1) + (xs.length - 1 - i) < m + 1) := by omega
        simp only [h1', ↓reduceDIte, h2', List.getElem_reverse]
        congr 1; omega
    have hfs : List.ofFn (ftail (ftake (k := m + 1) (p := xs.length) fun i => gsCall i w)) =
        listDec m (kp2 (kp2 (w 1))) := by
      rw [listDec_eq_ofFn m]
      congr 1
      funext l
      dsimp only [ftail, ftake, gsCall, Fin.val_succ]
      have h1 : ¬ (l.val + 1 = 0) := by omega
      have h2 : l.val + 1 < m + 1 := by omega
      simp only [h1, ↓reduceDIte, h2]
      rfl
    have h0 : ftake (k := m + 1) (p := xs.length) (fun i => gsCall i w) 0 = w 0 := rfl
    rw [hxs, hfs, h0]
  exact DefFun.sep_apply_curry hU hP

private theorem defFun_graphStV_param {fLen : Nat → Nat → Nat} {n : Nat}
    (hst : ∀ c, c < K → ∀ j, j < nCt c →
      DefFun ((fLen c j + 1) + n) fun v =>
        blockGraphStep ρ Rb0 ihv (revList (fdrop (k := fLen c j + 1) (p := n) v))
          (c, j, List.ofFn (ftail (ftake (k := fLen c j + 1) (p := n) v)))
          ((ftake (k := fLen c j + 1) (p := n) v) 0)) :
    DefFun (n + 2) fun v =>
      graphStV ρ Rb0 ihv K nCt fLen (revList (ftail (ftail v))) (v 0) (v 1) := by
  unfold graphStV
  refine defFun_decSwitch nCt fLen _ (DefFun.proj 0) K fun c hc j hj => ?_
  let m := fLen c j
  let gsSt : Fin ((m + 1) + n) → (Fin (n + 2) → V) → V := fun l v =>
    if hl0 : l.val = 0 then v 1
    else if hl1 : l.val < m + 1 then
      (listDec m (kp2 (kp2 (v 0)))).getD (l.val - 1) empty
    else v ⟨2 + (l.val - (m + 1)), by omega⟩
  have hgsSt : ∀ l, DefFun (n + 2) (gsSt l) := fun l => by
    dsimp only [gsSt]
    split
    · exact DefFun.proj 1
    · split
      · exact defFun_listDec_getD m (l.val - 1) (by omega)
          (DefFun.kp2_apply (DefFun.kp2_apply (DefFun.proj 0)))
      · exact DefFun.proj _
  refine ((hst c hc j hj).comp hgsSt).congr fun v => ?_
  have hxs : revList (fdrop (k := m + 1) (p := n) fun i => gsSt i v) =
      revList (ftail (ftail v)) := by
    congr 1
    funext l
    dsimp only [fdrop, ftail, gsSt]
    have h1 : ¬ ((m + 1) + l.val = 0) := by omega
    have h2 : ¬ ((m + 1) + l.val < m + 1) := by omega
    simp only [h1, ↓reduceDIte, h2]
    congr 1; ext; dsimp; omega
  have hfs : List.ofFn (ftail (ftake (k := m + 1) (p := n) fun i => gsSt i v)) =
      listDec m (kp2 (kp2 (v 0))) := by
    rw [listDec_eq_ofFn m]
    congr 1
    funext l
    dsimp only [ftail, ftake, gsSt, Fin.val_succ]
    have h1 : ¬ (l.val + 1 = 0) := by omega
    have h2 : l.val + 1 < m + 1 := by omega
    simp only [h1, ↓reduceDIte, h2]
    rfl
  have h1 : ftake (k := m + 1) (p := n) (fun i => gsSt i v) 0 = v 1 := rfl
  rw [hxs, hfs, h1]

private theorem defFun_graphStV_const {fLen : Nat → Nat → Nat} (xs : List V)
    (hst : ∀ c, c < K → ∀ j, j < nCt c →
      DefFun ((fLen c j + 1) + xs.length) fun v =>
        blockGraphStep ρ Rb0 ihv (revList (fdrop (k := fLen c j + 1) (p := xs.length) v))
          (c, j, List.ofFn (ftail (ftake (k := fLen c j + 1) (p := xs.length) v)))
          ((ftake (k := fLen c j + 1) (p := xs.length) v) 0)) :
    DefFun 2 fun v => graphStV ρ Rb0 ihv K nCt fLen xs (v 0) (v 1) := by
  obtain ⟨Gs, hGs, hspec⟩ := specialize_xs_rev (p := 2) xs
  refine ((defFun_graphStV_param (n := xs.length) hst).comp hGs).congr fun v => ?_
  obtain ⟨hft, hrev⟩ := hspec v
  have hv0 : (fun i => Gs i v) 0 = v 0 := hft ⟨0, by omega⟩
  have hv1 : (fun i => Gs i v) 1 = v 1 := hft ⟨1, by omega⟩
  have htail2 : revList (ftail (ftail (fun l => Gs l v))) = xs := by
    rw [show ftail (ftail (fun l => Gs l v)) =
        fun l : Fin xs.length => Gs ⟨2 + l.val, by omega⟩ v from
      funext fun l => congrArg (fun k => Gs k v) (Fin.ext (by dsimp; omega)), hrev]
  rw [hv0, hv1, htail2]

/-- **The graph kit over a step premise** (`graphKitG` with the step's
typing given directly), encoded over `V`. -/
noncomputable def graphKitR
    (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V) (uX nIdxX : Nat → Nat)
    (fLen : Nat → Nat → Nat) (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V)
    (hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs))
    (hDec_def : DefRel 2 fun v => graphDecV Is injX nCt fLen K fit xs (v 0) (v 1))
    (hpred_def : DefFun 1 fun v => graphPredV Is Cr K nCt fLen call hSep xs (v 0))
    (hst_def : DefFun 2 fun v => graphStV ρ Rb0 ihv K nCt fLen xs (v 0) (v 1))
    (hfit_len : ∀ c, c < K → ∀ j, j < nCt c → ∀ i fs, fit xs c i j fs → fs.length = fLen c j)
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ Is xs c →
      ∀ x, x ∈ˢ app (Cr xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (nIdxX c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hstep : ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)))
    (huniq : ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      ∀ e e', graphDecG Is injX nCt K fit xs u e → graphDecG Is injX nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v' ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v = v')
    (hind : ∀ P : V → Prop, HasSep (unionSet K (Is xs) (Cr xs)) P →
      (∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
        (∃ e, graphDecG Is injX nCt K fit xs u e ∧
          ∀ v, v ∈ˢ graphPredG Is Cr K call xs e (hSep xs e.1 e.2.1 e.2.2) → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u) :
    GraphRecKit ℓ (unionSet K (Is xs) (Cr xs)) where
  Dec := graphDecV Is injX nCt fLen K fit xs
  pred := graphPredV Is Cr K nCt fLen call hSep xs
  B := fun u => blockRecMotBranch K concl uX nIdxX ρ xs u K
  st := graphStV ρ Rb0 ihv K nCt fLen xs
  hDec_def := hDec_def
  hpred_def := hpred_def
  hB_def := defFun_blockRecMotBranch_const K concl uX nIdxX ρ xs
  hst_def := hst_def
  hpred := by
    intro _ _ d hd v hv
    obtain ⟨c, hc, j, hj, fsVec, rfl, _⟩ := hd
    rw [graphPredV_decEnc hc hj (by simp)] at hv
    exact (mem_graphPredG.mp hv).1
  hB := by
    intro u hu
    obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
    rw [blockRecMotBranch_tagged hc]
    exact blockRecMot_mem_univ hconclTy (tagged c i x) hu
  hst := by
    intro _ _ d hd g hg
    obtain ⟨c, hc, j, hj, fsVec, rfl, hdec⟩ := hd
    obtain ⟨-, -, i, hi, hfit, rfl⟩ := hdec
    have hgB : ∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, List.ofFn fsVec)
        (hSep xs c j (List.ofFn fsVec)) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v := by
      intro v hv
      have hhv : v ∈ˢ graphPredV Is Cr K nCt fLen call hSep xs (decEnc c j (List.ofFn fsVec)) := by
        rwa [graphPredV_decEnc hc hj (by simp)]
      have h1 := app_mem_of_mem_piSet hg hhv
      have h2 := gGraph_mem_B
        (fun u hu => by
          obtain ⟨c', hc', i', hi', x', hx', rfl⟩ := mem_unionSet.mp hu
          rw [blockRecMotBranch_tagged hc']
          exact blockRecMot_mem_univ hconclTy _ hu)
        (fun _ _ d' hd' v' hv' => by
          obtain ⟨c', hc', j', hj', fsVec', rfl, _⟩ := hd'
          rw [graphPredV_decEnc hc' hj' (by simp)] at hv'
          exact (mem_graphPredG.mp hv').1)
        (mem_graphPredG.mp hv).1 h1
      obtain ⟨c', hc', i', -, x', -, hveq⟩ := mem_unionSet.mp (mem_graphPredG.mp hv).1
      rw [hveq, blockRecMotBranch_tagged hc'] at h2
      rwa [hveq]
    rw [graphStV_decEnc hc hj (by simp), blockRecMotBranch_tagged hc]
    exact hstep c hc j hj i (List.ofFn fsVec) hi hfit g hgB
  huniq := by
    intro u hu d d' hd hd'
    obtain ⟨c, hc, j, hj, fsVec, rfl, hdec⟩ := hd
    obtain ⟨c', hc', j', hj', fsVec', rfl, hdec'⟩ := hd'
    rcases huniq u hu (c, j, List.ofFn fsVec) (c', j', List.ofFn fsVec') hdec hdec' with h | h
    · have hcEq : c = c' := congrArg Prod.fst h
      have hjEq : j = j' := congrArg (fun p => p.2.1) h
      have hfsEq : List.ofFn fsVec = List.ofFn fsVec' := congrArg (fun p => p.2.2) h
      have hlist : listEnc (List.ofFn fsVec) = listEnc (List.ofFn fsVec') :=
        congrArg listEnc hfsEq
      refine Or.inl ?_
      have hc1 : vnat (V := V) c = vnat c' := congrArg vnat hcEq
      have hj1 : vnat (V := V) j = vnat j' := congrArg vnat hjEq
      dsimp only [decEnc]
      rw [hc1, hj1, hlist]
    · obtain ⟨cu, hcu, iu, -, xu, -, hueq⟩ := mem_unionSet.mp hu
      refine Or.inr fun v v' hv hv' => ?_
      rw [hueq, blockRecMotBranch_tagged hcu] at hv hv'
      exact h v v' (by rwa [hueq]) (by rwa [hueq])
  ind := fun P hSepP hstepP => hind P hSepP fun u hu ⟨e, hdec, hP⟩ =>
    let ⟨i, _, hfit, _⟩ := hdec.2.2
    have hlen : e.2.2.length = fLen e.1 e.2.1 := hfit_len e.1 hdec.1 e.2.1 hdec.2.1 i e.2.2 hfit
    hstepP u hu ⟨decEnc e.1 e.2.1 e.2.2,
      (graphDecV_decEnc hlen).mpr hdec,
      fun v hv => hP v (by
        have hv' := hv
        rw [graphPredV_decEnc hdec.1 hdec.2.1 hlen] at hv'
        exact hv')⟩

set_option maxHeartbeats 1000000 in
/-- **`graphRecPre_core` over a step premise.**  The same candidate and
the same rows; the step's typing is `hstep`. -/
theorem graphRecPre_coreR {es ihs : Nat → Nat → List Term} {mk : Nat → Nat → Term}
    {rds : Nat → List Term} {RecTy : Nat → Term}
    (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V) (uX nIdxX : Nat → Nat)
    (tupX : Nat → List V → V)
    (fit : List V → Nat → V → Nat → List V → Prop)
    (hTyP : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrP_le : ∀ c, c < K → rP c ≤ (rds c).length)
    (hIs_def : ∀ c₀, c₀ < K → ∀ m, m < K → DefFun (rP c₀) fun xs : Fin (rP c₀) → V => Is (revList xs) m)
    (hCr_def : ∀ c₀, c₀ < K → ∀ m, m < K → DefFun (rP c₀) fun xs : Fin (rP c₀) → V => Cr (revList xs) m)
    (htup_def : ∀ c₀, c₀ < K →
      DefFun (rds c₀).length fun vs : Fin (rds c₀).length → V => tupX c₀ (idxOf (rP c₀) (revList vs)))
    (hinj_def : ∀ c, c < K → ∀ j, j < nCt c →
      DefFun (fdoms c j).length fun fs : Fin (fdoms c j).length → V => injX c j (List.ofFn fs))
    (hfit_len : ∀ xs c i j fs, c < K → j < nCt c → fit xs c i j fs → fs.length = (fdoms c j).length)
    (hfit_def : ∀ n c j, c < K → j < nCt c →
      DefRel (((fdoms c j).length + 1) + n) fun v =>
        fit (revList (fdrop (k := (fdoms c j).length + 1) (p := n) v)) c
          ((ftake (k := (fdoms c j).length + 1) (p := n) v) 0) j
          (List.ofFn (ftail (ftake (k := (fdoms c j).length + 1) (p := n) v))))
    (hcall_def : ∀ n c j, c < K → j < nCt c →
      DefRel (((fdoms c j).length + 1) + n) fun v =>
        call (revList (fdrop (k := (fdoms c j).length + 1) (p := n) v)) c j
          (List.ofFn (ftail (ftake (k := (fdoms c j).length + 1) (p := n) v)))
          ((ftake (k := (fdoms c j).length + 1) (p := n) v) 0))
    (hst_def : ∀ n c j, c < K → j < nCt c →
      DefFun (((fdoms c j).length + 1) + n) fun v =>
        blockGraphStep ρ Rb0 ihv (revList (fdrop (k := (fdoms c j).length + 1) (p := n) v))
          (c, j, List.ofFn (ftail (ftake (k := (fdoms c j).length + 1) (p := n) v)))
          ((ftake (k := (fdoms c j).length + 1) (p := n) v) 0))
    (hSep : ∀ xs c j fs, HasSep (unionSet K (Is xs) (Cr xs)) (call xs c j fs))
    (hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      tupX c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupX c (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c)) ys →
      blockRecMot K concl uX nIdxX ρ (prefOf (rP c) ys)
          (tagged c (tupX c (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c))
    (hconclTy : ∀ xs : List V, ∀ c, c < K → ∀ i, i ∈ˢ Is xs c →
      ∀ x, x ∈ˢ app (Cr xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (nIdxX c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hstep : ∀ xs : List V, ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)))
    (huniq : ∀ xs : List V, ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      ∀ e e', graphDecG Is injX nCt K fit xs u e → graphDecG Is injX nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v' ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v = v')
    (hind : ∀ xs : List V, ∀ P : V → Prop, HasSep (unionSet K (Is xs) (Cr xs)) P →
      (∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
        (∃ e, graphDecG Is injX nCt K fit xs u e ∧
          ∀ v, v ∈ˢ graphPredG Is Cr K call xs e (hSep xs e.1 e.2.1 e.2.2) → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u)
    (hrule : ∀ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K a ρ)) (mk c j)])))
    (hdec : ∀ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      fit xs c (tupX c ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) j fs ∧
      interp V (consList (xs ++ fs) (chainFrame K a ρ)) (mk c j) = injX c j fs)
    (hchain : ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < K → ∀ (is : List V) (x : V),
        xs.length = rP c' →
        SpineFit ρ ((rds c')) (xs ++ (is ++ [x])) →
        r (tagged c' (tupX c' is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        (hGr : HasGraph (graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs)) r) →
        ihv xs c j fs (graph r (graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs)) hGr)
          = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs
          (fun c j => (Rb0 c j).liftN K ((pdoms c).length + (fdoms c j).length
            + (ihs c j).length)),
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  let fLen : Nat → Nat → Nat := fun c j => (fdoms c j).length
  let D : GraphFamData V ℓ K rP rds concl ρ :=
    { Is := Is, Cr := Cr, tupOf := tupX,
      kit := fun xs => graphKitR (Rb0 := Rb0) (ihv := ihv) (call := call) (nCt := nCt)
        Is Cr injX uX nIdxX fLen fit xs hSep
        (defRel_graphDecV_const (fLen := fun c j => (fdoms c j).length) xs hinj_def
          (fun c hc j hj => hfit_def xs.length c j hc hj))
        (defFun_graphPredV_const (fLen := fun c j => (fdoms c j).length) xs
          (fun c hc j hj => hcall_def xs.length c j hc hj))
        (defFun_graphStV_const (fLen := fun c j => (fdoms c j).length) xs
          (fun c hc j hj => hst_def xs.length c j hc hj))
        (fun c hc j hj i fs hfit => hfit_len xs c i j fs hc hj hfit)
        (hconclTy xs) (hstep xs) (huniq xs) (hind xs),
      hIs_def := hIs_def,
      hCr_def := hCr_def,
      hDec_def := fun c₀ hc₀ =>
        defRel_graphDecV_param (fLen := fun c j => (fdoms c j).length) (hIs_def c₀ hc₀) hinj_def
          (fun c hc j hj => hfit_def (rP c₀) c j hc hj),
      hpred_def := fun c₀ hc₀ =>
        defFun_graphPredV_param (fLen := fun c j => (fdoms c j).length) (hIs_def c₀ hc₀)
          (hCr_def c₀ hc₀) (fun c hc j hj => hcall_def (rP c₀) c j hc hj),
      hB_def := fun c₀ hc₀ => defFun_blockRecMotBranch_param K concl uX nIdxX ρ (rP c₀),
      hst_def := fun c₀ hc₀ =>
        defFun_graphStV_param (fLen := fun c j => (fdoms c j).length)
          (fun c hc j hj => hst_def (rP c₀) c j hc hj),
      htupOf_def := htup_def,
      hrP_le := hrP_le,
      hsplit := hsplit,
      hconcl := fun c hc ys hsp => by
        dsimp only [graphKitR]
        rw [blockRecMotBranch_tagged hc]
        exact hconcl c hc ys hsp }
  have hTyC : ∀ c, c < K → famCandG D c ∈ˢ interp V ρ (RecTy c) := fun c hc => by
    rw [hTyP c hc]; exact famCandG_mem D hc
  refine famCandG_hCand D (fun _ c j fs => decEnc c j fs) hTyP hpl
    (hrule (famCandG D) hTyC) ?_ ?_
  · intro c hc j hj xs fs hxl hsp
    have hfit := hrule (famCandG D) hTyC c hc j hj xs fs hxl hsp
    have hxr : xs.length = rP c := by rw [hxl, hpl c hc]
    obtain ⟨-, -, hi, -⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    obtain ⟨hf, hmk⟩ := hdec (famCandG D) hTyC c hc j hj xs fs hxl hsp
    have hfs : fs.length = fLen c j := hfit_len xs c _ j fs hc hj hf
    exact (graphDecV_decEnc hfs).mpr ⟨hc, hj, _, hi, hf, by rw [hmk]⟩
  · intro c hc j hj xs fs hxl hsp
    have hlen : (xs ++ fs).length = (pdoms c).length + (fdoms c j).length := by
      rw [hsp.length_eq, List.length_append]
    obtain ⟨hf, -⟩ := hdec (famCandG D) hTyC c hc j hj xs fs hxl hsp
    have hfs : fs.length = fLen c j := hfit_len xs c _ j fs hc hj hf
    have hGr : HasGraph (graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs))
        (fun v => (D.kit xs).recAt v) := (D.kit xs).hasGraph_recAt _
    have hch := hchain (famCandG D) xs (fun v => (D.kit xs).recAt v)
      (fun c' hc' is x hxl' hsp' => (famCandG_fold D hc' hxl' hsp').symm) c hc j hj fs hxl hsp hGr
    have hpred_eq : (D.kit xs).pred (decEnc c j fs) =
        graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs) :=
      graphPredV_decEnc hc hj hfs
    have hst_eq : (D.kit xs).st (decEnc c j fs)
          (graph (fun v => (D.kit xs).recAt v) ((D.kit xs).pred (decEnc c j fs))
            ((D.kit xs).hasGraph_recAt _))
        = blockGraphStep ρ Rb0 ihv xs (c, j, fs)
            (graph (fun v => (D.kit xs).recAt v) (graphPredG Is Cr K call xs (c, j, fs) (hSep xs c j fs)) hGr) := by
      dsimp only [D, graphKitR]
      rw [graphStV_decEnc hc hj hfs]
      congr 1
      exact graph_ext hpred_eq _ hGr fun _ _ => rfl
    rw [hst_eq]
    dsimp only [blockGraphStep]
    rw [hch,
      show (pdoms c).length + (fdoms c j).length + (ihs c j).length
        = (xs ++ fs).length + ((ihs c j).map
            (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))).length from by
        rw [hlen, List.length_map],
      interp_Rb_chain]

end CoreR

/-! ## 2. The rows, by construction -/

section Rows

variable {K : Nat} {ρ : Nat → V} {rP : Nat → Nat}
  {pre idxB : Nat → List Term} {majB : Nat → Nat × Nat × Term}
  {uX : Nat → Nat}

/-- A fit of an appended chain whose first part has the first chain's
length splits there. -/
theorem spineFit_append_at {Ds₁ Ds₂ : List Term} {σ : Nat → V} {xs fs : List V}
    (hl : xs.length = Ds₁.length) (h : SpineFit σ (Ds₁ ++ Ds₂) (xs ++ fs)) :
    SpineFit σ Ds₁ xs ∧ SpineFit (consList xs σ) Ds₂ fs := by
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv h
  have hl1 : as₁.length = xs.length := by rw [h1.length_eq, hl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl1
  exact ⟨h1, h2⟩

end Rows

/-! ## 4. The generated `ih`s: they read the chain only at their calls

A generated `ih` is `λ a⃗, rec_t x⃗ e⃗ (f a⃗)` — at the rule's frame
`x⃗ ++ f⃗` (depth `D`), a λ-telescope whose body applies the CHAIN
variable of its callee `t` to the prefix variables, the index
arguments and the major argument.  Read at two chain valuations it
agrees as soon as the two recursors agree along every spine the body
applies them to — the `hihRead` premise of `graphRecPre_gen`, by
construction.  The telescope's domains and the arguments name no chain
variable (they are bounded below the chain). -/

section Ihs

/-- A fit is a fit at any frame agreeing below the chain's bound. -/
theorem spineFit_congr_domsBelow :
    ∀ {Ds : List Term} {k : Nat} {σ σ' : Nat → V} {bs : List V},
      DomsBelow k Ds → (∀ i, i < k → σ i = σ' i) → SpineFit σ Ds bs → SpineFit σ' Ds bs
  | [], _, _, _, [], _, _, _ => trivial
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | D :: Ds, k, σ, σ', b :: bs, hb, hag, h => by
    refine ⟨?_, spineFit_congr_domsBelow (k := k + 1) hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp_congr_below V D k σ σ' hb.1 hag]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)

/-- **The `ih` shape's chain reading**: an `ih`-shaped term reads alike
at two frames agreeing below its depth `D`, as soon as the head
variable's two values agree along every spine the body applies them
to. -/
theorem interp_ihShape_congr {m : Nat} (args : List Term) :
    ∀ (tele : List Term) {D : Nat} {σ σ' : Nat → V},
      DomsBelow D (tele) →
      (∀ e ∈ args, Term.bvarsBelow (D + tele.length) e) →
      (∀ i, i < D → σ i = σ' i) →
      (∀ bs, SpineFit σ (tele) bs →
        (args.map (interp V (consList bs σ))).foldl SetTheory.app (σ (D + m))
          = (args.map (interp V (consList bs σ))).foldl SetTheory.app (σ' (D + m))) →
      interp V σ (mkLamsAV tele (Term.mkAppN (.bvar (D + tele.length + m)) args))
        = interp V σ' (mkLamsAV tele (Term.mkAppN (.bvar (D + tele.length + m)) args))
  | [], D, σ, σ', _, hargs, hag, h => by
    simp only [mkLamsAV, List.length_nil, Nat.add_zero, interp_mkAppN, interp_bvar]
    have h0 := h [] trivial
    simp only [consList_nil] at h0
    have hmap : args.map (interp V σ') = args.map (interp V σ) :=
      List.map_congr_left fun e he =>
        (interp_congr_below V e D σ σ' (by simpa using hargs e he) hag).symm
    rw [← List.foldl_map, ← List.foldl_map (f := interp V σ'), hmap]
    exact h0
  | A :: tele, D, σ, σ', hb, hargs, hag, h => by
    simp only [mkLamsAV, interp_lam]
    have hA : interp V σ A = interp V σ' A := interp_congr_below V A D σ σ' hb.1 hag
    refine lamV_ext hA _ _ fun x hx => ?_
    have hidx : D + (A :: tele).length + m = (D + 1) + tele.length + m := by
      simp; omega
    rw [hidx]
    refine interp_ihShape_congr args tele (D := D + 1) hb.2 (fun e he => ?_)
      (fun i hi => ?_) (fun bs hbs => ?_)
    · have := hargs e he
      simpa [Nat.add_assoc, Nat.add_comm 1 tele.length] using this
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have hfit : SpineFit σ (A :: tele) (x :: bs) := ⟨hx, hbs⟩
      have := h (x :: bs) hfit
      simpa [consList_cons, Nat.add_right_comm D 1 m] using this

/-- One generated `ih`: its callee, its telescope, its index arguments
and its major argument. -/
abbrev IhDatum := Nat × List Term × List Term × Term

/-- **A generated `ih` term** at the rule's depth `D` (prefix `rP`):
`λ a⃗, rec_t x⃗ e⃗ m`, the callee the chain variable `K-1-t` below the
frame. -/
@[expose] def genIhAV (K rP D : Nat) (q : IhDatum) : Term :=
  mkLamsAV q.2.1 (Term.mkAppN (.bvar (D + q.2.1.length + (K - 1 - q.1)))
    (prefVarsAV rP (D - rP + q.2.1.length) ++ (q.2.2.1 ++ [q.2.2.2])))

/-- **The generated calls**: an `ih` of callee `t` at a fitting
telescope spine calls `t` at its index arguments' and major argument's
readings. -/
@[expose] def genIhCallAt (ρ : Nat → V) (ihd : Nat → Nat → List IhDatum) (xs : List V)
    (c j : Nat) (fs : List V) (t : Nat) (is : List V) (x : V) : Prop :=
  ∃ q ∈ ihd c j, q.1 = t ∧ ∃ bs : List V,
    SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs ∧
    is = q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))) ∧
    x = interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2

/-- The data of a generated `ih` names no chain variable: its telescope
and arguments are bounded below the chain. -/
@[expose] def IhDatumBelow (D : Nat) (q : IhDatum) : Prop :=
  DomsBelow D (q.2.1) ∧
  (∀ e ∈ q.2.2.1 ++ [q.2.2.2], Term.bvarsBelow (D + q.2.1.length) e)

/-- **`hihRead`, by construction** at the generated `ih`s. -/
theorem genIhs_hihRead {K : Nat} {ρ : Nat → V} {nCt : Nat → Nat}
    {pre : Nat → List Term} {fdoms : Nat → Nat → List Term}
    {ihd : Nat → Nat → List IhDatum}
    (hcal : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j, q.1 < K)
    (hbelow : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j,
      IhDatumBelow ((pre c).length + (fdoms c j).length) q) :
    ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a a' : Nat → V),
      xs.length = (pre c).length →
      SpineFit (chainFrame K a ρ) (pre c ++ fdoms c j) (xs ++ fs) →
      (∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        (xs ++ (is ++ [x])).foldl SetTheory.app (a t)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a' t)) →
      ((ihd c j).map (genIhAV K (pre c).length
          ((pre c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = ((ihd c j).map (genIhAV K (pre c).length
          ((pre c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a' ρ))) := by
  intro c hc j hj xs fs a a' hxl hsp hcall
  have hfl : fs.length = (fdoms c j).length := by
    have := hsp.length_eq
    simp only [List.length_append] at this
    omega
  have hD : (pre c).length + (fdoms c j).length = (xs ++ fs).length := by
    simp [hxl, hfl]
  simp only [List.map_map]
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hbT, hbA⟩ := hbelow c hc j hj q hq
  simp only [Function.comp, genIhAV]
  rw [hD] at hbT hbA ⊢
  refine interp_ihShape_congr _ q.2.1 hbT (fun e he => ?_) (fun i hi => ?_) (fun bs hbs => ?_)
  · rcases List.mem_append.mp he with he | he
    · -- a prefix variable: below the rule's frame
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      show Term.bvarsBelow _ (Term.bvar _)
      simp only [Term.bvarsBelow, List.mem_range] at hl ⊢
      omega
    · exact hbA e he
  · -- the two frames share the spine
    rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]
  · -- the head's two values, and the arguments' readings
    have hq1 := hcal c hc j hj q hq
    have hhead : ∀ b : Nat → V, consList (xs ++ fs) (chainFrame K b ρ)
        ((xs ++ fs).length + (K - 1 - q.1)) = b q.1 := by
      intro b
      rw [Nat.add_comm, consList_apply_add, chainFrame_apply hq1]
    rw [hhead a, hhead a']
    -- the arguments read the call's spine
    have hbsρ : SpineFit (consList (xs ++ fs) ρ) (q.2.1) bs := by
      refine spineFit_congr_domsBelow (k := (xs ++ fs).length) hbT (fun i hi => ?_) hbs
      rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]
    have hbl : bs.length = q.2.1.length := hbs.length_eq
    have hargR : ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))) e
          = interp V (consList bs (consList (xs ++ fs) ρ)) e := by
      intro e he
      refine interp_congr_below V e ((xs ++ fs).length + q.2.1.length) _ _ (hbA e he)
        fun i hi => ?_
      rw [← consList_append, ← consList_append,
        consList_getD_of_lt _ _ _ (by simp [hbl]; omega),
        consList_getD_of_lt _ _ _ (by simp [hbl]; omega)]
    have hpre : (prefVarsAV (pre c).length
          ((xs ++ fs).length - (pre c).length + q.2.1.length)).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ)))) = xs := by
      have h := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ bs)
        (ρ := chainFrame K a ρ) hxl
      rw [← List.append_assoc, consList_append] at h
      simpa [hbl, hxl, Nat.add_sub_cancel_left] using h
    have hcallq : genIhCallAt ρ ihd xs c j fs q.1
        (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))))
        (interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2) :=
      ⟨q, hq, rfl, bs, hbsρ, rfl, rfl⟩
    have heq := hcall _ _ _ hcallq
    have hargs : (prefVarsAV (pre c).length
          ((xs ++ fs).length - (pre c).length + q.2.1.length) ++
          (q.2.2.1 ++ [q.2.2.2])).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))))
        = xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]) := by
      rw [List.map_append, hpre, List.map_congr_left hargR]
      simp
    rw [hargs]
    exact heq

end Ihs

end ConLeche.Model
