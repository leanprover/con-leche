module

public import ConLeche.Model.Inductives.FixChains
public import ConLeche.Semantics.Tower.BlockFamI
public section

/-!
# The X-chains of a block member, graded at every family TUPLE (task #315 M3)

`FixChains.lean`'s walk at `k` members.  At every tuple `Y` of the
members' family space and every index tuple `t` of member `m`, a
constructor's X-chain — its ordinary domains lifted past `Y` and `t`,
its recursive slots reading `proj_c Y ⟨e⃗⟩` at the field's TARGET
member `c`, the index-equation terminator at member `m`'s own indices
— is graded (`FieldsOkB`) and its recursive slots fit (`SlotsFitXB`).

The shadow machinery is unchanged and reused from the one-member file
(`shadowFs`, `ShadowRel`, `agreeOff_shadow`, `slotFit_congr_shadow`,
`shadowVal`): **the shadow context is target-blind** — a recursive
position is replaced by `Sort 0` whatever it targets, so which member
a slot reads never enters the transport from the shadow frame to the
X-frame.  The ONE place the target appears is the recursive branch of
the walk, where the slot is read at its target's index-tuple sort and
telescope.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

section Walk

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {m nP nF : Nat} {ks : List RecFieldKind} {tgts : List Nat}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm}

/-- `ChainFacts` at `k` members: the per-position facts the walk
consumes, with a recursive position's slot fitting its TARGET member's
index telescope.  The four `nb*` clauses are the one-member file's
verbatim — they are about the shadow context, which is
target-blind. -/
structure ChainFactsB (k w nP nF : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (m : Nat)
    (ks : List RecFieldKind) (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Fs : List AnnotTerm) (Eis : List (List AnnotTerm)) (Es : List AnnotTerm) : Prop where
  hks : ks.length = nF
  hFs : Fs.length = nF
  hEs : Es.length = (Idss m).length
  nb : ∀ i, i < nF →
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default)
  nbT : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ q d, (tls.getD i [])[q]? = some d →
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + q)) d.2.2
  nbE : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ E ∈ Eis.getD i [],
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i + (tls.getD i []).length)) E
  nbEs : ∀ E ∈ Es, NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + nF) (nP + nF)) E
  /-- at a recursive position the target is a member and the slot fits
  THAT member's index telescope -/
  gr : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    WellDenoted V (consList as' ρp) (Fs.getD i default) ∧
    (¬ recAt nP ks (nP + i) → w ≠ 0 →
      interp V (consList as' ρp) (Fs.getD i default) ∈ˢ (univ w : V)) ∧
    (recAt nP ks (nP + i) → tgts.getD i 0 < k ∧
      SlotFit (uf (tgts.getD i 0)) w ρp (Idss (tgts.getD i 0)) (tls.getD i []) (Eis.getD i []) as')
  grE : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, WellDenoted V (consList as' ρp) E

/-- **The walk**, at `k` members: along the X-chain, beside a shadow
spine. -/
theorem blockChainWalk (hIall : BlockIdxOk (V := V) k uf ρp Idss) (hm : m < k) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {t : V} (ht : t ∈ˢ idxSet (uf m) ρp (Idss m))
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs Eis Es) :
    ∀ (n : Nat) (as as' : List V), nF - as.length = n → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsOkB w (consList as (cons t (cons Y ρp)))
        (chainXBIGo uf Idss (rsOf ks) tgts tls Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI (Idss m).length nF Es)]) ∧
      SlotsFitXB k w ρp uf Idss (rsOf ks) tgts tls Eis Y t as.length as (Fs.drop as.length) := by
  intro n
  induction n with
  | zero =>
    intro as as' hn hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by
      rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXBIGo, List.nil_append, SlotsFitXB, and_true]
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    have hEok : ∀ E ∈ Es, WellDenoted V (consList as ρp) E := fun E hE =>
      (WellDenoted_congr_noBVar E (hC.nbEs E hE) hag).mpr (hC.grE as' hspF E hE)
    refine ⟨idxEqAV_wellDenoted (eqsXI_wellDenoted (hIall m hm) ht hlen hEok hC.hEs),
      fun _ => idxEqAV_mem_univ _ _ _, fun _ _ => trivial⟩
  | succ n ih =>
    intro as as' hn hle hrel hsp
    have hi : as.length < nF := by omega
    have hdrop : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    rw [hdrop, chainXBIGo_cons, List.cons_append]
    have hag := agreeOff_shadow hrel ρp
    obtain ⟨hok', hbnd', hrec'⟩ := hC.gr as.length hi as' hsp
    have hFnb := hC.nb as.length hi
    have hokF : WellDenoted V (consList as ρp) (Fs.getD as.length default) :=
      (WellDenoted_congr_noBVar _ hFnb hag).mpr hok'
    have hvF : interp V (consList as ρp) (Fs.getD as.length default)
        = interp V (consList as' ρp) (Fs.getD as.length default) :=
      interp_congr_noBVar _ hFnb hag
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AnnotTerm.sort 0 else Fs.getD as.length default) →
        FieldsOkB w (consList (as ++ [a]) (cons t (cons Y ρp)))
          (chainXBIGo uf Idss (rsOf ks) tgts tls Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI (Idss m).length nF Es)]) ∧
        SlotsFitXB k w ρp uf Idss (rsOf ks) tgts tls Eis Y t (as.length + 1) (as ++ [a])
          (Fs.drop (as.length + 1)) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · -- a recursive slot, at its TARGET member
      obtain ⟨htlt, hfit'⟩ := hrec' hr
      have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      have hfit : SlotFit (uf (tgts.getD as.length 0)) w ρp (Idss (tgts.getD as.length 0))
          (tls.getD as.length []) (Eis.getD as.length []) as :=
        slotFit_congr_shadow hrel (hC.nbT as.length hi hr) (hC.nbE as.length hi hr) hfit'
      have hx : xEntryB uf Idss (rsOf ks) tgts tls Eis (Fs.getD as.length default) as.length
          = slotXBI (uf (tgts.getD as.length 0)) (Idss (tgts.getD as.length 0))
              (tgts.getD as.length 0) (tls.getD as.length []) (Eis.getD as.length []) as.length := by
        unfold xEntryB; rw [if_pos hrs]
      rw [hx]
      obtain ⟨hokX, huniv⟩ := slotXBI_wellDenoted hIall htlt hY as t hfit
      have hval := slotXBI_interp (Y := Y) (hIall _ htlt) as t hfit
      refine ⟨⟨hokX, fun hw => by rw [hval]; exact huniv hw, fun a ha => ?_⟩,
        fun _ => ⟨htlt, hfit⟩, fun a ha => ?_⟩
      · rw [consList_snoc']
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).1
      · rw [hx] at ha
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).2
    · -- an ordinary entry
      have hrs : (rsOf ks).getD as.length false = false := by
        have := rsOf_getD_iff (ks := ks) (i := as.length) (by rw [hC.hks]; exact hi)
        cases h : (rsOf ks).getD as.length false with
        | false => rfl
        | true =>
          exfalso
          apply hr
          refine ⟨Nat.le_add_right _ _, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact this.mp h
      have hx : xEntryB uf Idss (rsOf ks) tgts tls Eis (Fs.getD as.length default) as.length
          = (Fs.getD as.length default).liftN 2 as.length := by
        unfold xEntryB; rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      rw [hx]
      have hokL : WellDenoted V (consList as (cons t (cons Y ρp)))
          ((Fs.getD as.length default).liftN 2 as.length) :=
        (WellDenoted_chainXI_ord _ as t Y).mpr hokF
      have hvL : interp V (consList as (cons t (cons Y ρp)))
          ((Fs.getD as.length default).liftN 2 as.length)
          = interp V (consList as' ρp) (Fs.getD as.length default) := by
        rw [interp_chainXI_ord, hvF]
      refine ⟨⟨hokL, fun hw => by rw [hvL]; exact hbnd' hr hw, fun a ha => ?_⟩,
        fun h => absurd h (by rw [hrs]; exact Bool.false_ne_true), fun a ha => ?_⟩
      · rw [consList_snoc']
        rw [hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).1
      · rw [hx, hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).2

/-- **The block member's X-chain, graded and fitting**, from the walk
at the empty spine. -/
theorem blockChain_of (hIall : BlockIdxOk (V := V) k uf ρp Idss) (hm : m < k) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {t : V} (ht : t ∈ˢ idxSet (uf m) ρp (Idss m))
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs Eis Es) :
    FieldsOkB w (cons t (cons Y ρp))
      (chainXBI uf Idss (Idss m).length (rsOf ks) tgts tls Eis Fs Es) ∧
    SlotsFitXB k w ρp uf Idss (rsOf ks) tgts tls Eis Y t 0 [] Fs := by
  have h := blockChainWalk hIall hm hY ht hC nF [] [] (by simp) (by simp)
    (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXBI, hC.hFs]
  exact h

/-- **At ONE member** the block's chain facts ARE the one-member
file's: the target bound `0 < 1` is trivial and the target's index
telescope is the family's own. -/
theorem ChainFactsB.toFix {u w nP nF : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {ks : List RecFieldKind} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}
    (h : ChainFactsB (V := V) 1 w nP nF ρp (fun _ => u) (fun _ => Ids) 0 ks tgts tls Fs Eis Es) :
    ChainFacts (V := V) u w nP nF ρp Ids ks tls Fs Eis Es where
  hks := h.hks
  hFs := h.hFs
  hEs := h.hEs
  nb := h.nb
  nbT := h.nbT
  nbE := h.nbE
  nbEs := h.nbEs
  gr := fun i hi as' hsp =>
    ⟨(h.gr i hi as' hsp).1, (h.gr i hi as' hsp).2.1,
      fun hr => ((h.gr i hi as' hsp).2.2 hr).2⟩
  grE := h.grE

end Walk

end ConLeche.Model
