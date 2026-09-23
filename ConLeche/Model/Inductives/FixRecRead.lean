module

public import ConLeche.Model.Inductives.FixRecReadDefs
public import ConLeche.Verify.Inductives.FixRec
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
public section

/-!
# The generated recursive recursor's readings (task #188)

`ConLeche/Model/Inductives/SumRecRead.lean` with the inductive hypotheses:
the generated recursive recursor type reads to the Π-tower over
`fixRecDataAV` and rule `j` to the λ-tower over `fixRuleDataAV`
(`ConLeche/Model/Inductives/FixRecReadDefs.lean`).

The one genuinely new reading is the `ih` binder's domain
`∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)`.  A recursive field's own telescope and
its domain's index expressions are read at the constructor's OWN
opening — the parameters, the `i` earlier fields, then the telescope's
own openers (`FieldReadAt`, off `CtorReadR` by `fieldReadAt_of`) —
while the recursor's frame puts the fields `o` slots higher (the
motive and the earlier minors sit between) and `nF - i + l` binders
above.  Moving between the two frames is `Expr.shiftFrom` iterated
(`denoteMeta_instSeq_shift`), twice: once to insert the fields and the
earlier hypotheses below the field's own frame, once to insert the
`o` extras between the parameters and the fields — precisely
`ihIdxAtM`'s two lifts, the telescope's openers staying innermost
(task #202).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Reading through an inserted block of variables -/

/-- **`denoteMeta_shiftFrom`, iterated**: inserting `o` fresh variable
slots at index `p` lifts the reading by `o` at the cut `d - p`. -/
theorem denoteMeta_shiftFromN {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} :
    ∀ (o : Nat) {e : Expr} {d : Nat}, p ≤ d → Expr.WScoped d e →
      denoteMeta acval env φ (d + o) (Expr.shiftFromN p o e)
        = (denoteMeta acval env φ d e).map (AnnotTerm.liftN o · (d - p))
  | 0, e, d, _, _ => by
    show denoteMeta acval env φ (d + 0) e = _
    rw [Nat.add_zero]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v => simp only [Option.map_some, AnnotTerm.liftN_zero]
  | o + 1, e, d, hpd, hw => by
    show denoteMeta acval env φ (d + (o + 1)) (Expr.shiftFrom p (Expr.shiftFromN p o e)) = _
    rw [show d + (o + 1) = d + o + 1 from by omega,
      denoteMeta_shiftFrom hacl _ (d + o) (by omega) (Expr.WScoped_shiftFromN o hw),
      denoteMeta_shiftFromN hacl o hpd hw]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      exact AVExprSubst.liftN_liftN_absorb v (by omega) (by omega) 1

/-- **A closed expression at a shifted opening.**  `A` opens it at the
variables `0 … A.length - 1`; `B` opens it at the same variables with
those at or above `p` moved `o` slots up.  The reading moves with
them: it is lifted by `o` at the cut `d - p`. -/
theorem denoteMeta_instSeq_shift {m : EnvModel V env} {ψ : Name → Nat} {p o d t : Nat}
    {e : Expr} (hef : e.hasFvar = false)
    {A B : List Expr} (hlen : A.length = B.length) (hpd : p ≤ d)
    (hAw : ∀ (k : Nat) (x : Expr), A[k]? = some x → Expr.WScoped d x)
    (hAB : ∀ (k : Nat) (a b : Expr), A[k]? = some a → B[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧ b = Expr.fvar (if ia < p then ia else ia + o) tyb)
    {E : AnnotTerm}
    (hE : denoteMeta m.acval env ψ d (Expr.instSeq A t e) = some E) :
    denoteMeta m.acval env ψ (d + o) (Expr.instSeq B t e) = some (E.liftN o (d - p)) := by
  have hAcl : ∀ x ∈ A, Expr.WScoped d x := fun x hx => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    exact hAw q x hq
  have hw : Expr.WScoped d (Expr.instSeq A t e) :=
    Expr.instSeq_WScoped A t hAcl (Expr.WScoped.of_not_hasFvar hef)
  have hshift := denoteMeta_shiftFromN (acval := m.acval) (env := env) (φ := ψ)
    m.acval_closed (p := p) o hpd hw
  rw [hE, Option.map_some, Expr.shiftFromN_instSeq p o A t e,
    Expr.shiftFromN_eq_self_of_not_hasFvar o hef] at hshift
  have herased : Expr.ErasedEq (Expr.instSeq (A.map (Expr.shiftFromN p o)) t e)
      (Expr.instSeq B t e) := by
    refine Expr.instSeq_erasedEq_args _ _ t (Expr.ErasedEq.rfl e) ?_ (by simp [hlen])
    intro k a₁ a₂ ha₁ ha₂
    rw [List.getElem?_map] at ha₁
    cases hA : A[k]? with
    | none => rw [hA] at ha₁; exact nomatch ha₁
    | some a =>
      rw [hA, Option.map_some, Option.some.injEq] at ha₁
      obtain ⟨ia, tya, tyb, rfl, hb⟩ := hAB k a a₂ hA ha₂
      obtain ⟨ty', hsh⟩ := Expr.shiftFromN_fvar p o ia tya
      rw [← ha₁, hsh, hb]
      exact Eq.refl _
  rw [denoteMeta_erasedEq herased (d + o)] at hshift
  exact hshift

/-! ## Spine bookkeeping -/

/-- A read spine, re-read entry by entry at another frame. -/
theorem DenoteMetaSpine.map_map {acval : Name → (Name → Nat) → AnnotTerm} {d d' : Nat}
    {f g : Expr → Expr} {h : AnnotTerm → AnnotTerm} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as.map f) vs →
      (∀ (a : Expr) (v : AnnotTerm), a ∈ as → denoteMeta acval env φ d (f a) = some v →
        denoteMeta acval env φ d' (g a) = some (h v)) →
      DenoteMetaSpine acval env φ d' (as.map g) (vs.map h)
  | [], vs, hsp, _ => by
    cases hsp
    exact .nil
  | a :: as, vs, hsp, hfg => by
    rw [List.map_cons] at hsp
    cases hsp with
    | cons hd htl =>
      exact .cons (hfg a _ List.mem_cons_self hd)
        (DenoteMetaSpine.map_map htl fun x v hx hv => hfg x v (List.mem_cons_of_mem _ hx) hv)

/-- A pointwise-read mapped spine. -/
theorem DenoteMetaSpine.of_map {α : Type} {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat}
    {f : α → Expr} {g : α → AnnotTerm} :
    ∀ (l : List α), (∀ a ∈ l, denoteMeta acval env φ d (f a) = some (g a)) →
      DenoteMetaSpine acval env φ d (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h =>
    .cons (h a List.mem_cons_self)
      (DenoteMetaSpine.of_map l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Frames of the same variables -/

/-- Two frames of the same variables read an expression the same: the
variables' annotations do not matter (`denoteMeta_erasedEq`). -/
theorem denoteMeta_instSeq_congr {m : EnvModel V env} {ψ : Name → Nat} {d t : Nat} {e : Expr}
    {L L' : List Expr} (hlen : L.length = L'.length)
    (hidx : ∀ (k : Nat) (a b : Expr), L[k]? = some a → L'[k]? = some b →
      ∃ (q : Nat) (ty ty' : Expr), a = Expr.fvar q ty ∧ b = Expr.fvar q ty') :
    denoteMeta m.acval env ψ d (Expr.instSeq L t e)
      = denoteMeta m.acval env ψ d (Expr.instSeq L' t e) := by
  refine denoteMeta_erasedEq (Expr.instSeq_erasedEq_args L L' t (Expr.ErasedEq.rfl e) ?_ hlen) d
  intro k a b ha hb
  obtain ⟨q, ty, ty', rfl, rfl⟩ := hidx k a b ha hb
  exact Eq.refl _

/-- A frame of the variables `0 … D-1` is the canonical opening. -/
theorem denoteMeta_instSeq_canon {m : EnvModel V env} {ψ : Name → Nat} {d t D : Nat} {e : Expr}
    {L : List Expr} (hlen : L.length = D)
    (hidx : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    denoteMeta m.acval env ψ d (Expr.instSeq L t e)
      = denoteMeta m.acval env ψ d (Expr.instSeq (openFvars 0 D) t e) := by
  refine denoteMeta_instSeq_congr (by simp [hlen]) ?_
  intro k a b ha hb
  obtain ⟨ty, rfl⟩ := hidx k a ha
  have hk : k < D := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp ha).1
  rw [openFvars_getElem? hk, Nat.zero_add] at hb
  obtain rfl := (Option.some.inj hb).symm
  exact ⟨k, ty, _, rfl, rfl⟩

/-- A canonical opening's variables are scoped. -/
theorem openFvars_WScoped {base k d : Nat} (h : base + k ≤ d) :
    ∀ (q : Nat) (x : Expr), (openFvars base k)[q]? = some x → Expr.WScoped d x := by
  intro q x hq
  have hqk : q < k := by
    rcases Nat.lt_or_ge q k with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by simp; omega)] at hq
      exact nomatch hq
  rw [openFvars_getElem? hqk] at hq
  obtain rfl := (Option.some.inj hq).symm
  simp only [Expr.WScoped]
  exact ⟨by omega, trivial⟩

/-! ## The `ih` binders' index expressions -/

/-- A Π-tower's binders and body inherit its closedness and its
loose-bvar bound (each binder under the earlier ones). -/
theorem Expr.piBinders_props : ∀ (e : Expr) (c : Nat), e.hasFvar = false →
    e.looseBVarsBounded c = true →
    (∀ (k : Nat) (b : Expr × BinderMeta), (e.piBinders).1[k]? = some b →
        b.1.hasFvar = false ∧ b.1.looseBVarsBounded (c + k) = true) ∧
      (e.piBinders).2.hasFvar = false ∧
      (e.piBinders).2.looseBVarsBounded (c + (e.piBinders).1.length) = true
  | .forallE ty bd mt, c, hf, hb => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hk, hbf, hbb⟩ := Expr.piBinders_props bd (c + 1) hf.2 hb.2
    rw [Expr.piBinders_forallE]
    refine ⟨?_, hbf, ?_⟩
    · intro k b hbk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbk
        subst hbk
        exact ⟨hf.1, by rw [Nat.add_zero]; exact hb.1⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hbk
        obtain ⟨h1, h2⟩ := hk k b hbk
        exact ⟨h1, by rw [show c + (k + 1) = c + 1 + k from by omega]; exact h2⟩
    · simp only [List.length_cons]
      rw [show c + ((bd.piBinders).1.length + 1) = c + 1 + (bd.piBinders).1.length from by omega]
      exact hbb
  | .bvar _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .fvar .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .sort _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .const .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .app .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .lam .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .letE .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .lit _, _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩
  | .proj .., _, hf, hb => ⟨(fun _ _ hbk => nomatch hbk), hf, hb⟩

/-- A field's own telescope and the index expressions of its domain
inherit the constructor type's closedness and their frames' loose-bvar
bounds (the telescope's binder `k` under the `k` earlier ones, the
index expressions under the whole telescope). -/
theorem structFieldTele_props {cty : Expr} {nP nF i : Nat}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF) :
    (∀ (k : Nat) (b : Expr × BinderMeta),
        (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b →
        b.1.hasFvar = false ∧ b.1.looseBVarsBounded (nP + i + k) = true) ∧
      ∀ e ∈ ConLeche.structFieldIdxOf cty nP nF i,
        e.hasFvar = false ∧
          e.looseBVarsBounded (nP + i + (ConLeche.structFieldTeleOf cty nP nF i).length) = true := by
  obtain ⟨⟨cbs, cbody⟩, hs⟩ := Option.isSome_iff_exists.mp hstripC
  have hlenbs : cbs.length = nP + nF := Expr.stripPis_length _ hs
  obtain ⟨b, hb⟩ : ∃ b, cbs[nP + i]? = some b :=
    ⟨cbs[nP + i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hbd : cbs.getD (nP + i) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  have hbf : b.1.hasFvar = false :=
    (ConLeche.stripPis_not_hasFvar _ hs hCf).1 b (List.mem_of_getElem? hb)
  have hbb : b.1.looseBVarsBounded (nP + i) = true := by
    have := ConLeche.stripPis_binder_bounded (nP + nF) hs hCb (nP + i) b hb
    rwa [Nat.zero_add] at this
  have htele : ConLeche.structFieldTeleOf cty nP nF i = (b.1.piBinders).1 := by
    unfold ConLeche.structFieldTeleOf
    rw [hs]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hidx : ConLeche.structFieldIdxOf cty nP nF i = (b.1.piBinders).2.getAppArgs.drop nP := by
    unfold ConLeche.structFieldIdxOf
    rw [hs]
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  obtain ⟨hk, hpf, hpb⟩ := Expr.piBinders_props b.1 (nP + i) hbf hbb
  rw [htele, hidx]
  refine ⟨hk, ?_⟩
  intro e he
  have hmem : e ∈ (b.1.piBinders).2.getAppArgs := List.mem_of_mem_drop he
  exact ⟨ConLeche.hasFvar_getAppArgs hpf e hmem, ConLeche.looseBVarsBounded_getAppArgs hpb e hmem⟩

/-- **`structIdxAt`, instantiated at the recursor's frame under the
field's own telescope** — `ConLeche.instSeq_structIdxAt` with the
telescope's `j` openers below the frame (task #202). -/
theorem instSeq_structIdxAtM (P X F I A : List Expr) {nP o nF l i j : Nat} {e : Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hA : A.length = j)
    (hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true)
    (hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true)
    (hi : i ≤ nF) (heb : e.looseBVarsBounded (nP + i + j) = true) :
    Expr.instSeq (P ++ X ++ F ++ I ++ A) (nP + o + nF + l + j - 1)
        (ConLeche.structIdxAt nF o i l j e)
      = Expr.instSeq (P ++ F.take i ++ A) (nP + i + j - 1) e := by
  have hl1 : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    simp [hP, hX, hF, hI]
    omega
  have hl2 : (P ++ F.take i).length = nP + i := by
    simp [hP, hF]
    omega
  have hcore : Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l + j - 1)
      (ConLeche.structIdxAt nF o i l j e)
      = Expr.instSeq (P ++ F.take i) (nP + i + j - 1) e := by
    unfold ConLeche.structIdxAt
    have hq : (e.liftLooseBVars (nF - i + l) j).looseBVarsBounded
        (P.length + (nF + l + j)) = true := by
      have := Expr.looseBVarsBounded_liftLooseBVars (nF - i + l) e (b := nP + i + j) (c := j) heb
      exact Expr.looseBVarsBounded_mono (by rw [hP]; omega) this
    have h1 : Expr.instSeq (P ++ X) (nP + o + nF + l + j - 1)
        ((e.liftLooseBVars (nF - i + l) j).liftLooseBVars o (nF + l + j))
        = Expr.instSeq P (nP + nF + l + j - 1) (e.liftLooseBVars (nF - i + l) j) := by
      have h := ConLeche.instSeq_liftLooseBVars_mid P X (c := nF + l + j) hclP hq
      rw [hP, hX] at h
      rw [show nP + o + nF + l + j - 1 = nP + o + (nF + l + j) - 1 from by omega,
        show nP + nF + l + j - 1 = nP + (nF + l + j) - 1 from by omega]
      exact h
    have hsplit : P ++ X ++ F ++ I = (P ++ X) ++ (F ++ I) := by simp
    have hsplit2 : P ++ (F ++ I) = (P ++ F.take i) ++ (F.drop i ++ I) := by
      rw [List.append_assoc, ← List.append_assoc (F.take i), List.take_append_drop]
    have hlen2 : (F.drop i ++ I).length = nF - i + l := by simp [hF, hI]
    have hcl2 : ∀ a ∈ P ++ F.take i, a.looseBVarsBounded 0 = true := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hclP a h
      · exact hclF a (List.mem_of_mem_take h)
    have h2 : Expr.instSeq (P ++ (F ++ I)) (nP + nF + l + j - 1)
        (e.liftLooseBVars (nF - i + l) j)
        = Expr.instSeq (P ++ F.take i) (nP + i + j - 1) e := by
      rw [hsplit2]
      have := ConLeche.instSeq_liftLooseBVars_mid (P ++ F.take i) (F.drop i ++ I) (c := j) hcl2
        (by rw [hl2]; exact heb)
      rw [hl2, hlen2] at this
      rw [show nP + nF + l + j - 1 = nP + i + (nF - i + l) + j - 1 from by omega]
      exact this
    rw [hsplit, Expr.instSeq_append (P ++ X) (F ++ I)]
    show Expr.instSeq (F ++ I) (nP + o + nF + l + j - 1 - (P ++ X).length)
        (Expr.instSeq (P ++ X) (nP + o + nF + l + j - 1)
          ((e.liftLooseBVars (nF - i + l) j).liftLooseBVars o (nF + l + j))) = _
    rw [h1, show (P ++ X).length = nP + o from by simp [hP, hX],
      show nP + o + nF + l + j - 1 - (nP + o) = nP + nF + l + j - 1 - P.length from by
        rw [hP]; omega,
      ← Expr.instSeq_append P (F ++ I), h2]
  rw [Expr.instSeq_append (P ++ X ++ F ++ I) A, Expr.instSeq_append (P ++ F.take i) A, hcore,
    hl1, hl2]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hAnil : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hAnil
    rfl
  · rw [show nP + o + nF + l + j - 1 - (nP + o + nF + l) = nP + i + j - 1 - (nP + i) from by omega]

set_option maxHeartbeats 1600000 in
/-- **A recursive field's expression at the recursor's frame.**  The
constructor reads it at its own opening (the parameters, the `i`
earlier fields, then the `j` openers of the field's own telescope);
the frame `p⃗ x⃗ f⃗ ih⃗ a⃗` reads it at the same variables with the fields
`o` slots higher and `nF - i + l` binders below — the telescope's own
openers staying innermost — which is `ihIdxAtM`. -/
theorem denoteMeta_ihIdxAtM {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i j : Nat}
    {e : Expr} {E : AnnotTerm} (hef : e.hasFvar = false)
    (heb : e.looseBVarsBounded (nP + i + j) = true) (hi : i ≤ nF)
    {S : List Expr} (hS : S.length = nP + i)
    (hidxS : ∀ (k : Nat) (x : Expr), S[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hE : denoteMeta m.acval env ψ (nP + i + j)
      (Expr.instSeq (S ++ openFvars (nP + i) j) (nP + i + j - 1) e) = some E) :
    denoteMeta m.acval env ψ (nP + o + nF + l + j)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l) j)
          (nP + o + nF + l + j - 1) (ConLeche.structIdxAt nF o i l j e))
      = some (ihIdxAtM nF o i l j E) := by
  have hclP : ∀ a ∈ P, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxP q a hq
    rfl
  have hclF : ∀ a ∈ F, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxF q a hq
    rfl
  -- the source frame, canonically
  have hidxSA : ∀ (k : Nat) (x : Expr), (S ++ openFvars (nP + i) j)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [hS]; exact hk)] at hx
      exact hidxS k x hx
    · rw [List.getElem?_append_right (by rw [hS]; omega), hS] at hx
      have hlt : k - (nP + i) < j := by
        rcases Nat.lt_or_ge (k - (nP + i)) j with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hx
          exact nomatch hx
      rw [openFvars_getElem? hlt] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact ⟨.sort .zero, by congr 1; omega⟩
  have hlenSA : (S ++ openFvars (nP + i) j).length = nP + i + j := by
    rw [List.length_append, hS, openFvars_length]
  rw [denoteMeta_instSeq_canon hlenSA hidxSA] at hE
  have hlenA : (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j).length = nP + i + j := by
    rw [List.length_append, openFvars_length, openFvars_length]
  have hlenB : (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j).length
      = nP + i + j := by
    rw [List.length_append, List.length_append, openFvars_length, openFvars_length,
      openFvars_length]
  have hlenPF : (P ++ F.take i).length = nP + i := by
    rw [List.length_append, hP, List.length_take, hF]
    omega
  have hlenTgt : (P ++ F.take i ++ openFvars (nP + o + nF + l) j).length = nP + i + j := by
    rw [List.length_append, hlenPF, openFvars_length]
  -- the fields and the hypotheses, inserted between the field's frame and its telescope
  have hcorr1 : ∀ (k : Nat) (a b : Expr), (openFvars 0 (nP + i + j))[k]? = some a →
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧
          b = Expr.fvar (if ia < nP + i then ia else ia + (nF - i + l)) tyb := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at ha
        exact nomatch ha
    rw [openFvars_getElem? hka, Nat.zero_add] at ha
    obtain rfl := (Option.some.inj ha).symm
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk,
        Nat.zero_add] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_pos hk]
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_neg hk]
      congr 1
      omega
  have hshift1 := denoteMeta_instSeq_shift (m := m) (ψ := ψ) (p := nP + i) (o := nF - i + l)
    (d := nP + i + j) (t := nP + i + j - 1) (A := openFvars 0 (nP + i + j))
    (B := openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j) hef
    (by rw [openFvars_length, List.length_append, openFvars_length, openFvars_length])
    (by omega) (openFvars_WScoped (by omega)) hcorr1 hE
  rw [show nP + i + j + (nF - i + l) = nP + nF + l + j from by omega,
    show nP + i + j - (nP + i) = j from by omega] at hshift1
  -- the extras, inserted between the parameters and the fields
  have hcorr2 : ∀ (k : Nat) (a b : Expr),
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some a →
      (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)[k]? = some b →
      ∃ (ia : Nat) (tya tyb : Expr),
        a = Expr.fvar ia tya ∧ b = Expr.fvar (if ia < nP then ia else ia + o) tyb := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenA]; omega)] at ha
        exact nomatch ha
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk,
        Nat.zero_add] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_left
        (by rw [List.length_append, openFvars_length, openFvars_length]; omega)] at hb
      by_cases hk2 : k < nP
      · rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk2,
          Nat.zero_add] at hb
        obtain rfl := (Option.some.inj hb).symm
        refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
        rw [if_pos hk2]
      · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
          openFvars_getElem? (show k - nP < i from by omega)] at hb
        obtain rfl := (Option.some.inj hb).symm
        refine ⟨k, Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
        rw [if_neg hk2]
        congr 1
        omega
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_right
          (by rw [List.length_append, openFvars_length, openFvars_length]; omega),
        List.length_append, openFvars_length, openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      refine ⟨nP + nF + l + (k - (nP + i)), Expr.sort Level.zero, Expr.sort Level.zero, rfl, ?_⟩
      rw [if_neg (show ¬ nP + nF + l + (k - (nP + i)) < nP from by omega)]
      congr 1
      omega
  have hAw2 : ∀ (k : Nat) (x : Expr),
      (openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)[k]? = some x →
      Expr.WScoped (nP + nF + l + j) x := by
    intro k x hx
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenA]; omega)] at hx
        exact nomatch hx
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [openFvars_length]; omega)] at hx
      exact openFvars_WScoped (d := nP + nF + l + j) (by omega) k x hx
    · rw [List.getElem?_append_right (by rw [openFvars_length]; omega)] at hx
      exact openFvars_WScoped (d := nP + nF + l + j) (by omega) _ x hx
  have hshift2 := denoteMeta_instSeq_shift (m := m) (ψ := ψ) (p := nP) (o := o)
    (d := nP + nF + l + j) (t := nP + i + j - 1)
    (A := openFvars 0 (nP + i) ++ openFvars (nP + nF + l) j)
    (B := openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j) hef
    (by rw [hlenA, hlenB]) (by omega) hAw2 hcorr2 hshift1
  rw [show nP + nF + l + j + o = nP + o + nF + l + j from by omega,
    show nP + nF + l + j - nP = nF + l + j from by omega] at hshift2
  -- the frame, spelled at the recursor's own variables
  have hcorr3 : ∀ (k : Nat) (a b : Expr),
      (P ++ F.take i ++ openFvars (nP + o + nF + l) j)[k]? = some a →
      (openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)[k]? = some b →
      ∃ (q : Nat) (ty ty' : Expr), a = Expr.fvar q ty ∧ b = Expr.fvar q ty' := by
    intro k a b ha hb
    have hka : k < nP + i + j := by
      rcases Nat.lt_or_ge k (nP + i + j) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hlenTgt]; omega)] at ha
        exact nomatch ha
    by_cases hk : k < nP + i
    · rw [List.getElem?_append_left (by rw [hlenPF]; omega)] at ha
      rw [List.getElem?_append_left
        (by rw [List.length_append, openFvars_length, openFvars_length]; omega)] at hb
      by_cases hk2 : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at ha
        rw [List.getElem?_append_left (by rw [openFvars_length]; omega), openFvars_getElem? hk2,
          Nat.zero_add] at hb
        obtain ⟨ty, rfl⟩ := hidxP k a ha
        obtain rfl := (Option.some.inj hb).symm
        exact ⟨k, ty, _, rfl, rfl⟩
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at ha
        rw [List.getElem?_append_right (by rw [openFvars_length]; omega), openFvars_length,
          openFvars_getElem? (show k - nP < i from by omega)] at hb
        have ha' : F[k - nP]? = some a := by
          rw [← ha, List.getElem?_take, if_pos (show k - nP < i from by omega)]
        obtain ⟨ty, rfl⟩ := hidxF (k - nP) a ha'
        obtain rfl := (Option.some.inj hb).symm
        exact ⟨nP + o + (k - nP), ty, Expr.sort Level.zero, rfl, rfl⟩
    · rw [List.getElem?_append_right (by rw [hlenPF]; omega), hlenPF,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at ha
      obtain rfl := (Option.some.inj ha).symm
      rw [List.getElem?_append_right
          (by rw [List.length_append, openFvars_length, openFvars_length]; omega),
        List.length_append, openFvars_length, openFvars_length,
        openFvars_getElem? (show k - (nP + i) < j from by omega)] at hb
      obtain rfl := (Option.some.inj hb).symm
      exact ⟨_, _, _, rfl, rfl⟩
  rw [instSeq_structIdxAtM P X F I (openFvars (nP + o + nF + l) j) hP hX hF hI
    (openFvars_length _ _) hclP hclF hi heb,
    denoteMeta_instSeq_congr (L := P ++ F.take i ++ openFvars (nP + o + nF + l) j)
      (L' := openFvars 0 nP ++ openFvars (nP + o) i ++ openFvars (nP + o + nF + l) j)
      (by rw [hlenTgt, hlenB]) hcorr3]
  exact hshift2

set_option maxHeartbeats 1600000 in
/-- **A recursive field's index expressions at the recursor's frame**,
spine-wise. -/
theorem denoteMetaSpine_ihIdx {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o l i j : Nat} {cty : Expr} {Eis : List AnnotTerm}
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hj : j = (ConLeche.structFieldTeleOf cty nP nF i).length)
    {S : List Expr} (hS : S.length = nP + i)
    (hidxS : ∀ (k : Nat) (x : Expr), S[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (heis : DenoteMetaSpine m.acval env ψ (nP + i + j)
      ((ConLeche.structFieldIdxOf cty nP nF i).map
        (Expr.instSeq (S ++ openFvars (nP + i) j) (nP + i + j - 1))) Eis)
    {P X F I : List Expr}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF) (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty) :
    DenoteMetaSpine m.acval env ψ (nP + o + nF + l + j)
      ((ConLeche.structFieldIdxOf cty nP nF i).map
        (fun e => Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l) j)
          (nP + o + nF + l + j - 1) (ConLeche.structIdxAt nF o i l j e)))
      (Eis.map (ihIdxAtM nF o i l j)) := by
  refine DenoteMetaSpine.map_map heis ?_
  intro e E he hE
  obtain ⟨hef, heb⟩ := (structFieldTele_props hCf hCb hstripC hi).2 e he
  exact denoteMeta_ihIdxAtM hef (by rw [hj]; exact heb) (Nat.le_of_lt hi) hS hidxS hP hX hF hI
    hidxP hidxF hE

/-! ## The recursor's frame, variable by variable -/

/-- The frame `p⃗ x⃗ f⃗ ih⃗` is opened at the variables `0 … ` in order. -/
theorem frameIdx {P X F I : List Expr} {nP o nF : Nat}
    (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty) :
    ∀ (k : Nat) (x : Expr), (P ++ X ++ F ++ I)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
  intro k x hx
  by_cases h1 : k < nP + o + nF
  · rw [List.getElem?_append_left (by simp [hP, hX, hF]; omega)] at hx
    by_cases h2 : k < nP + o
    · rw [List.getElem?_append_left (by simp [hP, hX]; omega)] at hx
      by_cases h3 : k < nP
      · rw [List.getElem?_append_left (by rw [hP]; omega)] at hx
        exact hidxP k x hx
      · rw [List.getElem?_append_right (by rw [hP]; omega), hP] at hx
        obtain ⟨ty, hy⟩ := hidxX (k - nP) x hx
        exact ⟨ty, by rw [hy]; congr 1; omega⟩
    · rw [List.getElem?_append_right (by simp [hP, hX]; omega)] at hx
      simp only [List.length_append, hP, hX] at hx
      obtain ⟨ty, hy⟩ := hidxF (k - (nP + o)) x hx
      exact ⟨ty, by rw [hy]; congr 1; omega⟩
  · rw [List.getElem?_append_right (by simp [hP, hX, hF]; omega)] at hx
    simp only [List.length_append, hP, hX, hF] at hx
    obtain ⟨ty, hy⟩ := hidxI (k - (nP + o + nF)) x hx
    exact ⟨ty, by rw [hy]; congr 1; omega⟩

/-! ## Telescopes, read binderwise -/

/-- `structTeleAt` keeps the telescope's length. -/
theorem structTeleAt_length (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr × BinderMeta)) :
    (ConLeche.structTeleAt nF o i l pw tele).length = tele.length := by
  unfold ConLeche.structTeleAt
  rw [List.length_map, List.length_range]

/-- `structTeleAt`'s binder `k`: the telescope's own, its domain moved
to the `ih` binder's frame, its datum the elimination regime's (task
#202 A2). -/
theorem structTeleAt_getElem? {nF o i l k : Nat} {pw : PropWhen} {tele : List (Expr × BinderMeta)}
    {b : Expr × BinderMeta} (hb : tele[k]? = some b) :
    (ConLeche.structTeleAt nF o i l pw tele)[k]?
      = some (ConLeche.structIdxAt nF o i l k b.1, ⟨pw⟩) := by
  have hk : k < tele.length := (List.getElem?_eq_some_iff.mp hb).1
  unfold ConLeche.structTeleAt
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (show k < (List.range tele.length).length from by
      rw [List.length_range]; exact hk), List.getElem_range]
  simp only [Option.map_some, List.getD_eq_getElem?_getD, hb, Option.getD_some]

/-- `ihTeleAtGo`'s entry `q`: the datum's, its expression moved. -/
theorem ihTeleAtGo_getElem? (nF o i l : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)) (q : Nat),
      (ihTeleAtGo nF o i l k tl)[q]?
        = (tl[q]?).map fun d => (d.1, d.2.1, ihIdxAtM nF o i l (k + q) d.2.2)
  | _, [], _ => rfl
  | k, d :: tl, 0 => by simp [ihTeleAtGo]
  | k, d :: tl, q + 1 => by
    simp only [ihTeleAtGo, List.getElem?_cons_succ]
    rw [ihTeleAtGo_getElem? nF o i l (k + 1) tl q]
    congr 2
    funext d'
    rw [show k + 1 + q = k + (q + 1) from by omega]

/-! ## Π- and λ-towers over a frame -/

/-- The telescope's openers, re-associated: its first opener is the
frame's last variable. -/
theorem denoteMeta_frame_cons {m : EnvModel V env} {ψ : Name → Nat} {L : List Expr} {D : Nat}
    (hL : L.length = D)
    (hidxL : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (ty₀ : Expr) (k t dd : Nat) (e : Expr) :
    denoteMeta m.acval env ψ dd
        (Expr.instSeq (L ++ [Expr.fvar D ty₀] ++ openFvars (D + 1) k) t e)
      = denoteMeta m.acval env ψ dd (Expr.instSeq (L ++ openFvars D (k + 1)) t e) := by
  have hlen1 : (L ++ [Expr.fvar D ty₀]).length = D + 1 := by
    rw [List.length_append, hL, List.length_singleton]
  refine denoteMeta_instSeq_congr ?_ ?_
  · rw [List.length_append, hlen1, openFvars_length, List.length_append, hL, openFvars_length]
    omega
  · intro q a b ha hb
    rw [openFvars_succ] at hb
    by_cases hq : q < D
    · rw [List.getElem?_append_left (by rw [hlen1]; omega),
        List.getElem?_append_left (by rw [hL]; omega)] at ha
      rw [List.getElem?_append_left (by rw [hL]; omega)] at hb
      obtain rfl : a = b := Option.some.inj (ha.symm.trans hb)
      obtain ⟨ty, rfl⟩ := hidxL q a ha
      exact ⟨q, ty, ty, rfl, rfl⟩
    · by_cases hq2 : q = D
      · subst hq2
        rw [List.getElem?_append_left (by rw [hlen1]; omega),
          List.getElem?_append_right (by rw [hL]; omega), hL, Nat.sub_self] at ha
        rw [List.getElem?_append_right (by rw [hL]; omega), hL, Nat.sub_self] at hb
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha
        subst hb
        exact ⟨q, ty₀, Expr.sort Level.zero, rfl, rfl⟩
      · rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
          show q - (D + 1) = q - D - 1 from by omega] at ha
        rw [List.getElem?_append_right (by rw [hL]; omega), hL,
          show q - D = (q - D - 1) + 1 from by omega, List.getElem?_cons_succ] at hb
        obtain rfl : a = b := Option.some.inj (ha.symm.trans hb)
        have hlt : q - D - 1 < k := by
          rcases Nat.lt_or_ge (q - D - 1) k with h | h
          · exact h
          · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at ha
            exact nomatch ha
        rw [openFvars_getElem? hlt] at ha
        obtain rfl := (Option.some.inj ha).symm
        exact ⟨D + 1 + (q - D - 1), Expr.sort Level.zero, Expr.sort Level.zero, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **A Π-tower over a frame reads to the Π-tower of the readings**:
binder `k` read under the `k` earlier openers, the body under all. -/
theorem denoteMeta_instSeq_mkPisOf {m : EnvModel V env} {ψ : Name → Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (tl : List (Nat × Nat × AnnotTerm)) (body : Expr)
      (B : AnnotTerm) (L : List Expr) (D : Nat), L.length = D →
      (∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) →
      tl.length = tele.length →
      (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
        tele[k]? = some b → tl[k]? = some p →
        p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
          denoteMeta m.acval env ψ (D + k)
            (Expr.instSeq (L ++ openFvars D k) (D + k - 1) b.1) = some p.2.2) →
      denoteMeta m.acval env ψ (D + tele.length)
          (Expr.instSeq (L ++ openFvars D tele.length) (D + tele.length - 1) body) = some B →
      denoteMeta m.acval env ψ D (Expr.instSeq L (D - 1) (Expr.mkPisOf tele body))
        = some (mkPisAV tl B)
  | [], tl, body, B, L, D, _, _, hlen, _, hbody => by
    obtain rfl : tl = [] := List.eq_nil_of_length_eq_zero hlen
    rw [List.length_nil, Nat.add_zero, openFvars_zero, List.append_nil] at hbody
    exact hbody
  | (ty, mt) :: tele, tl, body, B, L, D, hL, hidxL, hlen, hbinders, hbody => by
    cases tl with
    | nil => simp at hlen
    | cons p tl' =>
    obtain ⟨hp1, hp2, hpty⟩ := hbinders 0 (ty, mt) p rfl rfl
    rw [Nat.add_zero, openFvars_zero, List.append_nil] at hpty
    have hnil : L = [] ∨ D - 1 + 1 = D := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · left
        exact List.eq_nil_of_length_eq_zero (by omega)
      · right
        omega
    have hlenL' : (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]).length = D + 1 := by
      rw [List.length_append, hL, List.length_singleton]
    have hidxL' : ∀ (k : Nat) (x : Expr),
        (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)])[k]? = some x →
        ∃ ty', x = Expr.fvar k ty' := by
      intro k x hx
      by_cases hk : k < D
      · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
        exact hidxL k x hx
      · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
        have hk0 : k - D = 0 := by
          rcases Nat.lt_or_ge (k - D) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by congr 1; omega⟩
    have hIH := denoteMeta_instSeq_mkPisOf tele tl' body B
      (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) (D + 1) hlenL' hidxL'
      (by simpa using hlen)
      (fun k b p' hb hp => by
        obtain ⟨h1, h2, h3⟩ := hbinders (k + 1) b p' (by simpa using hb) (by simpa using hp)
        refine ⟨h1, h2, ?_⟩
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) k (D + 1 + k - 1)
            (D + 1 + k) b.1,
          show D + 1 + k = D + (k + 1) from by omega]
        exact h3)
      (by
        rw [denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) tele.length
            (D + 1 + tele.length - 1) (D + 1 + tele.length) body,
          show D + 1 + tele.length = D + (tele.length + 1) from by omega]
        exact hbody)
    rw [Nat.add_sub_cancel] at hIH
    have hY : (Expr.instSeq L D (Expr.mkPisOf tele body)).instantiate1
        (Expr.fvar D (Expr.instSeq L (D - 1) ty)) 0
        = Expr.instSeq (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) D
            (Expr.mkPisOf tele body) := by
      rw [Expr.instSeq_append L [Expr.fvar D (Expr.instSeq L (D - 1) ty)], hL, Nat.sub_self]
      rfl
    show denoteMeta m.acval env ψ D
      (Expr.instSeq L (D - 1) (.forallE ty (Expr.mkPisOf tele body) mt)) = _
    rw [Expr.instSeq_forallE L (D - 1) _ _ _ (by omega),
      instSeq_idx_congr (sp := L) (t := D - 1 + 1) (t' := D) (Expr.mkPisOf tele body) hnil,
      denoteMeta_forallE, hpty, hY, hIH]
    show some (AnnotTerm.pi 0 (pwBit ψ mt.pw) p.2.2 (mkPisAV tl' B)) = some (mkPisAV (p :: tl') B)
    rw [show mkPisAV (p :: tl') B = AnnotTerm.pi p.1 p.2.1 p.2.2 (mkPisAV tl' B) from rfl, hp1, hp2]

set_option maxHeartbeats 1600000 in
/-- **A Π-tower over a frame, read**: the reading is the Π-tower of
the binders' readings over the body's. -/
theorem denoteMeta_instSeq_mkPisOf_inv {m : EnvModel V env} {ψ : Name → Nat} :
    ∀ (tele : List (Expr × BinderMeta)) (body : Expr) (L : List Expr) (D : Nat)
      (ea : AnnotTerm), L.length = D →
      (∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) →
      denoteMeta m.acval env ψ D (Expr.instSeq L (D - 1) (Expr.mkPisOf tele body)) = some ea →
      ∃ (tl : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ea = mkPisAV tl B ∧ tl.length = tele.length ∧
        (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
          tele[k]? = some b → tl[k]? = some p →
          p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
            denoteMeta m.acval env ψ (D + k)
              (Expr.instSeq (L ++ openFvars D k) (D + k - 1) b.1) = some p.2.2) ∧
        denoteMeta m.acval env ψ (D + tele.length)
          (Expr.instSeq (L ++ openFvars D tele.length) (D + tele.length - 1) body) = some B
  | [], body, L, D, ea, _, _, hread => by
    refine ⟨[], ea, rfl, rfl, ?_, ?_⟩
    · intro k b p hb _
      exact nomatch hb
    · rw [List.length_nil, Nat.add_zero, openFvars_zero, List.append_nil]
      exact hread
  | (ty, mt) :: tele, body, L, D, ea, hL, hidxL, hread => by
    have hnil : L = [] ∨ D - 1 + 1 = D := by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · left
        exact List.eq_nil_of_length_eq_zero (by omega)
      · right
        omega
    rw [show Expr.mkPisOf ((ty, mt) :: tele) body
        = .forallE ty (Expr.mkPisOf tele body) mt from rfl,
      Expr.instSeq_forallE L (D - 1) _ _ _ (by omega),
      instSeq_idx_congr (sp := L) (t := D - 1 + 1) (t' := D) (Expr.mkPisOf tele body) hnil]
      at hread
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hread
    have hlenL' : (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]).length = D + 1 := by
      rw [List.length_append, hL, List.length_singleton]
    have hidxL' : ∀ (k : Nat) (x : Expr),
        (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)])[k]? = some x →
        ∃ ty', x = Expr.fvar k ty' := by
      intro k x hx
      by_cases hk : k < D
      · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
        exact hidxL k x hx
      · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
        have hk0 : k - D = 0 := by
          rcases Nat.lt_or_ge (k - D) 1 with h | h
          · omega
          · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hx
            exact nomatch hx
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by congr 1; omega⟩
    have hY : (Expr.instSeq L D (Expr.mkPisOf tele body)).instantiate1
        (Expr.fvar D (Expr.instSeq L (D - 1) ty)) 0
        = Expr.instSeq (L ++ [Expr.fvar D (Expr.instSeq L (D - 1) ty)]) D
            (Expr.mkPisOf tele body) := by
      rw [Expr.instSeq_append L [Expr.fvar D (Expr.instSeq L (D - 1) ty)], hL, Nat.sub_self]
      rfl
    rw [hY] at hba
    obtain ⟨tl, B, rfl, hlen, hbinders, hbody⟩ :=
      denoteMeta_instSeq_mkPisOf_inv tele body _ (D + 1) ba hlenL' hidxL' hba
    refine ⟨(0, pwBit ψ mt.pw, ta) :: tl, B, rfl, by simp [hlen], ?_, ?_⟩
    · intro k b p hb hp
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hp
        subst hb
        subst hp
        refine ⟨rfl, rfl, ?_⟩
        rw [Nat.add_zero, openFvars_zero, List.append_nil]
        exact hta
      | succ k =>
        simp only [List.getElem?_cons_succ] at hb hp
        obtain ⟨h1, h2, h3⟩ := hbinders k b p hb hp
        refine ⟨h1, h2, ?_⟩
        rw [show D + (k + 1) = D + 1 + k from by omega,
          ← denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) k (D + 1 + k - 1)
            (D + 1 + k) b.1]
        exact h3
    · rw [List.length_cons, show D + (tele.length + 1) = D + 1 + tele.length from by omega,
        ← denoteMeta_frame_cons hL hidxL (Expr.instSeq L (D - 1) ty) tele.length
          (D + 1 + tele.length - 1) (D + 1 + tele.length) body]
      exact hbody

/-! ## The `ih` binders -/

/-- **What a recursive field contributes to the readings**: its own
telescope's binders, read at the constructor's frame (the parameters,
the `i` earlier fields, the telescope's own openers), are the datum's
entries — bits included — and its domain's index expressions, read
under the whole telescope, are the field's readings (task #202; a
finitary field: the telescope is empty and this is the old
`eisRead`). -/
@[expose] def FieldReadAt {env : Env} (m : EnvModel V env) (ψ : Name → Nat) (nP nF i : Nat) (cty : Expr)
    (fvs0 : List Expr) (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) : Prop :=
  tl.length = (ConLeche.structFieldTeleOf cty nP nF i).length ∧
  (∀ (k : Nat) (b : Expr × BinderMeta) (p : Nat × Nat × AnnotTerm),
    (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b → tl[k]? = some p →
    p.1 = 0 ∧ p.2.1 = pwBit ψ b.2.pw ∧
      denoteMeta m.acval env ψ (nP + i + k)
          (Expr.instSeq (fvs0.take (nP + i) ++ openFvars (nP + i) k) (nP + i + k - 1) b.1)
        = some p.2.2) ∧
  DenoteMetaSpine m.acval env ψ (nP + i + tl.length)
    ((ConLeche.structFieldIdxOf cty nP nF i).map
      (Expr.instSeq (fvs0.take (nP + i) ++ openFvars (nP + i) tl.length)
        (nP + i + tl.length - 1))) Eis

/-- **Every frame variable reads as itself** under an extension of the
frame by `n` fresh openers: the opening list is a descending fvar list,
and `denoteMeta` at the extended depth reads it straight back. -/
theorem denoteMeta_instSeq_ext_bvar {m : EnvModel V env} {ψ : Name → Nat}
    {L : List Expr} {D n q : Nat} (hL : L.length = D)
    (hidxL : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hq : q < D + n) :
    denoteMeta m.acval env ψ (D + n)
        (Expr.instSeq (L ++ openFvars D n) (D + n - 1) (Expr.bvar q))
      = some (AnnotTerm.bvar q) := by
  have hlenLA : (L ++ openFvars D n).length = D + n := by
    rw [List.length_append, hL, openFvars_length]
  have hidxLA : ∀ (k : Nat) (x : Expr), (L ++ openFvars D n)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    by_cases hk : k < D
    · rw [List.getElem?_append_left (by rw [hL]; omega)] at hx
      exact hidxL k x hx
    · rw [List.getElem?_append_right (by rw [hL]; omega), hL] at hx
      have hlt : k - D < n := by
        rcases Nat.lt_or_ge (k - D) n with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [openFvars_length]; omega)] at hx
          exact nomatch hx
      rw [openFvars_getElem? hlt] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact ⟨.sort .zero, by congr 1; omega⟩
  have hclLA : ∀ a ∈ L ++ openFvars D n, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨q', hq'⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidxLA q' a hq'
    rfl
  have hb := Expr.instSeq_bvar (L ++ openFvars D n) (D + n - 1) q hclLA (by omega)
    (by rw [hlenLA]; omega)
  obtain ⟨ty, hy⟩ := hidxLA _ _ hb
  rw [hy, denoteMeta_fvar, show D + n - 1 - (D + n - 1 - q) = q from by omega]

set_option maxHeartbeats 3200000 in
/-- **The generated `ih` spine, read at ANY head and any leading
arguments** (task #315, M5): the field's telescope moved binderwise
(`denoteMeta_ihIdxAtM` at each binder), then the head applied to the
leading arguments, the field's index readings and the field at the
telescope's own variables.

The one-member route's `ih` DOMAIN (`denoteMeta_ihDom` below) is the
instance at the MOTIVE (`hd = .bvar (nF + o - 1 + l + m)`, no leading
arguments); the uniform route's guarded CALL
(`blockIhSpinePis`, `Kernel/Inductives/BlockRec.lean`) is the instance
at a CALLEE RECURSOR (`hd = .const rec_{c'} us`) with the rule's own
prefix variables in front.  The two differ in nothing else, which is
why this is one theorem. -/
theorem denoteMeta_ihSpineAt {m : EnvModel V env} {ψ : Name → Nat} {nP nF o l i : Nat}
    {pw : PropWhen} {cty : Expr}
    {fvs0 : List Expr} {crest : Expr} {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hop0 : openPisAtFvars (nP + nF) cty 0 = some (fvs0, crest))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs0 tl Eis)
    {P X F I : List Expr} (hP : P.length = nP) (hX : X.length = o) (hF : F.length = nF)
    (hI : I.length = l)
    (hidxP : ∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hidxX : ∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty)
    (hidxF : ∀ (k : Nat) (x : Expr), F[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + k) ty)
    (hidxI : ∀ (k : Nat) (x : Expr), I[k]? = some x →
      ∃ ty, x = Expr.fvar (nP + o + nF + k) ty)
    {hd : Expr} {pre : List Expr} {hdA : AnnotTerm} {preA : List AnnotTerm}
    (hhd : denoteMeta m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) hd)
        = some hdA)
    (hpre : DenoteMetaSpine m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
        (pre.map (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1))) preA) :
    denoteMeta m.acval env ψ (nP + o + nF + l)
        (Expr.instSeq (P ++ X ++ F ++ I) (nP + o + nF + l - 1)
          (Expr.mkPisOf (ConLeche.structTeleAt nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i))
            (Expr.mkAppN hd
              (pre ++ (ConLeche.structFieldIdxOf cty nP nF i).map
                  (ConLeche.structIdxAt nF o i l (ConLeche.structFieldTeleOf cty nP nF i).length) ++
                [Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
                  (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)]))))
      = some (mkPisAV (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl))
          (AnnotTerm.mkAppN hdA
            (preA ++ Eis.map (ihIdxAtM nF o i l (ConLeche.structFieldTeleOf cty nP nF i).length) ++
              [AnnotTerm.mkAppN
                (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
                (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)]))) := by
  obtain ⟨hlenTl, hbind, hspSrc⟩ := hfr
  obtain ⟨hlen0, hidx0, hcl0, hw0⟩ := opening_vars hop0 hCf
  have hS : (fvs0.take (nP + i)).length = nP + i := by
    rw [List.length_take, hlen0]
    omega
  have hidxS : ∀ (k : Nat) (x : Expr), (fvs0.take (nP + i))[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP + i := by
      rcases Nat.lt_or_ge k (nP + i) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hS]; omega)] at hx
        exact nomatch hx
    rw [List.getElem?_take, if_pos hk] at hx
    exact hidx0 k x hx
  have hprops := structFieldTele_props hCf hCb hstripC hi
  have hlenL : (P ++ X ++ F ++ I).length = nP + o + nF + l := by
    rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hI]
  have hLidx := frameIdx hP hX hF hidxP hidxX hidxF hidxI
  have hbvarA : ∀ q : Nat, q < nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length →
      denoteMeta m.acval env ψ (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1) (Expr.bvar q))
        = some (AnnotTerm.bvar q) :=
    fun q hq => denoteMeta_instSeq_ext_bvar hlenL hLidx hq
  refine denoteMeta_instSeq_mkPisOf _ (ihTeleAtR nF o i l (rebit (pwBit ψ pw) tl)) _ _
    (P ++ X ++ F ++ I) (nP + o + nF + l) hlenL hLidx
    (by rw [ihTeleAtR_length, rebit_length, structTeleAt_length, hlenTl]) ?_ ?_
  · -- the telescope, binderwise
    intro k b p hb hp
    have hk : k < (ConLeche.structFieldTeleOf cty nP nF i).length := by
      rw [← structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
      exact (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, (ConLeche.structFieldTeleOf cty nP nF i)[k]? = some b₀ :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    rw [structTeleAt_getElem? (pw := pw) hb₀] at hb
    obtain rfl := (Option.some.inj hb).symm
    obtain ⟨d, hd⟩ : ∃ d, tl[k]? = some d := ⟨_, List.getElem?_eq_getElem (by rw [hlenTl]; exact hk)⟩
    rw [ihTeleAtR, ihTeleAtGo_getElem? nF o i l 0 _ k, rebit, List.getElem?_map, hd] at hp
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
    obtain rfl := hp.symm
    obtain ⟨h1, -, h3⟩ := hbind k b₀ d hb₀ hd
    obtain ⟨hef, heb⟩ := hprops.1 k b₀ hb₀
    exact ⟨h1, rfl, denoteMeta_ihIdxAtM hef heb (Nat.le_of_lt hi) hS hidxS hP hX hF hI hidxP hidxF h3⟩
  · -- the head at the leading arguments, the field's readings and the field at its telescope
    rw [structTeleAt_length nF o i l pw (ConLeche.structFieldTeleOf cty nP nF i)]
    have hspI := denoteMetaSpine_ihIdx (m := m) (ψ := ψ) (o := o) (l := l) hCf hCb hstripC hi rfl
      hS hidxS (by rw [hlenTl] at hspSrc; exact hspSrc) hP hX hF hI hidxP hidxF
    have hfieldApp : denoteMeta m.acval env ψ
        (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length)
          (Expr.instSeq (P ++ X ++ F ++ I ++ openFvars (nP + o + nF + l)
              (ConLeche.structFieldTeleOf cty nP nF i).length)
            (nP + o + nF + l + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)
            (Expr.mkAppN (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
              (ConLeche.structTeleVars (ConLeche.structFieldTeleOf cty nP nF i).length)))
        = some (AnnotTerm.mkAppN
            (.bvar (nF - 1 - i + l + (ConLeche.structFieldTeleOf cty nP nF i).length))
            (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)) := by
      rw [Expr.instSeq_mkAppN]
      refine denoteMeta_mkAppN ?_ (hbvarA _ (by omega))
      unfold ConLeche.structTeleVars teleVarsAV
      rw [List.map_map]
      simp only [Function.comp_def]
      exact DenoteMetaSpine.of_map (List.range (ConLeche.structFieldTeleOf cty nP nF i).length)
        (fun k hk => hbvarA _ (by rw [List.mem_range] at hk; omega))
    rw [Expr.instSeq_mkAppN, List.map_append, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    simp only [Function.comp_def]
    rw [denoteMeta_mkAppN ((hpre.append hspI).append (.cons hfieldApp .nil)) hhd]

end ConLeche.Model
