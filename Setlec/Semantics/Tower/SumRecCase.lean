import Setlec.Semantics.Tower.SumMk
import Setlec.Semantics.Tower.TowerRec
import Setlec.Semantics.Univ

/-!
# The sum recursor's case split, spelled (task #175 sum-types, stage S4a; indexed)

The body of a direct sum's recursor cases on the major's tag with a
nested `Nat.rec` tower (`caseRecAV`): stage `j` is a `Nat.rec` whose
motive is `λ k, Π (y : case (drop j) k), M ı⃗ (mk (succ^j k) y)`, whose
base is constructor `j`'s branch `λ (y : T_j), m_j (y.0) … (y.(nF_j - 1))`
(the minor applied along the uniform projections of the payload —
`towerRec`'s witness, as in the structure route; the payload's last
component, the index-equation proof, is not passed), and whose step
descends to stage `j + 1` on the predecessor tag; past the last
constructor the branch is the vacuous `λ (y : Empty), prf`.

**The frame** (task #175 indexed).  Every piece is spelled at an
explicit depth `D` below the recursor's **K-frame** — the frame
`(p⃗, motive, minors, ı⃗)` holding the parameters, the motive, the `n`
minors and the `nIdx` index variables — so the motive is `bvar (D +
nIdx + n)`, minor `j` is `bvar (D + nIdx + n - 1 - j)` and index `l` is
`bvar (D + nIdx - 1 - l)` (`RecFrameS`, with the values `frM`/`frMs`/
`frameIdx` read off the K-frame valuation `ρ₀`); the constructor
chains are the restricted chains `rChains (nIdx + n + 1) nIdx Fss Ess`
scoped at the K-frame (the field chains lifted from the parameter
frame `frP = shiftE (nIdx + n + 1) 0 ρ₀`, followed by the index
equation), and the motive is applied to the index variables before
the injection.  A plain sum is the `nIdx = 0` instance.  The nesting
(two binders per stage) is plain arithmetic and no substitution is
ever performed.

Semantically the stage-`j` motive at the numeral `i` is the product
`piR ℓ (f (j + i)) (λ y, Mi (inj (j + i) y))` (`motSem`, `Mi` the
motive at the frame's index tuple), the branch is `baseSem`, and the
three facts — membership in the motive, iota (the selected branch),
and grading — are one induction on the remaining constructor count
(`caseRec_facts`).  The minor space `minorSpI` is the structure
route's `minorSp` with an explicit conclusion function (`concI`: the
motive at the constructor's index tuple, at the injection of the
point-terminated tupler); the motive's own typing is the nested
product over the index telescope (`piTele`), from which its
applications at ANY tuple are truth values at a zero elimination
level (`piTele_app_univZero`: a fitting tuple lands in the motive's
space, an unfitting one in junk).  **The index equation is
discharged at the branch**: a payload of the restricted tower has its
index tuple equal to the frame's (`restricted_member_elim`), so the
minor's conclusion at the payload's projections IS the motive at the
frame's indices.  The case split serves the graph regime only (`w ≠
0`): at a squash instantiation the recursor body is spelled without
it (`Setlec/Semantics/Tower/SumRec.lean`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Numerals under successors -/

/-- `Nat.succ^j k`. -/
def succsAV : Nat → AVExpr → AVExpr
  | 0, k => k
  | j + 1, k => .app (.const .natSucc []) (succsAV j k)

theorem interp2_succsAV : ∀ (j : Nat) {k : AVExpr} {σ : Nat → V} {i : Nat},
    interp2 V σ k = vnat i → interp2 V σ (succsAV j k) = vnat (i + j)
  | 0, _, _, _, h => h
  | j + 1, k, σ, i, h => by
    show SetTheory.app (natSuccV2 V) (interp2 V σ (succsAV j k)) = vsucc (vnat (i + j))
    rw [interp2_succsAV j h, natSuccV2_app V (vnat_mem_omega _), natsucc_eq_vsucc]

theorem succsAV_ok2 : ∀ (j : Nat) {k : AVExpr} {σ : Nat → V} {i : Nat},
    AnnotOk2 V σ k → interp2 V σ k = vnat i → AnnotOk2 V σ (succsAV j k)
  | 0, _, _, _, hok, _ => hok
  | j + 1, k, σ, i, hok, h => by
    show AnnotOk2 V σ (.app (.const .natSucc []) (succsAV j k))
    rw [AnnotOk2_app]
    refine ⟨trivial, succsAV_ok2 j hok h, 1, omega, fun _ => omega, natSuccV2_mem V, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    rw [interp2_succsAV j h]
    exact vnat_mem_omega _

/-! ## The nested product over a telescope -/

/-- The nested product over a semantic telescope, the body at the
accumulated tuple. -/
noncomputable def piTele (v : Nat) : {k : Nat} → TeleS V k → (List V → V) → List V → V
  | _, .nil, B, acc => B acc
  | _, .cons A T, B, acc => piR v A fun a => piTele v (T a) B (acc ++ [a])

/-- A member of the nested product folds along a fitting tuple into
the body. -/
theorem piTele_fold {v : Nat} (hv : v ≠ 0) {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {f : V} {as : List V},
      f ∈ˢ piTele v T B acc → FitsS T as → as.foldl SetTheory.app f ∈ˢ B (acc ++ as)
  | _, .nil, acc, f, [], hf, _ => by simpa [piTele] using hf
  | _, .nil, _, _, _ :: _, _, hfit => hfit.elim
  | _, .cons _ _, _, _, [], _, hfit => hfit.elim
  | _, .cons A T, acc, f, a :: as, hf, hfit => by
    have := piTele_fold hv (T := T a) (acc := acc ++ [a]) (f := SetTheory.app f a) (as := as)
      (app_mem_piR_pos hv hf hfit.1) hfit.2
    rw [List.append_assoc, List.singleton_append] at this
    rw [List.foldl_cons]
    exact this

/-- The application chain `M i₀ … i_{k-1}` is graded: each prefix is a
member of a product the next index inhabits. -/
def AppChainOk (M : V) (is : List V) : Prop :=
  ∀ l, l < is.length → ∃ (v : Nat) (A : V) (B : V → V),
    (is.take l).foldl SetTheory.app M ∈ˢ piR v A B ∧ is.getD l pt ∈ˢ A ∧
    (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))

/-- The application chain along a fitting tuple is graded. -/
theorem piTele_chainOk {v : Nat} (hv : v ≠ 0) {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {f : V} {as : List V},
      f ∈ˢ piTele v T B acc → FitsS T as → AppChainOk f as
  | _, .nil, _, _, [], _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | _, .nil, _, _, _ :: _, _, hfit => hfit.elim
  | _, .cons _ _, _, _, [], _, hfit => hfit.elim
  | _, .cons A T, acc, f, a :: as, hf, hfit => by
    intro l hl
    cases l with
    | zero =>
      exact ⟨v, A, _, hf, hfit.1, fun h => absurd h hv⟩
    | succ l =>
      have ih := piTele_chainOk hv (T := T a) (acc := acc ++ [a]) (f := SetTheory.app f a)
        (as := as) (app_mem_piR_pos hv hf hfit.1) hfit.2 l (by simpa using hl)
      obtain ⟨v', A', B', hm, ha, hz⟩ := ih
      exact ⟨v', A', B', by simpa using hm, by simpa using ha, hz⟩

theorem foldl_app_empty : ∀ (as : List V), as.foldl SetTheory.app (empty : V) = empty
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_empty]; exact foldl_app_empty as

/-- A member of the nested product applied along ANY tuple of the
telescope's length is either in the body (the tuple fits) or junk. -/
theorem piTele_fold_or_empty {v : Nat} (hv : v ≠ 0) {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {f : V} {as : List V},
      f ∈ˢ piTele v T B acc → as.length = k →
      as.foldl SetTheory.app f ∈ˢ B (acc ++ as) ∨ as.foldl SetTheory.app f = empty
  | _, .nil, acc, f, [], hf, _ => Or.inl (by simpa [piTele] using hf)
  | _, .nil, _, _, _ :: _, _, hlen => by simp at hlen
  | _, .cons _ _, _, _, [], _, hlen => by simp at hlen
  | _, .cons A T, acc, f, a :: as, hf, hlen => by
    by_cases ha : a ∈ˢ A
    · have := piTele_fold_or_empty hv (T := T a) (acc := acc ++ [a]) (f := SetTheory.app f a)
        (as := as) (app_mem_piR_pos hv hf ha) (by simpa using hlen)
      rw [List.append_assoc, List.singleton_append] at this
      rw [List.foldl_cons]
      exact this
    · right
      rw [List.foldl_cons, (mem_piR_pos hv hf).2.2.1 a ha, foldl_app_empty]

/-- **The motive's applications are truth values at a zero
elimination level, at any tuple**: a fitting tuple lands in the motive
space (whose applications are in `univ 0`, or junk off the carrier),
an unfitting one is junk throughout. -/
theorem piTele_app_univZero {ℓ : Nat} (h0 : ℓ = 0) {famAt : List V → V}
    {k : Nat} {T : TeleS V k} {M : V}
    (hM : M ∈ˢ piTele (ℓ + 1) T (fun is' => piR (ℓ + 1) (famAt is') fun _ => (univ ℓ : V)) [])
    {as : List V} (hlen : as.length = k) (x : V) :
    SetTheory.app (as.foldl SetTheory.app M) x ∈ˢ (univZero : V) := by
  rcases piTele_fold_or_empty (Nat.succ_ne_zero ℓ) hM hlen with hin | hjunk
  · rw [List.nil_append] at hin
    by_cases hx : x ∈ˢ famAt as
    · have := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hin hx
      rw [h0, univ_zero] at this
      exact this
    · rw [(mem_piR_pos (Nat.succ_ne_zero ℓ) hin).2.2.1 x hx, ← univ_zero]
      exact empty_mem_univ 0
  · rw [hjunk, app_empty, ← univ_zero]
    exact empty_mem_univ 0

/-! ## The generalized minor space -/

/-- The minor space with an explicit conclusion: the Π-tower over the
field chain (bit `ℓ`) ending in the conclusion at the accumulated
tuple. -/
noncomputable def minorSpI (ℓ : Nat) (c : List V → V) :
    List AVExpr → (Nat → V) → List V → V
  | [], _, acc => c acc
  | F :: Fs, ρf, acc => piR ℓ (interp2 V ρf F)
      fun a => minorSpI ℓ c Fs (cons a ρf) (acc ++ [a])

/-- Constructor `j`'s value at a field tuple: the injection of the
point-terminated tupler, the point at squash. -/
noncomputable def ctorValI (w j : Nat) (acc : List V) : V :=
  if w = 0 then pt else inj j (mkTower (acc ++ [pt]))

/-- Constructor `j`'s minor conclusion at a field tuple: the motive at
the constructor's index tuple (read at the parameter frame), applied
to the constructor's value. -/
noncomputable def concI (w : Nat) (ρp : Nat → V) (M : V) (Es : List AVExpr) (j : Nat)
    (acc : List V) : V :=
  SetTheory.app ((idxValsAt ρp Es acc).foldl SetTheory.app M) (ctorValI w j acc)

theorem minorSpI_zero_univZero {ℓ : Nat} {c : List V → V} (h0 : ℓ = 0)
    (hc : ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ (Fs : List AVExpr) (ρf : Nat → V) (acc : List V),
      minorSpI ℓ c Fs ρf acc ∈ˢ (univZero : V)
  | [], _, _ => hc _
  | _ :: _, _, _ => by
    show piR ℓ _ _ ∈ˢ _
    rw [h0]
    exact piR_zero_mem_univZero

/-- The graded fold of a minor-space member along a graded fitting
spine (`minorSp_spine` with the explicit conclusion). -/
theorem minorSpI_spine {ℓ : Nat} {c : List V → V}
    (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs args : List AVExpr} {ρf : Nat → V} {acc : List V} {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f → interp2 V σ f ∈ˢ minorSpI ℓ c Fs ρf acc →
      ArgsOkFit σ args Fs ρf →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧
        interp2 V σ (AVExpr.mkAppN f args) ∈ˢ c (acc ++ args.map (interp2 V σ))
  | [], [], _, acc, f, σ, hokf, hmf, _ => by
    refine ⟨hokf, ?_⟩
    show interp2 V σ f ∈ˢ c (acc ++ [])
    rw [List.append_nil]
    exact hmf
  | [], _ :: _, _, _, _, _, _, _, hfit => hfit.elim
  | _ :: _, [], _, _, _, _, _, _, hfit => hfit.elim
  | F :: Fs, a :: args, ρf, acc, f, σ, hokf, hmf, hfit => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp2 V ρf F →
        minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app (interp2 V σ f) (interp2 V σ a)
        ∈ˢ minorSpI ℓ c Fs (cons (interp2 V σ a) ρf) (acc ++ [interp2 V σ a]) :=
      app_mem_piR hmf hfit.2.1 hB0
    have hoka : AnnotOk2 V σ (.app f a) := by
      rw [AnnotOk2_app]
      exact ⟨hokf, hfit.1, ⟨ℓ, interp2 V ρf F, _, hmf, hfit.2.1, hB0⟩⟩
    have hres := minorSpI_spine hc0 (Fs := Fs) (args := args) (f := .app f a) hoka happ hfit.2.2
    refine ⟨hres.1, ?_⟩
    have hassoc : (acc ++ [interp2 V σ a]) ++ args.map (interp2 V σ)
        = acc ++ (a :: args).map (interp2 V σ) := by simp
    rw [hassoc] at hres
    exact hres.2

/-- At elimination level `0` the minor space is inhabited exactly when
the conclusion is inhabited along a fitting spine. -/
theorem minorSpI_zero_inhab {c : List V → V} :
    ∀ {Fs : List AVExpr} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI 0 c Fs ρf acc → SpineFit ρf Fs as →
      ∃ y, y ∈ˢ c (acc ++ as)
  | [], _, acc, m, [], hm, _ => ⟨m, by simpa [minorSpI] using hm⟩
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have hm' : m ∈ˢ piR 0 (interp2 V ρf F)
      (fun a => minorSpI 0 c Fs (cons a ρf) (acc ++ [a])) := hm
    rw [piR_zero] at hm'
    obtain ⟨y, hy⟩ := of_mem_truthVal hm' a hsp.1
    have h := minorSpI_zero_inhab hy hsp.2
    rwa [List.append_assoc, List.singleton_append] at h

/-- The fit of the projection spine from a fitting spine of the
projections' values and their gradings. -/
theorem argsOkFit_of_projSpine {σ ρf : Nat → V} {y : V} :
    ∀ {Fs : List AVExpr} {k : Nat},
      SpineFit ρf Fs ((List.range' k Fs.length).map fun i => projS i y) →
      (∀ i, k ≤ i → i < k + Fs.length → AnnotOk2 V σ (projAV i (.bvar 0))) →
      (∀ i, interp2 V σ (projAV i (.bvar 0)) = projS i y) →
      ArgsOkFit σ ((List.range' k Fs.length).map fun i => projAV i (.bvar 0)) Fs ρf
  | [], _, _, _, _ => trivial
  | F :: Fs, k, hsp, hok, hv => by
    rw [List.length_cons] at hsp hok ⊢
    rw [List.range'_succ, List.map_cons] at hsp ⊢
    refine ⟨hok k (Nat.le_refl _) (by omega), by rw [hv]; exact hsp.1, ?_⟩
    rw [hv]
    exact argsOkFit_of_projSpine hsp.2 (fun i h1 h2 => hok i (by omega) (by omega)) hv

/-! ## The K-frame -/

/-- The recursor body's frame invariant at depth `D` below the K-frame
`ρ₀`. -/
def RecFrameS (D : Nat) (ρ₀ σ : Nat → V) : Prop := shiftE D 0 σ = ρ₀

/-- The motive's value at the K-frame. -/
def frM (n nIdx : Nat) (ρ₀ : Nat → V) : V := ρ₀ (nIdx + n)

/-- Minor `j`'s value at the K-frame. -/
def frMs (n nIdx : Nat) (ρ₀ : Nat → V) (j : Nat) : V := ρ₀ (nIdx + n - 1 - j)

/-- The motive at the frame's index tuple. -/
noncomputable def frMi (n nIdx : Nat) (ρ₀ : Nat → V) : V :=
  (frameIdx nIdx ρ₀).foldl SetTheory.app (frM n nIdx ρ₀)

/-- The parameter frame under the K-frame. -/
def frP (n nIdx : Nat) (ρ₀ : Nat → V) : Nat → V := shiftE (nIdx + n + 1) 0 ρ₀

omit [SetTheory V] in
theorem RecFrameS.apply {D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) (i : Nat) :
    σ (D + i) = ρ₀ i := by
  have := congrFun h i
  simp only [shiftE, Nat.not_lt_zero, if_false] at this
  rw [Nat.add_comm]; exact this

omit [SetTheory V] in
theorem RecFrameS.step {D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) (a b : V) :
    RecFrameS (D + 2) ρ₀ (cons a (cons b σ)) := by
  unfold RecFrameS at *
  rw [shiftE_step, h]

omit [SetTheory V] in
theorem RecFrameS.push {D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) (a : V) :
    RecFrameS (D + 1) ρ₀ (cons a σ) := by
  unfold RecFrameS at *
  rw [shiftE_succ_cons, h]

omit [SetTheory V] in
theorem RecFrameS.motive {n nIdx D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) :
    σ (D + nIdx + n) = frM n nIdx ρ₀ := by
  rw [show D + nIdx + n = D + (nIdx + n) from by omega, h.apply]; rfl

omit [SetTheory V] in
theorem RecFrameS.minor {n nIdx D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) {j : Nat}
    (hj : j < n) : σ (D + nIdx + n - 1 - j) = frMs n nIdx ρ₀ j := by
  rw [show D + nIdx + n - 1 - j = D + (nIdx + n - 1 - j) from by omega, h.apply]; rfl

theorem RecFrameS.idx {nIdx D : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D ρ₀ σ) {l : Nat}
    (hl : l < nIdx) : σ (D + nIdx - 1 - l) = (frameIdx nIdx ρ₀).getD l pt := by
  rw [show D + nIdx - 1 - l = D + (nIdx - 1 - l) from by omega, h.apply]
  unfold frameIdx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

omit [SetTheory V] in
theorem frameIdx_length (nIdx : Nat) (ρ₀ : Nat → V) : (frameIdx nIdx ρ₀).length = nIdx := by
  simp [frameIdx]

/-! ## The spelled pieces -/

/-- The index variables at depth `D'` below the K-frame. -/
def idxVarsAV (nIdx D' : Nat) : List AVExpr :=
  (List.range nIdx).map fun l => .bvar (D' + nIdx - 1 - l)

/-- The motive applied to the index variables at depth `D'`. -/
def motAppAV (n nIdx D' : Nat) : AVExpr :=
  AVExpr.mkAppN (.bvar (D' + nIdx + n)) (idxVarsAV nIdx D')

/-- The index variables read to the frame's index tuple. -/
theorem map_idxVarsAV_interp {nIdx D' : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D' ρ₀ σ) :
    (idxVarsAV nIdx D').map (interp2 V σ) = frameIdx nIdx ρ₀ := by
  unfold idxVarsAV frameIdx
  rw [List.map_map]
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_def, interp2_bvar]
  rw [show D' + nIdx - 1 - l = D' + (nIdx - 1 - l) from by
      have := List.mem_range.mp hl; omega,
    h.apply]

/-- An application spine graded by the chain: its grading and its
value as the fold. -/
theorem mkAppN_ok2_of_chain :
    ∀ {args : List AVExpr} {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f → (∀ a ∈ args, AnnotOk2 V σ a) →
      AppChainOk (interp2 V σ f) (args.map (interp2 V σ)) →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧
        interp2 V σ (AVExpr.mkAppN f args)
          = (args.map (interp2 V σ)).foldl SetTheory.app (interp2 V σ f)
  | [], _, _, hf, _, _ => ⟨hf, rfl⟩
  | a :: args, f, σ, hf, hargs, hchain => by
    obtain ⟨v, A, B, hm, ha, hz⟩ := hchain 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.map_cons, List.getD_cons_zero] at hm ha
    have hoka : AnnotOk2 V σ (.app f a) := by
      rw [AnnotOk2_app]
      exact ⟨hf, hargs a List.mem_cons_self, v, A, B, hm, ha, hz⟩
    have hchain' : AppChainOk (interp2 V σ (.app f a)) (args.map (interp2 V σ)) := by
      intro l hl
      obtain ⟨v', A', B', hm', ha', hz'⟩ := hchain (l + 1) (by simpa using hl)
      simp only [List.map_cons, List.take_succ_cons, List.foldl_cons, List.getD_cons_succ] at hm' ha'
      exact ⟨v', A', B', hm', ha', hz'⟩
    have ih := mkAppN_ok2_of_chain (args := args) (f := .app f a) hoka
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) hchain'
    rw [AVExpr.mkAppN_cons]
    exact ⟨ih.1, by rw [ih.2, List.map_cons, List.foldl_cons]; rfl⟩

/-- The stage-`j` motive body, under the motive's own tag binder
(`k = bvar 0`), at depth `D`: `Π (y : case (drop j) k), M ı⃗ (mk k y)`. -/
def caseMotiveBodyAV (ℓ w : Nat) (Fss : List (List AVExpr)) (n nIdx D j : Nat) : AVExpr :=
  .pi w ℓ (caseAVAt w ((Fss.map (towerBodyAV w)).drop j) (D + 1) (.bvar 0))
    (.app (motAppAV n nIdx (D + 2)) (sumInjAtAV w Fss (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))

/-- The numeral `imax w ℓ`. -/
def imaxN (w ℓ : Nat) : Nat := if ℓ = 0 then 0 else Nat.max w ℓ

theorem imaxN_zero (w : Nat) : imaxN w 0 = 0 := if_pos rfl
theorem imaxN_pos (w : Nat) {ℓ : Nat} (hℓ : ℓ ≠ 0) : imaxN w ℓ = Nat.max w ℓ := if_neg hℓ
theorem imaxN_eq_zero_iff (w ℓ : Nat) : imaxN w ℓ = 0 ↔ ℓ = 0 := by
  unfold imaxN
  by_cases h : ℓ = 0
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h' => absurd (Nat.le_zero.mp (h' ▸ Nat.le_max_right w ℓ)) h, fun h' => absurd h' h⟩

/-- The stage-`j` motive. -/
def caseMotiveAV (ℓ w : Nat) (Fss : List (List AVExpr)) (n nIdx D j : Nat) : AVExpr :=
  .lam (imaxN w ℓ + 1) natAV (caseMotiveBodyAV ℓ w Fss n nIdx D j)

/-- Constructor `j`'s branch at depth `D`: `λ (y : T_j), m_j (y.0) … (y.(nF - 1))`
over the first `ar j` projections (the field count — the restricted
tower's last component is the index-equation proof). -/
def caseBaseAV (ℓ w : Nat) (Fss : List (List AVExpr)) (ar : Nat → Nat) (n nIdx D j : Nat) :
    AVExpr :=
  .lam ℓ ((towerBodyAV w (Fss.getD j [])).liftN D 0)
    (AVExpr.mkAppN (.bvar (D + 1 + nIdx + n - 1 - j))
      ((List.range (ar j)).map fun i => projAV i (.bvar 0)))

/-- The case recursor from stage `j` with `r` constructors remaining,
at depth `D`, on the tag `k`. -/
def caseRecAV (ℓ w : Nat) (Fss : List (List AVExpr)) (ar : Nat → Nat) (n nIdx : Nat) :
    Nat → Nat → Nat → AVExpr → AVExpr
  | 0, _, _, _ => .lam ℓ (.const .empty [w]) .prf
  | r + 1, D, j, k =>
    natRecAV (imaxN w ℓ) (caseMotiveAV ℓ w Fss n nIdx D j) (caseBaseAV ℓ w Fss ar n nIdx D j)
      (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss n nIdx D j)
        (caseRecAV ℓ w Fss ar n nIdx r (D + 2) (j + 1) (.bvar 1))))
      k

/-! ## The semantic pieces -/

/-- The stage-`j` motive at a tag: the product over the `(j + i)`-th
fibre into the motive (at the frame's indices) at the injection. -/
noncomputable def motSem (ℓ w : Nat) (f : Nat → V) (Mi : V) (j : Nat) (k : V) : V :=
  natFibre (fun i => piR ℓ (f (j + i)) fun y => SetTheory.app Mi (injW w (j + i) y)) k

theorem motSem_vnat (ℓ w : Nat) (f : Nat → V) (Mi : V) (j i : Nat) :
    motSem ℓ w f Mi j (vnat i) = piR ℓ (f (j + i)) fun y => SetTheory.app Mi (injW w (j + i) y) :=
  natFibre_vnat _ i

/-- Constructor `j`'s branch: the minor applied along the payload's
first `nF` projections. -/
noncomputable def baseSem (ℓ : Nat) (f : Nat → V) (ms : Nat → V) (nF j : Nat) : V :=
  lamR ℓ (f j) fun y => ((List.range nF).map fun i => projS i y).foldl SetTheory.app (ms j)

/-! ## The hypotheses of the stage facts -/

/-- The semantic hypotheses of the recursor body at the K-frame `ρ₀`:
the restricted chains graded, the motive in the nested product over
the index telescope (`Ids`, read at the parameter frame) into the
family's carriers (`famAt`, the frame's tuple's carrier being the
tagged union of the restricted chains), the frame's index tuple
fitting the telescope, every minor in its space (over the field chain
at the parameter frame, with the conclusion `concI`), and the
counts. -/
structure RecHypS (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr))
    (Ids : List AVExpr) (famAt : List V → V) : Prop where
  hok : SumFieldsOkB w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
  hEs : ∀ j, j < Fss.length → (Ess.getD j []).length = Ids.length
  hlenE : Ess.length = Fss.length
  hMtele : frM Fss.length Ids.length ρ₀
    ∈ˢ piTele (ℓ + 1) (teleOfFields (frP Fss.length Ids.length ρ₀) Ids)
      (fun is' => piR (ℓ + 1) (famAt is') fun _ => (univ ℓ : V)) []
  hfit : SpineFit (frP Fss.length Ids.length ρ₀) Ids (frameIdx Ids.length ρ₀)
  hfam : famAt (frameIdx Ids.length ρ₀)
    = sumSet w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
  hms : ∀ j, j < Fss.length →
    frMs Fss.length Ids.length ρ₀ j
      ∈ˢ minorSpI ℓ
        (concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j)
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) []

namespace RecHypS

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
  {famAt : List V → V}

/-- The motive at the frame's index tuple is in its space. -/
theorem hM (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) :
    frMi Fss.length Ids.length ρ₀
      ∈ˢ piR (ℓ + 1) (sumSet w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)))
        fun _ => (univ ℓ : V) := by
  have := piTele_fold (Nat.succ_ne_zero ℓ) h.hMtele (fitsS_teleOfFields.mpr h.hfit)
  rw [List.nil_append, h.hfam] at this
  exact this

/-- The motive's index applications are graded. -/
theorem hMchain (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) :
    AppChainOk (frM Fss.length Ids.length ρ₀) (frameIdx Ids.length ρ₀) :=
  piTele_chainOk (Nat.succ_ne_zero ℓ) h.hMtele (fitsS_teleOfFields.mpr h.hfit)

/-- The motive's applications are truth values at a zero elimination
level, at any index tuple of the right length. -/
theorem hMapp0 (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (h0 : ℓ = 0) {is' : List V}
    (hlen : is'.length = Ids.length) (x : V) :
    SetTheory.app (is'.foldl SetTheory.app (frM Fss.length Ids.length ρ₀)) x ∈ˢ (univZero : V) :=
  piTele_app_univZero h0 h.hMtele hlen x

/-- The motive's applications are truth values at a zero elimination
level (at the frame's tuple). -/
theorem hM0 (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (h0 : ℓ = 0) :
    ∀ y : V, SetTheory.app (frMi Fss.length Ids.length ρ₀) y ∈ˢ (univZero : V) :=
  fun y => h.hMapp0 h0 (frameIdx_length _ _) y

/-- The motive at a carrier member lives in `univ ℓ`. -/
theorem hMapp (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) {y : V}
    (hy : y ∈ˢ sumSet w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))) :
    SetTheory.app (frMi Fss.length Ids.length ρ₀) y ∈ˢ (univ ℓ : V) :=
  app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hM hy

/-- The fibres live in `univ w`. -/
theorem fibre_univ (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (i : Nat) :
    sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) i ∈ˢ (univ w : V) := by
  unfold sumFibre
  cases hi : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[i]? with
  | none => exact empty_mem_univ w
  | some Fs => exact towerSet_univ_of_okB (fun hw => (h.hok Fs (List.mem_of_getElem? hi)).toBound hw)

/-- The stage motive at a numeral lives in `univ (imax w ℓ)`. -/
theorem motSem_univ (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (j i : Nat) :
    motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
      (frMi Fss.length Ids.length ρ₀) j (vnat i) ∈ˢ (univ (imaxN w ℓ) : V) := by
  rw [motSem_vnat]
  have := piR_mem_univ (u := w) (v := ℓ) (h.fibre_univ (j + i))
    (fun y hy => h.hMapp (injW_mem hy))
  exact this

/-- The conclusion at a zero elimination level is a truth value. -/
theorem conc_univZero (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (h0 : ℓ = 0) {j : Nat}
    (hj : j < Fss.length) :
    ∀ acc, concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀)
      (Ess.getD j []) j acc ∈ˢ (univZero : V) := by
  intro acc
  show SetTheory.app ((idxValsAt _ _ acc).foldl SetTheory.app _) (ctorValI w j acc) ∈ˢ _
  exact h.hMapp0 h0 (by rw [idxValsAt, List.length_map]; exact h.hEs j hj) _

/-- At a zero elimination level the minors are the point. -/
theorem minor_pt (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (h0 : ℓ = 0) {j : Nat}
    (hj : j < Fss.length) : frMs Fss.length Ids.length ρ₀ j = pt :=
  eq_pt_of_mem_univZero (h0 ▸ minorSpI_zero_univZero h0 (h.conc_univZero h0 hj) _ _ _)
    (h.hms j hj)

/-- Constructor `j`'s restricted chain. -/
theorem rChain_getElem? (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) {j : Nat} (hj : j < Fss.length) :
    (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[j]?
      = some (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) := by
  rw [rChains_getElem?, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by rw [h.hlenE]; exact hj)]
  rfl

theorem rChains_length' (h : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) :
    (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).length = Fss.length := by
  rw [rChains_length, h.hlenE]; simp

end RecHypS

/-! ## The motive's reading -/

/-- The motive's index application at a frame: its value and its
grading. -/
theorem motApp_facts {ℓ w D' : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V}
    (hfr : RecFrameS D' ρ₀ σ) (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) :
    interp2 V σ (motAppAV Fss.length Ids.length D') = frMi Fss.length Ids.length ρ₀ ∧
    AnnotOk2 V σ (motAppAV Fss.length Ids.length D') := by
  have hmot : interp2 V σ (.bvar (D' + Ids.length + Fss.length)) = frM Fss.length Ids.length ρ₀ := by
    rw [interp2_bvar]; exact hfr.motive
  have hargs : ∀ a ∈ idxVarsAV Ids.length D', AnnotOk2 V σ a := by
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    trivial
  have hchain : AppChainOk (interp2 V σ (.bvar (D' + Ids.length + Fss.length)))
      ((idxVarsAV Ids.length D').map (interp2 V σ)) := by
    rw [hmot, map_idxVarsAV_interp hfr]; exact hyp.hMchain
  have h := mkAppN_ok2_of_chain (args := idxVarsAV Ids.length D')
    (f := .bvar (D' + Ids.length + Fss.length)) (σ := σ) trivial hargs hchain
  refine ⟨?_, h.1⟩
  show interp2 V σ (AVExpr.mkAppN (.bvar (D' + Ids.length + Fss.length)) (idxVarsAV Ids.length D')) = _
  rw [h.2, hmot, map_idxVarsAV_interp hfr]
  rfl

/-- The stage-`j` motive body at a tag in `ω` reads to `motSem`, and
is graded. -/
theorem motiveBody_facts {ℓ w D : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (j : Nat) {k : V}
    (hk : k ∈ˢ (omega : V)) :
    interp2 V (cons k σ)
        (caseMotiveBodyAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          Fss.length Ids.length D j)
      = motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
          (frMi Fss.length Ids.length ρ₀) j k ∧
    AnnotOk2 V (cons k σ)
      (caseMotiveBodyAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        Fss.length Ids.length D j) := by
  generalize hR : rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess = Fss' at *
  have hok : SumFieldsOkB w ρ₀ Fss' := hR ▸ hyp.hok
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
  have hsh1 : shiftE (D + 1) 0 (cons (vnat i) σ) = ρ₀ := (hfr.push (vnat i))
  obtain ⟨hT, hokT⟩ := towers_facts hok
  have hTd : ∀ T ∈ (Fss'.map (towerBodyAV w)).drop j, interp2 V ρ₀ T ∈ˢ (univ w : V) :=
    fun T hT' => hT T (List.mem_of_mem_drop hT')
  have hokTd : ∀ T ∈ (Fss'.map (towerBodyAV w)).drop j, AnnotOk2 V ρ₀ T :=
    fun T hT' => hokT T (List.mem_of_mem_drop hT')
  -- the domain: the `(j + i)`-th fibre
  have hdom := caseAVAt_facts (w := w) (Ts := (Fss'.map (towerBodyAV w)).drop j) (d := D + 1)
    (k := .bvar 0) (σ := cons (vnat i) σ) (by rw [hsh1]; exact hTd) (by rw [hsh1]; exact hokTd)
    trivial (by rw [interp2_bvar]; exact hk)
  rw [hsh1] at hdom
  have hdomv : interp2 V (cons (vnat i) σ)
      (caseAVAt w ((Fss'.map (towerBodyAV w)).drop j) (D + 1) (.bvar 0))
      = sumFibre w ρ₀ Fss' (j + i) := by
    rw [hdom.2.1 i (by rw [interp2_bvar]; rfl)]
    unfold selFibre sumFibre
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, List.getElem?_map]
    cases hj : Fss'[j + i]? with
    | none => rfl
    | some Fs =>
      simp only [Option.map_some, Option.getD_some]
      exact towerBodyAV_interp (fun hw => (hok Fs (List.mem_of_getElem? hj)).toBound hw)
  -- the codomain: the motive at the injection
  have hfr2 : ∀ y : V, RecFrameS (D + 2) ρ₀ (cons y (cons (vnat i) σ)) := fun y => hfr.step y _
  have hsh2 : ∀ y : V, shiftE (D + 2) 0 (cons y (cons (vnat i) σ)) = ρ₀ := fun y => hfr2 y
  have htag : ∀ y : V, interp2 V (cons y (cons (vnat i) σ)) (succsAV j (.bvar 1)) = vnat (i + j) :=
    fun y => interp2_succsAV j (by rw [interp2_bvar]; rfl)
  have hMi := hR ▸ hyp.hM
  have hcod : ∀ y : V, y ∈ˢ sumFibre w ρ₀ Fss' (j + i) →
      interp2 V (cons y (cons (vnat i) σ))
          (.app (motAppAV Fss.length Ids.length (D + 2))
            (sumInjAtAV w Fss' (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))
        = SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w (j + i) y) ∧
      AnnotOk2 V (cons y (cons (vnat i) σ))
        (.app (motAppAV Fss.length Ids.length (D + 2))
          (sumInjAtAV w Fss' (D + 2) (succsAV j (.bvar 1)) (.bvar 0))) := by
    intro y hy
    have hpay : w ≠ 0 → interp2 V (cons y (cons (vnat i) σ)) (.bvar 0)
        ∈ˢ sumFibre w ρ₀ Fss' (i + j) := by
      intro _; rw [interp2_bvar, Nat.add_comm]; exact hy
    have hv := sumInjAtAV_interp (hsh2 y) hok (htag y) hpay
    rw [interp2_bvar] at hv
    have hij : i + j = j + i := Nat.add_comm i j
    obtain ⟨hMv, hMok⟩ := motApp_facts (hfr2 y) hyp
    refine ⟨?_, ?_⟩
    · rw [interp2_app, hMv, hv, hij, cons_zero]
    · rw [AnnotOk2_app]
      refine ⟨hMok, sumInjAtAV_ok2 (hsh2 y) hok (succsAV_ok2 j trivial
        (by rw [interp2_bvar]; rfl)) (htag y) trivial hpay,
        ℓ + 1, sumSet w (sumFibre w ρ₀ Fss'), fun _ => (univ ℓ : V), ?_, ?_,
        fun h => absurd h (Nat.succ_ne_zero _)⟩
      · rw [hMv]; exact hMi
      · rw [hv, hij, cons_zero]; exact injW_mem hy
  refine ⟨?_, ?_⟩
  · show piR ℓ _ _ = _
    rw [motSem_vnat, hdomv]
    exact piR_congr fun y hy => (hcod y hy).1
  · show AnnotOk2 V (cons (vnat i) σ) (.pi w ℓ _ _)
    rw [AnnotOk2_pi]
    refine ⟨hdom.2.2, fun y hy => ?_⟩
    rw [hdomv] at hy
    exact (hcod y hy).2

/-- The stage-`j` motive: its value, its membership in the motive space,
its applications, its grading. -/
theorem motive_facts {ℓ w D : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (j : Nat) :
    interp2 V σ (caseMotiveAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          Fss.length Ids.length D j)
        = lamR (imaxN w ℓ + 1) omega
            (motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
              (frMi Fss.length Ids.length ρ₀) j) ∧
      interp2 V σ (caseMotiveAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          Fss.length Ids.length D j) ∈ˢ natMotiveSpace V (imaxN w ℓ) ∧
      (∀ k, k ∈ˢ (omega : V) →
        SetTheory.app (interp2 V σ (caseMotiveAV ℓ w
            (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) Fss.length Ids.length D j)) k
          = motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
              (frMi Fss.length Ids.length ρ₀) j k) ∧
      AnnotOk2 V σ (caseMotiveAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        Fss.length Ids.length D j) := by
  have hv : interp2 V σ (caseMotiveAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        Fss.length Ids.length D j)
      = lamR (imaxN w ℓ + 1) omega
          (motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMi Fss.length Ids.length ρ₀) j) := by
    show lamR (imaxN w ℓ + 1) omega (fun k => interp2 V (cons k σ) (caseMotiveBodyAV ℓ w _ _ _ D j)) = _
    exact lamR_congr fun k hk => (motiveBody_facts hfr hyp j hk).1
  have hmot : ∀ k, k ∈ˢ (omega : V) →
      motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
        (frMi Fss.length Ids.length ρ₀) j k ∈ˢ (univ (imaxN w ℓ) : V) := by
    intro k hk
    obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
    exact hyp.motSem_univ j i
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [hv]
    exact lamR_mem_zero_agree
      ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h (Nat.succ_ne_zero _)⟩ hmot
  · intro k hk
    rw [hv]
    exact app_lamR_pos (Nat.succ_ne_zero _) hk
  · show AnnotOk2 V σ (.lam (imaxN w ℓ + 1) natAV (caseMotiveBodyAV ℓ w _ _ _ D j))
    rw [AnnotOk2_lam]
    refine ⟨trivial, fun k hk => (motiveBody_facts hfr hyp j hk).2,
      fun _ => (univ (imaxN w ℓ) : V), fun k hk => ?_, fun h => absurd h (Nat.succ_ne_zero _)⟩
    rw [(motiveBody_facts hfr hyp j hk).1]
    exact hmot k hk

/-! ## The base branch -/

/-- Constructor `j`'s branch (graph regime): its value, its grading,
its membership in the stage motive at the numeral `0`.  The index
equation is discharged here: the payload's index tuple is the frame's. -/
theorem base_facts {ℓ w D : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V}
    (hfr : RecFrameS D ρ₀ σ) (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) {j : Nat}
    (hj : j < Fss.length) :
    interp2 V σ (caseBaseAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) Fss.length Ids.length D j)
        = baseSem ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMs Fss.length Ids.length ρ₀) (Fss.getD j []).length j ∧
      AnnotOk2 V σ (caseBaseAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) Fss.length Ids.length D j) ∧
      interp2 V σ (caseBaseAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) Fss.length Ids.length D j)
        ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMi Fss.length Ids.length ρ₀) j (vnat 0) := by
  have hjF := hyp.rChain_getElem? hj
  have hokF : FieldsOkB w ρ₀
      (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
    hyp.hok _ (List.mem_of_getElem? hjF)
  have hfj : sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) :=
    sumFibre_of_getElem? hjF
  have hgetD : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j []
      = rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []) := by
    rw [List.getD_eq_getElem?_getD, hjF]; rfl
  have hdomv : interp2 V σ ((towerBodyAV w
        ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0)
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) := by
    rw [interp2_liftN, hfr, hgetD]
    exact towerBodyAV_interp (fun hw => hokF.toBound hw)
  have hokdom : AnnotOk2 V σ ((towerBodyAV w
      ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0) := by
    rw [AnnotOk2_liftN, hfr, hgetD]
    exact towerBodyAV_ok2 hokF
  have hminor : ∀ y : V, cons y σ (D + 1 + Ids.length + Fss.length - 1 - j)
      = frMs Fss.length Ids.length ρ₀ j :=
    fun y => (hfr.push y).minor hj
  have hms := hyp.hms j hj
  have hEslen : (Ess.getD j []).length = Ids.length := hyp.hEs j hj
  have hc0 : ℓ = 0 → ∀ acc, concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀)
      (Ess.getD j []) j acc ∈ˢ (univZero : V) :=
    fun h0 acc => hyp.conc_univZero h0 hj acc
  -- the body at a payload: the minor's fold along the projections
  have hbody : ∀ y : V, y ∈ˢ towerSet w (teleOfFields ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) →
      AnnotOk2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        = ((List.range (Fss.getD j []).length).map fun i => projS i y).foldl SetTheory.app
            (frMs Fss.length Ids.length ρ₀ j) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        ∈ˢ SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
    intro y hy
    have hval : interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        = ((List.range (Fss.getD j []).length).map fun i => projS i y).foldl SetTheory.app
            (frMs Fss.length Ids.length ρ₀ j) := by
      rw [interp2_mkAppN, List.foldl_map, List.foldl_map, interp2_bvar, hminor]
      congr 1
      funext acc i
      rw [projAV_interp, interp2_bvar]
      rfl
    -- the payload's projections: fitting, the index equation, the eta
    have helim := restricted_member_elim hw
      (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
      (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
      (ρ := ρ₀) (y := y) hy
    rw [liftFields_length] at helim
    obtain ⟨hspL, hlast, hall, heta⟩ := helim
    have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j [])
        (projList (Fss.getD j []).length y) :=
      (spineFit_liftFields (Ids.length + Fss.length + 1)).mp hspL
    have hidx : idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD j [])
        (projList (Fss.getD j []).length y) = frameIdx Ids.length ρ₀ :=
      (EqAll_idxEqsAt hEslen (projList_length _ _)).mp hall
    -- the projection spine fits the field chain
    have hbnd : FieldsBound w ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
      hokF.toBound hw
    have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])).length
        = (Fss.getD j []).length + 1 := rChain_length _ _ _ _
    have hfit : ArgsOkFit (cons y σ)
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) := by
      rw [List.range_eq_range']
      refine argsOkFit_of_projSpine (y := y) ?_ ?_ ?_
      · rw [← List.range_eq_range', ← projList_eq_map_range]; exact hspP
      · intro i _ hi
        exact projAV_ok2_tower (by simp) (by rw [interp2_bvar]; exact hy) hbnd (by omega)
      · intro i
        rw [projAV_interp, interp2_bvar]
        rfl
    have hsp := minorSpI_spine (V := V) hc0 (Fs := Fss.getD j [])
      (args := (List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
      (ρf := frP Fss.length Ids.length ρ₀) (acc := [])
      (f := .bvar (D + 1 + Ids.length + Fss.length - 1 - j)) (σ := cons y σ) (by simp)
      (by rw [interp2_bvar, hminor]; exact hms) hfit
    refine ⟨hsp.1, hval, ?_⟩
    have hmap : (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)).map
        (interp2 V (cons y σ))) = projList (Fss.getD j []).length y := by
      rw [List.map_map, projList_eq_map_range]
      apply List.map_congr_left
      intro i _
      show interp2 V _ (projAV i (.bvar 0)) = projS i y
      rw [projAV_interp, interp2_bvar]
      rfl
    have hconv : concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j
        ([] ++ ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)).map
          (interp2 V (cons y σ)))
        = SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
      rw [List.nil_append, hmap]
      unfold concI ctorValI frMi
      rw [hidx, if_neg hw, injW_pos hw, ← heta]
    have h := hsp.2
    rw [hconv] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · show lamR ℓ _ _ = _
    unfold baseSem
    rw [hdomv, hfj]
    exact lamR_congr fun y hy => (hbody y hy).2.1
  · show AnnotOk2 V σ (.lam ℓ _ _)
    rw [AnnotOk2_lam]
    refine ⟨hokdom, fun y hy => (hbody y (hdomv ▸ hy)).1,
      fun y => SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y),
      fun y hy => (hbody y (hdomv ▸ hy)).2.2, fun h0 y hy => ?_⟩
    have := hyp.hMapp (injW_mem (f := sumFibre w ρ₀
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) (i := j)
      (by rw [hfj]; exact hdomv ▸ hy))
    rwa [h0, univ_zero] at this
  · show lamR ℓ _ _ ∈ˢ _
    rw [motSem_vnat]
    simp only [Nat.add_zero]
    rw [hfj, hdomv]
    exact lamR_mem fun y hy => (hbody y hy).2.2

/-! ## The case recursor -/

/-- **The case recursor's facts** (graph regime), one induction on the
remaining constructor count: membership in the stage motive at every
tag in `ω`, iota (the tag `i < r` selects constructor `j + i`'s
branch), and the grading (at a zero elimination level from the
point-headed spine, so no numeral is needed; above it from
`Nat.rec`'s own chain). -/
theorem caseRec_facts {ℓ w : Nat} (hw : w ≠ 0) {ρ₀ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {k : AVExpr},
      RecFrameS D ρ₀ σ → j + r = Fss.length →
      ((interp2 V σ k ∈ˢ (omega : V) →
        interp2 V σ (caseRecAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
            (fun j => (Fss.getD j []).length) Fss.length Ids.length r D j k)
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
              (frMi Fss.length Ids.length ρ₀) j (interp2 V σ k) ∧
        ∀ i, interp2 V σ k = vnat i → i < r →
          interp2 V σ (caseRecAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
              (fun j => (Fss.getD j []).length) Fss.length Ids.length r D j k)
            = baseSem ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
                (frMs Fss.length Ids.length ρ₀) (Fss.getD (j + i) []).length (j + i)) ∧
      (AnnotOk2 V σ k → (ℓ ≠ 0 → interp2 V σ k ∈ˢ (omega : V)) →
        AnnotOk2 V σ (caseRecAV ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length) Fss.length Ids.length r D j k)))
  | 0, D, j, σ, k, hfr, hjr => by
    refine ⟨fun hk => ⟨?_, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩, fun _ _ => ?_⟩
    · obtain ⟨i, hki⟩ := mem_omega_iff.mp hk
      rw [hki, motSem_vnat]
      show lamR ℓ (empty : V) _ ∈ˢ _
      rw [sumFibre_of_ge (by rw [hyp.rChains_length']; omega)]
      exact lamR_mem fun _ hx => absurd hx (not_mem_empty _)
    · show AnnotOk2 V σ (.lam ℓ (.const .empty [w]) .prf)
      rw [AnnotOk2_lam]
      exact ⟨trivial, fun _ hx => absurd hx (not_mem_empty _), fun _ => unitSet,
        fun _ hx => absurd hx (not_mem_empty _), fun _ _ hx => absurd hx (not_mem_empty _)⟩
  | r + 1, D, j, σ, k, hfr, hjr => by
    have hjn : j < Fss.length := by omega
    obtain ⟨hMv, hMsp, hMapp, hMok⟩ := motive_facts hfr hyp j
    obtain ⟨hzv, hzok, hzm⟩ := base_facts hw hfr hyp hjn
    generalize hR : rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess = Fss' at *
    generalize hAr : (fun j => (Fss.getD j []).length) = ar at *
    have hz : interp2 V σ (caseBaseAV ℓ w Fss' ar Fss.length Ids.length D j)
        ∈ˢ SetTheory.app (interp2 V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) natzero := by
      rw [hMapp natzero natzero_mem, natzero_eq_vnat]; exact hzm
    -- the step's inner recursor at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp2 V (cons a (cons b σ))
            (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) b ∧
        (∀ i, b = vnat i → i < r →
          interp2 V (cons a (cons b σ))
              (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
            = baseSem ℓ (sumFibre w ρ₀ Fss') (frMs Fss.length Ids.length ρ₀)
                (Fss.getD (j + 1 + i) []).length (j + 1 + i)) ∧
        AnnotOk2 V (cons a (cons b σ))
          (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := by
      intro a b hb
      have h := caseRec_facts hw hyp r (D := D + 2) (j := j + 1) (σ := cons a (cons b σ))
        (k := .bvar 1) (hfr.step a b) (by omega)
      rw [hR, hAr] at h
      have hb' : interp2 V (cons a (cons b σ)) (.bvar 1) ∈ˢ (omega : V) := by
        rw [interp2_bvar]; exact hb
      refine ⟨(h.1 hb').1, fun i hi hir => (h.1 hb').2 i (by rw [interp2_bvar]; exact hi) hir,
        h.2 trivial (fun _ => hb')⟩
    -- the motive at a successor is the next stage's motive
    have hsucc : ∀ (i : Nat), motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat (i + 1))
        = motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) (vnat i) := by
      intro i
      rw [motSem_vnat, motSem_vnat, show j + (i + 1) = j + 1 + i from by omega]
    -- the step: its value and its membership in the step space
    have hsv : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        = lamR (imaxN w ℓ) omega fun b =>
            lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              fun a => interp2 V (cons a (cons b σ))
                (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := rfl
    have hmb := fun (b : V) (hb : b ∈ˢ (omega : V)) => motiveBody_facts hfr hyp j hb
    rw [hR] at hmb
    have hs : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        ∈ˢ natStepSpace2 V (imaxN w ℓ) (interp2 V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) := by
      rw [hsv]
      unfold natStepSpace2
      refine lamR_mem fun b hb => ?_
      rw [hMapp b hb, hMapp (natsucc b) (natsucc_mem hb), (hmb b hb).1]
      refine lamR_mem fun a _ => ?_
      obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
      rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
      exact (hinner a _ hb).1
    refine ⟨fun hk => ⟨?_, ?_⟩, fun hokk hkω => ?_⟩
    · -- membership
      have h := natRecAV_mem hMsp hz hs hk
      rwa [hMapp _ hk] at h
    · -- iota
      intro i hi hir
      show interp2 V σ (natRecAV (imaxN w ℓ) _ _ _ k) = _
      rw [interp2_natRecAV hMsp hz hs hk, hi, natrec_vnat]
      -- the iteration's values inhabit the stage motive
      have hiter : ∀ i', natIter (interp2 V σ (caseBaseAV ℓ w Fss' ar Fss.length Ids.length D j))
          (interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
            (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
            (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))) i'
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat i') := by
        intro i'
        have h := natRecV2_mem_fibre V hMsp hz hs (vnat_mem_omega i')
        rwa [natrec_vnat, hMapp _ (vnat_mem_omega i')] at h
      cases i with
      | zero =>
        rw [Nat.add_zero]
        exact hzv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i) = _
        by_cases h0 : ℓ = 0
        · -- the zero level: everything is the point
          have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
          rw [hsv, hz', lamR_zero, app_pt, app_pt]
          unfold baseSem
          rw [h0, lamR_zero]
        · have hz' : imaxN w ℓ ≠ 0 := fun h => h0 ((imaxN_eq_zero_iff w ℓ).mp h)
          rw [hsv, app_lamR_pos hz' (vnat_mem_omega i),
            app_lamR_pos hz' (by
              rw [(hmb _ (vnat_mem_omega i)).1]
              exact hiter i),
            (hinner _ _ (vnat_mem_omega i)).2.1 i rfl (by omega),
            show j + 1 + i = j + (i + 1) from by omega]
    · -- the grading
      by_cases h0 : ℓ = 0
      · -- the point-headed spine
        have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
        refine (mkAppN_ok2_of_pt_head (f := .const .natRec [imaxN w ℓ]) (σ := σ) trivial
          (by show natRecV2 V (imaxN w ℓ) = pt; rw [hz', natRecV2, lamR_zero]) ?_).1
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hMok
        · exact hzok
        · rw [AnnotOk2_lam]
          refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
              (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
              (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
            fun b hb => ?_, fun _ b hb => by rw [hz']; exact piR_zero_mem_univZero⟩
          · rw [AnnotOk2_lam]
            refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
              fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
              fun a _ => ?_, fun _ a _ => ?_⟩
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
              exact (hinner a _ hb).1
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc,
                motSem_vnat, h0]
              exact piR_zero_mem_univZero
          · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              (fun a => interp2 V (cons a (cons b σ))
                (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
            rw [(hmb b hb).1]
            refine lamR_mem fun a _ => ?_
            obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
            rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
            exact (hinner a _ hb).1
        · exact hokk
      · -- `Nat.rec`'s own chain
        refine natRecAV_ok2 hMok hzok ?_ hokk hMsp hz hs (hkω h0)
        rw [AnnotOk2_lam]
        refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
            (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
            (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
          fun b hb => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
        · rw [AnnotOk2_lam]
          refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
            fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
            fun a _ => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1
        · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
            (fun a => interp2 V (cons a (cons b σ))
              (caseRecAV ℓ w Fss' ar Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
          rw [(hmb b hb).1]
          refine lamR_mem fun a _ => ?_
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1

/-- At a zero elimination level the case recursor with constructors
remaining is the point. -/
theorem caseRec_zero {ℓ w : Nat} (h0 : ℓ = 0) (Fss : List (List AVExpr)) (ar : Nat → Nat)
    (n nIdx r D j : Nat) (k : AVExpr) (σ : Nat → V) :
    interp2 V σ (caseRecAV ℓ w Fss ar n nIdx (r + 1) D j k) = pt := by
  show interp2 V σ (natRecAV (imaxN w ℓ) _ _ _ k) = pt
  rw [interp2_natRecAV_raw, (imaxN_eq_zero_iff w ℓ).mpr h0, natRecV2, lamR_zero, app_pt, app_pt,
    app_pt, app_pt]

end Setlec.Semantics
