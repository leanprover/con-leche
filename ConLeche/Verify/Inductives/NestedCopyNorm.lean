module

public import ConLeche.Verify.Inductives.NestedCopyTele
public import ConLeche.Verify.Inductives.MutualNormPres
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.NestedCopyKinds

public section

/-!
# The constructors' normalisation keeps the residual (task #315 L-B)

`normCtorValM` (`Kernel/Inductives/MutualInstall.lean`) opens a
constructor's type at its `nP` parameters, normalises the `nF` field
DOMAINS positively (`normPosDomM`) and closes the telescope back up
around the residual it never touched.  `normCtorValM_resid`
(`NestedCopyRewrite`'s neighbour `NestedInv`) already says the stored
type is that re-closure; what a READER of the stored type needs on top
is that the re-closure can be opened again and gives the same residual
back.

That is a frame fact and this module is it: the positivity walk keeps
a term bound-variable closed (`normPosDomM_bounded` —
`normPosDomM_pres` without its scoping half, which the copy's binders
do not supply), hence so does the field telescope
(`normFieldDomsM_bounded`), hence the re-closure is a telescope over
CLOSED domains (`normCtorValM_frame`), which is exactly the hypothesis
of the round trip `openPisAtFvars_closeTelescope`.  The consumer
`normCtorValM_openResid` reads the stored type's two-stage opening and
lands on the residual of the GIVEN type, modulo annotations.

The module's second half does the same for a FIELD DOMAIN: the walk is
the identity on a stuck inductive-headed application
(`normPosDomM_indApp`), the field walk is positional
(`normFieldDomsM_getD`) and the round trip carries the binder domains
as well as the residual (`openPisAtFvars_closeTelescope_doms`), so the
stored constructor's opened field domain keeps the head the given
one's had (`normCtorValM_domHead`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A member of a `zipWith` is its function at members of the two
lists. -/
private theorem mem_zipWithD {α β γ : Type} {g : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β} {c : γ}, c ∈ List.zipWith g l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, c = g a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWithD h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

/-- Two consecutive openings are one. -/
private theorem openPisAtFvars_addD :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr}
      {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, _m, _e, _d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, e, d, fvs, fvs', o, o', h, h' => by
    match e, h with
    | .forallE _dom _body _mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next _fvs₁ _e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h'' := openPisAtFvars_addD n h₁
          (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
        rw [show n + 1 + m = n + m + 1 from by omega]
        simp only [openPisAtFvars]
        rw [h'']
        rfl
      · exact nomatch h
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- **The positivity normalisation keeps a term bound-variable
closed**: `normPosDomM_pres` without the `WScoped` half.  Each `whnf`
step preserves the bound (`whnf_looseBVars`) and the Π step opens at a
fresh `fvar` and closes with `abstract1`, which is exactly the
`instantiate1`/`abstract1` round trip on the bound.  The scoping half
is dropped because a copy's stored binders carry no context depth to
state it at — the reader only ever needs closedness. -/
theorem normPosDomM_bounded {env : Env} (henv : EnvWF env) {memberNames : List Name} {F : Nat} :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr},
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok e' →
      e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro d e e' h hb
    rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
    · exact hb
    have hwb : w.looseBVarsBounded 0 = true := whnf_looseBVars henv F hw hb
    rcases hcase with rfl | ⟨dom, body, bm, body', fuel', rfl, rfl, -, hbody', rfl⟩
    · exact hwb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwb
    have hopenb : (body.instantiate1 (.fvar d dom)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hwb.2
    have hb' := ih fuel' (by omega) hbody' hopenb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hwb.1, looseBVarsBounded_abstract1 body' 0 hb'⟩

/-- **The field telescope's domains are bound-variable closed**: the
walk peels a `∀` whose domain is closed because the whole type is,
normalises it (`normPosDomM_bounded`) and recurses on the body OPENED
at a fresh variable, which is closed again.  This is the hypothesis
`openPisAtFvars_closeTelescope` asks of the binders the constructor's
normalisation re-closes. -/
theorem normFieldDomsM_bounded {env : Env} (henv : EnvWF env) {memberNames : List Name} {F : Nat} :
    ∀ {n i : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames i n e = .ok (bs, r) →
      e.looseBVarsBounded 0 = true →
      ∀ b ∈ bs, b.1.looseBVarsBounded 0 = true := by
  intro n
  induction n with
  | zero =>
    intro i e bs r h _hb
    obtain ⟨rfl, -⟩ := normFieldDomsM_zero_inv h
    intro b hbmem
    exact absurd hbmem (by simp)
  | succ n ih =>
    intro i e bs r h hb
    obtain ⟨dom, body, bm, dom', bs', rfl, hdom, hrec, rfl⟩ := normFieldDomsM_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hdom' : dom'.looseBVarsBounded 0 = true :=
      normPosDomM_bounded henv 1024 hdom hb.1
    have hopen : (body.instantiate1 (.fvar i dom)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    intro b hbmem
    rcases List.mem_cons.mp hbmem with rfl | hbmem
    · exact hdom'
    · exact ih hrec hopen b hbmem

/-- **THE STORED CONSTRUCTOR'S TYPE IS A CLOSED TELESCOPE OVER THE
GIVEN TYPE'S RESIDUAL** (`normCtorValM_resid` with the two facts its
reader needs): the re-closed telescope has exactly `nP + nF` binders —
one per opened parameter (`openPisAtFvars_length`, `stripPis_length`)
and one per normalised field (`normFieldDomsM_open`) — and every one of
their domains is bound-variable closed: the parameters' are the
openers' own types (`openPisAtFvars_bounded`), the fields' are
`normFieldDomsM_bounded`'s.  It also names the telescope's two halves
(task #315 L-B): the field half `fbs` IS the output of the
`normFieldDomsM` call the conclusion carries, sitting past `nP`
parameter binders, which is what lets a reader of a FIELD binder
(`normCtorValM_domHead`) find it positionally. -/
theorem normCtorValM_frame {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true) :
    cvCa' = cvCa ∨
      ∃ (bs fbs pbs : List (Expr × BinderMeta)) (fvs xFvs : List Expr) (crest xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvs, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        bs.length = nP + nF ∧
        (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) ∧
        cvCa'.type = closeTelescope bs 0 xrest ∧
        normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames nP nF crest
          = .ok (fbs, xrest) ∧
        pbs.length = nP ∧ bs = pbs ++ fbs := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cres⟩ := q
  try simp only at h
  obtain ⟨rr, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvs, crest⟩ := rr
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  try simp only at h
  obtain ⟨xFvs, hopX, hfbs⟩ := normFieldDomsM_open hu
  have hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest) := unwrapOr_ok hr
  have hcbs : cbs.length = nP := Expr.stripPis_length nP (unwrapOr_ok hq)
  have hfvs : fvs.length = nP := Verify.openPisAtFvars_length nP hop1
  obtain ⟨hcrest, hfvsb⟩ := Verify.openPisAtFvars_bounded nP hop1 hb
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  · refine Or.inr ⟨List.zipWith (fun (x : Expr) (bb : Expr × BinderMeta) => (x.fvarTypeD, bb.2))
        fvs cbs ++ fbs, fbs,
      List.zipWith (fun (x : Expr) (bb : Expr × BinderMeta) => (x.fvarTypeD, bb.2)) fvs cbs,
      fvs, xFvs, crest, resid, hop1, hopX, ?_, ?_, ?_, hu, ?_, rfl⟩
    · simp [hfvs, hcbs, hfbs]
    · intro b hbmem
      rcases List.mem_append.mp hbmem with hbmem | hbmem
      · obtain ⟨x, hx, _bb, -, rfl⟩ := mem_zipWithD hbmem
        exact hfvsb x hx
      · exact normFieldDomsM_bounded henv hu hcrest b hbmem
    · rw [checkConstantValPre_ok h]
    · simp [hfvs, hcbs]

/-- **THE STORED TYPE READS BACK TO THE GIVEN TYPE'S RESIDUAL** (task
#315 L-B): open the constructor type the normalisation STORED at its
`nP` parameters and then at its `nF` fields, and what is left is the
residual the same two-stage opening of the type the normalisation was
GIVEN hands back — modulo annotations, which the re-closure's
`abstract1`/`instantiate1` round trip may move (`Expr.ErasedEq`).
Either the stage stored its input unchanged, or `normCtorValM_frame`'s
telescope is re-opened by `openPisAtFvars_closeTelescope`, at the very
length the two openings consume. -/
theorem normCtorValM_openResid {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true)
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    {fvs' xFvs' : List Expr} {crest' xrest' : Expr}
    (hop1' : openPisAtFvars nP cvCa'.type 0 = some (fvs', crest'))
    (hop2' : openPisAtFvars nF crest' nP = some (xFvs', xrest')) :
    Expr.ErasedEq xrest' xrest := by
  rcases normCtorValM_frame henv h hb with rfl |
    ⟨bs, _fbs, _pbs, fvs₀, xFvs₀, crest₀, xrest₀, hA, hB, hlen, hdoms, hty,
      _hfields, _hpl, _hbseq⟩
  · -- the stage stored its input: the two openings are the same calls
    rw [hop1] at hop1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
    obtain ⟨rfl, rfl⟩ := hop1'
    rw [hop2] at hop2'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop2'
    obtain ⟨rfl, rfl⟩ := hop2'
    exact Expr.ErasedEq.rfl _
  -- the given type's openings are the ones the frame hands back
  rw [hop1] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  obtain ⟨rfl, rfl⟩ := hA
  rw [hop2] at hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨rfl, rfl⟩ := hB
  have hxb : xrest.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop2 (Verify.openPisAtFvars_bounded nP hop1 hb).1).1
  obtain ⟨fvs₃, r₃, hop₃, -, her₃⟩ := openPisAtFvars_closeTelescope bs 0 xrest hdoms hxb
  rw [hlen] at hop₃
  have hadd : openPisAtFvars (nP + nF) cvCa'.type 0 = some (fvs' ++ xFvs', xrest') :=
    openPisAtFvars_addD nP hop1' (by simpa using hop2')
  rw [hty, hop₃] at hadd
  simp only [Option.some.injEq, Prod.mk.injEq] at hadd
  obtain ⟨-, rfl⟩ := hadd
  exact her₃

/-! ## The field domains, read off the stored constructor (task #315 L-B) -/

/-- **THE POSITIVITY WALK IS THE IDENTITY ON A STUCK INDUCTIVE
APPLICATION** (task #315 L-B): a field domain that is a stored
inductive type former applied to a spine mentions a member only inside
that spine, and `whnf` cannot move it (K.22, `whnf_indApp_eq`).  So
the walk's `whnf` hands back the very term it was given, that term is
not a `∀` (`mkAppN_const_ne_forallE`), the Π arm cannot fire and the
normalisation stores the domain unchanged. -/
theorem normPosDomM_indApp {env : Env} {memberNames : List Name} {F fuel d : Nat}
    {J : Name} {lvls : List Level} {args : List Expr} {cv : ConstantVal} {caps : IndCaps}
    {e' : Expr}
    (hJ : env.find? J = some (.indInfo cv caps))
    (h : normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel
        (Expr.mkAppN (.const J lvls) args) = .ok e') :
    e' = Expr.mkAppN (.const J lvls) args := by
  rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
  · rfl
  have hwe : w = Expr.mkAppN (.const J lvls) args := whnf_indApp_eq hJ hw
  rcases hcase with rfl | ⟨dom, body, bm, _body', _fuel', -, hforall, -, -, -⟩
  · exact hwe
  · exact absurd (hwe.symm.trans hforall) (mkAppN_const_ne_forallE J lvls args dom body bm)

/-- `openPisAtFvars_erasedEq` with the OPENERS: the two runs plant
`.fvar` leaves at the same depths, and the annotation each carries is
the binder domain it came from — erasure-equal because the two terms
are.  (`openPisAtFvars_erasedEq` itself keeps only the openers' count,
which is all its consumers ask of it.) -/
private theorem openPisAtFvars_erasedEq_doms :
    ∀ (k : Nat) {e e' : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      Expr.ErasedEq e e' → openPisAtFvars k e' d = some (fvs, body) →
      ∃ (fvs' : List Expr) (body' : Expr),
        openPisAtFvars k e d = some (fvs', body') ∧ fvs'.length = fvs.length ∧
        Expr.ErasedEq body' body ∧
        ∀ (j : Nat) (a a' : Expr), fvs'[j]? = some a → fvs[j]? = some a' →
          Expr.ErasedEq a.fvarTypeD a'.fvarTypeD := by
  intro k
  induction k with
  | zero =>
    intro e e' d fvs body he h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], e, rfl, rfl, he, fun j a a' ha _ => by simp at ha⟩
  | succ k ih =>
    intro e e' d fvs body he h
    match e', h with
    | .forallE dom' body' m', h =>
      match e, he with
      | .forallE dom bodyE m, he =>
        obtain ⟨rfl, hdom, hbody⟩ := he
        simp only [openPisAtFvars] at h
        cases hop : openPisAtFvars k (body'.instantiate1 (.fvar d dom') 0) (d + 1) with
        | none => rw [hop] at h; exact nomatch h
        | some q =>
          rw [hop] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨fvs₂, body₂, hop₂, hlen₂, he₂, hdoms₂⟩ := ih
            (Expr.ErasedEq.instantiate1 hbody
              (show Expr.ErasedEq (Expr.fvar d dom) (Expr.fvar d dom') from rfl)) hop
          refine ⟨Expr.fvar d dom :: fvs₂, body₂, ?_, by simp [hlen₂], he₂, ?_⟩
          · show (match openPisAtFvars k (bodyE.instantiate1 (.fvar d dom) 0) (d + 1) with
              | some (fvs, e) => some (Expr.fvar d dom :: fvs, e)
              | none => none) = _
            rw [hop₂]
          · intro j a a' ha ha'
            cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ha'
              subst ha
              subst ha'
              exact hdom
            | succ j =>
              simp only [List.getElem?_cons_succ] at ha ha'
              exact hdoms₂ j a a' ha ha'

/-- **THE ROUND TRIP, WITH THE DOMAINS** (task #315 L-B): the
telescope closed over bound-variable-closed binders and re-opened at
the same depth hands back openers whose annotations are the closing
telescope's own domains — `openPisAtFvars_closeTelescope` with the
binder side of the round trip, which a reader of a FIELD's domain
needs and the residual alone does not give.  The head binder is
re-opened at `.fvar i dom` with `dom` verbatim; the deeper ones come
from the induction hypothesis, transported along the
`abstract1`/`instantiate1` round trip by
`openPisAtFvars_erasedEq_doms`. -/
theorem openPisAtFvars_closeTelescope_doms :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (r : Expr),
      (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) → r.looseBVarsBounded 0 = true →
      ∃ (fvs : List Expr) (r' : Expr),
        openPisAtFvars bs.length (closeTelescope bs i r) i = some (fvs, r') ∧
        fvs.length = bs.length ∧ Expr.ErasedEq r' r ∧
        ∀ (k : Nat) (a : Expr) (bb : Expr × BinderMeta),
          fvs[k]? = some a → bs[k]? = some bb → Expr.ErasedEq a.fvarTypeD bb.1
  | [], _, r, _, _ =>
    ⟨[], r, rfl, rfl, Expr.ErasedEq.rfl r, fun _ _ _ ha _ => by simp at ha⟩
  | (dom, bm) :: bs, i, r, hbs, hr => by
    obtain ⟨fvs, r', hop, hlen, her, hdoms⟩ :=
      openPisAtFvars_closeTelescope_doms bs (i + 1) r
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) hr
    obtain ⟨fvs₂, body₂, hop₂, hlen₂, he₂, hdoms₂⟩ := openPisAtFvars_erasedEq_doms bs.length
      (abstract1_instantiate1_erasedEq (ty := dom) (closeTelescope bs (i + 1) r) 0
        (looseBVarsBounded_closeTelescope bs (i + 1) r
          (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) hr)) hop
    refine ⟨Expr.fvar i dom :: fvs₂, body₂, ?_, by simp [hlen₂, hlen], he₂.trans her, ?_⟩
    · show (match openPisAtFvars bs.length
          (((closeTelescope bs (i + 1) r).abstract1 i 0).instantiate1 (.fvar i dom) 0) (i + 1) with
        | some (fvs, e) => some (Expr.fvar i dom :: fvs, e)
        | none => none) = _
      rw [hop₂]
    · intro k a bb ha hbb
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hbb
        subst ha
        subst hbb
        exact Expr.ErasedEq.rfl _
      | succ k =>
        simp only [List.getElem?_cons_succ] at ha hbb
        have hk : k < fvs.length := by
          rcases Nat.lt_or_ge k fvs₂.length with hlt | hge
          · omega
          · rw [List.getElem?_eq_none hge] at ha; exact nomatch ha
        exact (hdoms₂ k a fvs[k] ha (List.getElem?_eq_getElem hk)).trans
          (hdoms k fvs[k] bb (List.getElem?_eq_getElem hk) hbb)

/-- **THE FIELD WALK IS POSITIONAL** (task #315 L-B): `normFieldDomsM`
and `openPisAtFvars` peel the SAME `∀` binders and open each at the
same `.fvar i dom`, so the binder the walk stores at position `k` is
the positivity normalisation of the `k`-th opener's own domain, run at
the depth that opener sits at.  This is what names the stored
telescope's field binders in terms of the type the stage was
given. -/
theorem normFieldDomsM_getD {env : Env} {memberNames : List Name} {F : Nat} :
    ∀ {n i : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr} {fvs : List Expr},
      normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames i n e = .ok (bs, r) →
      openPisAtFvars n e i = some (fvs, r) →
      ∀ (k : Nat) (a : Expr), fvs[k]? = some a →
        ∃ (d' : Expr) (bm : BinderMeta),
          normPosDomM (m := CheckM) (fueledOps mode F) env memberNames (i + k) 1024 a.fvarTypeD
            = .ok d' ∧ bs[k]? = some (d', bm) := by
  intro n
  induction n with
  | zero =>
    intro i e bs r fvs _h hop k a ha
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact absurd ha (by simp)
  | succ n ih =>
    intro i e bs r fvs h hop k a ha
    obtain ⟨dom, body, bm, dom', bs', rfl, hdom, hrec, rfl⟩ := normFieldDomsM_inv h
    simp only [openPisAtFvars] at hop
    cases hq : openPisAtFvars n (body.instantiate1 (.fvar i dom) 0) (i + 1) with
    | none => rw [hq] at hop; exact nomatch hop
    | some q =>
      rw [hq] at hop
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        exact ⟨dom', bm, by simpa [Expr.fvarTypeD] using hdom, rfl⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at ha ⊢
        obtain ⟨d', bm', hd', hbs'⟩ := ih hrec hq k a ha
        exact ⟨d', bm', by rw [show i + (k + 1) = i + 1 + k from by omega]; exact hd', hbs'⟩

/-- An erasure-equal partner of a constant IS that constant: `ErasedEq`
reads a constant's name and levels. -/
private theorem erasedEq_const_inv {T : Name} {lvls : List Level} {e : Expr}
    (h : Expr.ErasedEq e (.const T lvls)) : e = .const T lvls := by
  match e, h with
  | .const n us, h =>
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- **THE STORED CONSTRUCTOR'S FIELD DOMAIN IS THE GIVEN ONE** (task
#315 L-B): open the constructor type the normalisation STORED at its
`nP` parameters and then at its `nF` fields; if the field `l` of the
type the stage was GIVEN has a domain that is a stored INDUCTIVE type
former applied to a spine, then the stored type's field `l` carries
that very domain, up to the openers' annotations (`ErasedEq`, which is
all a reading sees).  Either the stage stored its input unchanged and
the two openings coincide, or `normCtorValM_frame`'s re-closed
telescope is re-opened by `openPisAtFvars_closeTelescope_doms`, whose
binder at `nP + l` is `normFieldDomsM_getD`'s — the positivity
normalisation of the given field's domain, which `normPosDomM_indApp`
leaves alone. -/
theorem normCtorValM_domErased {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true)
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    {fvs' xFvs' : List Expr} {crest' xrest' : Expr}
    (hop1' : openPisAtFvars nP cvCa'.type 0 = some (fvs', crest'))
    (hop2' : openPisAtFvars nF crest' nP = some (xFvs', xrest'))
    {l : Nat} {x x' : Expr} (hx : xFvs[l]? = some x) (hx' : xFvs'[l]? = some x')
    {T : Name} {lvls : List Level} {args : List Expr} {cv : ConstantVal} {caps : IndCaps}
    (hT : env.find? T = some (.indInfo cv caps))
    (hhead : x.fvarTypeD = Expr.mkAppN (.const T lvls) args) :
    Expr.ErasedEq x'.fvarTypeD x.fvarTypeD := by
  rcases normCtorValM_frame henv h hb with rfl |
    ⟨bs, fbs, pbs, fvs₀, xFvs₀, crest₀, xrest₀, hA, hB, hlen, hdoms, hty, hfields, hpl, hbseq⟩
  · -- the stage stored its input: the two openings are the same calls
    rw [hop1] at hop1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
    obtain ⟨rfl, rfl⟩ := hop1'
    rw [hop2] at hop2'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop2'
    obtain ⟨rfl, rfl⟩ := hop2'
    obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
    exact Expr.ErasedEq.rfl _
  -- the given type's openings are the ones the frame hands back
  rw [hop1] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  obtain ⟨rfl, rfl⟩ := hA
  rw [hop2] at hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨rfl, rfl⟩ := hB
  have hxb : xrest.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop2 (Verify.openPisAtFvars_bounded nP hop1 hb).1).1
  obtain ⟨fvs₃, r₃, hop₃, -, -, hdoms₃⟩ :=
    openPisAtFvars_closeTelescope_doms bs 0 xrest hdoms hxb
  rw [hlen] at hop₃
  have hadd : openPisAtFvars (nP + nF) cvCa'.type 0 = some (fvs' ++ xFvs', xrest') :=
    openPisAtFvars_addD nP hop1' (by simpa using hop2')
  rw [hty, hop₃] at hadd
  simp only [Option.some.injEq, Prod.mk.injEq] at hadd
  obtain ⟨rfl, -⟩ := hadd
  -- the stored opener at `nP + l` is the field opener `l`
  have hfvs' : fvs'.length = nP := Verify.openPisAtFvars_length nP hop1'
  have hidx : (fvs' ++ xFvs')[nP + l]? = some x' := by
    rw [List.getElem?_append_right (by omega), hfvs',
      show nP + l - nP = l from by omega]
    exact hx'
  -- and the stored binder at `nP + l` is the field walk's `l`-th
  obtain ⟨d', bm', hd', hfbsl⟩ := normFieldDomsM_getD hfields hop2 l x hx
  rw [hhead] at hd'
  have hbb : bs[nP + l]? = some (d', bm') := by
    rw [hbseq, List.getElem?_append_right (by omega), hpl,
      show nP + l - nP = l from by omega]
    exact hfbsl
  have her : Expr.ErasedEq x'.fvarTypeD d' := hdoms₃ (nP + l) x' (d', bm') hidx hbb
  rw [normPosDomM_indApp hT hd', ← hhead] at her
  exact her

/-- **THE STORED FIELD DOMAIN'S HEAD** — `normCtorValM_domErased` read
through `ErasedEq.getApp`: an erasure-equal partner of a constant IS
that constant, so the stored domain is that former applied to a spine
of its own.  (The head is all `CopyCtorShape.recF`'s classification
half asks for; the arm's readings take the erasure equality itself.) -/
theorem normCtorValM_domHead {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true)
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    {fvs' xFvs' : List Expr} {crest' xrest' : Expr}
    (hop1' : openPisAtFvars nP cvCa'.type 0 = some (fvs', crest'))
    (hop2' : openPisAtFvars nF crest' nP = some (xFvs', xrest'))
    {l : Nat} {x x' : Expr} (hx : xFvs[l]? = some x) (hx' : xFvs'[l]? = some x')
    {T : Name} {lvls : List Level} {args : List Expr} {cv : ConstantVal} {caps : IndCaps}
    (hT : env.find? T = some (.indInfo cv caps))
    (hhead : x.fvarTypeD = Expr.mkAppN (.const T lvls) args) :
    ∃ args', x'.fvarTypeD = Expr.mkAppN (.const T lvls) args' := by
  have her := normCtorValM_domErased henv h hb hop1 hop2 hop1' hop2' hx hx' hT hhead
  rw [hhead] at her
  obtain ⟨hfn, -, -⟩ := ErasedEq.getApp her
  rw [Expr.getAppFn_mkAppN] at hfn
  have hgf : (x'.fvarTypeD).getAppFn = Expr.const T lvls :=
    erasedEq_const_inv (show Expr.ErasedEq _ (Expr.const T lvls) from hfn)
  exact ⟨(x'.fvarTypeD).getAppArgs, by rw [← hgf, Expr.mkAppN_getApp]⟩

end ConLeche
