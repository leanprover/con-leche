module

public import ConLeche.Verify.Inductives.NestedCopyTele
public import ConLeche.Verify.Inductives.MutualNormPres
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Inductives.NestedCopyKinds
-- the `mapM` length, for the jobs' inversion (task #315 M8)
import ConLeche.Verify.Inductives.NestedElimInv
-- the container's stored constructors, for the same (task #315 M8)
import ConLeche.Verify.Inductives.NestedGroupInv

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

/-! ## The walk under a reflexive field's own binders (task #315 L-B)

`normPosDomM_indApp` is the finitary half: a field domain that IS a
stuck inductive application survives the positivity normalisation
verbatim.  A REFLEXIVE field's domain is a `∀`-tower over such an
application, and there the walk does move: it peels each binder, opens
it at the binder's own `.fvar`, recurses, and closes it again
(`abstract1`).  That round trip is the identity on a term whose free
variables all sit BELOW the binder's depth — which is what
`fvarsBelow` records and what the openers of a constructor's telescope
satisfy by construction.  So the tower, too, comes back unchanged, up
to the `fvar` annotations an interpretation does not read
(`normPosDomM_piIndApp`). -/

/-- Every reachable `fvar` index below `d`, read off the leaves
(`fvarsBelow` does not descend into an annotation, so the leaf list is
more than enough). -/
theorem fvarsBelow_of_leaves {d : Nat} :
    ∀ {e : Expr}, (∀ lf ∈ e.fvarLeaves, lf.1 < d) → Expr.fvarsBelow d e := by
  intro e
  induction e <;> intro h <;>
    simp_all [Expr.fvarLeaves, Expr.fvarsBelow]

/-- **THE OPENERS KEEP THE TERM'S OWN FVAR BOUND**, one depth per
binder: `openPisAtFvars` plants `.fvar (d + i)` carrying the `i`-th
binder's domain, and that domain's free variables are the term's own
plus the openers before it. -/
theorem openPisAtFvars_fvarsBelow :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) → Expr.fvarsBelow d e →
      (∀ (i : Nat) (x : Expr), fvs[i]? = some x → Expr.fvarsBelow (d + i) x.fvarTypeD) ∧
        Expr.fvarsBelow (d + k) body := by
  intro k
  induction k with
  | zero =>
    intro e d fvs body hop hfb
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨fun i x hx => by simp at hx, hfb⟩
  | succ k ih =>
    intro e d fvs body hop hfb
    match e, hop with
    | .forallE ty rest bm, hop =>
      simp only [openPisAtFvars] at hop
      cases hq : openPisAtFvars k (rest.instantiate1 (.fvar d ty) 0) (d + 1) with
      | none => rw [hq] at hop; exact nomatch hop
      | some q =>
        obtain ⟨afvs, bodyq⟩ := q
        rw [hq] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨hty, hrest⟩ : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d rest := hfb
        obtain ⟨hdoms, hbody⟩ := ih hq (Expr.fvarsBelow_instantiate1 0 hrest)
        refine ⟨fun i x hx => ?_, by rw [show d + (k + 1) = d + 1 + k from by omega]; exact hbody⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          simpa [Expr.fvarTypeD] using hty
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          rw [show d + (i + 1) = d + 1 + i from by omega]
          exact hdoms i x hx

/-- `ErasedEq` is a congruence for `abstract1`: the closing reads an
`fvar`'s INDEX and nothing else, which is exactly what an erasure
equality keeps. -/
private theorem erasedEq_abstract1 {d : Nat} :
    ∀ {e e' : Expr} (k : Nat), Expr.ErasedEq e e' →
      Expr.ErasedEq (e.abstract1 d k) (e'.abstract1 d k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' k he
    match e', he with
    | .bvar j, he => exact he
  | fvar idx ty ih =>
    intro e' k he
    match e', he with
    | .fvar j ty', he =>
      obtain rfl : idx = j := he
      simp only [Expr.abstract1]
      split
      · exact Expr.ErasedEq.rfl _
      · exact rfl
  | sort u =>
    intro e' k he
    match e', he with
    | .sort v, he => exact he
  | const n us =>
    intro e' k he
    match e', he with
    | .const n' us', he => exact he
  | lit l =>
    intro e' k he
    match e', he with
    | .lit l', he => exact he
  | app f a ihf iha =>
    intro e' k he
    match e', he with
    | .app g b, he => exact ⟨ihf k he.1, iha k he.2⟩
  | lam ty b m ihty ihb =>
    intro e' k he
    match e', he with
    | .lam ty' b' m', he => exact ⟨he.1, ihty k he.2.1, ihb (k + 1) he.2.2⟩
  | forallE ty b m ihty ihb =>
    intro e' k he
    match e', he with
    | .forallE ty' b' m', he => exact ⟨he.1, ihty k he.2.1, ihb (k + 1) he.2.2⟩
  | letE ty v b ihty ihv ihb =>
    intro e' k he
    match e', he with
    | .letE ty' v' b', he => exact ⟨ihty k he.1, ihv k he.2.1, ihb (k + 1) he.2.2⟩
  | proj s i e ih =>
    intro e' k he
    match e', he with
    | .proj s' i' e₂, he => exact ⟨he.1, he.2.1, ih k he.2.2⟩

/-- **THE POSITIVITY WALK IS THE IDENTITY ON A Π-TOWER OVER A STUCK
INDUCTIVE APPLICATION** (task #315 L-B): `normPosDomM_indApp` under
binders.  A REFLEXIVE field's domain is `n` `∀`s over an inductive
application; the walk peels them one by one — each binder's domain is
handed back verbatim (the walk only recurses into the BODY, and
rejects a domain that mentions a member), the tower's leaf is the
stuck application `normPosDomM_indApp` leaves alone — and the
`instantiate1`/`abstract1` round trip each peel performs is the
identity on a term whose free variables sit below the binder's depth.
The conclusion is an `ErasedEq` because the openers the walk plants
carry their own annotations. -/
theorem normPosDomM_piIndApp {env : Env} {memberNames : List Name} {F : Nat}
    {J : Name} {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hJ : env.find? J = some (.indInfo cv caps)) :
    ∀ (n : Nat) {d fuel : Nat} {e e' : Expr} {fvs : List Expr} {args : List Expr},
      openPisAtFvars n e d = some (fvs, Expr.mkAppN (.const J lvls) args) →
      Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok e' →
      Expr.ErasedEq e' e := by
  intro n
  induction n with
  | zero =>
    intro d fuel e e' fvs args hop _ _ h
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact Expr.ErasedEq.of_eq (normPosDomM_indApp hJ h)
  | succ n ih =>
    intro d fuel e e' fvs args hop hfb hb h
    match e, hop with
    | .forallE ty rest bm, hop =>
      simp only [openPisAtFvars] at hop
      cases hq : openPisAtFvars n (rest.instantiate1 (.fvar d ty) 0) (d + 1) with
      | none => rw [hq] at hop; exact nomatch hop
      | some q =>
        obtain ⟨afvs, bodyq⟩ := q
        rw [hq] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨hty, hrest⟩ : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d rest := hfb
        obtain ⟨hbty, hbrest⟩ : ty.looseBVarsBounded 0 = true ∧ rest.looseBVarsBounded 1 = true := by
          simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hb
        rcases normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
        · exact Expr.ErasedEq.rfl _
        have hwe : w = Expr.forallE ty rest bm := whnf_forallE_eq hw
        rcases hcase with rfl | ⟨dom, body, bm', body', fuel', -, hforall, -, hrec, rfl⟩
        · exact Expr.ErasedEq.of_eq hwe
        rw [hwe] at hforall
        obtain ⟨rfl, rfl, rfl⟩ : ty = dom ∧ rest = body ∧ bm = bm' := by
          simpa using hforall
        have hIH := ih hq (Expr.fvarsBelow_instantiate1 0 hrest)
          (looseBVarsBounded_instantiate1 rest 0 hbrest) hrec
        refine ⟨rfl, Expr.ErasedEq.rfl _, ?_⟩
        have h1 := erasedEq_abstract1 (d := d) 0 hIH
        rwa [ConLeche.instantiate1_abstract1_self rest 0 hrest hbrest] at h1


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

/-- A substitution of a member-free value into a member-free term is
member-free (`Expr.mentionsConst_instantiate1` with both sides). -/
private theorem mentionsConst_instantiate1_false {v : Expr} {m : Name}
    (hv : v.mentionsConst m = false) :
    ∀ {e : Expr} {j : Nat}, e.mentionsConst m = false →
      (e.instantiate1 v j).mentionsConst m = false := by
  intro e
  induction e with
  | bvar i =>
    intro j _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar idx ty ih => intro j h; simpa [Expr.instantiate1] using h
  | sort u => intro j h; exact h
  | const n us => intro j h; exact h
  | lit l => intro j h; exact h
  | app f a ihf iha =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b bm ihty ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b bm ihty ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE ty v' b ihty ihv ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨⟨ihty h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨h.1, ih h.2⟩

/-- The openers of a member-free `∀`-tower are member-free. -/
private theorem mentionsMember_openPisAtFvars_false {memberNames : List Name} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {leaf : Expr},
      openPisAtFvars n e d = some (fvs, leaf) →
      mentionsMember memberNames e = false →
      ∀ x ∈ fvs, mentionsMember memberNames x.fvarTypeD = false := by
  intro n
  induction n with
  | zero =>
    intro e d fvs leaf hop _
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact fun x hx => nomatch hx
  | succ n ih =>
    intro e d fvs leaf hop hm
    match e, hop with
    | .forallE ty rest bm, hop =>
      simp only [openPisAtFvars] at hop
      cases hq : openPisAtFvars n (rest.instantiate1 (.fvar d ty) 0) (d + 1) with
      | none => rw [hq] at hop; exact nomatch hop
      | some q =>
        obtain ⟨afvs, bodyq⟩ := q
        rw [hq] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hsplit : ∀ T ∈ memberNames,
            Expr.mentionsConst T ty = false ∧ Expr.mentionsConst T rest = false := by
          intro T hT
          have hT' : (Expr.mentionsConst T ty || Expr.mentionsConst T rest) = false := by
            have h0 := List.any_eq_false.mp hm T hT
            simpa [Expr.mentionsConst] using h0
          exact Bool.or_eq_false_iff.mp hT'
        have hrest : mentionsMember memberNames (rest.instantiate1 (.fvar d ty) 0) = false :=
          List.any_eq_false.mpr fun T hT => by
            simp [mentionsConst_instantiate1_false (v := .fvar d ty)
              (by simpa [Expr.mentionsConst] using (hsplit T hT).1) (hsplit T hT).2]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.any_eq_false.mpr fun T hT => by
            simp [Expr.fvarTypeD, (hsplit T hT).1]
        · exact ih hq hrest x hx

/-- **THE WALK AT A `∀`, INVERTED** (task #315 L-B): `normPosDomM_inv`
at a term that IS a `∀` — the `whnf` is then the identity
(`whnf_forallE_eq`), so the walk either handed the tower back because
it mentions no member, or took its Π arm, whose guard is that the
BINDER DOMAIN mentions none.  The general inversion keeps the middle
case's mention test to itself, and this is the case distinction a
reflexive field's telescope needs. -/
theorem normPosDomM_forallE_inv {env : Env} {memberNames : List Name} {F : Nat}
    {d fuel : Nat} {ty rest e' : Expr} {bm : BinderMeta}
    (h : normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel
      (.forallE ty rest bm) = .ok e') :
    (mentionsMember memberNames (Expr.forallE ty rest bm) = false ∧
        e' = Expr.forallE ty rest bm) ∨
      (mentionsMember memberNames ty = false ∧ ∃ (body' : Expr) (fuel' : Nat),
        normPosDomM (m := CheckM) (fueledOps mode F) env memberNames (d + 1) fuel'
            (rest.instantiate1 (.fvar d ty) 0) = .ok body' ∧
          e' = Expr.forallE ty (body'.abstract1 d 0) bm) := by
  cases fuel with
  | zero => simp only [normPosDomM] at h; exact nomatch h
  | succ fuel =>
    unfold normPosDomM at h
    by_cases hm : mentionsMember memberNames (Expr.forallE ty rest bm) = true
    case neg =>
      rw [if_pos (by simpa using hm)] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl ⟨by simpa using hm, h.symm⟩
    rw [if_neg (by simpa using hm)] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨w, hw, h⟩ := exceptBind_ok h
    have hwe : w = Expr.forallE ty rest bm := whnf_forallE_eq hw
    subst hwe
    rw [if_neg (by simpa using hm)] at h
    simp only at h
    by_cases hd : mentionsMember memberNames ty = true
    · rw [if_pos hd] at h; exact nomatch h
    rw [if_neg hd] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨body', hbody, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr ⟨by simpa using hd, body', fuel, hbody, h.symm⟩

/-- **A REFLEXIVE FIELD'S TELESCOPE DOMAINS ARE MEMBER-FREE** (task
#315 L-B): whatever the positivity walk accepted, every binder domain
of the field's own `∀`-tower mentions no member of the block — the walk
either handed the tower back untouched (and then the whole tower, its
binder domains included, mentions no member) or took its Π arm at every
binder, whose guard is that very test.  This is what lets the rewrite's
PRUNE apply to a reflexive field's telescope one binder at a time. -/
theorem normPosDomM_piDomsFree {env : Env} {memberNames : List Name} {F : Nat} :
    ∀ (n : Nat) {d fuel : Nat} {e e' : Expr} {fvs : List Expr} {leaf : Expr},
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok e' →
      openPisAtFvars n e d = some (fvs, leaf) →
      ∀ x ∈ fvs, mentionsMember memberNames x.fvarTypeD = false := by
  intro n
  induction n with
  | zero =>
    intro d fuel e e' fvs leaf _ hop
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact fun x hx => nomatch hx
  | succ n ih =>
    intro d fuel e e' fvs leaf h hop
    match e, hop, h with
    | .forallE ty rest bm, hop, h =>
      simp only [openPisAtFvars] at hop
      cases hq : openPisAtFvars n (rest.instantiate1 (.fvar d ty) 0) (d + 1) with
      | none => rw [hq] at hop; exact nomatch hop
      | some q =>
        obtain ⟨afvs, bodyq⟩ := q
        rw [hq] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hop' : openPisAtFvars (n + 1) (Expr.forallE ty rest bm) d
            = some (Expr.fvar d ty :: afvs, bodyq) := by
          simp only [openPisAtFvars, hq]
        rcases normPosDomM_forallE_inv h with ⟨hmf, -⟩ | ⟨hdomf, body', fuel', hrec, -⟩
        · exact mentionsMember_openPisAtFvars_false (n + 1) hop' hmf
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [Expr.fvarTypeD] using hdomf
        · exact ih hrec hq x hx

/-- **The field walk ran** — whatever `normCtorValM` decided to store,
it normalised the field telescope first (`normCtorValM_frame` keeps the
walk only in the arm where the store changed something; a reader of the
walk itself needs it in both). -/
theorem normCtorValM_fieldWalk {env : Env} {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    {fvs : List Expr} {crest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest)) :
    ∃ (fbs : List (Expr × BinderMeta)) (resid : Expr),
      normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames nP nF crest
        = .ok (fbs, resid) := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cres⟩ := q
  try simp only at h
  obtain ⟨rr, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvs₀, crest₀⟩ := rr
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  have hop1' : openPisAtFvars nP cvCa.type 0 = some (fvs₀, crest₀) := unwrapOr_ok hr
  rw [hop1] at hop1'
  simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
  obtain ⟨-, rfl⟩ := hop1'
  exact ⟨fbs, resid, hu⟩

/-- **A REFLEXIVE FIELD'S TELESCOPE DOMAINS ARE MEMBER-FREE, AT THE
CONSTRUCTOR** (task #315 L-B): `normPosDomM_piDomsFree` at the field
the walk ran on — the `l`-th opened domain of the type the stage was
GIVEN, peeled at its own `Π` binders.  What the caller does with it is
the rewrite's PRUNE: a fired `replaceAllNested` plants a member of the
block, and no binder domain of this tower mentions one. -/
theorem normCtorValM_domPiFree {env : Env} {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    {l : Nat} {x : Expr} (hx : xFvs[l]? = some x)
    {n : Nat} {tbs : List (Expr × BinderMeta)} {body : Expr}
    (hpeel : x.fvarTypeD.stripPis n = some (tbs, body)) :
    ∀ k, k < n → mentionsMember memberNames (tbs.getD k default).1 = false := by
  obtain ⟨fbs, resid, hfields⟩ := normCtorValM_fieldWalk h hop1
  obtain ⟨xFvs₀, hopX, -⟩ := normFieldDomsM_open hfields
  rw [hop2] at hopX
  simp only [Option.some.injEq, Prod.mk.injEq] at hopX
  obtain ⟨-, rfl⟩ := hopX
  obtain ⟨d', bm', hd', -⟩ := normFieldDomsM_getD hfields hop2 l x hx
  have htbsLen : tbs.length = n := Expr.stripPis_length _ hpeel
  have hmk : x.fvarTypeD = mkPisB tbs body := stripPis_mkPisB _ hpeel
  obtain ⟨afvs, hafvsLen, -, hlaw⟩ := openPisAtFvars_mkPisB n tbs htbsLen (nP + l)
  have hopA : openPisAtFvars n x.fvarTypeD (nP + l)
      = some (afvs, Expr.instSeq afvs (n - 1) body) := by rw [hmk]; exact hlaw _
  have hfree := normPosDomM_piDomsFree n hd' hopA
  intro k hk
  obtain ⟨a, ha⟩ : ∃ a, afvs[k]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by rw [hafvsLen]; exact hk)⟩
  have hbd : tbs[k]? = some (tbs.getD k default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [htbsLen]; exact hk)]
    rfl
  have hdom : a.fvarTypeD = Expr.instSeq (afvs.take k) (k - 1) (tbs.getD k default).1 :=
    Verify.openPisAtFvars_domain n hopA hpeel k a (tbs.getD k default) ha hbd
  have hma := hfree a (List.mem_of_getElem? ha)
  rw [hdom] at hma
  refine List.any_eq_false.mpr fun T hT => ?_
  have := List.any_eq_false.mp hma T hT
  simp only [Bool.not_eq_true] at this ⊢
  exact mentionsConst_instSeq_false _ _ (by simpa using this)

/-- **THE STORED CONSTRUCTOR'S REFLEXIVE FIELD DOMAIN IS THE GIVEN
ONE** (task #315 L-B): `normCtorValM_domErased` at a field whose given
domain is a `∀`-TOWER over a stored inductive application — a
REFLEXIVE field.  Same frame, same round trip; only the walk's own
identity changes (`normPosDomM_piIndApp` in place of
`normPosDomM_indApp`), and it asks for the given domain's free
variables to sit below the field's depth, which
`openPisAtFvars_fvarsBelow` reads off the constructor body's. -/
theorem normCtorValM_domErasedPi {env : Env} (henv : EnvWF env) {memberNames : List Name}
    {nP nF F : Nat} {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    (hb : cvCa.type.looseBVarsBounded 0 = true)
    {fvs xFvs : List Expr} {crest xrest : Expr}
    (hop1 : openPisAtFvars nP cvCa.type 0 = some (fvs, crest))
    (hop2 : openPisAtFvars nF crest nP = some (xFvs, xrest))
    (hfb : Expr.fvarsBelow nP crest)
    {fvs' xFvs' : List Expr} {crest' xrest' : Expr}
    (hop1' : openPisAtFvars nP cvCa'.type 0 = some (fvs', crest'))
    (hop2' : openPisAtFvars nF crest' nP = some (xFvs', xrest'))
    {l : Nat} {x x' : Expr} (hx : xFvs[l]? = some x) (hx' : xFvs'[l]? = some x')
    {n : Nat} {afvs targs : List Expr} {J : Name} {lvls : List Level}
    {cv : ConstantVal} {caps : IndCaps}
    (hJ : env.find? J = some (.indInfo cv caps))
    (hopA : openPisAtFvars n x.fvarTypeD (nP + l)
      = some (afvs, Expr.mkAppN (.const J lvls) targs)) :
    Expr.ErasedEq x'.fvarTypeD x.fvarTypeD := by
  have hxfb : Expr.fvarsBelow (nP + l) x.fvarTypeD :=
    (openPisAtFvars_fvarsBelow nF hop2 hfb).1 l x hx
  have hxb : x.fvarTypeD.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop2
      (Verify.openPisAtFvars_bounded nP hop1 hb).1).2 x (List.mem_of_getElem? hx)
  rcases normCtorValM_frame henv h hb with rfl |
    ⟨bs, fbs, pbs, fvs₀, xFvs₀, crest₀, xrest₀, hA, hB, hlen, hdoms, hty, hfields, hpl, hbseq⟩
  · rw [hop1] at hop1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
    obtain ⟨rfl, rfl⟩ := hop1'
    rw [hop2] at hop2'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop2'
    obtain ⟨rfl, rfl⟩ := hop2'
    obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
    exact Expr.ErasedEq.rfl _
  rw [hop1] at hA
  simp only [Option.some.injEq, Prod.mk.injEq] at hA
  obtain ⟨rfl, rfl⟩ := hA
  rw [hop2] at hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨rfl, rfl⟩ := hB
  have hxb₀ : xrest.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop2 (Verify.openPisAtFvars_bounded nP hop1 hb).1).1
  obtain ⟨fvs₃, r₃, hop₃, -, -, hdoms₃⟩ :=
    openPisAtFvars_closeTelescope_doms bs 0 xrest hdoms hxb₀
  rw [hlen] at hop₃
  have hadd : openPisAtFvars (nP + nF) cvCa'.type 0 = some (fvs' ++ xFvs', xrest') :=
    openPisAtFvars_addD nP hop1' (by simpa using hop2')
  rw [hty, hop₃] at hadd
  simp only [Option.some.injEq, Prod.mk.injEq] at hadd
  obtain ⟨rfl, -⟩ := hadd
  have hfvs' : fvs'.length = nP := Verify.openPisAtFvars_length nP hop1'
  have hidx : (fvs' ++ xFvs')[nP + l]? = some x' := by
    rw [List.getElem?_append_right (by omega), hfvs', show nP + l - nP = l from by omega]
    exact hx'
  obtain ⟨d', bm', hd', hfbsl⟩ := normFieldDomsM_getD hfields hop2 l x hx
  have hbb : bs[nP + l]? = some (d', bm') := by
    rw [hbseq, List.getElem?_append_right (by omega), hpl, show nP + l - nP = l from by omega]
    exact hfbsl
  have her : Expr.ErasedEq x'.fvarTypeD d' := hdoms₃ (nP + l) x' (d', bm') hidx hbb
  exact her.trans (normPosDomM_piIndApp hJ n hopA hxfb hxb hd')

/-- **A MEMBER-FREE FIELD DOMAIN SURVIVES THE NORMALISATION** (task
#315 L-B): `normCtorValM_domErased`'s twin at the walk's own guard —
the positivity normalisation is the identity on a domain mentioning no
member (`normPosDomM_no_mention`), so the stored constructor's field
`l` carries the domain the stage was given, up to the openers'
annotations.  This is the arm `CopyCtorShape.ordF`'s LEFT half runs
on. -/
theorem normCtorValM_domUnchanged {env : Env} (henv : EnvWF env) {memberNames : List Name}
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
    (hm : mentionsMember memberNames x.fvarTypeD = false) :
    Expr.ErasedEq x'.fvarTypeD x.fvarTypeD := by
  rcases normCtorValM_frame henv h hb with rfl |
    ⟨bs, fbs, pbs, fvs₀, xFvs₀, crest₀, xrest₀, hA, hB, hlen, hdoms, hty, hfields, hpl, hbseq⟩
  · rw [hop1] at hop1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop1'
    obtain ⟨rfl, rfl⟩ := hop1'
    rw [hop2] at hop2'
    simp only [Option.some.injEq, Prod.mk.injEq] at hop2'
    obtain ⟨rfl, rfl⟩ := hop2'
    obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
    exact Expr.ErasedEq.rfl _
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
  have hfvs' : fvs'.length = nP := Verify.openPisAtFvars_length nP hop1'
  have hidx : (fvs' ++ xFvs')[nP + l]? = some x' := by
    rw [List.getElem?_append_right (by omega), hfvs', show nP + l - nP = l from by omega]
    exact hx'
  obtain ⟨d', bm', hd', hfbsl⟩ := normFieldDomsM_getD hfields hop2 l x hx
  have hbb : bs[nP + l]? = some (d', bm') := by
    rw [hbseq, List.getElem?_append_right (by omega), hpl, show nP + l - nP = l from by omega]
    exact hfbsl
  have her : Expr.ErasedEq x'.fvarTypeD d' := hdoms₃ (nP + l) x' (d', bm') hidx hbb
  rwa [normPosDomM_no_mention hd' hm] at her

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

/-! ## THE MINTED COPY'S POSITIVITY RUN, INVERTED (task #315 L-B, DESIGN §U.76)

K.42's record is two functions: `nestedOrdDomPairs` collects, per pin,
per constructor, per field the filter admits — ORDINARY, or with a
target below `p.k` — the pair of domains (the MINTED one and the STORED
one) at that field's depth, and `nestedOrdNorms`
runs `normPosDomM` on every minted one.  The model consumes them at ONE
field of ONE constructor of ONE pin, so these two theorems are the
addressing: the first says the job list HOLDS that field's triple (the
forward run of the three-layer `Option` walk, every `let ... ←`
discharged by the caller's own read), the second says the recorded run
at a job of the list IS `normPosDomM`'s, with the error handler's
reclassification seen through. -/

/-- **A JOB'S MINTED DOMAIN IS SCOPED AT ITS OWN DEPTH** (task #315 M8,
the cached run obligation): the job `(nP + l, xM.fvarTypeD, _)` carries
the `l`-th opener's domain of the container constructor's type
instantiated at the pin's arguments, so its scope is the container's
stored type (fvar-free), the pin's arguments (the block's parameter
openers) and the openers before it — exactly what
`normPosDomM`'s simulation asks of the term it walks. -/
theorem nestedDomPair_WScoped {p : NestedParts} {J : ContainerMember}
    {cJ : ContainerCtor} {lvls : List Level} {Ds : List Expr} {cI : Expr}
    {nF : Nat} {xsM : List Expr} {restM : Expr} {l : Nat} {xM : Expr}
    (hctor : cJ.type.hasFvar = false) (hDs : ∀ D ∈ Ds, Expr.WScoped p.nP D)
    (hcI : Expr.instPis (Expr.instantiateLevelParams J.lps lvls cJ.type) Ds = some cI)
    (hopM : openPisAtFvars nF cI p.nP = some (xsM, restM))
    (hxM : xsM[l]? = some xM) :
    Expr.WScoped (p.nP + l) xM.fvarTypeD := by
  have hlp : Expr.WScoped p.nP (Expr.instantiateLevelParams J.lps lvls cJ.type) :=
    wscoped_instLevels_of_not_hasFvar hctor J.lps lvls
  have hcIw : Expr.WScoped p.nP cI := instPis_WScoped hcI hlp hDs
  obtain ⟨hall, -⟩ := openPisAtFvars_WScoped nF cI p.nP hopM hcIw
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index nF cI p.nP hopM l xM hxM
  have hx := hall _ (List.mem_of_getElem? hxM)
  simp only [Expr.WScoped] at hx
  exact hx.2

/-- **THE JOB AT A FIELD THE RECORD INSPECTS.**  Every hypothesis is one
of `nestedOrdDomPairs`' own lookups, in the order the walk makes them,
so the model supplies them from the reads it already has; the
conclusion is the walk's triple `(p.nP + l, the MINTED domain, the
STORED one)`.

`hwide` is the walk's own filter, in Prop form: the field is classified
ORDINARY, **or** its target lies below `p.k`, i.e. at a MEMBER of the
block being installed rather than at a mimic (task #315 M8 session 3's
widening, lane L-B's request — DESIGN "THE `mintedAt` FIX, AND TWO
MEASUREMENTS" (d)).  The member-target disjunct is what lane L-B's
`ordF`-right arm reads. -/
theorem nestedOrdDomPairs_mem {env : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {kinds : List (List (List (RecFieldKind × Nat)))}
    {jobs : List (Nat × Expr × Expr)}
    (h : nestedOrdDomPairs env p st stored (some kinds) = some jobs)
    {q : Nat} (hq : q < st.pins.length)
    {t : AuxType} (ht : st.types[p.k + q]? = some t)
    {Jn : Name} {lvls : List Level} {Ds : List Expr} (hsrc : t.src = some (Jn, lvls, Ds))
    {a : AuxStored} (ha : stored[p.k + q]? = some a)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env Jn = some ci)
    {J : ContainerMember} (hJ : ci.members.find? (fun J => J.name == Jn) = some J)
    (hlvls : lvls.length = J.lps.length)
    {j : Nat} {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {cvS : ConstantVal} {nI nF : Nat} (hcS : a.ctors[j]? = some (cvS, nI, nF))
    {cI : Expr} (hcI : Expr.instPis (Expr.instantiateLevelParams J.lps lvls cJ.type) Ds = some cI)
    {xsM : List Expr} {restM : Expr} (hopM : openPisAtFvars nF cI p.nP = some (xsM, restM))
    {fvsS : List Expr} {crestS : Expr} (hopS : openPisAtFvars p.nP cvS.type 0 = some (fvsS, crestS))
    {xsS : List Expr} {restS : Expr} (hopS2 : openPisAtFvars nF crestS p.nP = some (xsS, restS))
    {l : Nat} {r : RecFieldKind} {n : Nat} (hkfl : kf[l]? = some (r, n))
    (hwide : r = RecFieldKind.ordinary ∨ n < p.k)
    {xM xS : Expr} (hxM : xsM[l]? = some xM) (hxS : xsS[l]? = some xS) :
    (p.nP + l, xM.fvarTypeD, xS.fvarTypeD) ∈ jobs := by
  have hrange : ∀ {n i : Nat}, i < n → (List.range n)[i]? = some i := by
    intro n i hi; simp [hi]
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.1 hkf
  obtain ⟨hllt, -⟩ := List.getElem?_eq_some_iff.1 hkfl
  rw [nestedOrdDomPairs] at h
  simp only [bind, Option.bind] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i rows hrows
  simp only [pure, Option.some.injEq] at h
  subst h
  -- the row of pin `q`
  obtain ⟨rowq, hrowq, hFq⟩ := mapM_option_inv hrows q q (hrange hq)
  refine List.mem_flatten.mpr ⟨rowq, List.mem_of_getElem? hrowq, ?_⟩
  simp only [ht, hsrc, ha, hks, hci, hJ, hlvls, bne_self_eq_false, Bool.false_eq_true,
    if_false] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i perCtor hperCtor
  simp only [pure, Option.some.injEq] at hFq
  subst hFq
  -- the row of constructor `j`
  obtain ⟨rowj, hrowj, hGj⟩ := mapM_option_inv hperCtor j j (hrange hjlt)
  refine List.mem_flatten.mpr ⟨rowj, List.mem_of_getElem? hrowj, ?_⟩
  simp only [hkf, hcJ, hcS, hcI, hopM, hopS, hopS2] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i perField hperField
  simp only [pure, Option.some.injEq] at hGj
  subst hGj
  -- the row of field `l`, a singleton at a kind the filter admits
  obtain ⟨rowl, hrowl, hHl⟩ := mapM_option_inv hperField l l (hrange hllt)
  refine List.mem_flatten.mpr ⟨rowl, List.mem_of_getElem? hrowl, ?_⟩
  rcases hwide with rfl | hlt
  · simp only [hkfl, hxM, hxS, beq_self_eq_true, Bool.true_or, if_true, pure,
      Option.some.injEq] at hHl
    subst hHl
    simp
  · simp only [hkfl, hxM, hxS, hlt, decide_true, Bool.or_true, if_true, pure,
      Option.some.injEq] at hHl
    subst hHl
    simp

/-- **THE COPIES' SOURCE ARGUMENTS ARE SCOPED AT THE BLOCK'S PARAMETERS**
(task #315 M8): a copy's `src` records the container's arguments, and
those ARE the pin's arguments (`nestedCopySrcOk`); the pin's free
variables are the block's parameter openers (`pinsScoped`), so the
arguments are scoped where the positivity walk needs them.  The first
type's own scope is the caller's — it is the annotated former, whose
door left it fvar-free. -/
theorem nestedCopySrc_Ds_WScoped {env : Env} {p : NestedParts} {st : ElimState}
    (hsrc : nestedCopySrcOk env p st = true) (hsc : pinsScoped p.nP st = true)
    (ht₀w : ∀ t₀, st.types.head? = some t₀ → Expr.WScoped 0 t₀.type) :
    ∀ (q : Nat), q < st.pins.length → ∀ t, st.types[p.k + q]? = some t →
      ∀ Jn lvls Ds, t.src = some (Jn, lvls, Ds) → ∀ D ∈ Ds, Expr.WScoped p.nP D := by
  intro q hq t ht Jn lvls Ds hsrceq D hD
  obtain ⟨t₀, params, o, ht₀, hop, hpins⟩ := pinsScoped_inv hsc
  obtain ⟨qn, hqn⟩ : ∃ qn, st.pins[q]? = some qn := ⟨_, List.getElem?_eq_getElem hq⟩
  obtain ⟨t₀', pbs', body', h1', h2', hall⟩ := nestedCopySrcOk_inv hsrc
  obtain ⟨t', Jn', lvls', Ds', ci, J, c, ht', hsrc', -, hpin, -, -, -, -, -, -, -⟩ :=
    hall q qn hqn
  obtain rfl : t' = t := by rw [ht] at ht'; exact (Option.some.inj ht').symm
  obtain ⟨rfl, rfl, rfl⟩ : Jn' = Jn ∧ lvls' = lvls ∧ Ds' = Ds := by
    rw [hsrceq] at hsrc'
    simpa using hsrc'.symm
  -- the pin is scoped at the parameters: its leaves are the openers
  obtain ⟨-, hleaves⟩ := hpins qn (List.mem_of_getElem? hqn)
  obtain ⟨hparams, -⟩ := openPisAtFvars_WScoped p.nP t₀.type 0 hop (ht₀w t₀ ht₀)
  have hpinW : Expr.WScoped p.nP qn.pin := by
    refine Expr.WScoped_of_leaves _ ?_
    intro l hl
    have hmem := hleaves l hl
    have := hparams _ hmem
    simp only [Expr.WScoped, Nat.zero_add] at this
    exact this
  rw [hpin] at hpinW
  exact (WScoped_of_mkAppN hpinW).2 D hD

/-- **EVERY ORDINARY-FIELD JOB IS SCOPED** (task #315 M8, the cached run
obligation): the inversion of `nestedOrdDomPairs`' three `mapM`s, fed
to `nestedDomPair_WScoped`.  The container's stored constructor types
come from `EnvWF`; the pins' arguments are the caller's (`pinsScoped`
with `nestedCopySrcOk_inv` supply them). -/
theorem nestedOrdDomPairs_WScoped {env : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {kinds : List (List (List (RecFieldKind × Nat)))}
    {jobs : List (Nat × Expr × Expr)} (henv : EnvWF env)
    (hDs : ∀ (q : Nat), q < st.pins.length → ∀ t, st.types[p.k + q]? = some t →
      ∀ Jn lvls Ds, t.src = some (Jn, lvls, Ds) → ∀ D ∈ Ds, Expr.WScoped p.nP D)
    (h : nestedOrdDomPairs env p st stored (some kinds) = some jobs) :
    ∀ je ∈ jobs, Expr.WScoped je.1 je.2.1 := by
  intro je hje
  rw [nestedOrdDomPairs] at h
  simp only [bind, Option.bind] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i rows hrows
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨row, hrowmem, hjerow⟩ := List.mem_flatten.mp hje
  obtain ⟨q, hq⟩ := List.getElem?_of_mem hrowmem
  have hqlt : q < st.pins.length := by
    have hlen := mapM_option_length hrows
    have := (List.getElem?_eq_some_iff.mp hq).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨rowq, hrowq, hFq⟩ := mapM_option_inv hrows q q (by simp [hqlt])
  obtain rfl : row = rowq := by rw [hq] at hrowq; exact Option.some.inj hrowq
  -- the pin's row: the copy's source and the container's member
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i t ht
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i src hsrceq
  obtain ⟨Jn, lvls, Ds⟩ := src
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i a ha
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i ks hks
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i ci hci
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i J hJ
  try simp only [] at hFq
  split at hFq
  case isTrue => exact absurd hFq (by simp)
  case isFalse =>
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i perCtor hperCtor
  simp only [pure, Option.some.injEq] at hFq
  subst hFq
  -- the constructor's row
  obtain ⟨crow, hcrowmem, hjecrow⟩ := List.mem_flatten.mp hjerow
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcrowmem
  have hjlt : j < ks.length := by
    have hlen := mapM_option_length hperCtor
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨crowj, hcrowj, hGj⟩ := mapM_option_inv hperCtor j j (by simp [hjlt])
  obtain rfl : crow = crowj := by rw [hj] at hcrowj; exact Option.some.inj hcrowj
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i kf hkf
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cJ hcJ
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cS hcS
  obtain ⟨cvS, nI, nF⟩ := cS
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cI hcI
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qM hqM
  obtain ⟨xsM, restM⟩ := qM
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qS hqS
  obtain ⟨fvsS, crestS⟩ := qS
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qS2 hqS2
  obtain ⟨xsS, restS⟩ := qS2
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i perField hperField
  simp only [pure, Option.some.injEq] at hGj
  subst hGj
  -- the field's row: a singleton exactly where the filter admits it
  obtain ⟨frow, hfrowmem, hjefrow⟩ := List.mem_flatten.mp hjecrow
  obtain ⟨l, hl⟩ := List.getElem?_of_mem hfrowmem
  have hllt : l < kf.length := by
    have hlen := mapM_option_length hperField
    have := (List.getElem?_eq_some_iff.mp hl).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨frowl, hfrowl, hHl⟩ := mapM_option_inv hperField l l (by simp [hllt])
  obtain rfl : frow = frowl := by rw [hl] at hfrowl; exact Option.some.inj hfrowl
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i rt hrt
  obtain ⟨r, tgt⟩ := rt
  try simp only [] at hHl
  split at hHl
  case isFalse =>
    simp only [pure, Option.some.injEq] at hHl
    subst hHl
    exact absurd hjefrow (by simp)
  case isTrue =>
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i xM hxM
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i xS hxS
  simp only [pure, Option.some.injEq] at hHl
  subst hHl
  obtain rfl : je = (p.nP + l, xM.fvarTypeD, xS.fvarTypeD) := by simpa using hjefrow
  -- the container's stored constructor type is fvar-free
  obtain ⟨cvT, caps, cvR, mIc, rPc, rulesc, h1c, h2c, h3c, h4c, hmem⟩ := containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc', rulesC, hf1, hf2, hl1, hl2, hl3, hlen4, hctors⟩ :=
    hmem J (List.mem_of_find?_eq_some hJ)
  obtain ⟨r', cvc, -, -, hfindC, hcJty⟩ := hctors j cJ hcJ
  have hctorF : cJ.type.hasFvar = false := by
    rw [hcJty]
    exact (henv _ (List.mem_of_find?_eq_some hfindC)).1
  exact nestedDomPair_WScoped hctorF
    (hDs q hqlt t ht Jn lvls Ds hsrceq) hcI hqM hxM

/-- **AND EVERY PIN-TARGET JOB** (K.51's list) (task #315 M8, the cached run
obligation): the same
inversion at the other filter — the fields a copy classifies recursive
or reflexive at a MIMIC target. -/
theorem nestedPinDomPairs_WScoped {env : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {kinds : List (List (List (RecFieldKind × Nat)))}
    {jobs : List (Nat × Expr × Expr)} (henv : EnvWF env)
    (hDs : ∀ (q : Nat), q < st.pins.length → ∀ t, st.types[p.k + q]? = some t →
      ∀ Jn lvls Ds, t.src = some (Jn, lvls, Ds) → ∀ D ∈ Ds, Expr.WScoped p.nP D)
    (h : nestedPinDomPairs env p st stored (some kinds) = some jobs) :
    ∀ je ∈ jobs, Expr.WScoped je.1 je.2.1 := by
  intro je hje
  unfold nestedPinDomPairs at h
  simp only [bind, Option.bind] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i rows hrows
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨row, hrowmem, hjerow⟩ := List.mem_flatten.mp hje
  obtain ⟨q, hq⟩ := List.getElem?_of_mem hrowmem
  have hqlt : q < st.pins.length := by
    have hlen := mapM_option_length hrows
    have := (List.getElem?_eq_some_iff.mp hq).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨rowq, hrowq, hFq⟩ := mapM_option_inv hrows q q (by simp [hqlt])
  obtain rfl : row = rowq := by rw [hq] at hrowq; exact Option.some.inj hrowq
  -- the pin's row: the copy's source and the container's member
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i t ht
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i src hsrceq
  obtain ⟨Jn, lvls, Ds⟩ := src
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i a ha
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i ks hks
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i ci hci
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i J hJ
  try simp only [] at hFq
  split at hFq
  case isTrue => exact absurd hFq (by simp)
  case isFalse =>
  try simp only [] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i perCtor hperCtor
  simp only [pure, Option.some.injEq] at hFq
  subst hFq
  -- the constructor's row
  obtain ⟨crow, hcrowmem, hjecrow⟩ := List.mem_flatten.mp hjerow
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcrowmem
  have hjlt : j < ks.length := by
    have hlen := mapM_option_length hperCtor
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨crowj, hcrowj, hGj⟩ := mapM_option_inv hperCtor j j (by simp [hjlt])
  obtain rfl : crow = crowj := by rw [hj] at hcrowj; exact Option.some.inj hcrowj
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i kf hkf
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cJ hcJ
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cS hcS
  obtain ⟨cvS, nI, nF⟩ := cS
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i cI hcI
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qM hqM
  obtain ⟨xsM, restM⟩ := qM
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qS hqS
  obtain ⟨fvsS, crestS⟩ := qS
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i qS2 hqS2
  obtain ⟨xsS, restS⟩ := qS2
  try simp only [] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i perField hperField
  simp only [pure, Option.some.injEq] at hGj
  subst hGj
  -- the field's row: a singleton exactly where the filter admits it
  obtain ⟨frow, hfrowmem, hjefrow⟩ := List.mem_flatten.mp hjecrow
  obtain ⟨l, hl⟩ := List.getElem?_of_mem hfrowmem
  have hllt : l < kf.length := by
    have hlen := mapM_option_length hperField
    have := (List.getElem?_eq_some_iff.mp hl).1
    simp only [hlen, List.length_range] at this
    exact this
  obtain ⟨frowl, hfrowl, hHl⟩ := mapM_option_inv hperField l l (by simp [hllt])
  obtain rfl : frow = frowl := by rw [hl] at hfrowl; exact Option.some.inj hfrowl
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i rt hrt
  obtain ⟨r, tgt⟩ := rt
  try simp only [] at hHl
  split at hHl
  case isTrue =>
    simp only [pure, Option.some.injEq] at hHl
    subst hHl
    exact absurd hjefrow (by simp)
  case isFalse =>
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i xM hxM
  try simp only [] at hHl
  split at hHl
  case h_1 => exact absurd hHl (by simp)
  rename_i xS hxS
  simp only [pure, Option.some.injEq] at hHl
  subst hHl
  obtain rfl : je = (p.nP + l, xM.fvarTypeD, xS.fvarTypeD) := by simpa using hjefrow
  -- the container's stored constructor type is fvar-free
  obtain ⟨cvT, caps, cvR, mIc, rPc, rulesc, h1c, h2c, h3c, h4c, hmem⟩ := containerInfo?_inv hci
  obtain ⟨cvC, capsC, cvRc, mIc', rulesC, hf1, hf2, hl1, hl2, hl3, hlen4, hctors⟩ :=
    hmem J (List.mem_of_find?_eq_some hJ)
  obtain ⟨r', cvc, -, -, hfindC, hcJty⟩ := hctors j cJ hcJ
  have hctorF : cJ.type.hasFvar = false := by
    rw [hcJty]
    exact (henv _ (List.mem_of_find?_eq_some hfindC)).1
  exact nestedDomPair_WScoped hctorF
    (hDs q hqlt t ht Jn lvls Ds hsrceq) hcI hqM hxM

/-- A handler that always throws never produces the `.ok`: a successful
`tryCatchThe` in `Except` is a successful body. -/
private theorem tryCatchThrow_ok {α : Type} {x : CheckM α} {e : CheckError} {w : α}
    (h : tryCatchThe CheckError x (fun _ => throw e) = .ok w) : x = .ok w := by
  cases x with
  | ok v => simpa [tryCatchThe, throwThe, MonadExceptOf.tryCatch, Except.tryCatch] using h
  | error err => simp [tryCatchThe, throwThe, MonadExceptOf.tryCatch, Except.tryCatch,
      throw, MonadExceptOf.throw] at h

/-- **THE RECORD AT ONE JOB.**  `nestedOrdNorms` ran the positivity
normalisation on every job's MINTED domain; when its results are the
jobs' STORED domains (`heq`, the check the record makes), the run at
any job of the list is that job's own — the `.internal`
reclassification of the handler seen through. -/
theorem nestedOrdNorms_job {ops : CheckerOps CheckM} {envN : Env}
    {memberNames : List Name} {jobs : List (Nat × Expr × Expr)} {ws : List Expr}
    (h : nestedOrdNorms (m := CheckM) ops envN memberNames jobs = .ok ws)
    (heq : ws = jobs.map (·.2.2))
    {je : Nat × Expr × Expr} (hmem : je ∈ jobs) :
    normPosDomM (m := CheckM) ops envN memberNames je.1 1024 je.2.1 = .ok je.2.2 := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
  obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.1 hi
  rw [nestedOrdNorms] at h
  obtain ⟨-, hall⟩ := mapM_except_inv h
  obtain ⟨je', w, hje', hw, hrun⟩ := hall i hilt
  rw [hi] at hje'
  obtain rfl := Option.some.inj hje'
  have hww : w = je.2.2 := by
    subst heq
    rw [List.getElem?_map, hi] at hw
    exact (Option.some.inj hw).symm
  subst hww
  exact tryCatchThrow_ok hrun

/-! ## THE PIN TARGETS' RUN, INVERTED (task #315 L-B, K.51)

K.51's record is the twin of K.42's at the fields the latter's filter
leaves out — a copy field classified recursive or reflexive at a target
AT OR ABOVE `p.k`, pointing at a MIMIC rather than at a member of the
block being installed.  `nestedPinDomPairs` collects the same triple
`(depth, MINTED, STORED)` by the same three-layer `Option` walk, so the
addressing lemma below is `nestedOrdDomPairs_mem` with the filter's
other branch; what differs is the COMPARISON, which at a pin target
runs the normalisation's output through the elimination's own
`replaceAllNested` before matching the stored domain (and checks that
the state does not grow, which says the re-run minted nothing).  So the
record is inverted in three steps rather than two: the job, the run at
it, and the rewrite at it. -/

/-- **THE JOB AT A PIN-TARGET FIELD.**  `nestedOrdDomPairs_mem`'s twin:
every hypothesis is one of `nestedPinDomPairs`' own lookups, in the
order the walk makes them, and the conclusion is the walk's triple.

`hpin` is the walk's filter at this list — the field is NOT ordinary and
its target is NOT below `p.k` — which is exactly the complement of
`nestedOrdDomPairs`', so the two lists together cover every field. -/
theorem nestedPinDomPairs_mem {env : Env} {p : NestedParts} {st : ElimState}
    {stored : List AuxStored} {kinds : List (List (List (RecFieldKind × Nat)))}
    {jobs : List (Nat × Expr × Expr)}
    (h : nestedPinDomPairs env p st stored (some kinds) = some jobs)
    {q : Nat} (hq : q < st.pins.length)
    {t : AuxType} (ht : st.types[p.k + q]? = some t)
    {Jn : Name} {lvls : List Level} {Ds : List Expr} (hsrc : t.src = some (Jn, lvls, Ds))
    {a : AuxStored} (ha : stored[p.k + q]? = some a)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {ci : ContainerInfo} (hci : containerInfo? env Jn = some ci)
    {J : ContainerMember} (hJ : ci.members.find? (fun J => J.name == Jn) = some J)
    (hlvls : lvls.length = J.lps.length)
    {j : Nat} {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {cvS : ConstantVal} {nI nF : Nat} (hcS : a.ctors[j]? = some (cvS, nI, nF))
    {cI : Expr} (hcI : Expr.instPis (Expr.instantiateLevelParams J.lps lvls cJ.type) Ds = some cI)
    {xsM : List Expr} {restM : Expr} (hopM : openPisAtFvars nF cI p.nP = some (xsM, restM))
    {fvsS : List Expr} {crestS : Expr} (hopS : openPisAtFvars p.nP cvS.type 0 = some (fvsS, crestS))
    {xsS : List Expr} {restS : Expr} (hopS2 : openPisAtFvars nF crestS p.nP = some (xsS, restS))
    {l : Nat} {r : RecFieldKind} {n : Nat} (hkfl : kf[l]? = some (r, n))
    (hpin : r ≠ RecFieldKind.ordinary ∧ ¬ n < p.k)
    {xM xS : Expr} (hxM : xsM[l]? = some xM) (hxS : xsS[l]? = some xS) :
    (p.nP + l, xM.fvarTypeD, xS.fvarTypeD) ∈ jobs := by
  have hrange : ∀ {n i : Nat}, i < n → (List.range n)[i]? = some i := by
    intro n i hi; simp [hi]
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.1 hkf
  obtain ⟨hllt, -⟩ := List.getElem?_eq_some_iff.1 hkfl
  rw [nestedPinDomPairs] at h
  simp only [bind, Option.bind] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i rows hrows
  simp only [pure, Option.some.injEq] at h
  subst h
  -- the row of pin `q`
  obtain ⟨rowq, hrowq, hFq⟩ := mapM_option_inv hrows q q (hrange hq)
  refine List.mem_flatten.mpr ⟨rowq, List.mem_of_getElem? hrowq, ?_⟩
  simp only [ht, hsrc, ha, hks, hci, hJ, hlvls, bne_self_eq_false, Bool.false_eq_true,
    if_false] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i perCtor hperCtor
  simp only [pure, Option.some.injEq] at hFq
  subst hFq
  -- the row of constructor `j`
  obtain ⟨rowj, hrowj, hGj⟩ := mapM_option_inv hperCtor j j (hrange hjlt)
  refine List.mem_flatten.mpr ⟨rowj, List.mem_of_getElem? hrowj, ?_⟩
  simp only [hkf, hcJ, hcS, hcI, hopM, hopS, hopS2] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i perField hperField
  simp only [pure, Option.some.injEq] at hGj
  subst hGj
  -- the row of field `l`, a singleton at a kind the filter leaves to
  -- THIS list
  obtain ⟨rowl, hrowl, hHl⟩ := mapM_option_inv hperField l l (hrange hllt)
  refine List.mem_flatten.mpr ⟨rowl, List.mem_of_getElem? hrowl, ?_⟩
  obtain ⟨hord, hlt⟩ := hpin
  have hordB : (r == RecFieldKind.ordinary) = false := by
    simp only [beq_eq_false_iff_ne]; exact hord
  have hltB : decide (n < p.k) = false := by simp only [decide_eq_false_iff_not]; exact hlt
  simp only [hkfl, hxM, hxS, hordB, hltB, Bool.or_self, Bool.false_eq_true, if_false,
    pure, Option.some.injEq] at hHl
  subst hHl
  simp

/-- **THE PIN-TARGET RUN AT ONE JOB.**  `nestedPinNorms` ran the
positivity normalisation on every job's MINTED domain; unlike K.42's
list its outputs are NOT the stored domains (they are rewritten first),
so the lemma hands back the output AT THE JOB'S OWN INDEX, which is
what `nestedPinRewrites` pairs it with. -/
theorem nestedPinNorms_job {ops : CheckerOps CheckM} {envN : Env}
    {memberNames : List Name} {jobs : List (Nat × Expr × Expr)} {ws : List Expr}
    (h : nestedPinNorms (m := CheckM) ops envN memberNames jobs = .ok ws)
    {i : Nat} {je : Nat × Expr × Expr} (hje : jobs[i]? = some je) :
    ∃ w, ws[i]? = some w ∧
      normPosDomM (m := CheckM) ops envN memberNames je.1 1024 je.2.1 = .ok w := by
  obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.1 hje
  rw [nestedPinNorms] at h
  obtain ⟨-, hall⟩ := mapM_except_inv h
  obtain ⟨je', w, hje', hw, hrun⟩ := hall i hilt
  rw [hje] at hje'
  obtain rfl := Option.some.inj hje'
  exact ⟨w, hw, tryCatchThrow_ok hrun⟩

/-- **THE REWRITE AT ONE JOB.**  The record's `all` over the zipped
lists, read at one index: the normalisation's output, rewritten by the
elimination's own `replaceAllNested` at the FINAL state, IS the job's
stored domain, and the state does not grow. -/
theorem nestedPinRewrites_job {env : Env} {p : NestedParts} {st : ElimState}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)}
    {jobs : List (Nat × Expr × Expr)} {ws : List Expr}
    (h : nestedPinRewrites env p st params pbs₀ jobs ws = true)
    {i : Nat} {je : Nat × Expr × Expr} {w : Expr}
    (hje : jobs[i]? = some je) (hw : ws[i]? = some w) :
    ∃ st' : ElimState,
      replaceAllNested env (p.lps.map Level.param) params pbs₀ st w = .ok (je.2.2, st') ∧
      st'.types.length = st.types.length ∧ st'.pins.length = st.pins.length := by
  obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.1 hje
  obtain ⟨hiw, -⟩ := List.getElem?_eq_some_iff.1 hw
  have hmem : (je, w) ∈ jobs.zip ws :=
    List.mem_of_getElem? (i := i) (List.getElem?_zip_eq_some.mpr ⟨hje, hw⟩)
  rw [nestedPinRewrites] at h
  have hat := (List.all_eq_true.mp h) _ hmem
  simp only at hat
  cases hrep : replaceAllNested env (p.lps.map Level.param) params pbs₀ st w with
  | error e => rw [hrep] at hat; exact nomatch hat
  | ok pr =>
    obtain ⟨w', st'⟩ := pr
    rw [hrep] at hat
    simp only [Bool.and_eq_true, beq_iff_eq] at hat
    obtain ⟨⟨hw', htys⟩, hpins⟩ := hat
    subst hw'
    exact ⟨st', rfl, by simpa using htys, by simpa using hpins⟩

/-! ## (R8) THE TWO NAME LISTS ARE ONE (task #315 L-B)

The elimination's occurrence test looks for `st.newNames`; the auxiliary
block's positivity walk looks for `b.memberNames`.  They are the same
list — `auxBlock` reads its formers off `st.types`, name by name, and
`newNames` is that same projection — but the route has twice found a
real gap behind a same-set-by-two-names identity (K.58: two drivers
computing one quantity with nothing checking they agreed).  So it is
PROVED here rather than noted.

Its consumer: a REFLEXIVE field's binder domain is certified
member-free by the positivity walk (`normPosDomM_inv`'s Π arm), and the
rewrite's PRUNE therefore returns it unchanged — which is what keeps a
copy out of the copy's own telescope, and with it the circularity that
would otherwise move from the target into the telescope. -/

/-- **THE ELIMINATION'S GROWING NAMES ARE THE AUXILIARY BLOCK'S
MEMBERS** (task #315 L-B): `auxBlock` builds one former per entry of
`st.types`, keeping its name, and `ElimState.newNames` is that same
projection. -/
theorem auxBlock_newNames {p : ConLeche.NestedParts} {st : ConLeche.ElimState}
    {b : ConLeche.MutualBlock} (h : ConLeche.auxBlock p st = some b) :
    b.memberNames = st.newNames := by
  obtain ⟨-, hat⟩ := ConLeche.auxBlock_former h
  have hlen : b.formers.length = st.types.length := by
    unfold ConLeche.auxBlock at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨formers, hformers, rfl⟩ := h
    exact ConLeche.mapM_option_length hformers
  refine List.ext_getElem? (fun i => ?_)
  show (b.formers.map (·.1.name))[i]? = (st.types.map (·.name))[i]?
  rw [List.getElem?_map, List.getElem?_map]
  cases hst : st.types[i]? with
  | none =>
    have hge : st.types.length ≤ i := by
      rcases Nat.lt_or_ge i st.types.length with hlt | hge
      · rw [List.getElem?_eq_getElem hlt] at hst; exact nomatch hst
      · exact hge
    rw [List.getElem?_eq_none (by omega)]
    rfl
  | some t =>
    obtain ⟨nIdx, hfo, -⟩ := hat i t hst
    rw [hfo]
    rfl

/-- **A MEMBER-FREE TERM IS PRUNED BY THE REWRITE** (task #315 L-B):
the consumer form of `auxBlock_newNames`, stated exactly as
`replaceAllNested_of_no_mention` wants it.  The positivity walk's Π arm
certifies a reflexive field's binder domains member-free
(`normPosDomM_inv`), and this turns that verdict into the rewrite's
prune. -/
theorem newNames_no_mention_of_memberFree {p : ConLeche.NestedParts}
    {st : ConLeche.ElimState} {b : ConLeche.MutualBlock}
    (h : ConLeche.auxBlock p st = some b) {e : ConLeche.Expr}
    (hm : ConLeche.mentionsMember b.memberNames e = false) :
    (st.newNames.any fun T => e.mentionsConst T) = false := by
  rw [← auxBlock_newNames h]
  exact hm

/-! ## The positivity walk's Π-TOWER has member-free domains (task #315 R3)

A REFLEXIVE copy field's stored domain is a `∀`-telescope, and the
`ordF`-right arm at a PIN target has to peel that telescope on BOTH
sides — the stored domain and the container-headed normalisation `w`
the elimination rewrote into it — and align the two peels.  The
alignment is by INERTNESS: the rewrite must return `w`'s binder
domains unchanged, so that the two towers are towers over the SAME
binder list and their readings share a Π-prefix.

The certificate for that is the walk's own Π arm (`normPosDomM_inv`):
every binder it goes under has a member-free domain, and a member-free
term is what `replaceAllNested`'s prune returns untouched
(`newNames_no_mention_of_memberFree`, just above).  `normPosDomM_inv`
states the mention test only in the arm that TOOK it, so the walk's
two non-Π arms need their own reading (`normPosDomM_free_or_pi`); from
there the tower fact is an induction on the tower's LENGTH, with the
`abstract1` the Π arm closes with carried along
(`mentionsConst_abstract1_false`: an abstraction replaces variables by
bound variables and can only DELETE a constant occurrence). -/

/-- **`abstract1` cannot manufacture a constant occurrence.** -/
theorem mentionsConst_abstract1_false {T : Name} :
    ∀ (e : Expr) (d k : Nat), e.mentionsConst T = false →
      (e.abstract1 d k).mentionsConst T = false
  | .bvar _, _, _, h => h
  | .sort _, _, _, h => h
  | .lit _, _, _, h => h
  | .const _ _, _, _, h => h
  | .fvar idx ty, d, k, h => by
    show (if idx = d then Expr.bvar k else Expr.fvar idx ty).mentionsConst T = false
    split
    · rfl
    · exact h
  | .app f a, d, k, h => by
    show (Expr.app (f.abstract1 d k) (a.abstract1 d k)).mentionsConst T = false
    show ((f.abstract1 d k).mentionsConst T || (a.abstract1 d k).mentionsConst T) = false
    have h' : (f.mentionsConst T || a.mentionsConst T) = false := h
    simp only [Bool.or_eq_false_iff] at h' ⊢
    exact ⟨mentionsConst_abstract1_false f d k h'.1, mentionsConst_abstract1_false a d k h'.2⟩
  | .lam ty b m, d, k, h => by
    show ((ty.abstract1 d k).mentionsConst T || (b.abstract1 d (k + 1)).mentionsConst T) = false
    have h' : (ty.mentionsConst T || b.mentionsConst T) = false := h
    simp only [Bool.or_eq_false_iff] at h' ⊢
    exact ⟨mentionsConst_abstract1_false ty d k h'.1,
      mentionsConst_abstract1_false b d (k + 1) h'.2⟩
  | .forallE ty b m, d, k, h => by
    show ((ty.abstract1 d k).mentionsConst T || (b.abstract1 d (k + 1)).mentionsConst T) = false
    have h' : (ty.mentionsConst T || b.mentionsConst T) = false := h
    simp only [Bool.or_eq_false_iff] at h' ⊢
    exact ⟨mentionsConst_abstract1_false ty d k h'.1,
      mentionsConst_abstract1_false b d (k + 1) h'.2⟩
  | .letE ty v b, d, k, h => by
    show (((ty.abstract1 d k).mentionsConst T || (v.abstract1 d k).mentionsConst T) ||
      (b.abstract1 d (k + 1)).mentionsConst T) = false
    have h' : ((ty.mentionsConst T || v.mentionsConst T) || b.mentionsConst T) = false := h
    simp only [Bool.or_eq_false_iff] at h' ⊢
    exact ⟨⟨mentionsConst_abstract1_false ty d k h'.1.1,
      mentionsConst_abstract1_false v d k h'.1.2⟩,
      mentionsConst_abstract1_false b d (k + 1) h'.2⟩
  | .proj s i e, d, k, h => by
    show (s == T || (e.abstract1 d k).mentionsConst T) = false
    have h' : (s == T || e.mentionsConst T) = false := h
    simp only [Bool.or_eq_false_iff] at h' ⊢
    exact ⟨h'.1, mentionsConst_abstract1_false e d k h'.2⟩

theorem mentionsMember_abstract1_false {ms : List Name} {e : Expr} (d k : Nat)
    (h : mentionsMember ms e = false) : mentionsMember ms (e.abstract1 d k) = false := by
  simp only [mentionsMember, List.any_eq_false] at h ⊢
  exact fun T hT => by simpa using mentionsConst_abstract1_false e d k (by simpa using h T hT)

/-- The tower predicate the induction travels on: the first `n`
binders of a term have member-free domains.  A term that is not a `∀`
where a binder is asked for carries no obligation — the walk's own
stopping arm returns exactly such a term (the stuck member
application), and the consumer only ever instantiates the predicate at
a real tower. -/
private def PisDomsFree (ms : List Name) : Nat → Expr → Prop
  | 0, _ => True
  | n + 1, .forallE dom body _ => mentionsMember ms dom = false ∧ PisDomsFree ms n body
  | _ + 1, _ => True

private theorem PisDomsFree.of_free {ms : List Name} :
    ∀ (n : Nat) {e : Expr}, mentionsMember ms e = false → PisDomsFree ms n e
  | 0, _, _ => trivial
  | n + 1, e, h => by
    cases e
    case forallE dom body bm =>
      obtain ⟨hd, hb⟩ := mentionsMember_forallE_false h
      exact ⟨hd, PisDomsFree.of_free n hb⟩
    all_goals exact trivial

private theorem PisDomsFree.abstract1 {ms : List Name} :
    ∀ (n : Nat) {e : Expr} (d k : Nat), PisDomsFree ms n e →
      PisDomsFree ms n (e.abstract1 d k)
  | 0, _, _, _, _ => trivial
  | n + 1, e, d, k, h => by
    cases e
    case forallE dom body bm =>
      obtain ⟨hd, hb⟩ := h
      exact ⟨mentionsMember_abstract1_false d k hd, PisDomsFree.abstract1 n d (k + 1) hb⟩
    case fvar idx ty =>
      show PisDomsFree ms (n + 1) (if idx = d then Expr.bvar k else Expr.fvar idx ty)
      split <;> exact trivial
    all_goals exact trivial

private theorem PisDomsFree.mkPisB {ms : List Name} :
    ∀ (bs : List (Expr × BinderMeta)) {res : Expr},
      PisDomsFree ms bs.length (mkPisB bs res) →
      ∀ b ∈ bs, mentionsMember ms b.1 = false
  | [], _, _, _, hb => by simp at hb
  | b₀ :: bs, res, h, b, hb => by
    rw [mkPisB_cons] at h
    obtain ⟨hd, hrest⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact PisDomsFree.mkPisB bs hrest b hb

/-- **The walk's output has member-free binder domains**, to any
depth.  Three arms and each gives the predicate for its own reason:
the two stopping arms return a term the walk has just tested
member-free OR a term that is not a `∀` at all (the stuck member
application — where the predicate asks nothing), and the `Π` arm is
the one that carries content: it went under the binder only after
testing the domain member-free, and closes with an `abstract1`, which
cannot manufacture a constant occurrence. -/
private theorem normPosDomM_PisDomsFree {env : Env} {memberNames : List Name} {F : Nat} :
    ∀ (n : Nat) {d fuel : Nat} {e w : Expr},
      normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok w →
      PisDomsFree memberNames n w
  | 0, _, _, _, _, _ => trivial
  | n + 1, d, fuel, e, w, h => by
    cases fuel with
    | zero => exfalso; simp [normPosDomM, throw, throwThe, MonadExceptOf.throw] at h
    | succ fuel =>
      unfold normPosDomM at h
      by_cases hm : mentionsMember memberNames e = true
      case neg =>
        rw [if_pos (by simpa using hm)] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact PisDomsFree.of_free _ (by rw [← h]; simpa using hm)
      rw [if_neg (by simpa using hm)] at h
      try simp only [bind, Except.bind] at h
      obtain ⟨v, -, h⟩ := exceptBind_ok h
      by_cases hmw : mentionsMember memberNames v = true
      case neg =>
        rw [if_pos (by simpa using hmw)] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact PisDomsFree.of_free _ (by rw [← h]; simpa using hmw)
      rw [if_neg (by simpa using hmw)] at h
      cases v
      case forallE dom body bm =>
        simp only at h
        by_cases hd : mentionsMember memberNames dom = true
        · exfalso
          rw [if_pos hd] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        rw [if_neg hd] at h
        try simp only [bind, Except.bind] at h
        obtain ⟨body', hbody, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]
        exact ⟨by simpa using hd,
          PisDomsFree.abstract1 n d 0 (normPosDomM_PisDomsFree n hbody)⟩
      all_goals
        (simp only [pure, Except.pure, Except.ok.injEq] at h
         rw [← h]
         exact trivial)

/-- **THE INERTNESS CERTIFICATE** (task #315 R3): every binder domain
of the positivity walk's OUTPUT, read as a `∀`-telescope, is
member-free — so `replaceAllNested`'s prune returns it unchanged and
the stored domain's telescope is the normalisation's own, binder for
binder. -/
theorem normPosDomM_mkPisB_free {env : Env} {memberNames : List Name} {F : Nat}
    {d fuel : Nat} {e w : Expr} {bs : List (Expr × BinderMeta)} {res : Expr}
    (h : normPosDomM (m := CheckM) (fueledOps mode F) env memberNames d fuel e = .ok w)
    (hw : w = mkPisB bs res) :
    ∀ b ∈ bs, mentionsMember memberNames b.1 = false :=
  PisDomsFree.mkPisB bs (hw ▸ normPosDomM_PisDomsFree bs.length h)

/-! ## The walk's environment is the block's (task #315 WIDE (3) (4c), K.69)

`normPosDomM_indApp` asks `env.find? J = some (.indInfo …)` at the
environment the walk RAN in.  The nested route's copy constructors are
normalised at the block's own environment, `consMutualFormers (fms.take
p.k) env` — the pre-block environment with the auxiliary block's type
FORMERS consed on — while the head the walk meets is answered for at
the PRE-BLOCK one: it is either a J-pin CONTAINER, a stored constant
that the cons does not touch, or a minted copy's AUXILIARY, which is
one of the consed formers.  Both are `indInfo` at the walk's
environment, and that is all `normPosDomM_indApp` reads.

So the "whnf-monotonicity under environment extension" the K.69 row
names as missing is not what is needed here — the fact used is the much
weaker one that a constant-headed inductive application reduces at
NEITHER environment, and the only transport is of the `find?` verdict's
CONSTRUCTOR.  These two lemmas are that transport; the walk's own
identity then comes back unchanged.
-/

/-- **AN `indInfo` SURVIVES THE FORMERS' CONSES**: the conses only add
`indInfo`s, so a name the pre-block environment answers for with an
`indInfo` is answered for with an `indInfo` at the block's own
environment — possibly a DIFFERENT one, where a former shadows it,
which is all a positivity walk's head test reads. -/
theorem consMutualFormers_find?_indInfo :
    ∀ {fms : List MutualFormerA} {env : Env} {n : Name} {cv : ConstantVal} {caps : IndCaps},
      env.find? n = some (.indInfo cv caps) →
      ∃ (cv' : ConstantVal) (caps' : IndCaps),
        (consMutualFormers fms env).find? n = some (.indInfo cv' caps')
  | [], _, _, cv, caps, h => ⟨cv, caps, h⟩
  | g :: gs, env, n, cv, caps, h => by
    show ∃ cv' caps', (consMutualFormers gs ⟨.indInfo g.cvTa {} :: env.consts⟩).find? n
      = some (.indInfo cv' caps')
    by_cases hn : (ConstantInfo.indInfo g.cvTa {} : ConstantInfo).name = n
    · exact consMutualFormers_find?_indInfo
        (show (⟨.indInfo g.cvTa {} :: env.consts⟩ : Env).find? n = some (.indInfo g.cvTa {}) from
          by rw [Env.find?_cons, if_pos hn])
    · exact consMutualFormers_find?_indInfo
        (show (⟨.indInfo g.cvTa {} :: env.consts⟩ : Env).find? n = some (.indInfo cv caps) from
          by rw [Env.find?_cons, if_neg hn]; exact h)

/-- **A CONSED FORMER IS AN `indInfo` AT ITS OWN NAME** — no
`Nodup` needed: the first cons of the name answers with an `indInfo`,
and the later conses keep it one (`consMutualFormers_find?_indInfo`). -/
theorem consMutualFormers_find?_indInfo_mem :
    ∀ {fms : List MutualFormerA} {env : Env} {f : MutualFormerA}, f ∈ fms →
      ∃ (cv' : ConstantVal) (caps' : IndCaps),
        (consMutualFormers fms env).find? f.cvTa.name = some (.indInfo cv' caps')
  | [], _, _, hf => nomatch hf
  | g :: gs, env, f, hf => by
    show ∃ cv' caps', (consMutualFormers gs ⟨.indInfo g.cvTa {} :: env.consts⟩).find?
      f.cvTa.name = some (.indInfo cv' caps')
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact consMutualFormers_find?_indInfo (Env.find?_cons_self (.indInfo f.cvTa {}) env)
    · exact consMutualFormers_find?_indInfo_mem hf'

/-- **THE POSITIVITY WALK IS THE IDENTITY AT THE BLOCK'S OWN
ENVIRONMENT** (task #315 WIDE (3), K.69's owed `nestedOrdNorm_norm_of`
at its CONSTANT-HEAD path): `normPosDomM_indApp` transported across the
formers' conses, for a head the PRE-BLOCK environment records as an
inductive — a J-pin container. -/
theorem normPosDomM_indApp_cons {fms : List MutualFormerA} {env : Env}
    {memberNames : List Name} {F fuel d : Nat}
    {J : Name} {lvls : List Level} {args : List Expr} {cv : ConstantVal} {caps : IndCaps}
    {e' : Expr}
    (hJ : env.find? J = some (.indInfo cv caps))
    (h : normPosDomM (m := CheckM) (fueledOps mode F) (consMutualFormers fms env)
        memberNames d fuel (Expr.mkAppN (.const J lvls) args) = .ok e') :
    e' = Expr.mkAppN (.const J lvls) args := by
  obtain ⟨cv', caps', hfind⟩ := consMutualFormers_find?_indInfo (fms := fms) hJ
  exact normPosDomM_indApp hfind h

/-- **THE SAME AT A MINTED COPY'S AUXILIARY** (task #315 WIDE (3)): the
head a FIRED copy field carries is one of the block's own formers, and
a former is an `indInfo` at the block's environment by construction —
no pre-block lookup at all. -/
theorem normPosDomM_indApp_former {fms : List MutualFormerA} {env : Env}
    {memberNames : List Name} {F fuel d : Nat}
    {f : MutualFormerA} {lvls : List Level} {args : List Expr} {e' : Expr}
    (hf : f ∈ fms)
    (h : normPosDomM (m := CheckM) (fueledOps mode F) (consMutualFormers fms env)
        memberNames d fuel (Expr.mkAppN (.const f.cvTa.name lvls) args) = .ok e') :
    e' = Expr.mkAppN (.const f.cvTa.name lvls) args := by
  obtain ⟨cv', caps', hfind⟩ := consMutualFormers_find?_indInfo_mem (env := env) hf
  exact normPosDomM_indApp hfind h

end ConLeche
