module

public import ConLeche.Model.Inductives.BlockRep

public section

/-!
# A guarded call's arguments, certified against the telescope

The residue's typing run infers a guarded call's `ih r a⃗` node as an
application spine at the constructors' environment; what the recursor
model needs of it is that each argument was certified against the
`ih` opener's own domain — the field's telescope.  This file is that
inversion (`certs_of_infer_mkAppN`) and the Π-tower bookkeeping it
stands on (`PiSpine`, the opener's stored type as the run leaves it).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A guarded call's ARGUMENTS are certified against the
telescope

The residue's typing run infers the opened body at the CONSTRUCTORS'
environment, and a guarded call's node `ih_r a⃗` is an application
spine there.  What the recursor model needs of it is that each argument
`a_t` was certified against the ih opener's own domain, i.e. against
the field's telescope.  That is one INVERSION of the typing relation,
and it is clean at the `.full` grade because the io site
(`Infer.appSkip`, which certifies no argument at all) is not
available there: `appSkip` is stated at `.io` only.

(At `.io` the claim is FALSE, and that is the io licence, not an
omission: `Model/IOLicense.lean`'s `io_domain_transfer` is what pays
for it.  The rule stage runs `inferType` at the checker's certified
grade, so the `.full` inversion is the one that applies.) -/

/-- **The application node, inverted at the full grade** — the head's
type reduces to a `∀` and the argument is certified against its
domain.  `Infer.appSkip` is `.io`-only, so at `.full` there is exactly
one way to infer an application. -/
theorem infer_app_inv_full {env : Env} {d : Nat} {f a T : Expr}
    (h : ConLeche.Rules.Infer env .full d (.app f a) T) :
    ∃ (tf ty body ta : Expr) (mt : ConLeche.BinderMeta),
      ConLeche.Rules.Infer env .full d f tf ∧
      ConLeche.Rules.Red env d tf (.forallE ty body mt) ∧
      ConLeche.Rules.Infer env .full d a ta ∧
      ConLeche.Rules.DefEq env d ta ty ∧
      T = body.instantiate1 a := by
  cases h with
  | app hf hr ha hd => exact ⟨_, _, _, _, _, hf, hr, ha, hd, rfl⟩

/-- The head of a `.full`-inferred application spine is itself
inferred. -/
theorem infer_mkAppN_head {env : Env} {d : Nat} :
    ∀ (cs : List Expr) {g T : Expr},
      ConLeche.Rules.Infer env .full d (Expr.mkAppN g cs) T →
      ∃ tg : Expr, ConLeche.Rules.Infer env .full d g tg
  | [], _, T, h => ⟨T, h⟩
  | c :: cs, g, T, h => by
    obtain ⟨tg, hg⟩ := infer_mkAppN_head cs (g := .app g c) h
    obtain ⟨tf, -, -, -, -, hif, -, -, -, -⟩ := infer_app_inv_full hg
    exact ⟨tf, hif⟩

/-! ### As a TELESCOPE certificate

`infer_app_inv_full` above says each argument is certified, but
against an EXISTENTIAL domain, which no consumer can use: the fit
needed is a chain of memberships in the ih opener's OWN
telescope.  What names those domains is `Certs` (`Rules/Rel.lean`),
the relation whose soundness (`certs_sound` → `CertsSem`) already
concludes `TeleFitPA` — the fit itself.  So the usable form is
"the spine is a `Certs` walk of the head's type".

The obstruction is that `Infer.app` REDUCES the head's type at every
step (`Red env d tf (.forallE ty body mt)`) while `Certs` peels a
LITERAL `∀`.  They meet because an ih opener's type IS a literal
Π-tower and reduction cannot move it: `Red` out of a `∀` or a sort is
the identity (`red_rigidTy`), since the only rules whose subject is
neither an application, a projection nor a literal are `refl`,
`trans`, `delta` and the three RESCUES — and `unfoldDefinition` is
`none` off a non-`const` head while a rescue's subject has a
constant-headed inferred type, which a `∀`'s (a sort) is not. -/

/-- A sort's and a `∀`'s inferred type is a SORT — the fact that
closes the rescue rules in `red_rigidTy`. -/
theorem infer_rigidTy_sort {env : Env} {g : ConLeche.Rules.Grade} {d : Nat} {s t : Expr}
    (h : ConLeche.Rules.Infer env g d s t)
    (hs : (∃ u, s = .sort u) ∨ (∃ A B mb, s = .forallE A B mb)) :
    ∃ u, t = .sort u := by
  rcases hs with ⟨u, rfl⟩ | ⟨A, B, mb, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩

/-- A sort and a `∀` are their own application head, so no
constant-headed premise can be about them. -/
theorem getAppFn_rigidTy {e : Expr} {n : ConLeche.Name} {us : List ConLeche.Level}
    (hs : (∃ u, e = .sort u) ∨ (∃ A B mb, e = .forallE A B mb))
    (h : e.getAppFn = .const n us) : False := by
  rcases hs with ⟨u, rfl⟩ | ⟨A, B, mb, rfl⟩
  · rw [show (Expr.sort u).getAppFn = Expr.sort u from rfl] at h
    exact ConLeche.Expr.noConfusion h
  · rw [show (Expr.forallE A B mb).getAppFn = Expr.forallE A B mb from rfl] at h
    exact ConLeche.Expr.noConfusion h

/-- `Red`'s motive for `red_rigidTy` — a single `Prop` in the subject
and the reduct, as `RedSem` is, so that the equation compiler can
recurse on the derivation alone. -/
@[expose] def RedRigid (s e : Expr) : Prop :=
  ((∃ u, s = .sort u) ∨ (∃ A B mb, s = .forallE A B mb)) → e = s

/-- The motive at a subject that is neither a sort nor a `∀` — the
nine rules whose subject is an application, a projection or a
literal. -/
theorem redRigid_absurd {s e : Expr}
    (hne : ∀ u : ConLeche.Level, s ≠ .sort u)
    (hne2 : ∀ (A B : Expr) (mb : ConLeche.BinderMeta), s ≠ .forallE A B mb) :
    RedRigid s e := by
  rintro (⟨u, hu⟩ | ⟨A, B, mb, hu⟩)
  · exact absurd hu (hne u)
  · exact absurd hu (hne2 A B mb)

/-- The motive composes along `Red.trans`. -/
theorem redRigid_trans {e₁ e₂ e₃ : Expr} (h₁ : RedRigid e₁ e₂) (h₂ : RedRigid e₂ e₃) :
    RedRigid e₁ e₃ := fun hs => by
  have a1 := h₁ hs
  have a2 := h₂ (by rw [a1]; exact hs)
  rw [a2, a1]

/-- The motive at a RESCUE: the subject's io-inferred type is
constant-headed after reduction, and a sort's is not. -/
theorem redRigid_rescue {env : Env} {d : Nat} {major tm tmaj fab : Expr}
    {T : ConLeche.Name} {ust : List ConLeche.Level}
    (htm : ConLeche.Rules.Infer env .io d major tm) (ihm : RedRigid tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust) : RedRigid major fab := fun hs => by
  obtain ⟨u, rfl⟩ := infer_rigidTy_sort htm hs
  rw [ihm (Or.inl ⟨u, rfl⟩)] at hthead
  exact absurd hthead (fun h => getAppFn_rigidTy (Or.inl ⟨u, rfl⟩) h)

/-- **Reduction is the identity on a sort and on a `∀`.**  The two
shapes travel together: a rescue constrains its subject only through
the subject's io-inferred type, and a `∀`'s inferred type is a sort,
so the sort case is what closes the `∀` case.

`Red` is mutually inductive, so this is written with the equation
compiler (as `red_sound` is) and not with `induction`; the hypothesis
lives in the motive (`RedRigid`) and every recursive call is in TERM
position, for the same reason — a trailing premise whose type mentions
the subject, or a recursive call under a tactic block, blocks the
structural elimination. -/
theorem red_rigidTy {env : Env} {d : Nat} :
    ∀ {s e : Expr}, ConLeche.Rules.Red env d s e → RedRigid s e
  | _, _, .refl => fun _ => rfl
  | _, _, .trans h₁ h₂ => redRigid_trans (red_rigidTy h₁) (red_rigidTy h₂)
  | _, _, .appFn .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .projArg .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .betaGate .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .beta .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natLit .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .strLit .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natSucc .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natOp .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .proj .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .delta hu => fun hs => by
    rcases hs with ⟨u, hq⟩ | ⟨A, B, mb, hq⟩
    · subst hq
      rw [show ConLeche.unfoldDefinition env (Expr.sort u) = none from rfl] at hu
      exact absurd hu (by simp)
    · subst hq
      rw [show ConLeche.unfoldDefinition env (Expr.forallE A B mb) = none from rfl] at hu
      exact absurd hu (by simp)
  | _, _, .iota hhead .. => fun hs => absurd hhead (fun h => getAppFn_rigidTy hs h)
  | _, _, .rescueK _ _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead
  | _, _, .rescueEta _ _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead
  | _, _, .rescueAnd _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead

/-- **Every grade implies the io grade.**  `Certs` certifies its
arguments at `.io`, `Infer.app` at the grade of the spine; the one
place the two differ is the λ rule's domain check, whose premises are
guarded by `g = .full` and therefore vacuous at `.io`.

The grade is a VARIABLE here and not `.full`: a fixed index is not a
variable, and the structural elimination of an inductive FAMILY needs
one. -/
theorem infer_io_of_grade {env : Env} :
    ∀ {g : ConLeche.Rules.Grade} {d : Nat} {e t : Expr},
      ConLeche.Rules.Infer env g d e t → ConLeche.Rules.Infer env .io d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar h => .fvar h
  | _, _, _, _, .const h1 h2 h3 => .const h1 h2 h3
  | _, _, _, _, .natLit h => .natLit h
  | _, _, _, _, .strLit h => .strLit h
  | _, _, _, _, .forallE h1 h2 h3 h4 h5 =>
    .forallE (infer_io_of_grade h1) h2 (infer_io_of_grade h3) h4 h5
  | _, _, _, _, .lam _ _ hb hpw hio hred hz =>
    .lam (s := .sort .zero) (u := .zero)
      (fun h => ConLeche.Rules.Grade.noConfusion h)
      (fun h => ConLeche.Rules.Grade.noConfusion h) (infer_io_of_grade hb) hpw hio hred hz
  | _, _, _, _, .app hf hr ha hd =>
    .app (infer_io_of_grade hf) hr (infer_io_of_grade ha) hd
  | _, _, _, _, .appSkip hf hr hn => .appSkip (infer_io_of_grade hf) hr hn
  | _, _, _, _, .proj hp hr h1 h2 h3 h4 h5 =>
    .proj (infer_io_of_grade hp) hr h1 h2 h3 h4 h5

/-- **The head's type is a literal Π-tower deep enough for the
spine**, the domains instantiated along it — the hypothesis under
which `Infer.app`'s reduction step is the identity
(`red_rigidTy`). -/
inductive PiSpine : Expr → List Expr → Prop
  | nil {T : Expr} : PiSpine T []
  | cons {ty body a : Expr} {mb : ConLeche.BinderMeta} {as : List Expr} :
      PiSpine (body.instantiate1 a) as → PiSpine (.forallE ty body mb) (a :: as)

/-! ### `PiSpine`, from the run's own Π-count

`PiSpine` is what `certs_of_infer_mkAppN` needs of the head's type,
and the run states its Π-tower with `stripPis`.  The two meet through ONE
observation: `stripPis` peels a `∀` without instantiating and
`PiSpine` peels it WITH, and `instantiate1` maps a `∀` to a `∀`, so
"has at least `n` leading `∀`s" survives every instantiation the
spine performs. -/

/-- Instantiation preserves the leading Π-count. -/
theorem stripPis_isSome_instantiate1 :
    ∀ (n : Nat) {e : Expr} (a : Expr) (k : Nat),
      (e.stripPis n).isSome = true → ((e.instantiate1 a k).stripPis n).isSome = true
  | 0, _, _, _, _ => rfl
  | n + 1, e, a, k, h => by
    cases e with
    | forallE ty body mb =>
      have hb : (body.stripPis n).isSome = true := by
        simpa only [ConLeche.Expr.stripPis, Option.isSome_map] using h
      show ((Expr.forallE (ty.instantiate1 a k) (body.instantiate1 a (k + 1)) mb).stripPis
        (n + 1)).isSome = true
      simp only [ConLeche.Expr.stripPis, Option.isSome_map]
      exact stripPis_isSome_instantiate1 n a (k + 1) hb
    | _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **The seam**: a head type with at least as many leading `∀`s as
the spine has arguments IS a `PiSpine`. -/
theorem piSpine_of_stripPis :
    ∀ (as : List Expr) {e : Expr}, (e.stripPis as.length).isSome = true → PiSpine e as
  | [], _, _ => .nil
  | a :: as, e, h => by
    cases e with
    | forallE ty body mb =>
      have hb : (body.stripPis as.length).isSome = true := by
        simpa only [List.length_cons, ConLeche.Expr.stripPis, Option.isSome_map] using h
      exact .cons (piSpine_of_stripPis as (stripPis_isSome_instantiate1 as.length a 0 hb))
    | _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- A generated Π-tower has its own length's worth of leading `∀`s —
the shape of every `ih` opener's type. -/
theorem stripPis_isSome_mkPisOf :
    ∀ (tele : List (Expr × ConLeche.BinderMeta)) (body : Expr) (n : Nat),
      n ≤ tele.length → ((Expr.mkPisOf tele body).stripPis n).isSome = true
  | _, _, 0, _ => rfl
  | (ty, mt) :: tele, body, n + 1, h => by
    show ((Expr.forallE ty (Expr.mkPisOf tele body) mt).stripPis (n + 1)).isSome = true
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_mkPisOf tele body n (by simpa using h)

/-- **The call's certificates, in the form a consumer can use.**  A `.full`-inferred spine
whose head's inferred type is pinned (an fvar's is: `Infer.fvar`
reads the stored annotation) and is a literal Π-tower IS a `Certs`
walk of that tower — so `certs_sound` gives `CertsSem`, whose
conclusion is the `TeleFitPA` the fit needs.

The two hypotheses are exactly what an `ih` opener supplies: its
inferred type is its stored type, and that type is the generated
Π-tower over the field's telescope. -/
theorem certs_of_infer_mkAppN {env : Env} {d : Nat} :
    ∀ (as : List Expr) {f T tf : Expr},
      ConLeche.Rules.Infer env .full d (Expr.mkAppN f as) T →
      (∀ t, ConLeche.Rules.Infer env .full d f t → t = tf) →
      PiSpine tf as →
      ConLeche.Rules.Certs env d false tf as
  | [], _, _, _, _, _, _ => .nil
  | b :: bs, f, T, tf, h, hdet, hpi => by
    cases hpi with
    | cons hrest =>
      obtain ⟨tg, hg⟩ := infer_mkAppN_head bs (g := .app f b) h
      obtain ⟨tf₀, ty₀, body₀, ta, mt₀, hif, hred, hia, hdq, rfl⟩ := infer_app_inv_full hg
      obtain rfl := hdet tf₀ hif
      have heq := red_rigidTy hred (Or.inr ⟨_, _, _, rfl⟩)
      injection heq with e1 e2 e3
      subst e1; subst e2; subst e3
      refine .cert (infer_io_of_grade hia) hdq ?_
      refine certs_of_infer_mkAppN bs (f := .app f b) h ?_ hrest
      intro t ht
      obtain ⟨tf₁, ty₁, body₁, ta₁, mt₁, hif₁, hred₁, -, -, rfl⟩ := infer_app_inv_full ht
      obtain rfl := hdet tf₁ hif₁
      have heq₁ := red_rigidTy hred₁ (Or.inr ⟨_, _, _, rfl⟩)
      injection heq₁ with f1 f2 f3
      subst f1; subst f2; subst f3
      rfl

end ConLeche.Model
