module

public import InLeanProof.BodiesI
public import InLeanProof.EnvPresI

/-!
# The knot's environment hypotheses from the relation (task #451, lane P3b)

`EnvBodiesI fe L` (`BodiesI.lean`), everything the knot's bodies read of the
environment, from P3a's relation `EnvPresI fe L`, con-leche's well-formedness
`EnvWF L`, and one more fact about InLean's projection bodies
(`ProjBodiesInRange`); so the knot simulates at every fuel from these and the
projection guard's spec (`ssimI_of_pres`).

**Why the extra premise.**  `ProjEntryRel` wants a projection body a stored
term, in range (`StoredT`), and `EnvPresI`'s `TableRelI` gives the body's
closed reading only.  The range does not follow from the constructor type's:
`projBodyAt` instantiates the parameters by `bvar (nP - k)`, lifted under
binders, so a parameter's index in field `0`'s domain grows by one, and a
constructor type in range (indices up to `maxBVarIdx`) can yield a body that
is not (`EO.liftLooseBVars` writes `bvar (i + d)` unchecked).  InLean's block
check computes the bodies (`structProjBodies`) without checking their range,
so the premise is not preserved by any group step today; closing it needs an
executable check (DESIGN, lane P3b).

`EnvWF L` comes from the theorem's own premise, con-leche's fold invariant
(`envWF_of_modelOk`).
-/

public section

namespace InLeanProof

open Lean InLean

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-- **Every projection body InLean reads is in range.** -/
@[expose] def ProjBodiesInRange (fe : InLean.FEnv) : Prop :=
  ∀ T i e, fe.findProj? T i = some e →
    ∀ b, InLean.projBodyAt e.structName e.numParams e.idx e.ctorType = some b → Expr.RangeOk b

/-- **`EnvProjI`** from the relation and the bodies' range. -/
theorem envProjI_of (hP : EnvPresI fe L) (hR : ProjBodiesInRange fe) : EnvProjI fe L where
  find := by
    intro T i e h
    have hRe := hR T i e h
    have ht := hP.table T
    unfold ConLeche.Env.findProj?
    cases hL : L.findTable? (toName T) with
    | none =>
      rw [hL] at ht
      rw [findProj_none_of ht] at h; cases h
    | some tbl =>
      rw [hL] at ht
      obtain ⟨v, c, cv, hT, hcs, hI, hc, hp, h1, h2, h3, h4, h5, hb⟩ := ht
      rw [findProj_of hT hcs hI hc hp] at h
      split at h
      · rename_i hi
        simp only [Option.some.injEq] at h; subst h
        refine ⟨tbl.entry i, by simp [h5, hi], ?_⟩
        refine ⟨h1, rfl, h4, h3, h5, h2, ?_⟩
        intro body hbody
        obtain ⟨b, hb1, hb2, hb3⟩ := hb i hi
        rw [hb1, Option.some.injEq] at hbody; subst hbody
        exact ⟨hb2, hRe _ hb1, hb3⟩
      · cases h

/-- **What the knot's bodies read of the environment**, from the relation,
con-leche's well-formedness and the projection bodies' range. -/
theorem envBodiesI_of (hP : EnvPresI fe L) (hwf : ConLeche.EnvWF L) (hR : ProjBodiesInRange fe) :
    EnvBodiesI fe L :=
  ⟨hwf, envRelI_of hP, envDomI_of hP, envDefnI_of hP, envViewI_of hP, envRecI_of hP,
    defeqEnvI_of hP, envProjI_of hP hR⟩

/-- **The knot simulates at every fuel** from the relation, con-leche's
well-formedness, the projection bodies' range and the guard's spec. -/
theorem ssimI_of_pres (hP : EnvPresI fe L) (hwf : ConLeche.EnvWF L) (hR : ProjBodiesInRange fe)
    (hpg : ∀ b f, SSimI b L fe f → ProjGuardSpecI b L (coreKnotI .verified b fe f) fe)
    {eager : Bool} (f : Nat) : SSimI eager L fe f :=
  ssimI_of_env (envBodiesI_of hP hwf hR) hpg f

universe w

/-- **`EnvWF` from con-leche's fold invariant** (the theorem's premise on `L`,
`AddDeclSound`): its carrier's base model holds it. -/
theorem envWF_of_modelOk {V : Type w} [ConLeche.SetTheory V] (h : ConLeche.Model.EnvModelOk V L) :
    ConLeche.EnvWF L :=
  h.1.elim fun mp _ => mp.base2.wf

end InLeanProof
