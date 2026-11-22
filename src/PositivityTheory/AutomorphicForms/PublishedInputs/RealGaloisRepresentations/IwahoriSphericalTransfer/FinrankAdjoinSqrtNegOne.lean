module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.RealGal

structure QCM (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] where

  K : IntermediateField F Ω
  nf : NumberField ↥K
  cm : @IsCMField ↥K _ nf.to_charZero
  two : Module.finrank F ↥K = 2

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

instance (Q : QCM F Ω) : NumberField ↥Q.K := Q.nf

instance (Q : QCM F Ω) : IsCMField ↥Q.K := Q.cm

instance [IsAlgClosure F Ω] (Q : QCM F Ω) : IsAlgClosure ↥Q.K Ω :=
  ⟨IsAlgClosure.isAlgClosed F, haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩

section Gauss

open Polynomial
open scoped IntermediateField

end Gauss

def AttRes [IsTotallyReal F] {l : ℕ} [Fact l.Prime] {a : ℕ} (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω] (r : G L Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, π.HasSat (w.under (𝓞 F)) B ∧ FrobEig ι r w ((algSat a (normV (w.under (𝓞 F))) B).map (· ^ f))

section Att

variable {L : Type} [Field L] [NumberField L] [Algebra F L]

theorem AttRes.normV_eq_pow (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  have nv {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [nv, nv]
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

end Att

end GlobalTheory.RealGal

end
