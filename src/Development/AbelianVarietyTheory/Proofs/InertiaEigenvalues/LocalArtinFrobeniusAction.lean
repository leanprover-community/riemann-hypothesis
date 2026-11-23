module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import GroundTheory.LocalFields.LocalArtinMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompareApply

theorem lift_localArtinMap_apply : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι σ τ hτ z hz
  have H := GlobalTheory.ArtinCompare.restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ τ hτ
  set M := maximalAbelianExtension (w.adicCompletion E) (Kbar w)
  set g := localArtinMap (w.adicCompletion E) (Kbar w) (a σ)
  have e : AlgEquiv.restrictNormalHom M τ (g ⟨z, hz⟩) = ⟨z, hz⟩ := by
    rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have e2 := congrArg (fun y : M => (y : Kbar w)) e
  simp only [AlgEquiv.restrictNormalHom_apply] at e2
  exact e2

end GlobalTheory.ArtinCompareApply
