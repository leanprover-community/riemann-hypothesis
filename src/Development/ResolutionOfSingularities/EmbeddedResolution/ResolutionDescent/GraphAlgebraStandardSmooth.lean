module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
public import Mathlib.RingTheory.Smooth.StandardSmooth
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

noncomputable section

abbrev graphJacobianMinorDet [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det

abbrev GraphAlgebraAway [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) : Type u :=
  Localization.Away (graphJacobianMinorDet f v)

theorem isUnit_algebraMap_graphJacobianMinorDet [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)) :=
  IsLocalization.map_units (M := Submonoid.powers (graphJacobianMinorDet f v)) (GraphAlgebraAway f v)
    ⟨graphJacobianMinorDet f v, Submonoid.mem_powers _⟩

theorem isUnit_algebraMap_jacobian_graphPreSubmersive [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)
      (graphPreSubmersivePresentation f v hv).jacobian) := by
  rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
  exact ((isUnit_one.neg).pow _).mul (isUnit_algebraMap_graphJacobianMinorDet f v)

private def graphAlgebraAwayLocalizationPresentation [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Algebra.SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)

private def graphAlgebraAwayPreSubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v) (Unit ⊕ σ) (Unit ⊕ τ) :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)

private theorem isUnit_jacobian_presentation_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (isUnit_algebraMap_jacobian_graphPreSubmersive f v hv).mul (graphAlgebraAwayLocalizationPresentation f v).jacobian_isUnit

private def graphAlgebraAwaySubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.SubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (Fintype.card σ)) (Unit ⊕ Fin (Fintype.card τ)) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway f v hv }
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin σ).symm)
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin τ).symm)

theorem isStandardSmooth_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by
  constructor
  exact ⟨Unit ⊕ Fin (Fintype.card σ), Unit ⊕ Fin (Fintype.card τ), inferInstance, inferInstance,
    ⟨graphAlgebraAwaySubmersivePresentation f v hv⟩⟩

end

end FunctorialResolution.EmbeddedResolution
