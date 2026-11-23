module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]

theorem smooth_specMap_algebraMap_graphAlgebraAway [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) :=
    isStandardSmooth_graphAlgebraAway f v hv
  show @Algebra.Smooth _ _ _ _ (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra
  have h : (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra =
      (inferInstance : Algebra (MvPolynomial τ R) (GraphAlgebraAway f v)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [h]
  refine ⟨?_, ?_⟩ <;> infer_instance

theorem isOpenImmersion_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) := by
  have : IsLocalization.Away (graphJacobianMinorDet f v) (GraphAlgebraAway f v) := inferInstance
  exact IsOpenImmersion.of_isLocalization (graphJacobianMinorDet f v) ..

instance instIsOpenImmersionSpecMapGraphAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) :=
  isOpenImmersion_specMap_algebraMap_graphAlgebraAway f v

theorem range_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) (graphJacobianMinorDet f v)
  exact h

theorem algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)) =
      (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)).comp
        (algebraMap (MvPolynomial τ R) (GraphAlgebra f)) :=
  IsScalarTower.algebraMap_eq (MvPolynomial τ R) (GraphAlgebra f) (GraphAlgebraAway f v)

theorem specMap_algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v))) =
      Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebra f))) := by
  rw [algebraMap_graphAlgebraAway_eq_comp f v, CommRingCat.ofHom_comp, Spec.map_comp]

end FunctorialResolution.EmbeddedResolution
