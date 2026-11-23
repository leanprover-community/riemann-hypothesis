module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoordsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnitStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRangeStatement
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
  (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
  (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k))

theorem tV_isUnit (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  first
    | exact GlobalTheory.T.torus_coordinate_isUnit ..
    | (intros; apply GlobalTheory.T.torus_coordinate_isUnit <;> assumption)

theorem tpow_mem_range (he : 0 < e) (S : Finset (Fin (d + 1)))
    (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)) :
    ∀ m ∈ expS S, tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  first
    | exact GlobalTheory.T.torus_monomial_mem_range ..
    | (intros; apply GlobalTheory.T.torus_monomial_mem_range <;> assumption)

theorem isIntegral_torusS (he : 0 < e) (q : X ⟶ Spec (CommRingCat.of K)) (hiq : i ≫ PSpace.str K N = q)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (ht : ∀ k, IsUnit (tV i y hy V hV k)) :
    letI := (strV q V).toAlgebra
    ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first
    | exact GlobalTheory.T.noether_normalization_finite ..
    | (intros; apply GlobalTheory.T.noether_normalization_finite <;> assumption)

theorem algebraicIndependent_tV [IsIntegral X] (he : 0 < e) (q : X ⟶ Spec (CommRingCat.of K))
    (hiq : i ≫ PSpace.str K N = q)
    (halg : AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (hne : (V : Set X).Nonempty) :
    letI := (strV q V).toAlgebra
    AlgebraicIndependent K (tV i y hy V hV) := by
  first
    | exact GlobalTheory.T.algebraically_independent_coords ..
    | (intros; apply GlobalTheory.T.algebraically_independent_coords <;> assumption)

theorem isAlgebraic_of_integral_torusS {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ)
    (h : ∀ r : R, IsIntegral (torusS K t Finset.univ) r) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  first
    | exact GlobalTheory.T.algebraic_over_torus_of_integral ..
    | (intros; apply GlobalTheory.T.algebraic_over_torus_of_integral <;> assumption)

end CrystallineSemistableComparison.Pb
