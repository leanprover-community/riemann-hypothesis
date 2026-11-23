module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoice
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

theorem _root_.GlobalTheory.T.low_degree_comparison_independent_of_choice : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  exact @GlobalTheory.CompanionTheory.HopfC.dictionary_pull
