module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijective
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

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

theorem _root_.GlobalTheory.T.model_comparison_degree_one_bijective : ∀ (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F'), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Function.Bijective (th1 m) → Function.Bijective (th2 m) → ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F', ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)), ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F', e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  exact @GlobalTheory.CompanionTheory.PerfVB.Cls.model_comparison_degree_zero_bijective
