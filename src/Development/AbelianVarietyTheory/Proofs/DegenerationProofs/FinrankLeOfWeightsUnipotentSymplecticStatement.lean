module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankLeOfWeightsUnipotentSymplectic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic : ∀ (𝕜 V : Type) [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V), B.Nondegenerate → (∀ x y, B y x = - B x y) → ∀ (S Φ : V ≃ₗ[𝕜] V) (q : ℕ), 2 ≤ q → IsNilpotent ((S : V →ₗ[𝕜] V) - 1) → (∀ x y, B (S x) (S y) = B x y) → (∀ x y, B (Φ x) (Φ y) = q * B x y) → Φ * S = S ^ q * Φ → ∀ (W : Submodule 𝕜 V) (P : Polynomial ℤ), (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ x ∈ W, Φ x = (q : 𝕜) • x) → (∀ x, S x = x → Polynomial.aeval (Φ : V →ₗ[𝕜] V) P x ∈ W) → Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker ((S : V →ₗ[𝕜] V) - 1)) + Module.finrank 𝕜 W := by
  first | exact @GlobalTheory.SS.LinCore.finrank_le_of_weights | exact GlobalTheory.SS.LinCore.finrank_le_of_weights | (intros; apply GlobalTheory.SS.LinCore.finrank_le_of_weights <;> assumption)
