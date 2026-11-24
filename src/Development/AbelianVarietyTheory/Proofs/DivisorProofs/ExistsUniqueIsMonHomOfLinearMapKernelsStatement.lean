module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomOfLinearMapKernels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  first | exact @GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker | exact GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker | (intros; apply GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker <;> assumption)
