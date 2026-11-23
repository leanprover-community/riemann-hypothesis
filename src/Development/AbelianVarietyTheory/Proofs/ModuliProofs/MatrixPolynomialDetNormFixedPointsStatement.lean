module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixPolynomialDetNormFixedPoints
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.matrix_polynomial_det_norm_fixed_points : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q] (s : Module.End ℤ Q), (∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) → ∃ U : Matrix (Fin m) (Fin m) ℤ_[l], (∀ F : Polynomial ℤ, Finite {x : Q // Polynomial.aeval s F x = 0} → ‖(Polynomial.aeval U F).det‖ = ‖((Nat.card {x : Q // Polynomial.aeval s F x = 0} : ℕ) : ℚ_[l])‖) ∧ (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ∀ (j : ℕ) (x : Q), l ^ j • x = 0 → Polynomial.aeval s F x = 0) ∧ ∀ (j : ℕ) (pt : Fin m → Q) (Mat : Matrix (Fin m) (Fin m) (ZMod (l ^ j))), (∀ i, l ^ j • pt i = 0) → (∀ y : Q, l ^ j • y = 0 → ∃! c : Fin m → ZMod (l ^ j), ∑ i, (c i).val • pt i = y) → (∀ i, s (pt i) = ∑ i', (Mat i' i).val • pt i') → PadicInt.toZModPow j U.det = Mat.det := by
  first | exact @GlobalTheory.TorsionMatrix.exists_padic_matrix | exact GlobalTheory.TorsionMatrix.exists_padic_matrix | (intros; apply GlobalTheory.TorsionMatrix.exists_padic_matrix <;> assumption)
