module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBound
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


theorem _root_.GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin n))) (R : ℝ), 1 ≤ n → 1 < R → (∀ w ∈ Λ, w ≠ 0 → R ≤ ∏ τ, ‖w τ‖) → ∀ s : Finset (ι → EuclideanSpace ℂ (Fin n)), (∀ w ∈ s, w ∈ Λ ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ ≤ Real.exp ((6 * n + 9) * Fintype.card ι) / R := by
  first | exact @GlobalTheory.ProdNormSum.lattice_sum_le | exact GlobalTheory.ProdNormSum.lattice_sum_le | (intros; apply GlobalTheory.ProdNormSum.lattice_sum_le <;> assumption)
