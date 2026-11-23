module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.IdealCycleValues.HomogeneousSumLinearChangeClasses
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem subst_abs_list : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  exact @BaseChangeColon.homogeneous_sum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
