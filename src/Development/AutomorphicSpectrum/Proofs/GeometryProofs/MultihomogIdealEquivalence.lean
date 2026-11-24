module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
