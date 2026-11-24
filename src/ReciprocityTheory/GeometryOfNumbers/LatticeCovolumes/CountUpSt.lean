module

public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory
open scoped ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem HermFam.nrm_smul_up (h : HermFam K V) (σ : K →+* ℂ) (c : K) (x : V) :
    h.nrm σ (c • x) = ‖σ c‖ * h.nrm σ x := by
  unfold HermFam.nrm
  have h2 : h.form σ (c • x) x = starRingEnd ℂ (σ c) * h.form σ x x := by
    rw [← h.conj_symm σ x (c • x), h.smul_right, map_mul, h.conj_symm σ x x]
  have h1 : h.form σ (c • x) (c • x) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) * h.form σ x x := by
    rw [h.smul_right, h2, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

end ReciprocityTheory.GeometryOfNumbersTheory
