module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Localization.Integer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)

      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
