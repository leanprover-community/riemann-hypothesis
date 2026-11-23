module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace MultiProjectiveCoordinates

theorem adjoin_rat_clear {Ω : Type} [Field Ω] [CharZero Ω] (T : Set Ω) (x : Ω) (hx : x ∈ Algebra.adjoin ℚ T) :
    ∃ N : ℕ, 0 < N ∧ (N : Ω) * x ∈ Algebra.adjoin ℤ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have h : ((r.den : ℚ) * r) = (r.num : ℚ) := Rat.den_mul_eq_num r
      have := congrArg (algebraMap ℚ Ω) h
      rwa [map_mul, map_natCast, map_intCast] at this
    rw [this]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x + y) = (M : Ω) * (N * x) + (N : Ω) * (M * y) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x * y) = (N * x) * (M * y) := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

theorem integral_rat_clear {Ω : Type} [Field Ω] [CharZero Ω] (T : Set Ω) (x : Ω)
    (hx : IsIntegral (Algebra.adjoin ℚ T) x) :
    ∃ N : ℕ, 0 < N ∧ IsIntegral (Algebra.adjoin ℤ T) ((N : Ω) * x) := by
  classical
  obtain ⟨p, hmon, hp⟩ := hx
  have hc : ∀ i, ∃ N : ℕ, 0 < N ∧ (N : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T :=
    fun i => adjoin_rat_clear T _ (p.coeff i).2
  choose N hN hNm using hc
  obtain ⟨M, hM⟩ : ∃ M, M = ∏ i ∈ Finset.range (p.natDegree + 1), N i := ⟨_, rfl⟩
  have hMpos : 0 < M := hM ▸ Finset.prod_pos fun i _ => hN i
  have hMc : ∀ i, (M : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hM, ← Finset.mul_prod_erase _ _ hi, Nat.cast_mul, mul_comm (N i : Ω), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hNm i)
    · rw [Finset.mem_range, not_lt] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have hlift : Polynomial.C (M : Ω) * p.map (algebraMap (Algebra.adjoin ℚ T) Ω) ∈
      Polynomial.lifts (algebraMap (Algebra.adjoin ℤ T) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    exact ⟨⟨_, hMc n⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinj : Function.Injective (algebraMap (Algebra.adjoin ℤ T) Ω) := Subtype.val_injective
  have hpm : (p.map (algebraMap (Algebra.adjoin ℚ T) Ω)).Monic := hmon.map _
  have hlc : algebraMap _ Ω q.leadingCoeff = (M : Ω) := by
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, hq, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, hpm.leadingCoeff, mul_one]
  have hroot : Polynomial.aeval x q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_map, hp, mul_zero]
  have hint := isIntegral_leadingCoeff_smul q x hroot
  refine ⟨M, hMpos, ?_⟩
  rwa [Algebra.smul_def, hlc] at hint

theorem exists_integer_multiple_in_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) [CharZero Ω] (d : ℕ) (a : K → ℤ) (s : Ω), (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))) → ∃ N₀ : ℕ, 0 < N₀ ∧ (N₀ : Ω) * s ∈ chartLatNm y a 1 := by
  intro K _ ι _ Ω _ y _ d a s hs
  classical
  have hc : ∀ c : ∀ k, ι k, ∃ N : ℕ, 0 < N ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      IsIntegral (chartRingZ y c) ((N : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k))))) := by
    intro c
    by_cases hy : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨N, hN, hint⟩ := integral_rat_clear _ _ (hs c hy)
      exact ⟨N, hN, fun _ => hint⟩
    · exact ⟨1, one_pos, fun h => absurd h hy⟩
  choose N hN hNint using hc
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hN c, ?_⟩
  intro c hy
  rw [mem_integralClosure_iff]
  simp only [Nat.cast_one, one_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Nat.cast_mul, mul_comm (N c : Ω), mul_assoc, mul_assoc]
  exact IsIntegral.mul (isIntegral_natCast _) (by simpa only [mul_assoc] using hNint c hy)

end MultiProjectiveCoordinates
