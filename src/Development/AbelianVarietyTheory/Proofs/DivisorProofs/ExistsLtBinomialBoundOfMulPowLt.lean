module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem elementary_binom_bound : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  intro c k h d hk hh hcd
  have hhk : 0 < h ^ k := pow_pos hh k
  set a : ℚ := (c : ℚ) * ((k : ℚ) / h) ^ k with ha
  have had : a < d := by
    rw [ha, div_pow, ← mul_div_assoc, div_lt_iff₀ hhk]; linarith
  refine ⟨(a + d) / 2, by linarith, ?_⟩
  intro l₀
  have hlim : Tendsto (fun l : ℕ => (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) atTop
      (nhds ((c : ℚ) * ((k : ℚ) / h + 0) ^ k)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℚ))).pow k).const_mul _
  rw [add_zero] at hlim
  have hev1 : ∀ᶠ l : ℕ in atTop, (c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k < (a + d) / 2 :=
    hlim.eventually (gt_mem_nhds (by rw [← ha]; linarith))
  have hev2 : ∀ᶠ l : ℕ in atTop, h < (l : ℚ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop h)
  obtain ⟨l, hl1, hl2, hl0⟩ := (hev1.and (hev2.and (eventually_ge_atTop l₀))).exists
  have hlpos : (0 : ℚ) < l := lt_trans hh hl2
  set x : ℚ := (k : ℚ) * l / h with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨l, ⌊x⌋₊ + 1, hl0, by omega, ?_, hl2, ?_⟩
  · have := Nat.lt_floor_add_one x
    push_cast
    rw [hx, div_lt_iff₀ hh] at this
    linarith
  · have hfl : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx0
    have hcast : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) = (⌊x⌋₊ : ℚ) + k := by
      have : ⌊x⌋₊ + 1 + k - 1 = ⌊x⌋₊ + k := by omega
      rw [this]; push_cast; ring
    have hch : (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ) ≤ (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial :=
      Nat.choose_le_pow_div k _
    have hfact : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hbase : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ≤ (l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) := by
      rw [hcast, mul_add, hx]
      have e1 : (l : ℚ) * ((k : ℚ) / h) = (k : ℚ) * l / h := by ring
      have e2 : (l : ℚ) * ((k : ℚ) / l) = k := by field_simp
      rw [e1, e2]; linarith [hfl]
    have hpow : (((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k ≤ ((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have hlk : (0 : ℚ) < (l : ℚ) ^ k := pow_pos hlpos k
    push_cast
    calc (c : ℚ) * (((⌊x⌋₊ + 1 + k - 1).choose k : ℕ) : ℚ)
        ≤ (c : ℚ) * ((((⌊x⌋₊ + 1 + k - 1 : ℕ)) : ℚ) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ ≤ (c : ℚ) * (((l : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ))) ^ k / k.factorial) := by
          gcongr
      _ = ((c : ℚ) * ((k : ℚ) / h + (k : ℚ) / (l : ℚ)) ^ k) * (l : ℚ) ^ k / k.factorial := by
          rw [mul_pow]; ring
      _ < (a + d) / 2 * (l : ℚ) ^ k / k.factorial := by
          apply div_lt_div_of_pos_right _ hfact
          exact mul_lt_mul_of_pos_right hl1 hlk

end GlobalTheory
