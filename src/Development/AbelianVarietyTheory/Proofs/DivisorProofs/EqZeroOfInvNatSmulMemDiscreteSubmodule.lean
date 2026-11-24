module

public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory

theorem discrete_submodule_inv_smul_eq_zero : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  intro g Λ hΛ d hd
  have hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0) := by
    simpa using hc1.smul_const d
  let f : ℕ → Λ := fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [tendsto_subtype_rng]
    simpa [f] using hlim
  rw [nhds_discrete, Filter.tendsto_pure] at hf
  obtain ⟨k, hk⟩ := hf.exists
  have h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0 := congrArg Subtype.val hk
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exfalso
    rw [inv_eq_zero] at h0
    exact (Nat.cast_ne_zero.mpr k.succ_ne_zero) h0
  · exact h0

end GlobalTheory
