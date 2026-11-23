module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_tate_of_character :
    ∀ (Γ : Type) [Group Γ] (U : Type) [CommGroup U] (p : ℕ), 1 ≤ p → (∀ a b : Γ, a * b = b * a) → ∀ e : ℕ → Γ → Γ → U, (∀ k : ℕ, 1 ≤ k → (∀ (l : ℕ) (z s : Γ), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Γ → U, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Γ, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z) → ∀ κ : Γ → U, (∀ z z', (∃ m, z ^ (p ^ m) = 1) → (∃ m, z' ^ (p ^ m) = 1) → κ (z * z') = κ z * κ z') → ∃ s : ℕ → Γ, (∀ m, s m ^ (p ^ m) = 1 ∧ s (m + 1) ^ p = s m) ∧ ∀ m z, z ^ (p ^ m) = 1 → e (p ^ m) z (s m) = κ z := by
  intro Γ _ U _ p hp hc e he κ hκ
  have hpm : ∀ m : ℕ, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ hp
  have key : ∀ m : ℕ, ∃! s : Γ, s ^ (p ^ m) = 1 ∧ ∀ z, z ^ (p ^ m) = 1 → e (p ^ m) z s = κ z :=
    fun m => (he (p ^ m) (hpm m)).2 κ (fun z z' hz hz' => hκ z z' ⟨m, hz⟩ ⟨m, hz'⟩)
  choose s hs hu using key
  refine ⟨s, fun m => ⟨(hs m).1, ?_⟩, fun m => (hs m).2⟩
  have h1 : s (m + 1) ^ (p ^ m * p) = 1 := by rw [← pow_succ]; exact (hs (m + 1)).1
  apply hu m
  refine ⟨by rw [← pow_mul, mul_comm]; exact h1, fun z hz => ?_⟩
  rw [← (he (p ^ m) (hpm m)).1 p z (s (m + 1)) hp hz h1, ← pow_succ]
  apply (hs (m + 1)).2
  rw [pow_succ, pow_mul, hz, one_pow]

end GlobalTheory.ChTor
