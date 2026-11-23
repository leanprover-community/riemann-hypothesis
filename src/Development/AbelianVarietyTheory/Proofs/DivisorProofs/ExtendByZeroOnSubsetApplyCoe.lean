module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y


open scoped Classical in
def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
