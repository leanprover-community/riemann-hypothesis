module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.Published

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

namespace L2Extension

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def jacAt (A : WeightedAtlas n Y ι La) (s : Fin n → ι → Y → ℂ) (P : Y) : ℂ :=
  (fderiv ℂ (A.zLoc (fun _ _ => 1) s (A.pick P)) (A.chart (A.pick P) P)).det

def psi (A : WeightedAtlas n Y ι La) (L : La) (s : Fin n → ι → Y → ℂ) (y : Y) : ℝ :=
  (n : ℝ) * Real.log (A.sqn L s y)

def resSq (A : WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) : ℝ :=
  ‖c / jacAt A s P‖ ^ 2 * Real.exp (-A.ph E (A.pick P) P + (n : ℝ) * A.ph L (A.pick P) P)

def resConst (r : ℕ) : ℝ :=
  2 ^ (r + 1) * Real.pi ^ r / ((r - 1).factorial : ℝ)

end L2Extension


open L2Extension in
def L2ExtensionLogCanonical : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι : Type) (La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),

    (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (A.ph H i) y ξ) →
  ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) →
  ∀ hS : (A.zeroSet s).Finite,

    (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) →

    (∀ y, A.sqn L s y ≤ 1) →
  ∀ δ : ℝ, 0 < δ →

    (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s →
      ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) →
  ∀ f : Y → ℂ, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + E) F ∧
    (∀ P ∈ A.zeroSet s, F (A.pick P) P = f P) ∧
    ∫⁻ y, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) *
        A.nsq (A.kap + E) F y * Real.exp (-psi A L s y))) ∂A.mu ≤
      ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P)))

end

end GlobalTheory.Published
