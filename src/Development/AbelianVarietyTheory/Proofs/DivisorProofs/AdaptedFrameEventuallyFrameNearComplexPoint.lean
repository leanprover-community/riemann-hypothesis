module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem frame_eventually_near : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  intro F _ σ X ι _ m k E y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    (hP τ).2.2.2⟩

end GlobalTheory.ChernCalc
