module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
public import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def QuadraticHeckeZeroEstimates : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 →
    ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ∃ (𝒬 β : ℝ) (θ : ℤ) (S : Set (HeightOneSpectrum (𝓞 K))),
      4 * |(discr K : ℝ)| ≤ 𝒬 ∧ 𝒬 ≤ 4 * |(discr K : ℝ)| * (Ideal.absNorm 𝔮 : ℝ) ∧ (θ = 0 ∨ θ = 1) ∧
      (θ = 1 → 1 - 1 / (8 * Real.log 𝒬) < β ∧ cS / (𝒬 ^ 2 * Real.log 𝒬) ≤ 1 - β) ∧
      (∀ v ∈ S, v.asIdeal ∣ 𝔮) ∧
      ∀ X : ℝ, 𝒬 ^ c₂ ≤ X →
        |(rayNo 𝔮 : ℝ) * (((rayPrimes 𝔮 X).ncard : ℝ) + ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.ncard : ℝ)) -
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log 𝒬) + Real.exp (-Real.sqrt (c₃ * Real.log X / 2))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X

end GlobalTheory.Mem.An
