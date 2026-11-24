module

public import Formalism.LatticeTheta.Statement
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

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def LatticeSummableDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (g : V → ℂ) (b : ℝ),
    (Module.finrank ℝ V : ℝ) < b → g =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Summable (fun l : L => g l)

def Periodization [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b → f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Integrable f ∧ (∀ x : V, Summable (fun l : Λ => f ((l : V) + x))) ∧
    Continuous (fun x : V => ∑' l : Λ, f ((l : V) + x)) ∧
    ∀ (l₀ : Λ) (x : V), ∑' l : Λ, f ((l : V) + ((l₀ : V) + x)) = ∑' l : Λ, f ((l : V) + x)

def UnfoldCoeff [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Integrable f →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume → ∀ μ ∈ dual Λ,
      ∫ y in D, (∑' l : Λ, f ((l : V) + y)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ

def LatticeFourierSeries [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (G : V → ℂ), Continuous G →
    (∀ (l : Λ) (x : V), G ((l : V) + x) = G x) →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume →
    Summable (fun μ : dual Λ =>
      ∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) →
    ∀ x : V, HasSum (fun μ : dual Λ =>
        (ZLattice.covolume Λ : ℂ)⁻¹ *
          (∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) *
          Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
      (G x)

def SchwartzDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (f : 𝓢(V, ℂ)) (b : ℝ),
    (f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) ∧
    (𝓕 (f : V → ℂ) : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b))

end Formalism.H
