module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nUnit :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∃ N : W ≃ₗᵢ[ℂ] V, M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨N, hN⟩ := nEx M (resInv M B β β' k1 k2 u1 u2 ha hc)
  have hl : M.swap.abelian₂ M.swap.T₀ M.swap.T₀ = M.abelian₂ M.T₀ M.T₀ := (projLaws M).2.2.2.1 _ _
  obtain ⟨N', hN'⟩ := nEx M.swap (resInv M.swap B β' β k2 k1 u2 u1 ⟨ha.2, ha.1⟩ (hl ▸ hc))
  have i1 := (nIso M).2 N hN
  have i2 := (nIso M.swap).2 N' hN'
  let A : W →ₗᵢ[ℂ] V := ⟨N, i1⟩
  let A' : V →ₗᵢ[ℂ] W := ⟨N', i2⟩
  have hd : Module.finrank ℂ W = Module.finrank ℂ V :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective A.injective) (LinearMap.finrank_le_finrank_of_injective A'.injective)
  exact ⟨A.toLinearIsometryEquiv hd, hN⟩
