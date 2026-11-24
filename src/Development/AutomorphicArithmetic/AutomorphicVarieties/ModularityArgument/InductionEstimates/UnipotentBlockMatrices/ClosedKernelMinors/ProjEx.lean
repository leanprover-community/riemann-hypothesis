module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem exists_orthogonal_projection {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) : ∃ P, IsOrthogonalProjectionTwoLines J J' P := by
  let S : Submodule ℂ H := (LinearMap.range J.toLinearMap ⊔ LinearMap.range J'.toLinearMap)ᗮ
  refine ⟨Sᗮ.starProjection, isSelfAdjoint_starProjection _, (Sᗮ.isIdempotentElem_starProjection).eq, fun h => ?_⟩
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  simp only [S]
  rw [← Submodule.inf_orthogonal,
    Submodule.mem_inf, Submodule.mem_orthogonal, Submodule.mem_orthogonal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u => h1 _ ⟨u, rfl⟩, fun v => h2 _ ⟨v, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rintro _ ⟨u, rfl⟩; exact h1 u, by rintro _ ⟨v, rfl⟩; exact h2 v⟩

private theorem cutZero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (T : ℝ) (u : L V) : ∀ᵐ x : ℝ, x ≤ T → UpperTheory.V.Z.IntegralApplyAeEq.cut V (Ioi T) u x = 0 := by
  obtain ⟨h1, -, -, -, -, -, -, h2, -⟩ := UpperTheory.V.Z.IntegralApplyAeEq.cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  rw [inter_self] at h1
  filter_upwards [(h2 _).1 (DFunLike.congr_fun h1 u)] with x hx hT
  exact hx (not_lt.2 hT)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.projEx :
    ProjExC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A'
  have hc := (pairFacts K μ μ₂ τ₁ τ₂ hp D d d' A A').2
  refine ⟨exists_orthogonal_projection _ _, fun T hT => ⟨_, (UpperTheory.V.Z.IntegralApplyAeEq.truncEq A.J A'.J T _ fun u v => ?_).2 rfl⟩⟩
  refine hc T _ _ (cutZero T u) ?_
  filter_upwards [cutZero T v] with x hx hx'
  exact hx (by linarith)
