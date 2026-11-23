module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.scalSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ), Continuous φ → HasCompactSupport φ → Ker (scal V φ) ∧ (shF V).av φ = conv (scal V φ) ∧ kv (scal V φ) = sv V fun x => φ (-x) := by
  intro V _ _ _ _ φ h1 h2
  have hk : Ker (scal V φ) := ⟨h1.smul continuous_const, h2.smul_right (f' := fun _ => ContinuousLinearMap.id ℂ V)⟩
  refine ⟨hk, ?_, ?_⟩
  · ext1 u
    rw [(((avSpec (shF V)).2.2.2 φ (h1.integrable_of_hasCompactSupport h2)).1 u).2, (convSpec _ hk u).2.2]
    refine integral_congr_ae (Eventually.of_forall fun t => Lp.ext ?_)
    filter_upwards [Lp.coeFn_smul (φ t) (sh V t u), (scal V φ t).coeFn_compLpL (sh V t u)] with x a b
    rw [b]; exact a
  · ext1 e
    have hm : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    refine Lp.ext ?_
    filter_upwards [((kvSpec _ hk).1 e).1, ((svSpec (V := V)).1 _ hm e).1] with x a b
    rw [a, b]; rfl
