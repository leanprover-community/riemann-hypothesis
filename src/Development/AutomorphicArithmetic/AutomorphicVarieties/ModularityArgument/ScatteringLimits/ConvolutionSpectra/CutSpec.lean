module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s : Set ℝ), MeasurableSet s → ∀ u : L V, ∀ᵐ x : ℝ, cut V s u x = s.indicator u x := by
  intro V _ _ _ _ s hs
  have hm : ∀ u : L V, MemLp (s.indicator (u : ℝ → V)) 2 volume := fun u => (Lp.memLp u).indicator hs.nullMeasurableSet
  let A : L V →ₗ[ℂ] L V :=
    { toFun := fun u => (hm u).toLp _
      map_add' := fun u v => Lp.ext (by
        filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx]; exact h4
        · simp [hx])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((hm u).toLp _)] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h4]) }
  have hb : ∀ u, ‖A u‖ ≤ 1 * ‖u‖ := fun u => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [(hm u).coeFn_toLp] with x h
    show ‖((hm u).toLp _ : ℝ → V) x‖ ≤ _
    rw [h]
    exact norm_indicator_le_norm_self _ _
  exact Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x)
    ⟨A.mkContinuous 1 hb, fun u => (hm u).coeFn_toLp⟩
