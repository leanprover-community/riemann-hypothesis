module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
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
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
import GroundTheory.AutomorphicForms.CuspidalProjection.Global

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.qhtTw :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ),
      ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ x : G1 K n, qht (θ.e x) ≤ C * qht x ^ c := by
  intro K _ _ n μ _ θ
  obtain ⟨C, c, h⟩ := θ.height_le
  have hb : ∀ x : G1 K n, BddBelow (Set.range fun γ : Gam K n =>
      AutomorphicForm.height (((γ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)) :=
    fun x => ⟨1, by rintro _ ⟨γ, rfl⟩; exact AutomorphicForm.one_le_height _⟩
  refine ⟨max C 0, c, le_max_right _ _, fun x => ?_⟩
  have hmono : Monotone fun t : ℝ => max C 0 * (max t 0) ^ c := fun a b hab =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) (max_le_max hab le_rfl) c) (le_max_right _ _)
  have hcont : Continuous fun t : ℝ => max C 0 * (max t 0) ^ c := by fun_prop
  have h1 : 0 ≤ qht x := le_ciInf fun γ => (AutomorphicForm.height_pos _).le
  have := hmono.map_ciInf_of_continuousAt (hcont.continuousAt) (hb x)
  change max C 0 * (max (qht x) 0) ^ c = _ at this
  rw [max_eq_left h1] at this
  rw [this]
  refine le_ciInf fun γ => ?_
  refine (ciInf_le (hb (θ.e x)) ⟨θ.e γ, (θ.mem_gam _).2 γ.2⟩).trans ?_
  change AutomorphicForm.height ((θ.e γ * θ.e x : G1 K n) : AdelicGLn.AdelicGL K n) ≤ max C 0 * (max (AutomorphicForm.height (((γ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)) 0) ^ c
  rw [← map_mul, max_eq_left (AutomorphicForm.height_pos _).le]
  refine (h _).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (AutomorphicForm.height_pos _).le _)
