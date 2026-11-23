module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
