module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.Analysis.OscPhase

private lemma norm_exp_two_pi_I_mul_real (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_integral_oscillating_phase
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  have hnorm : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := norm_exp_two_pi_I_mul_real
  have hmeasE : ∀ t : ℝ,
      Measurable fun y => Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) :=
    fun t => by fun_prop
  have hdiff : ∀ (y : X) (t : ℝ), HasDerivAt
      (fun t : ℝ => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I *
        ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))) t := by
    intro y t
    have h1 : HasDerivAt (fun t : ℝ => ((t * M y : ℝ) : ℂ)) ((M y : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).mul_const (M y)).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (g y)
    exact h2.congr_deriv (by ring)
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun (t : ℝ) y => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
    (F' := fun (t : ℝ) y => 2 * Real.pi * Complex.I *
      ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ))))
    (bound := fun y => ‖2 * Real.pi * Complex.I‖ * ‖(M y : ℂ) * g y‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      hg.aestronglyMeasurable.mul (hmeasE t).aestronglyMeasurable)
    (hg.mono (hg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, hnorm, mul_one]))
    ((hMg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable).const_mul _)
    (ae_of_all _ fun y t _ => by simp only [norm_mul, hnorm, mul_one, le_refl])
    (hMg.norm.const_mul _)
    (ae_of_all _ fun y t _ => hdiff y t)
  rwa [integral_const_mul] at hd

end GlobalTheory.CompanionTheory.Analysis.OscPhase
