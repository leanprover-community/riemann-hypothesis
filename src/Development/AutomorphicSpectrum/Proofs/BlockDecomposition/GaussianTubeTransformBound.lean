module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
