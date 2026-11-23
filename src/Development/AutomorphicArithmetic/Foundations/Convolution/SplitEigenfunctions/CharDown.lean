module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.L2.Host GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem charDown : CharDown := by
  intro E _ _ _ D χ h
  have hE : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b]
    simp
  have hθ : D.θ ≠ 0 := by
    rw [← D.b1]
    exact D.b.ne_zero 1
  have hσ : D.σ ≠ 1 := by
    intro h1
    have h2 := D.conj
    rw [h1] at h2
    have h3 : D.θ = -D.θ := by simpa using h2
    have h4 : (2 : E) * D.θ = 0 := by linear_combination h3
    exact hθ (by simpa using h4)
  refine A.normChar_of_inv hE χ fun c z => ?_
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl
  · rw [one_smul]
  · have h1 := h z
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : Units.map (D.bar : A E →* A E) z = D.σ • z := Units.ext (coe_smul_idele D.σ z).symm
    rw [← h2]
    exact h1.symm

end UpperTheory.ConvolutionTheory.RankTwoDescent
