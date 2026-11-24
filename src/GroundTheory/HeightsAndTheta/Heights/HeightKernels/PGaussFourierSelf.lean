module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory
open scoped FourierTransform

namespace PGaussFourierSelf

lemma ofReal_gauss {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end PGaussFourierSelf

theorem GaussFourierSelf.proof : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end GroundTheory.Heights₂.Heights
