module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeDefs
import Aesop.Main
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
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeChange
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset Real

variable {r : ℕ}

theorem sum_mul_tailSum (s y : Fin r → ℝ) :
    ∑ i, s i * tailSum y i = ∑ k, partialSum s k * y k := by
  simp only [tailSum, partialSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem exp_sum_mul_tailSum_eq (s : Fin r → ℝ) :
    (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) =
      fun y => ∏ k, (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) k (y k) := by
  funext y
  rw [sum_mul_tailSum, Real.exp_sum]

theorem integrableOn_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    IntegrableOn (fun x => exp (∑ i, s i * x i)) (logCone r c) := by
  rw [integrableOn_logCone_iff]
  show IntegrableOn (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) (lowerBox r c)
  rw [exp_sum_mul_tailSum_eq, IntegrableOn, lowerBox, volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod (E := ℝ) (f := fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))
    (μ := fun _ => volume.restrict (Set.Ici c)) fun k => ?_
  show IntegrableOn (fun t : ℝ => exp (partialSum s k * t)) (Set.Ici c)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (hs k) c

end ReciprocityTheory.ThetaSummability.Est
