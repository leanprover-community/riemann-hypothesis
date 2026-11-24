module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.PhMajProof

theorem local_integrable (n : ℕ) (ε : Fin n → Bool) (h s : ℝ) (hs : 0 ≤ s)
    (hyp : rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) :
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  rcases hyp with h0 | hlt
  · have key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) =
        fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      funext g
      rw [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]
      simp [decE]
    rw [key]
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)
  · have hh : 0 ≤ h := by
      have : 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) :=
        mul_nonneg (by positivity) (add_nonneg hs (by positivity))
      linarith
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)

theorem phMaj : PhMaj := by
  intro B d h hds hloc
  have hd : ∀ v, 0 < d v := fun v => (hds v).2.2.2.1
  have hdp : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).le
  have hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) := by
    intro v
    have hon := (hds v).2.1.2.2.1.2.2 (B.w v)
    refine hon.comp_continuous ?_ ?_
    · unfold uMat
      exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    · intro g
      exact (g v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold ph
    exact continuous_const.mul (continuous_star.comp
      (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))
  · intro g
    unfold ph majPh
    rw [norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp
  · intro s hs hyp
    have key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf =>
        (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v)))) := by
      funext g
      unfold majPh dSum
      rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [key]
    unfold muInf
    have hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v,
        (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v)))))
        (Measure.pi fun v => muG (B.I.ε v)) :=
      Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)
    exact hprod.const_mul _

end GlobalTheory.Dec.PhMajProof
