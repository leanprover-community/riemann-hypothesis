module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

private theorem norm_lterm {W : Type} (q : W → ℕ) (hq : ∀ w, 0 < q w) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ)
    (s : ℂ) (p : W × ℕ) : ‖lterm q α β s p‖ =
      ‖∑ a, α p.1 a ^ (p.2 + 1)‖ * ‖∑ b, β p.1 b ^ (p.2 + 1)‖ * ((q p.1 : ℝ) ^ (-s.re)) ^ (p.2 + 1) / ‖(p.2 : ℂ) + 1‖ := by
  rw [lterm, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_natCast_cpow_of_pos (hq _), Complex.neg_re]

theorem UpperTheory.V.Z.Tf.GOne.extId :
    ExtId := by
  intro W q X d A hS x y
  classical
  obtain ⟨F, σ0, hFa, hFe⟩ := hS.rs x y
  refine ⟨F, hFa, ?_⟩
  have hq : ∀ w, 0 < q w := fun w => lt_of_lt_of_le two_pos (hS.primes.two w)
  have hC := (convergence_of_landau_euler landauL euler_product_log_bound W q X d A hS x y).1
  have hSa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ (fun s => ∑' p, lterm q (A x) (A y) s p) σ := by
    intro σ hσ
    have hU : IsOpen {s : ℂ | (1 + σ) / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ (fun s => ∑' p, lterm q (A x) (A y) s p) {s : ℂ | (1 + σ) / 2 < s.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hC ((1 + σ) / 2) (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)
      · refine Differentiable.differentiableOn ?_
        unfold lterm
        refine Differentiable.div_const (Differentiable.const_mul (Differentiable.pow ?_ _) _) _
        exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (hq p.1).ne'))
      · rw [norm_lterm q hq, norm_lterm q hq, Complex.ofReal_re]
        have hs' : (1 + σ) / 2 < s.re := hs
        have h1 : (1 : ℝ) ≤ q p.1 := by exact_mod_cast hq p.1
        have h2 : (q p.1 : ℝ) ^ (-s.re) ≤ (q p.1 : ℝ) ^ (-((1 + σ) / 2)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        gcongr
    exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith))
  have ha1 : AnalyticOnNhd ℝ (fun t : ℝ => F t) (Set.Ioi 1) := fun t ht => by
    have h1 : AnalyticAt ℝ F (t : ℂ) := (hFa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have ha2 : AnalyticOnNhd ℝ (fun t : ℝ => (if x = y then (t : ℂ) - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) t p))
      (Set.Ioi 1) := fun t ht => by
    have h : AnalyticAt ℂ (fun s : ℂ => (if x = y then s - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) s p)) (t : ℂ) := by
      refine AnalyticAt.mul ?_ (hSa t (Set.mem_Ioi.1 ht)).cexp
      split_ifs
      · exact analyticAt_id.sub analyticAt_const
      · exact analyticAt_const
    exact (h.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hid := ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := max σ0 2 + 1)
    (Set.mem_Ioi.2 (by linarith [le_max_right σ0 2])) (by
      filter_upwards [Ioi_mem_nhds (show max σ0 2 < max σ0 2 + 1 by linarith)] with t ht
      have h1 : σ0 < t := lt_of_le_of_lt (le_max_left _ _) ht
      have h2 : (2 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
      rw [hFe t h1, (euler_product_log_bound W q _ _ (A x) (A y) t hS.primes (hS.bd _) (hS.bd _) (by simpa using h2)).2.1])
  exact fun σ hσ => hid (Set.mem_Ioi.2 hσ)
