module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasPsB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem casL_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, DifferentiableOn ℂ (Lhol X (psM T μ)) U) ∧
      ∀ z ∈ U, casL (psM T μ) z = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
  have := compactSpace_KG ε
  have hh := psM_holo T μ
  rcases hh with ⟨U, hUo, hpos, hΩ, hdiff, hfd⟩
  refine ⟨U, hUo, hpos, hdiff, fun X => CasPsB.differentiableOn_lhol T μ hUo hΩ hfd X, fun z hz => ?_⟩
  have hint : ∀ a b : Fin n, Integrable (fun k =>
      CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z))) (muK ε) := fun a b =>
    (CasPsB.integrable_K (CasPsB.continuous_FY' T μ hUo hΩ hfd _ hz)).apply_continuousLinearMap _
  calc casL (psM T μ) z
      = ∑ a, ∑ b, ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          CasPsB.lhol_lhol_psM T μ hUo hΩ hfd _ _ hz
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ∑ a, ∑ b, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) := by
        rw [integral_finsetSum Finset.univ
          (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hint a b)), Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum Finset.univ (fun b _ => hint a b), Finset.smul_sum]
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ((casVal lam : ℝ) : ℂ) • (PhiM μ (toMK k⁻¹ * z * toMK k) •
            (T.op k * projW T * T.op k⁻¹)) ∂(muK ε) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
          CasPsB.sum_FY' T μ lam hμ k (hΩ z hz k))
    _ = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
        rw [integral_smul, smul_comm]
        rfl

end ReciprocityTheory.ChartRestriction.DS.S7
