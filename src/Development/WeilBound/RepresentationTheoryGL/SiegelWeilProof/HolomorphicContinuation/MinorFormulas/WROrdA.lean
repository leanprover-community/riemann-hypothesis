module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section

open Function

namespace PositivityTheory.Rg.Sw.SP

theorem entire_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℕ)
    (h : ∀ j < r, iteratedDeriv j f 0 = 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ r * g z := by
  have hdiff : ∀ k : ℕ, Differentiable ℂ ((swap dslope (0 : ℂ))^[k] f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (Complex.differentiableOn_dslope (f := (swap dslope (0 : ℂ))^[k] f) (s := Set.univ) (c := 0)
        Filter.univ_mem).2 ih.differentiableOn
      simpa [swap, differentiableOn_univ] using this
  obtain ⟨p, hp⟩ := hf.analyticAt 0
  obtain ⟨R, hR⟩ := hp
  have hcoeff : ∀ k < r, p.coeff k = 0 := by
    intro k hk
    have h1 := hR.factorial_smul (y := (1 : ℂ)) k
    have h2 : iteratedDeriv k f 0 = iteratedFDeriv ℂ k f 0 (fun _ => 1) := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [← h2, h k hk] at h1
    have h3 : p.coeff k = p k (fun _ => 1) := rfl
    rw [h3]
    rw [nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h4 | h4
    · exact absurd h4 (by exact_mod_cast Nat.factorial_ne_zero k)
    · exact h4
  have hzero : ∀ k < r, (swap dslope (0 : ℂ))^[k] f 0 = 0 := by
    intro k hk
    have := (hR.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
    rw [← this, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
    exact hcoeff k hk
  refine ⟨(swap dslope (0 : ℂ))^[r] f, hdiff r, fun z => ?_⟩
  have := pow_sub_smul_iterate_dslope_of_zero r hzero z
  simpa [smul_eq_mul] using this.symm

end PositivityTheory.Rg.Sw.SP
