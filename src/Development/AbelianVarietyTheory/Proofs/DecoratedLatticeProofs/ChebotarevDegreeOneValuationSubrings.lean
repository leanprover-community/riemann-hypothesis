module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
