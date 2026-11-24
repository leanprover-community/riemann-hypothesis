module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

@[expose] public section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.S7

theorem isPsiFor_psiM {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ)
    (hlam : IsHCParam lam) (hμ : IsMu lam μ) (hh : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) (h8 : 8 * (n : ℝ) * q0 ε < h) :
    IsPsiFor ε lam T (PsiM T μ) ∧ ContinuousOn (PsiM T μ) (UJset ε) := by
  refine ⟨⟨fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ,
    fun g hg => psiM_casimir T μ hμ hg, fun ν hν => ?_⟩, psiM_continuousOn T μ hμ⟩
  have := hν
  exact (psiM_integrable T μ hμ hlam hh hq ν).2.1 h8

end ReciprocityTheory.ChartRestriction.DS.S7
