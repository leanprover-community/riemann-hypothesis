module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem psiAll : PsiAllStatement n := by
  unfold PsiAllStatement
  intro ε lam h T hHC hgap hq
  obtain ⟨μ, hμ⟩ := exists_mu hHC
  refine ⟨PsiM T μ, fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ,
    fun g hg => psiM_casimir T μ hμ hg, fun k X hX => psiM_dec T μ hμ hHC hgap hq k hX,
    fun ν hν => ?_, fun k g hg => psiM_gelfand T μ hμ k hg, fun μ' hμ' X hX => ?_⟩
  · haveI := hν
    exact psiM_integrable T μ hμ hHC hgap hq ν
  · rw [isMu_unique hμ hμ']
    exact psiM_exp_formula T μ hX

theorem psiExists : PsiExistsStatement n := by
  have hA : PsiAllStatement n := psiAll
  unfold PsiAllStatement at hA
  unfold PsiExistsStatement
  intro ε lam h T hHC hgap hq
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6, -, -⟩ := hA ε lam h T hHC hgap hq
  exact ⟨Ψ, h1, h2, h3, h4, h5, h6⟩

end ReciprocityTheory.ChartRestriction.DS.S7
