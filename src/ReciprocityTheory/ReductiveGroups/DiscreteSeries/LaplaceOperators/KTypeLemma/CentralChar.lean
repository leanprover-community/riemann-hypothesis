module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapQdet
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.HcVOfCentralChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem centralChar (n : ℕ) : CentralCharStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  obtain ⟨hg, hnpq, h8, -⟩ := gapCentral n ε lam h hgap
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) := by
    refine ⟨fun k₁ k₂ g hg' => S7.psiM_equiv T μ k₁ k₂ hg', S7.psiM_one T μ,
      S7.psiM_smooth T μ hμ, fun g hg' => S7.psiM_casimir T μ hμ hg', ?_⟩
    intro ν hν
    exact (S7.psiM_integrable T μ hμ hlam hg hq0 ν).2.1
      (by unfold S7.q0; push_cast; exact h8)
  have hstd : StdGap ε lam := ⟨hanti, h, hg, hnpq⟩
  have hV0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have key := capelli_data hstd hσ hD hV hcas hVK hV0 hP
    (fun Y g hg' => S7.psiCapelli (n := n) ε lam T μ hμ Y g hg') (ω - ((n : ℂ) - 1) / 2) y hy
  rw [sub_add_cancel] at key
  rw [capelliQdet.1 (Module.End ℂ D) n E ω, key, capelliQdet.{0}.2]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
