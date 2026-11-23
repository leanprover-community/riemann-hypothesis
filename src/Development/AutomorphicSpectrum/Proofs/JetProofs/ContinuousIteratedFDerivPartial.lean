module

import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingAvg
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.ParSmooth

theorem continuous_iteratedFDeriv_partial {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (k : ℕ) :
    Continuous fun z : P × Q => iteratedFDeriv ℝ k (fun y => Ψ (y, z.2)) z.1 := by
  apply CompanionTheory.D.gk.admitted.Gard.continuous_iter_partial <;> assumption

theorem contDiff_integral_comp_compact {P Q E β : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace β] [T2Space β]
    [SecondCountableTopology β] [CompactSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (q : β → Q)
    (hq : Continuous q) : ContDiff ℝ ∞ fun y => ∫ a, Ψ (y, q a) ∂ν := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := ν) (fun y a => Ψ (y, q a))
    (fun a => hΨ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_)
    (fun _ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ,
      fun _ _ a ha => absurd (Set.mem_univ a) ha⟩)
  have h : Continuous fun p : P × β => (p.1, q p.2) :=
    continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iteratedFDeriv_partial Ψ hΨ k).comp h

end GlobalTheory.CompanionTheory.ParSmooth
