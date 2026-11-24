module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

namespace GlobalTheory.EntireFunctionHalfPlane

open Filter Topology

theorem entire_eq_of_eqOn_halfPlane {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (a : ℝ) (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((a + 1 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re} := by
    simp
  have hev : f =ᶠ[𝓝 ((a + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq hf' hg' hev

end GlobalTheory.EntireFunctionHalfPlane
