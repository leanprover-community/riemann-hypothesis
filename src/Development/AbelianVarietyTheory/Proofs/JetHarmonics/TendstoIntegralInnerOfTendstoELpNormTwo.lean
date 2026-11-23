module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.MeasureTheory.Function.L2Space
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
public import Mathlib.Analysis.InnerProductSpace.Continuous

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
