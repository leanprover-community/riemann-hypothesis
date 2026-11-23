module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormOrdStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ) (x : M) (m : ℕ),
    IsLocalHomeomorph z → Holo n z f → VanishesBeyond n z f x m →
    Norm.VanishOrder n z f x (m + 1)

theorem normOrd : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy

end ReciprocityTheory.L2DbarEstimates
