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

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem holoSection : holoSectionStatement.{u} := by
  intro n M _ z f hz hf s w hs hzs
  obtain ⟨e, hxe, rfl⟩ := hz (s w)
  have hchart : IsChart n e e := fun _ _ => rfl
  have hw : e (s w) = w := hzs.self_of_nhds
  have htarget : e.target ∈ 𝓝 w := by
    rw [← hw]
    exact e.open_target.mem_nhds (e.map_source hxe)
  have hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source := hs (e.open_source.mem_nhds hxe)
  have heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s := by
    filter_upwards [hsrc, hzs] with v h1 h2
    simp only [Function.comp_apply]
    rw [show e.symm v = s v by rw [← e.left_inv h1, h2]]
  exact ((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm

end ReciprocityTheory.L2DbarEstimates.Norm
