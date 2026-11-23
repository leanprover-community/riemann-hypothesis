module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.GaugeCharW

theorem extChar : ExtChar := by
  intro G _ _ _ K U hU g hg hKU
  let j : K →+ G ⧸ U := (QuotientAddGroup.mk' U).comp K.subtype
  have hker : ∀ k ∈ j.ker, g.comp K.subtype k = 0 := by
    intro k hk
    have hkU : (k : G) ∈ U := (QuotientAddGroup.eq_zero_iff _).mp hk
    exact hKU k k.2 hkU
  let g' : K ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker (g.comp K.subtype) hker
  obtain ⟨η', hη'⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g'
  let η : G →+ AddCircle (1 : ℝ) := η'.comp (QuotientAddGroup.mk' U)
  have hηU : ∀ x ∈ U, η x = 0 := fun x hx => by
    show η' (QuotientAddGroup.mk' U x) = 0
    rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]
  refine ⟨g - η, ?_, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero (g - η) ?_
    have hmem : (U : Set G) ∈ nhds (0 : G) := hU.mem_nhds U.zero_mem
    refine hg.continuousAt.congr ?_
    filter_upwards [hmem] with u hu
    rw [AddMonoidHom.sub_apply, hηU u hu, sub_zero]
  · intro x hx
    have h1 : η x = g' (QuotientAddGroup.mk (⟨x, hx⟩ : K)) := by
      rw [← hη']; rfl
    rw [AddMonoidHom.sub_apply, h1]
    show g x - (g.comp K.subtype) ⟨x, hx⟩ = 0
    exact sub_self _
  · intro x hx
    rw [AddMonoidHom.sub_apply, hηU x hx, sub_zero]

end PI.GaugeCharW
