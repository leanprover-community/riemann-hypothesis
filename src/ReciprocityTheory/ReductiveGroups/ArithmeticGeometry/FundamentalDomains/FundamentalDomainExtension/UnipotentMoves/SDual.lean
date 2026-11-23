module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sDual : SDual E := by
  intro t ht
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := by
    intro i
    rw [NumberField.integralBasis_apply]
    exact (NumberField.RingOfIntegers.basis E i).isIntegral_coe
  have hx : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := ht y
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 E) E y = (y : E) from rfl, hk]
    simp
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hI := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hx
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one, map_intCast] at hI
  let α : 𝓞 E := ⟨_, hI⟩
  have hα : (α : E) = (NumberField.discr E : E) * t := rfl
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · refine ⟨α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = (((NumberField.discr E).natAbs : ℤ) : E) :=
      congrArg _ h
    rw [hα, h', Int.cast_natCast]
  · refine ⟨-α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = ((-((NumberField.discr E).natAbs : ℤ) : ℤ) : E) :=
      congrArg _ h
    show -(α : E) = _
    rw [hα, h', Int.cast_neg, Int.cast_natCast]
    ring

end UnipMove
