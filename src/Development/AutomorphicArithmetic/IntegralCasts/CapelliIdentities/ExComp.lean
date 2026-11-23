module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh44.ex_comp :
    ∀ {F M Ω : Type} [inst : Field F] [NumberField F] [inst_2 : Field M]
    [NumberField M] [inst_4 : Field Ω] [inst_5 : Algebra F Ω] [Algebra.IsAlgebraic F Ω] (g : M →+* Ω),
    FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range (⇑g : M → Ω))) := by
  intro F M Ω _ _ _ _ _ _ _ g
  let b := Module.finBasis ℚ M
  have h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω))
      = IntermediateField.adjoin F (Set.range (fun i => g (b i))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩

      rw [← b.sum_repr x, map_sum]
      refine sum_mem (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  rw [h]
  haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
