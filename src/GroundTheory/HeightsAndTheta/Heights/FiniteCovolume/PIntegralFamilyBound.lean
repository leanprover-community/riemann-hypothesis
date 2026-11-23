module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
