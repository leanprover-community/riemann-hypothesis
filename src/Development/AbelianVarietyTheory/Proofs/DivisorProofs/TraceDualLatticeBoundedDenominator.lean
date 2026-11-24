module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem exists_den_traceDual_ringOfIntegers :
    ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F,
      (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _
  refine ⟨(NumberField.discr F).natAbs, Int.natAbs_pos.mpr (NumberField.discr_ne_zero F), ?_⟩
  intro ξ hξ
  have hint := GlobalTheory.discr_mul_isIntegral_of_traceDual F ξ hξ
  have hint' : IsIntegral ℤ (((NumberField.discr F).natAbs : F) * ξ) := by
    rcases Int.natAbs_eq (NumberField.discr F) with h | h
    · have : ((NumberField.discr F).natAbs : F) = (NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = NumberField.discr F := by omega
        rw [← Int.cast_natCast, h']
      rw [this]; exact hint
    · have : ((NumberField.discr F).natAbs : F) = -(NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = -(NumberField.discr F) := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

end GlobalTheory
