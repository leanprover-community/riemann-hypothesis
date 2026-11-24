module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

theorem UpperTheory.dvr_of_norm_integral :
    ∀ {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x) → IsDiscreteValuationRing (integralClosure ℤ_[l] K) := by
  intro l _ K _ h
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K _
  have hfr : IsFractionRing (integralClosure ℤ_[l] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] K _
  have key : ∀ x : K, ‖(x : PadicAlgCl l)‖ ≤ 1 →
      IsLocalization.IsInteger (integralClosure ℤ_[l] K) x := by
    intro x hx
    have hi : IsIntegral ℤ_[l] x :=
      (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp (h _ hx)
    exact ⟨⟨x, hi⟩, rfl⟩
  have hval : ValuationRing (integralClosure ℤ_[l] K) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ K]
    intro x
    rcases le_total ‖(x : PadicAlgCl l)‖ 1 with hx | hx
    · exact Or.inl (key x hx)
    · refine Or.inr (key _ ?_)
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ hx
  have hinjK : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, RingHom.coe_comp]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l]
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hf)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] K) hnf).out 1 2).mpr hval
