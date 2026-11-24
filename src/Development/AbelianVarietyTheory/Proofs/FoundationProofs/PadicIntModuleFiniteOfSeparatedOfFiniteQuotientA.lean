module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory

theorem padicInt_module_finite_of_separated_of_finite_quotient (l : ℕ) [Fact l.Prime] (X : Type)
    [AddCommGroup X] [Module ℤ_[l] X]
    (hfin : Finite (X ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1))))
    (hsep : ∀ x : X, (∀ r : ℕ, ∃ y, (l : ℤ_[l]) ^ r • y = x) → x = 0) :
    Module.Finite ℤ_[l] X := by
  have hI : IsLocalRing.maximalIdeal ℤ_[l] = Ideal.span {(l : ℤ_[l])} :=
    PadicInt.maximalIdeal_eq_span_p
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[l]) X := by
    refine ⟨fun x hx => hsep x fun r => ?_⟩
    have h := hx r
    rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨y, -, hy⟩ := h
    exact ⟨y, hy⟩
  have hE : (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X) =
      LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ 1)) := by
    ext x
    rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp [LinearMap.mem_range]
  have : Module.Finite ℤ_[l] (X ⧸ (IsLocalRing.maximalIdeal ℤ_[l] • ⊤ : Submodule ℤ_[l] X)) := by
    rw [hE]
    exact Module.Finite.of_finite
  exact finite_of_isHausdorff_of_finite_quotient (IsLocalRing.maximalIdeal ℤ_[l]) X

end GlobalTheory
