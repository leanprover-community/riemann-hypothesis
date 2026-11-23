module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J]

def formOfFamily (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : LinearMap.BilinForm ℤ (J → 𝓞 E) :=
  LinearMap.mk₂ ℤ (fun y z => ∑ i, ∑ j, φ i j (H.bar (y i) * z j))
    (by intro y y' z; simp [map_add (f := _), add_mul, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, smul_mul_assoc, Finset.smul_sum])
    (by intro y z z'; simp [map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, mul_smul_comm, Finset.smul_sum])

theorem formOfFamily_apply (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) (y z : J → 𝓞 E) :
    formOfFamily H J φ y z = ∑ i, ∑ j, φ i j (H.bar (y i) * z j) := rfl

theorem formOfFamily_mem (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : formOfFamily H J φ ∈ balBil H.bar (J → 𝓞 E) := by
  intro a y z
  simp only [formOfFamily_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf

def balBilEquiv : balBil H.bar (J → 𝓞 E) ≃ₗ[ℤ] (J → J → (𝓞 E →ₗ[ℤ] ℤ)) where
  toFun β := fun i j => (β.1 (Pi.single i 1)) ∘ₗ LinearMap.single ℤ (fun _ : J => 𝓞 E) j
  map_add' β β' := by ext; simp
  map_smul' c β := by ext; simp
  invFun φ := ⟨formOfFamily H J φ, formOfFamily_mem H J φ⟩
  left_inv β := by
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    have hy : y = ∑ i, y i • (Pi.single i (1 : 𝓞 E) : J → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      rcases eq_or_ne k i with rfl | h <;> simp [*]
    conv_rhs => rw [hy]

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [β.2 (y i) (Pi.single i 1) z]
    conv_rhs => rw [← Finset.univ_sum_single (H.bar (y i) • z)]

    rw [map_sum]
    rfl
  right_inv φ := by
    funext i j
    refine LinearMap.ext fun c => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_apply, hj]
    · simp
    · intro i' _ hi; simp [Pi.single_apply, hi]
    · simp

theorem finrank_balBil_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J]
    [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) =
      Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  intro E _ _ _ H J _ _
  rw [(balBilEquiv H J).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap, Module.finrank_self, mul_one,
    NumberField.RingOfIntegers.rank, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

end GlobalTheory.BalRank
