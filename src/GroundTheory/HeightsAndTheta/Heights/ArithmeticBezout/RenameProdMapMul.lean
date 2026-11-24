module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
