module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateFieldStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

namespace GlobalTheory.FieldSize

theorem natAbs_discr_le_of_map_different_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    (discr L).natAbs ≤ (discr F').natAbs ^ Module.finrank F' L * (discr F).natAbs ^ Module.finrank F L := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)]
  refine Nat.mul_le_mul_right _ ?_
  have h1 := Ideal.absNorm_dvd_absNorm_of_le h
  rw [Ideal.absNorm_algebraMap (𝓞 F') (𝓞 L), absNorm_differentIdeal F' (𝓞 F')] at h1
  have h2 : Module.finrank (𝓞 F') (𝓞 L) = Module.finrank F' L :=
    (IsFractionRing.finrank_eq (𝓞 F') F' (𝓞 L) L).symm
  rw [h2] at h1
  exact Nat.le_of_dvd (pow_pos (Int.natAbs_pos.2 (discr_ne_zero F')) _) h1

theorem log_discr_div_le (F F' L : Type) [Field F] [Field F'] [Field L]
    [NumberField F] [NumberField F'] [NumberField L] [Algebra F L] [Algebra F' L]
    (h : (differentIdeal ℤ (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) ≤ differentIdeal (𝓞 F) (𝓞 L)) :
    Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤
      Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F + Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' := by
  have h1 := natAbs_discr_le_of_map_different_le F F' L h
  have h2 : |((discr L : ℤ) : ℝ)| ≤ |((discr F' : ℤ) : ℝ)| ^ Module.finrank F' L * |((discr F : ℤ) : ℝ)| ^ Module.finrank F L := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    simpa [Nat.cast_natAbs] using this
  have p : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < |((discr K : ℤ) : ℝ)| := fun K _ _ =>
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have h3 := Real.log_le_log (p L) h2
  rw [Real.log_mul (pow_pos (p F') _).ne' (pow_pos (p F) _).ne', Real.log_pow, Real.log_pow] at h3
  have e1 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F * Module.finrank F L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F L).symm
  have e2 : (Module.finrank ℚ L : ℝ) = Module.finrank ℚ F' * Module.finrank F' L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F' L).symm
  have q : ∀ (K : Type) [Field K] [NumberField K], (0 : ℝ) < Module.finrank ℚ K := fun K _ _ => by
    exact_mod_cast Module.finrank_pos
  have qL := q L
  have qF := q F
  have qF' := q F'
  rw [div_le_iff₀ qL, add_mul]
  have a1 : Real.log |((discr F : ℤ) : ℝ)| / Module.finrank ℚ F * Module.finrank ℚ L =
      Module.finrank F L * Real.log |((discr F : ℤ) : ℝ)| := by
    rw [e1]; field_simp
  have a2 : Real.log |((discr F' : ℤ) : ℝ)| / Module.finrank ℚ F' * Module.finrank ℚ L =
      Module.finrank F' L * Real.log |((discr F' : ℤ) : ℝ)| := by
    rw [e2]; field_simp
  rw [a1, a2]; linarith

theorem sz_sup : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  rintro F F' a b a' b' ⟨i1, ha, hb⟩ ⟨i2, ha', hb'⟩
  haveI i3 : FiniteDimensional ℚ ↥(F ⊔ F') := IntermediateField.finiteDimensional_sup F F'
  letI : NumberField F := NumberField.mk
  letI : NumberField F' := NumberField.mk
  letI : NumberField ↥(F ⊔ F') := NumberField.mk
  refine ⟨i3, ?_, ?_⟩
  · have h1 : (Module.finrank ℚ ↥(F ⊔ F') : ℝ) ≤ Module.finrank ℚ F * Module.finrank ℚ F' := by
      exact_mod_cast IntermediateField.finrank_sup_le F F'
    have q : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (0 : ℝ) < Module.finrank ℚ K := fun K _ => by
      exact_mod_cast Module.finrank_pos
    have h2 := Real.log_le_log (q _) h1
    rw [Real.log_mul (q F).ne' (q F').ne'] at h2
    linarith
  · letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    letI : Algebra F' ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    have h := log_discr_div_le F F' ↥(F ⊔ F') (GlobalTheory.T.map_different_le_different_sup_intermediateField F F')
    exact h.trans (add_le_add hb hb')

end GlobalTheory.FieldSize
