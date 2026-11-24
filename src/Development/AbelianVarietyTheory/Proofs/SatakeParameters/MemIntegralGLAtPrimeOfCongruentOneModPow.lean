module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    IntAt P a ↔ a ∈ (P.valuation E).integer := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, Valuation.mem_integer_iff]

theorem mem_stdAt {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := by
  letI : StarRing E := starRingOfComm
  exact mem_localization_standardLattice P x

theorem intAt_mulVec (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a b, IntAt P (A a b)) (w : Fin n → E) (hw : ∀ i, IntAt P (w i)) (i : Fin n) :
    IntAt P ((A *ᵥ w) i) := by
  rw [intAt_iff_mem]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ ((intAt_iff_mem P _).1 (hA i j)) ((intAt_iff_mem P _).1 (hw j))

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_of_cong (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d : ℕ) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b))) (a b : Fin n) :
    IntAt P (M a b) := by
  have hq : ((qOf P : E) ^ d) ≠ 0 := pow_ne_zero _ (qOf_ne_zero P)
  have e : M a b = (1 : Matrix (Fin n) (Fin n) E) a b +
      (qOf P : E) ^ d * (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b)) := by
    field_simp
    ring
  rw [e, intAt_iff_mem]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ ?_ ((intAt_iff_mem P _).1 (h a b)))
  · rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · exact Subring.pow_mem _ (natCast_mem _ _) _

theorem map_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n →ₗ[E] Sp E n)
    (hf : ∀ a b, IntAt P (LinearMap.toMatrix' f a b)) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    f x ∈ stdAt E n P := by
  rw [mem_stdAt] at hx ⊢
  intro i
  rw [← LinearMap.toMatrix'_mulVec]
  exact intAt_mulVec P _ hf x hx i

theorem glint_of_cong {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P := by
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => map_stdAt P g.toLinearMap (intAt_of_cong P d _ hg) hx⟩, ?_⟩
  · have := map_stdAt P g.symm.toLinearMap (intAt_of_cong P d _ hg') hx
    simpa using this
  · intro w hw
    set A : Matrix (Fin n) (Fin n) E :=
      ((qOf P : E) ^ d)⁻¹ • (LinearMap.toMatrix' g.toLinearMap - (1 : Matrix (Fin n) (Fin n) E)) with hA
    have hAi : ∀ a b, IntAt P (A a b) := by
      intro a b
      simpa [hA, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hg a b
    have e : ((qOf P : E) ^ d)⁻¹ • (g w - w) = A *ᵥ w := by
      have h1 : (g w : Sp E n) = LinearMap.toMatrix' g.toLinearMap *ᵥ w := by
        rw [LinearMap.toMatrix'_mulVec]; rfl
      rw [hA, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← h1]
    rw [e, mem_stdAt]
    rw [mem_stdAt] at hw
    exact intAt_mulVec P _ hAi w hw

end GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow
