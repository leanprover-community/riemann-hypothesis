module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_isQuad : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E),
      IsQuad δ θ σ := by
  intro F _ _ δ hδ
  have hroot : ∀ b : F, b ^ 2 ≠ δ := fun b hb => hδ ⟨b, by rw [← hb, sq]⟩
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C δ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
  have hmon : (Polynomial.X ^ 2 - Polynomial.C δ).Monic := Polynomial.monic_X_pow_sub_C δ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C δ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C _
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C δ)) := ⟨hirr⟩
  set p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C δ with hp
  have hsq : AdjoinRoot.root p ^ 2 = AdjoinRoot.of p δ := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hneg : Polynomial.eval₂ (↑(Algebra.ofId F (AdjoinRoot p)) : F →+* AdjoinRoot p)
      (-AdjoinRoot.root p) (Polynomial.X ^ 2 - Polynomial.C δ) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, neg_sq, hsq, sub_eq_zero]
    rfl
  let τ : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot p)) (-AdjoinRoot.root p) hneg
  have hτ : τ (AdjoinRoot.root p) = -AdjoinRoot.root p := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hττ : τ.comp τ = AlgHom.id F (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hτ, map_neg, neg_neg]
  have hp0 : p ≠ 0 := hmon.ne_zero
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p)).injective
  have : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans F (AdjoinRoot p)
  refine ⟨AdjoinRoot p, inferInstance, { }, inferInstance, AdjoinRoot.root p,
    AlgEquiv.ofAlgHom τ τ hττ hττ, ⟨hδ, ?_, hτ, ?_⟩⟩
  · rw [AdjoinRoot.algebraMap_eq]; exact hsq
  · intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have hp1 : p ≠ 1 := fun h => by
      rw [h, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
    have hlt := Polynomial.natDegree_modByMonic_lt g hmon hp1
    rw [hdeg] at hlt
    have hr := Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hlt)
    refine ⟨(g %ₘ p).coeff 0, (g %ₘ p).coeff 1, ?_⟩
    have hmk : AdjoinRoot.mk p g = AdjoinRoot.mk p (g %ₘ p) := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div g p]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    conv_lhs => rw [hr]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq, add_comm]

end GlobalTheory.QNorm
