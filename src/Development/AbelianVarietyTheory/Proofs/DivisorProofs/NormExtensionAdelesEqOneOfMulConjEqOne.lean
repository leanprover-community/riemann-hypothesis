module

import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.NormOne

theorem algebraMap_norm_eq_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (β : Module.Basis (Fin 2) R A) (h0 : β 0 = 1) (C : R) (hC : β 1 * β 1 = algebraMap R A C)
    (s : A →ₐ[R] A) (hs : s (β 1) = -β 1) (z : A) :
    algebraMap R A (Algebra.norm R z) = z * s z := by
  apply GlobalTheory.Published.algebraMap_norm_of_basis_one_sqrt <;> assumption

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have h1 := h.2.2.2 τ x
    rw [hc x] at h1
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]
    exact h1.symm
  exact (NumberField.InfinitePlace.isComplex_mk_iff.mp (h.2.1.isComplex _)) hr

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (bE : Module.Basis (Fin 2) F E) (c : F), bE 0 = 1 ∧ σ (bE 1) = -bE 1 ∧ bE 1 * bE 1 = algebraMap F E c := by
  obtain ⟨x, hx⟩ := exists_moved h
  set θ := x - σ x with hθ
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, invol h]; ring
  have hθ0 : θ ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0).symm
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add (f := _), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower, map_one, hσθ, map_zero] at h2
    have h3 : (2 * t) • θ = 0 := by
      have : (2 * t) • θ = (s • (1 : E) + t • θ) - (s • 1 + t • -θ) := by
        rw [smul_neg, mul_smul, two_smul]; abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
      · exact absurd h4 hθ0
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero, smul_eq_zero] at hst
    exact hst.resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let bE := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑bE = ![(1 : E), θ] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : bE 0 = 1 := by rw [hb]; rfl
  have hb1 : bE 1 = θ := by rw [hb]; rfl
  set p := bE.repr (θ * θ) 0
  set q := bE.repr (θ * θ) 1
  have hsq : θ * θ = p • (1 : E) + q • θ := by
    have h5 := bE.sum_repr (θ * θ)
    rw [Fin.sum_univ_two, hb0, hb1] at h5
    exact h5.symm
  have hsq' : θ * θ = p • (1 : E) - q • θ := by
    have h6 := congrArg σ hsq
    rw [map_mul, hσθ, map_add (f := _), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower, map_one, hσθ, neg_mul_neg, smul_neg] at h6
    rw [h6, sub_eq_add_neg]
  have hq : q = 0 := by
    have h7 : (2 * q) • θ = 0 := by
      have : (2 * q) • θ = (p • (1 : E) + q • θ) - (p • (1 : E) - q • θ) := by
        rw [mul_smul, two_smul]; abel
      rw [this, ← hsq, ← hsq', sub_self]
    rcases smul_eq_zero.mp h7 with h8 | h8
    · exact (mul_eq_zero.mp h8).resolve_left two_ne_zero
    · exact absurd h8 hθ0
  refine ⟨bE, p, hb0, by rw [hb1]; exact hσθ, ?_⟩
  rw [hb1, hsq, hq, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.NormOne

namespace GlobalTheory.NormOne

theorem norm_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ z : AE F E, z * cA σ z = 1 → Algebra.norm (AF F) z = 1 := by
  intro F E _ _ _ _ _ σ h z hz
  obtain ⟨bE, c, h0, h1, hc⟩ := exists_basis h
  let β := Algebra.TensorProduct.basis (AF F) bE
  have hβ : ∀ i, β i = (1 : AF F) ⊗ₜ[F] bE i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hβ0 : β 0 = 1 := by rw [hβ, h0]; rfl
  have hβC : β 1 * β 1 = algebraMap (AF F) (AE F E) (algebraMap F (AF F) c) := by
    rw [hβ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hc, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one (A := E) c, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one (A := AF F) c]
    rfl
  have hs : cA σ (β 1) = -β 1 := by
    rw [hβ, cA, Algebra.TensorProduct.map_tmul, h1, TensorProduct.tmul_neg]
    rfl
  have key := algebraMap_norm_eq_mul β hβ0 _ hβC (cA σ) hs z
  rw [hz] at key
  have e : ∀ r : AF F, β.repr (algebraMap (AF F) (AE F E) r) 0 = r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, ← hβ0, map_smul, Module.Basis.repr_self]
    simp
  rw [← e (Algebra.norm (AF F) z), key, ← map_one (algebraMap (AF F) (AE F E)), e]

end GlobalTheory.NormOne
