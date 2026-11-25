module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitIdele
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

alias conj_conj := _root_.GlobalTheory.AdelicU.cm_conj_conj

theorem exists_anti (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_contra hc
  push Not at hc
  have hfix : ∀ x, σ x = x := fun x => by
    by_contra hne
    exact hc (x - σ x) (sub_ne_zero.mpr (Ne.symm hne)) (by rw [map_sub, conj_conj h]; ring)
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hfix] at this
    exact this.symm
  have hc' := h.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex] at hc'
  exact hc' (InfinitePlace.isReal_mk_iff.mpr hreal)

theorem exists_isQuad (h : IsCMExt F E σ) : ∃ ξ : AE F E, IsQuad (cA σ) ξ := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_anti h
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    simp only [Algebra.smul_def, mul_one] at hsu
    have h2 := congrArg σ hsu
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hξ, map_zero] at h2
    have h3 : algebraMap F E u * ξ = 0 := by linear_combination (hsu - h2) / 2
    have hu : u = 0 := (map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)
    subst hu
    refine ⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = ![(1 : E), ξ] i := fun i => by simp [b]
  refine ⟨(1 : AF F) ⊗ₜ[F] ξ, ⟨?_, ?_, ⟨Algebra.TensorProduct.basis (AF F) b, ?_, ?_⟩⟩⟩
  · refine ⟨⟨(1 : AF F) ⊗ₜ[F] ξ, (1 : AF F) ⊗ₜ[F] ξ⁻¹, ?_, ?_⟩, rfl⟩ <;>
      simp [Algebra.TensorProduct.tmul_mul_tmul, hξ0, ← Algebra.TensorProduct.one_def]
  · simp [cA, Algebra.TensorProduct.map_tmul, hξ, TensorProduct.tmul_neg]
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl

end GlobalTheory.SplitIdele

end
