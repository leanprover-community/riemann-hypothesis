module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFactsStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_real_eq_pos_add_tReal (F : Type) [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    Nat.card (F →+* ℝ) = Nat.card {φ : F →+* ℝ // 0 < φ δ} + tReal F δ := by
  classical
  have h := Set.ncard_add_ncard_compl {φ : F →+* ℝ | 0 < φ δ}
  have hc : {φ : F →+* ℝ | 0 < φ δ}ᶜ = {φ : F →+* ℝ | φ δ < 0} := by
    ext φ
    have : φ δ ≠ 0 := by simpa using hδ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun a => lt_of_le_of_ne a this, le_of_lt⟩
  rw [hc] at h
  rw [← h]
  rfl

theorem two_mul_card_pos_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (h : IsQuad δ θ σ) :
    2 * Nat.card {φ : F →+* ℝ // 0 < φ δ} ≤ Nat.card (E →+* ℝ) := by
  classical
  have hext := (GlobalTheory.T.isQuadraticSqrtExtension_isGalois_and_embedding F E δ θ σ h).2.2 ℝ
  have key : ∀ p : Bool × {φ : F →+* ℝ // 0 < φ δ}, ∃ ψ : E →+* ℝ,
      (∀ a : F, ψ (algebraMap F E a) = p.2.1 a) ∧ (0 < ψ θ ↔ p.1 = true) := by
    rintro ⟨b, φ, hφ⟩
    have hs : 0 < Real.sqrt (φ δ) := Real.sqrt_pos.mpr hφ
    cases b
    · obtain ⟨ψ, h1, h2⟩ := hext φ (-Real.sqrt (φ δ)) (by rw [neg_sq, Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simp only [Bool.false_eq_true, iff_false, not_lt]
      linarith
    · obtain ⟨ψ, h1, h2⟩ := hext φ (Real.sqrt (φ δ)) (by rw [Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simpa using hφ
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p q hpq
    refine Prod.ext ?_ (Subtype.ext (RingHom.ext fun a => ?_))
    · have := (hf2 p).symm.trans (hpq ▸ hf2 q)
      exact Bool.eq_iff_iff.mpr this
    · rw [← hf1 p a, ← hf1 q a, hpq]
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this

theorem two_mul_card_infinitePlace_le :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F)
      (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ →
      2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  intro F E _ _ _ _ _ δ θ σ h
  have hδ : δ ≠ 0 := fun h0 => h.nonsq (h0 ▸ IsSquare.zero)
  have h1 := card_real_eq_pos_add_tReal F δ hδ
  have h2 := two_mul_card_pos_le F E δ θ σ h
  rw [GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces'] at h1 h2
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h4 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : Module.finrank F E = 2 := (GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ h).2.2.2.2.2.2
  have h8 := Module.finrank_mul_finrank ℚ F E
  rw [h7] at h8
  omega

end GlobalTheory.QNorm
