module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm

@[expose] public section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

section Ring

variable {R : Type} [CommRing R] {n n₁ k : ℕ}

end Ring

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.LeviSplit
