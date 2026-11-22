module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXEvUniq

open scoped Classical

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
  {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem schr_add [Invertible (2 : R)] (ψ : AddChar R ℂ) (a b : (α → R) × (α → R)) (h : a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (φ : (α → R) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x, ← h]
  congr 2
  have h2 : (⅟(2 : R)) * 2 = 1 := invOf_mul_self _
  linear_combination (a.1 ⬝ᵥ b.2) * h2

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}

end GlobalTheory.MixXEvUniq

end
