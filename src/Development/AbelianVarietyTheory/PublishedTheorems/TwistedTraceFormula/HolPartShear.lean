import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.Published.Metaplectic.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem shear_mem (C : Matrix ι ι ℝ) (hC : Cᵀ = C) : fromBlocks 1 0 C 1 ∈ symplecticGroup ι ℝ := by
  rw [SymplecticGroup.mem_iff]
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hC]

def chirp (C : Matrix ι ι ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => cexp (-π * I * ((x ⬝ᵥ C *ᵥ x : ℝ) : ℂ)) * f x


omit [Fintype ι] in
theorem holPart_shear (C : Matrix ι ι ℝ) (i : ι) : holPart (fromBlocks 1 0 C 1) i i = (2 + I * C i i) / 2 := by
  simp [holPart]; norm_num


def sgnRep (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousConstSMul ℂ E] :
    ℤˣ →* (E →L[ℂ] E) where
  toFun g := (((g : ℤ) : ℂ)) • (1 : E →L[ℂ] E)
  map_one' := by simp
  map_mul' g h := by ext; simp [smul_smul, mul_comm]

theorem empty_case (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀) := by
  have hs : Subsingleton (symplecticGroup ι ℝ) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hsq : ∀ g : ℤˣ, (((g : ℤ) : ℂ)) ^ 2 = 1 := by
    intro g; rcases Int.units_eq_one_or g with rfl | rfl <;> simp
  let φ₀ : 𝓢(ι → ℝ, ℂ) := (HasCompactSupport.of_compactSpace (fun _ : ι → ℝ => (1 : ℂ))).toSchwartzMap contDiff_const
  refine ⟨ℤˣ, inferInstance, inferInstance, inferInstance, 1, sgnRep _, sgnRep _, φ₀, fun a => ⟨1, Subsingleton.elim _ _⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_discrete _, ?_⟩
    have : Finite ((1 : ℤˣ →* symplecticGroup ι ℝ) ⁻¹' {x}) := inferInstance
    refine ⟨Equiv.toHomeomorphOfDiscrete
      { toFun := fun g => (⟨x, trivial⟩, ⟨g.1, Subsingleton.elim _ _⟩)
        invFun := fun y => ⟨y.2.1, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun y => Prod.ext (Subtype.ext (Subsingleton.elim _ _)) rfl }, fun _ => Subsingleton.elim _ _⟩
  · simp
  · intro g f
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep]
  · intro f; exact continuous_of_discreteTopology
  · intro g φ
    change ((g : ℤ) : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume φ = SchwartzMap.toLpCLM ℂ ℂ 2 volume (((g : ℤ) : ℂ) • φ)
    rw [map_smul]
  · change Continuous fun x : ℤˣ × 𝓢(ι → ℝ, ℂ) => (((x.1 : ℤ) : ℂ)) • x.2
    exact ((continuous_of_discreteTopology (f := fun g : ℤˣ => ((g : ℤ) : ℂ))).comp continuous_fst).smul continuous_snd
  · intro g w φ
    rw [Subsingleton.elim (act _ w) w]
    simp [sgnRep]
  · intro g _ hg φ
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact absurd rfl hg
    · simp [sgnRep]
  · intro x; simp [φ₀, dotProduct]
  · intro g
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep, integral_neg]
  · intro g _
    exact ⟨_, by simp [hsq g], rfl⟩

end GlobalTheory.Published.Metaplectic.Model

end
