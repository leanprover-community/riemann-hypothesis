import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_lie_algebra_mem_unitary (k r : ℕ) (X : CayleySignature.Mat k r) (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨-, hH2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  set Hm := Formalism.QuantumDeterminants.Hpk k r with hHm
  set Y : CayleySignature.Mat k r := (t : ℂ) • X with hYdef
  have hY : Yᴴ * Hm + Hm * Y = 0 := by
    have h1 : Yᴴ = (t : ℂ) • Xᴴ := by simp [hYdef, Matrix.conjTranspose_smul]
    have h2 : Xᴴ * Hm + Hm * X = 0 := hX
    rw [h1, hYdef, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h2, smul_zero]
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hH2
  have hYh : Yᴴ = Hm * (-Y) * Hm⁻¹ := by
    rw [hinv]
    have h1 : Yᴴ * Hm = -(Hm * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * (Hm * Hm) := by rw [hH2, Matrix.mul_one]
      _ = (Yᴴ * Hm) * Hm := by rw [Matrix.mul_assoc]
      _ = Hm * (-Y) * Hm := by rw [h1, Matrix.mul_neg]
  have hu : IsUnit Hm := ⟨⟨Hm, Hm, hH2, hH2⟩, rfl⟩
  have hdet : IsUnit (NormedSpace.exp Y).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp Y)
  show (NormedSpace.exp Y)ᴴ * Hm * NormedSpace.exp Y = Hm
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg]
  calc Hm * (NormedSpace.exp Y)⁻¹ * Hm * Hm * NormedSpace.exp Y
      = Hm * (NormedSpace.exp Y)⁻¹ * (Hm * Hm) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = Hm * ((NormedSpace.exp Y)⁻¹ * NormedSpace.exp Y) := by rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hm := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

section Move

variable {k r : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']







end Move

def DiscreteSeriesUniqueUpToUnitaryEquiv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')),
    IsDSHpk k r ε lam σ' →
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

def HighestWeightUnique : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsHCParam u →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (Vp' : Type) [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] [FiniteDimensional ℂ Vp']
    (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')), IsHCTypeW k r z u π' →
  ∃ A : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)

def PositionChange : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) →
  ∀ (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' → (∀ a, c' a ≠ 0) → (∃ g', IsFrameW k r z' g') →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (B : H → Vp) (N : ℕ), IsBesselMapSm z (psiGen k r z c) σ π B → HasOrdLe k r N σ B →
    (∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
  ∃ (π' : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z' u π' ∧
    ∃ B' : H → Vp, IsBesselMapSm z' (psiGen k r z' c') σ π' B' ∧ HasOrdLe k r N σ B' ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B' x ≠ 0



end Formalism.MainNotions.LeviCoordinates

end
