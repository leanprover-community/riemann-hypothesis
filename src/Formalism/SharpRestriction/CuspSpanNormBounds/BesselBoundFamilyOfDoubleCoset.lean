import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₄

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' UH (Hpk k r))


def DoubleCosetSpanBesselBound {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∃ l : H → Wp, IsBesselMapSm z (psi k r z c) σ π l ∧
    (∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0,
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l u)) ∧
    ∀ u ∈ DDsp σ w0, u ≠ 0 → ∀ v ∈ DDsp σ w0,
      ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g u)) =
        ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ u)

def DoubleCosetBesselBound (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DoubleCosetSpanBesselBound L.z L.c L.π L.μW L.μN μG νq σ w0 ∧ DoubleCosetSpanBesselBound L.z' L.c L.π' L.μW' L.μN μG νq' σ w0

def ExtSm (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      (DoubleCosetSpanBesselBound L.z L.c L.π L.μW L.μN μG νq σ w0 → atFormAtPoint L.z L.c L.π L.μW L.μN μG νq σ) ∧
      (DoubleCosetSpanBesselBound L.z' L.c L.π' L.μW' L.μN μG νq' σ w0 → atFormAtPoint L.z' L.c L.π' L.μW' L.μN μG νq' σ)



section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyDoubleCosetBesselBound (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), DoubleCosetBesselBound (Fm.D x i) Ch Cg Cq

def ExtSmF (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), ExtSm (Fm.D x i) Ch Cg Cq


end Family

end Formalism.MainNotions.BridgeLemma₄
