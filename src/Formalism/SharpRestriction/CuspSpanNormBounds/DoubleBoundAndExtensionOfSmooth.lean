import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def DDSmoothAt (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, u ∈ smoothVecs (k := k) (r := r) σ

def KZeroAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B → (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → B v = 0) →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, B w = 0

def ExtDDAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, Integrable (FI z c π σ u v) (μW.prod μN) ∧
    ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B →
      (∀ v' : H, IsKFinHpk (k := k) (r := r) σ v' →
        ∫ p, FI z c π σ u v' p ∂(μW.prod μN) = (innerSL ℂ (B v')).smulRight (B u)) →
      ∫ p, FI z c π σ u v p ∂(μW.prod μN) = (innerSL ℂ (B v)).smulRight (B u)


end Side

def DDSteps (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DDSmoothAt σ w0 ∧ (ExtDDAt L.z L.c L.π L.μW L.μN σ w0 ∧ KZeroAt L.z L.c L.π σ) ∧
        (ExtDDAt L.z' L.c L.π' L.μW' L.μN σ w0 ∧ KZeroAt L.z' L.c L.π' σ)




end Formalism.MainNotions.DoubleDerivativeSmoothness
