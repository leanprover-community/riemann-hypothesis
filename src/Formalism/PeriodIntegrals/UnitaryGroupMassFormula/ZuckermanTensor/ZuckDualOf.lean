import Mathlib
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.DSExist

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

structure Fam (n : ℕ) where
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)

attribute [instance] Fam.nH Fam.iH Fam.cH

def Ineq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam lam' : Fin n → ℝ), vNormSq ε (lowK ε lam) ≠ vNormSq ε (lowK ε lam') →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      IsDS ε lam' σ' → ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

def ToSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ + Pi.single s 1) → IsDS ε (μ + Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ + Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ + Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ + Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

def ToSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ F : Fam n, (∀ s, IsHCParam (μ - Pi.single s 1) → IsDS ε (μ - Pi.single s 1) (F.σs s)) →
    ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, F.Hs (sI i)),
      (∀ i, IsHCParam (μ - Pi.single (sI i) 1) ∧ IsKFin ε (F.σs (sI i)) (vI i) ∧ IsKFin ε (F.σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, F.σs (sI i) g (vI i)⟫_ℂ

def OfSumd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
    ∀ (s : Fin n), IsHCParam (μ - Pi.single s 1) →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsDS ε (μ - Pi.single s 1) σ' →
    ∀ v w : H', IsKFin ε σ' v → IsKFin ε σ' w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ' g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

def NormNe : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ), IsHCParam μ → ∀ s s' : Fin n, s ≠ s' →
    vNormSq ε (lowK ε (μ + Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ + Pi.single s' 1)) ∧
    vNormSq ε (lowK ε (μ - Pi.single s 1)) ≠ vNormSq ε (lowK ε (μ - Pi.single s' 1))




end PI.ZuckTensorWork
end
