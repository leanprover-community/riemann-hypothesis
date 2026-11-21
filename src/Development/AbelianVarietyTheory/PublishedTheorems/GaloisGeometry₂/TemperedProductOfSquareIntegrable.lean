import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def TemperedProductOfSquareIntegrable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ), 1 ≤ N →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
      (IsTemperedCoeff π ↔ ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty (π.Equiv (prodIrr δ hd)))

namespace TemperedProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem coeffLp_of_equiv {N : ℕ} {p : ℝ} {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv σ) (h : CoeffLp p π) : CoeffLp p σ := by
  intro _ _ μ hμ w l hl
  have hφ : ∀ g v, φ.toLinearEquiv (π g v) = σ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  have hs : {g : GL (Fin N) k | (l ∘ₗ φ.toLinearEquiv.toLinearMap) ∘ₗ π g = l ∘ₗ φ.toLinearEquiv.toLinearMap} =
      {g : GL (Fin N) k | l ∘ₗ σ g = l} := by
    ext g
    refine ⟨fun H => LinearMap.ext fun x => ?_, fun H => LinearMap.ext fun x => ?_⟩
    · have h1 : l (φ.toLinearEquiv (π g (φ.toLinearEquiv.symm x))) = l (φ.toLinearEquiv (φ.toLinearEquiv.symm x)) :=
        LinearMap.congr_fun H (φ.toLinearEquiv.symm x)
      rwa [hφ, LinearEquiv.apply_symm_apply] at h1
    · show l (φ.toLinearEquiv (π g x)) = l (φ.toLinearEquiv x)
      rw [hφ]
      exact LinearMap.congr_fun H _
  obtain ⟨F, hF, hF'⟩ := h μ hμ (φ.toLinearEquiv.symm w) (l ∘ₗ φ.toLinearEquiv.toLinearMap) (hs ▸ hl)
  refine ⟨F, fun g => ?_, hF'⟩
  rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, hφ, LinearEquiv.apply_symm_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  refine QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun g => ?_)
  generalize (_⁻¹ * _ : GL (Fin 1) k) = c
  ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]




end TemperedProduct

end GlobalTheory.Published
