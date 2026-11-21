import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import BuildAid.ForwardExisting

section
namespace GlobalTheory.PolynomialCoeffEq

open Module

theorem coeff_eq {R : Type} [AddCommGroup R] [Module ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) {n : ℕ} (v : Basis (Fin n) ℝ R)
    (hv : ∀ i j, i ≠ j → g (v i) (v j) = 0) (x : R) (k : Fin n) :
    g x (v k) = v.repr x k * g (v k) (v k) := by
  conv_lhs => rw [← v.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · intro i _ hik
    rw [hv i k hik, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem main : ∀ {R : Type} [inst : AddCommGroup R] [inst_1 : Module ℝ R] [FiniteDimensional ℝ R] (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ (u v : R), ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) v = ((g : R → R →ₗ[ℝ] ℝ) v : R → ℝ) u) → (∀ (u : R), u ≠ (0 : R) → (0 : ℝ) < ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) u) → ∃ (n : ℕ) (e : Fin n → R), ∀ (x : R), ∑ k : Fin n, ((g : R → R →ₗ[ℝ] ℝ) x : R → ℝ) (e k) • e k = x := by
  intro R _ _ _ g hsym hpos
  have h2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g) ⟨hsym⟩
  have hv' : ∀ i j, i ≠ j → g (v i) (v j) = 0 := LinearMap.BilinForm.iIsOrtho_def.mp hv
  have hpos' : ∀ k, 0 < g (v k) (v k) := fun k => hpos _ (v.ne_zero k)
  refine ⟨_, fun k => (Real.sqrt (g (v k) (v k)))⁻¹ • v k, fun x => ?_⟩
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, coeff_eq g v hv' x k, smul_smul]
  congr 1
  have hs := Real.mul_self_sqrt (hpos' k).le
  have he : (Real.sqrt (g (v k) (v k)))⁻¹ * (v.repr x k * g (v k) (v k)) *
      (Real.sqrt (g (v k) (v k)))⁻¹ =
      v.repr x k * (g (v k) (v k) * (Real.sqrt (g (v k) (v k)) * Real.sqrt (g (v k) (v k)))⁻¹) := by
    ring
  rw [he, hs, mul_inv_cancel₀ (hpos' k).ne', mul_one]

end GlobalTheory.PolynomialCoeffEq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeylNumber

theorem exists_parseval_family {R : Type} [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u) :
    ∃ (n : ℕ) (e : Fin n → R), ∀ x, ∑ k, g x (e k) • e k = x := by
  first
  | exact @_root_.GlobalTheory.PolynomialCoeffEq.main
  | exact _root_.GlobalTheory.PolynomialCoeffEq.main
  | (apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialCoeffEq.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialCoeffEq.main ..)

theorem weyl_number : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  intro M R _ _ _ _ _ Dop om κ j hadd hsmul hκ hcomm hanti hjj hom hpos
  have h1 : ∀ u v, om (j u) v = -om u (j v) := fun u v => by
    rw [← hom (j u) v, hjj]; simp
  have hc : ∀ u v, Dop u * Dop v = Dop v * Dop u + (κ * (om u v : ℝ)) • (1 : Module.End ℂ M) :=
    fun u v => by rw [← hcomm]; abel
  have hneg : ∀ u, Dop (-u) = -Dop u := fun u => by
    have := hsmul (-1) u
    simpa using this
  have hac : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) =
      (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) +
        (2 * κ * ((om u v : ℝ) - Complex.I * (om u (j v) : ℝ))) • (1 : Module.End ℂ M) := by
    intro u v
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  have haa : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v + Complex.I • Dop (j v)) =
      (Dop v + Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) := by
    intro u v
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  refine ⟨fun u v => ⟨_, by rw [hac u v, add_sub_cancel_left]⟩, ?_⟩
  obtain ⟨n, e, he⟩ := exists_parseval_family (om.compl₂ j)
    (fun u v => by
      simp only [LinearMap.compl₂_apply]
      rw [hanti (j u) v, h1, neg_neg])
    (fun u hu => by simpa using hpos u hu)
  simp only [LinearMap.compl₂_apply] at he
  let A : R →+ Module.End ℂ M := AddMonoidHom.mk' (fun u => Dop u + Complex.I • Dop (j u))
    (fun u v => by simp only [map_add, hadd, smul_add]; abel)
  have hA : ∀ u, A u = Dop u + Complex.I • Dop (j u) := fun _ => rfl
  have hAs : ∀ (c : ℝ) u, A (c • u) = (c : ℂ) • A u := fun c u => by
    simp only [hA, map_smul, hsmul]; module
  have hAj : ∀ u, A (j u) = (-Complex.I) • A u := fun u => by
    simp only [hA, hjj, hneg, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  have hsum : ∀ x, ∑ k, ((om x (j (e k)) : ℝ) : ℂ) • A (e k) = A x := fun x => by
    conv_rhs => rw [← he x, map_sum]
    simp only [hAs]
  refine ⟨n, e, -4 * Complex.I * κ, by simp [hκ], fun u => ?_⟩
  have key : ∀ k, A u * ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) =
      ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) * A u +
        ((2 * κ) • (((om (j u) (j (e k)) : ℝ) : ℂ) • A (e k))
          - (2 * κ * Complex.I) • (((om u (j (e k)) : ℝ) : ℂ) • A (e k))) := fun k => by
    rw [← mul_assoc, hA u, hac, add_mul, mul_assoc, mul_assoc, hA (e k), haa u, hom,
      smul_mul_assoc, one_mul]
    module
  simp only [← hA]
  rw [Finset.mul_sum, add_mul, Finset.sum_mul, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    hsum, hsum, hAj, smul_mul_assoc, one_mul]
  module

end GlobalTheory.WeylNumber
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalCommutationRelations_weylNumber : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  atlas_forward_decl GlobalTheory.WeylNumber.weyl_number
end
