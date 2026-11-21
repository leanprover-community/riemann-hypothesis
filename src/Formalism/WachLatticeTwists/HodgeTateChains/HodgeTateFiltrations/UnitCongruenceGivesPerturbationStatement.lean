import Formalism.WachLatticeTwists.HodgeTateChains.UnitCongruenceGivesPerturbation
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MemSmulTopOf

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix


theorem unitCongruenceGivesPerturbation_statement : UnitCongruenceGivesPerturbation := by
  intro ℓ _ R _ _ Xm _ _ _ _ ϖ z z' r V g0 hzz hc hz hinj hsur hV
  choose B hB using hV
  let g : (Fin r → Xm) →ₗ[R] (Fin r → Xm) := LinearMap.pi (fun k => g0 ∘ₗ LinearMap.proj k)
  let Bop : (Fin r → Xm) →ₗ[R] (Fin r → Xm) :=
    LinearMap.pi (fun k => ∑ t, B k t • LinearMap.proj t)
  have hg : ∀ v k, g v k = g0 (v k) := fun v k => rfl
  have hBop : ∀ v k, Bop v k = ∑ t, B k t • v t := by
    intro v k
    simp [Bop, LinearMap.pi_apply, LinearMap.sum_apply]
  have hkey : ∀ v : Fin r → Xm, (fun k => ∑ t, V k t • g0 (v t)) = g v + (z * ϖ) • Bop (g v) := by
    intro v
    ext k
    rw [Pi.add_apply, Pi.smul_apply, hBop, hg, Finset.smul_sum]
    have e1 : g0 (v k) = ∑ t, (1 : Matrix (Fin r) (Fin r) R) k t • g0 (v t) := by
      simp [Matrix.one_apply]
    rw [e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hg, smul_smul, ← hB k t, ← add_smul, Matrix.sub_apply]
    congr 1
    ring
  obtain ⟨h1, h2⟩ := unit_congruence_gives_perturbation ℓ R (Fin r → Xm) ϖ z z' hzz hc
    (fun v hv => funext fun k => hz _ (congrFun hv k)) g Bop
    (fun v hv => funext fun k => hinj _ (congrFun hv k))
    (fun v => by
      choose y hy using fun k => hsur (v k)
      exact ⟨y, funext fun k => hy k⟩)
  refine ⟨fun v hv => h1 v (by rw [← hkey]; exact hv), fun v => ?_⟩
  obtain ⟨y, hy⟩ := h2 v
  exact ⟨y, by rw [hkey]; exact hy⟩

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
