import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKTypeDatum

noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsHeckeTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ J W) (q : ℕ) (T : ℕ → Module.End ℂ (indSpace J τ)) : Prop :=
  2 ≤ q ∧ FiniteDimensional ℂ (indSpace J τ) ∧
    (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ i, i + 1 < t → ∀ κ : KO k (Fin N), T i * ind J τ κ = ind J τ κ * T i) ∧
    (∀ i, i + 1 < t → (T i - (q : ℂ) • 1) * (T i + 1) = 0) ∧
    (∀ i j, j + 1 < t → i + 2 ≤ j → T i * T j = T j * T i) ∧
    (∀ i, i + 2 < t → T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1)) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ F, IsKMap (KO k (Fin N)) (ind J τ) (prodIrr y hd) F →
      (∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F) → F = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (F : indSpace J τ →ₗ[ℂ] _), F ≠ 0 ∧
      IsKMap (KO k (Fin N)) (ind J τ) (prodIrr (fun _ : Fin t => π₀) hN) F ∧
      ∀ i, i + 1 < t → F ∘ₗ T i = (q : ℂ) • F

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

section Generic

variable {G : Type} [Group G] {K : Subgroup G} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
  [Module ℂ V] {σ : Representation ℂ K U} {ρ : Representation ℂ G V} {e : Module.End ℂ U}

theorem range_stable (hc : ∀ κ : K, σ κ * e = e * σ κ) :
    ∀ κ : K, ∀ f ∈ LinearMap.range e, σ κ f ∈ LinearMap.range e := by
  rintro κ _ ⟨x, rfl⟩
  refine ⟨σ κ x, ?_⟩
  have := congrArg (fun L : Module.End ℂ U => L x) (hc κ)
  simpa [Module.End.mul_apply] using this.symm






end Generic

end GlobalTheory.KTypeDatum

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end GlobalTheory.KTypeDatum
