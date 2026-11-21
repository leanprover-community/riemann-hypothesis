import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystemsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresentsStatement

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]

theorem isCompl_dualAnnihilator {K N : Submodule R C} (h : IsCompl K N) :
    IsCompl K.dualAnnihilator N.dualAnnihilator := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro f hf
    rw [mem_inf, mem_dualAnnihilator, mem_dualAnnihilator] at hf
    rw [mem_bot]
    ext c
    rw [← projection_add_projection_eq_self h c, map_add, hf.1 _ (projection_apply_mem h c),
      hf.2 _ (projection_apply_mem h.symm c)]
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add, add_comm, projection_add_projection_eq_self h c]
    rw [e]
    refine add_mem_sup ?_ ?_
    · rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk]
    · rw [mem_dualAnnihilator]
      intro n hn
      simp [projection_apply_of_mem_right h hn]

theorem dualAnnihilator_dualCoannihilator_eq [Projective R C] {K N : Submodule R C}
    (h : IsCompl K N) : K.dualAnnihilator.dualCoannihilator = K := by
  refine le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)
  rw [mem_dualCoannihilator] at hc
  have hn : N.projection K h.symm c = 0 := by
    rw [← forall_dual_apply_eq_zero_iff R]
    intro φ
    have := hc (φ ∘ₗ N.projection K h.symm) (by
      rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk])
    simpa using this
  rw [← projection_add_projection_eq_self h c, hn, add_zero]
  exact projection_apply_mem h c

theorem mem_smul_top_of_forall_dual [Projective R C] (I : Ideal R) (c : C)
    (h : ∀ x : Dual R C, x c ∈ I) : c ∈ I • (⊤ : Submodule R C) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  rw [← hs c, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem exists_dual_lift [Projective R C] (hπ : Function.Surjective π) (ρ : C →ₛₗ[π] C₀)
    (y : Dual R₀ C₀) : ∃ x : Dual R C, ∀ c, π (x c) = y (ρ c) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  refine ⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩
  conv_rhs => rw [← hs c]
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]

theorem exists_dual_descent {ρ : C →ₛₗ[π] C₀} (hπ : Function.Surjective π)
    (hρ : Function.Surjective ρ) (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (x : Dual R C) : ∃ y : Dual R₀ C₀, ∀ c, y (ρ c) = π (x c) := by
  have hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b) := by
    intro a b hab
    have h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C) := (hker _).mp (by rw [map_sub, hab, sub_self])
    have h2 := hI h1
    rw [Submodule.mem_comap, map_sub] at h2
    rw [← sub_eq_zero, ← map_sub]
    exact (RingHom.mem_ker).mp h2
  let g := Function.surjInv hρ
  have hg : ∀ v, ρ (g v) = v := Function.surjInv_eq hρ
  refine ⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩
  · intro a b
    rw [show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]
    exact hx _ _ (by rw [map_add, hg, hg, hg])
  · intro r v
    obtain ⟨r', rfl⟩ := hπ r
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← map_mul, ← smul_eq_mul, ← map_smul]
    exact hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])

end GlobalTheory.DualSummand

namespace GlobalTheory.DualSummand

open Module Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]
variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem eq_zero_of_forall_dual_reduction [Projective R C] {ρ : C →ₛₗ[π] C₀}
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (v : C₀) (hv : ∀ φ : Dual R₀ C₀, φ v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hρ v
  rw [hker]
  refine mem_smul_top_of_forall_dual _ c fun x => ?_
  obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker x
  rw [RingHom.mem_ker, ← hy]
  exact hv y

theorem exists_eq_dualAnnihilator [Projective R C] [Module.Finite R C]
    {G H : Submodule R (Dual R C)} (hGH : IsCompl G H) :
    ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  have hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ := by
    intro ψ
    obtain ⟨k, hk⟩ := (Module.bijective_dual_eval R C).2 ψ
    exact ⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩
  have hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ :=
    projection_add_projection_eq_self hGH
  have hKL : IsCompl G.dualCoannihilator H.dualCoannihilator := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro c hc
      rw [mem_inf, mem_dualCoannihilator, mem_dualCoannihilator] at hc
      rw [mem_bot, ← forall_dual_apply_eq_zero_iff R]
      intro φ
      rw [← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ),
        hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      obtain ⟨k, hk⟩ := hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)
      obtain ⟨l, hl⟩ := hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)
      refine Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩
      · rw [mem_dualCoannihilator]
        intro g hg
        rw [hk g]
        simp [projection_apply_of_mem_right hGH.symm hg]
      · rw [mem_dualCoannihilator]
        intro h hh
        rw [hl h]
        simp [projection_apply_of_mem_right hGH hh]
      · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]
        intro φ
        rw [map_sub, map_add, hk φ, hl φ]
        simp only [LinearMap.comp_apply, Dual.eval_apply]
        rw [← LinearMap.add_apply, add_comm, hsplit φ, sub_self]
  refine ⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_dualAnnihilator]
    intro k hk
    exact (mem_dualCoannihilator _).mp hk g hg
  · intro φ hφ
    rw [mem_dualAnnihilator] at hφ
    have h0 : H.projection G hGH.symm φ = 0 := by
      ext c
      obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)
      have e : H.projection G hGH.symm φ = φ - G.projection H hGH φ := by
        rw [eq_sub_iff_add_eq, add_comm, hsplit φ]
      rw [map_add, (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e,
        LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]
      simp
    rw [← hsplit φ, h0, add_zero]
    exact projection_apply_mem hGH φ

end GlobalTheory.DualSummand

namespace GlobalTheory.LiftSys

open Module Submodule GlobalTheory.DualSummand

theorem summand_dual_reduction :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  intro R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩
  refine ⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩,
    dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩
  have hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c :=
    projection_add_projection_eq_self hKN
  have hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0 := fun k hk =>
    projection_apply_of_mem_right hKN.symm hk
  constructor
  · intro hL y
    constructor
    · intro hy
      rw [mem_dualAnnihilator] at hy
      obtain ⟨x₀, hx₀⟩ := exists_dual_lift hπ ρ y
      refine ⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩
      · rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk]
      · rw [LinearMap.comp_apply, hx₀]
        conv_lhs => rw [← hsplit c]
        rw [map_add, map_add,
          hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]
    · rintro ⟨x, hx, hxy⟩
      rw [mem_dualAnnihilator] at hx ⊢
      intro f hf
      obtain ⟨c, rfl⟩ := hρ f
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp ((hL c).mpr hf)
      rw [map_add, (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]
  · intro hR c
    constructor
    · intro hc
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp hc
      rw [map_add, (hker m).mpr hm, add_zero]
      have hv : N₀.projection F₀ hF.symm (ρ k) = 0 := by
        refine eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_
        obtain ⟨x, hx, hxy⟩ := (hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by
          rw [mem_dualAnnihilator]
          intro f hf
          simp [projection_apply_of_mem_right hF.symm hf])
        have := hxy k
        rw [LinearMap.comp_apply] at this
        rw [this, (mem_dualAnnihilator _).mp hx k hk, map_zero]
      rw [← projection_add_projection_eq_self hF (ρ k), hv, add_zero]
      exact projection_apply_mem hF _
    · intro hc
      rw [← hsplit c]
      refine add_mem_sup (projection_apply_mem hKN c) ?_
      refine mem_smul_top_of_forall_dual _ _ fun x₀ => ?_
      obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)
      have hyF : y ∈ F₀.dualAnnihilator := (hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by
        rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk], hy⟩
      rw [RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]
      exact (mem_dualAnnihilator _).mp hyF _ hc

end GlobalTheory.LiftSys
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summand_dualAnnihilator_reduction_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  atlas_forward_decl GlobalTheory.LiftSys.summand_dual_reduction
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

open TensorProduct in

theorem oneTmul_surjective_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (M : Type*) [AddCommGroup M] [Module R M] :
    letI := π.toAlgebra
    Function.Surjective (TensorProduct.mk R R₀ M 1) ∧
      ∀ m : M, (1 : R₀) ⊗ₜ[R] m = 0 ↔ m ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ := Ideal.quotientKerAlgEquivOfSurjective (f := (Algebra.ofId R R₀)) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π • (⊤ : Submodule R M)) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)) ≪≫ₗ quotTensorEquivQuotSMul M (RingHom.ker π)
  have hE : ∀ m : M, E (1 ⊗ₜ m) = Submodule.Quotient.mk m := fun m ↦ by
    simp [E, map_one]
  refine ⟨fun t ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (E t)
    exact ⟨m, E.injective (by rw [← hm]; exact hE m)⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← hE, LinearEquiv.map_eq_zero_iff]

theorem mem_smul_top_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (L : M ≃ₗ[R] N) (x : M) :
    L x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have e : (I • ⊤ : Submodule R N) = (I • ⊤ : Submodule R M).map (L : M →ₗ[R] N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 L.surjective]
  rw [e, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem rhoBC_of_abelianLift : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    RhoBC hI hk A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  letI := π.toAlgebra
  have := hA.smooth
  have := hA.proper
  haveI : Smooth A₀.hom := MorphismProperty.of_isPullback (P := @Smooth) h'.1 hA.smooth
  haveI : IsProper A₀.hom := MorphismProperty.of_isPullback (P := @IsProper) h'.1 hA.proper
  have w : i' ≫ A'.hom = A₀.hom ≫ spMap π := h'.1.w
  have hm : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact w)
  have hn : IsMor (dp0 R) A'.hom (dp0 R₀) A₀.hom π i' := IsMor.of_dividedPowersZeroIdeal _ w
  have bm : Function.Bijective hm.pull1 :=
    (H1.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
      inferInstance inferInstance inferInstance h'.1 hm).1
  have comp : ∀ c, rho hI hk A₀.hom (hm.pull1 c) = hn.pull1 c := fun c ↦
    IsMor.pullback1_comp hm (redMor hI hk A₀.hom) hn (fun _ ↦ rfl) (Category.id_comp _) c
  have b' := H1.bijective_cechDeRhamComparison_degreeOne A'.hom inferInstance inferInstance inferInstance
  have b₀ := H1.bijective_cechDeRhamComparison_degreeOne A₀.hom inferInstance inferInstance inferInstance
  obtain ⟨⟨e, he⟩, -, -⟩ := (H2 R A' g hA hg).2.2.2.2.2 R₀ A₀.left A₀.hom i' h'.1
  have key : ∀ c, cmp1 A₀.hom (hn.pull1 c) = e (1 ⊗ₜ cmp1 A'.hom c) := fun c ↦
    (pairRes_injective i' A₀.hom).2.2 ((comparison_pullback hn c).symm.trans (he _))
  obtain ⟨hsurj, hker⟩ := oneTmul_surjective_ker I π hπ hk (HH1 A'.hom)
  let L := LinearEquiv.ofBijective hm.pull1 bm
  let C := LinearEquiv.ofBijective (cmp1 A'.hom) b'
  refine ⟨fun y ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨t, ht⟩ := e.surjective (cmp1 A₀.hom y)
    obtain ⟨m, rfl⟩ := hsurj t
    obtain ⟨c', rfl⟩ := b'.2 m
    exact ⟨hm.pull1 c', by rw [comp]; exact b₀.1 ((key c').trans ht)⟩
  · obtain ⟨c', rfl⟩ := bm.2 c
    rw [comp, show hm.pull1 c' = L c' from rfl, mem_smul_top_of_equiv I L c', ← mem_smul_top_of_equiv I C c',
      ← hker]
    change _ ↔ (1 : R₀) ⊗ₜ cmp1 A'.hom c' = 0
    rw [← LinearEquiv.map_eq_zero_iff e, ← key, ← map_zero (cmp1 A₀.hom)]
    exact ⟨fun h ↦ by rw [h], fun h ↦ b₀.1 h⟩

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → RhoBC hI hk A₀.hom := by
  atlas_forward_decl GlobalTheory.LiftSys.rhoBC_of_abelianLift
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

section Lin

variable {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem smul_top_le_comap (f : M →ₗ[S] N) (J : Ideal S) :
    J • (⊤ : Submodule S M) ≤ (J • (⊤ : Submodule S N)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hr trivial

theorem mem_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (x : M) :
    e x ∈ J • (⊤ : Submodule S N) ↔ x ∈ J • (⊤ : Submodule S M) :=
  ⟨fun h ↦ by simpa using smul_top_le_comap (e.symm : N →ₗ[S] M) J h,
   fun h ↦ smul_top_le_comap (e : M →ₗ[S] N) J h⟩

theorem mem_sup_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (K : Submodule S N) (x : M) :
    x ∈ K.comap (e : M →ₗ[S] N) ⊔ J • ⊤ ↔ e x ∈ K ⊔ J • ⊤ := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [map_add]
    exact Submodule.add_mem_sup ha ((mem_smul_top_equiv e J b).2 hb)
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    have hx : x = e.symm a + e.symm b := by rw [← map_add, hab, LinearEquiv.symm_apply_apply]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ((mem_smul_top_equiv e J _).1 (by simpa using hb))
    simpa using ha

theorem exists_isCompl_comap_iff (e : M ≃ₗ[S] N) (K : Submodule S N) :
    (∃ L, IsCompl K L) ↔ ∃ L, IsCompl (K.comap (e : M →ₗ[S] N)) L := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨L.comap (e : M →ₗ[S] N), (Submodule.orderIsoMapComap e).symm.isCompl h⟩
  · rintro ⟨L, h⟩
    refine ⟨L.map (e : M →ₗ[S] N), ?_⟩
    have := (Submodule.orderIsoMapComap e).isCompl h
    simpa [Submodule.orderIsoMapComap, Submodule.map_comap_eq_of_surjective e.surjective] using this

end Lin

theorem admissible_classification : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  obtain ⟨-, -, pc, bij, fin, proj, hA₀, hg₀⟩ :=
    abelianLift_facts H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨rs, rk⟩ := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨-, ⟨N₀, hN₀⟩, -⟩ := GlobalTheory.AbelianHodge.abelianDeRham_hodge H1 H2 R₀ A₀ g hA₀ hg₀
  let P := prim (divided₂ hI) (spMap π) A₀
  let Ψ : primDR A' ≃ₗ[R] P := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').pull bij
  let Φ : primDR A' ≃ₗ[R] Cr hI π A₀.hom := Ψ.trans (LinearEquiv.ofTop _ pc)
  have hΦ : ∀ c, Φ c = ((Ψ c : P) : Cr hI π A₀.hom) := fun _ ↦ rfl
  let ρ := (GrothendieckMessing.redMor h').pull
  have mT : IsMor (dp0 R₀) (A₀.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have mT' : IsMor (dp0 R₀) A₀.hom (dp0 R₀) (A₀.hom ≫ 𝟙 _) (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have back : ∀ x, mT'.pull1 (mT.pull1 x) = x := fun x ↦
    (IsMor.pullback1_comp mT mT' (IsMor.id _ _) (fun _ ↦ rfl) (Category.id_comp _) x).trans
      (IsMor.pullCohomologyOne_id _ x)
  have inj : Function.Injective mT.pull1 := Function.LeftInverse.injective back
  have mD : IsMor (dp0 R) (A'.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom π i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id]; exact h'.1.w)
  have key : ∀ c : primDR A',
      mT.pull1 ((ρ c : primDR A₀) : FirstDeRham (A₀.hom ≫ 𝟙 _)) = rho hI hk A₀.hom (Φ c) := by
    intro c
    rw [hΦ]
    exact (IsMor.pullback1_comp _ mT mD (fun _ ↦ rfl) (Category.id_comp _) c.1).trans
      (IsMor.pullback1_comp _ (redMor hI hk A₀.hom) mD (fun _ ↦ rfl) (Category.id_comp _) c.1).symm
  have F1iff : ∀ c : primDR A', ρ c ∈ PrimitiveSubmodule A₀ ↔ rho hI hk A₀.hom (Φ c) ∈ F1 A₀.hom := by
    intro c
    rw [← key]
    constructor
    · intro h
      exact mT.pullback1_mem_hodgeFiltration h
    · intro h
      have := mT'.pullback1_mem_hodgeFiltration h
      rw [back] at this
      exact this
  have ρker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R (primDR A')) := by
    intro c
    rw [hk, ← mem_smul_top_equiv Φ, ← rk, ← key, map_eq_zero_iff _ inj, Submodule.coe_eq_zero]
  have ρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨d, hd⟩ := rs (mT.pull1 y.1)
    refine ⟨Φ.symm d, Subtype.ext (inj ?_)⟩
    rw [key, LinearEquiv.apply_symm_apply, hd]
  obtain ⟨D1, D2⟩ := GlobalTheory.T.summand_dualAnnihilator_reduction_projective R R₀ π hπ (primDR A') (primDR A₀) (Module.Finite.equiv Φ.symm)
    (Module.Projective.of_equiv Φ.symm) ρ ρsurj ρker (PrimitiveSubmodule A₀) ⟨N₀, hN₀⟩
  have cond : ∀ K : Submodule R (Cr hI π A₀.hom),
      (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ↔
        ∀ c, c ∈ K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) ⊔ RingHom.ker π • ⊤ ↔
          ρ c ∈ PrimitiveSubmodule A₀ := by
    intro K
    rw [hk]
    constructor
    · intro H c
      rw [mem_sup_smul_top_equiv, F1iff]
      exact H (Φ c)
    · intro H c
      have := H (Φ.symm c)
      rwa [mem_sup_smul_top_equiv, F1iff, LinearEquiv.apply_symm_apply] at this
  have crysSurj : Function.Surjective (crysToDR (divided₂ hI) h') := fun y ↦
    ⟨y.comp (Ψ.symm : P →ₗ[R] primDR A'), LinearMap.ext fun c ↦ by
      rw [crysToDR_apply]
      exact congrArg y (Ψ.symm_apply_apply c)⟩
  have ann : ∀ K : Submodule R (Cr hI π A₀.hom),
      (K.comap P.subtype).dualAnnihilator =
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator.comap
          (crysToDR (divided₂ hI) h') := by
    intro K
    ext d
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator, crysToDR_apply]
    constructor
    · intro H c hc
      exact H _ hc
    · intro H p hp
      have e : (liftMor (divided₂ hI) h').pull (Ψ.symm p) = p := Ψ.apply_symm_apply p
      have hm : Φ (Ψ.symm p) ∈ K := by
        rw [hΦ, Ψ.apply_symm_apply]
        exact hp
      have := H (Ψ.symm p) hm
      rwa [crysToDR_apply, e] at this
  have eqiff : ∀ (K : Submodule R (Cr hI π A₀.hom)) (F : Submodule R (HdR A')),
      (K.comap P.subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h') ↔
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator = F := by
    intro K F
    rw [ann]
    exact (Submodule.comap_injective_of_surjective crysSurj).eq_iff
  refine ⟨fun K hK hc ↦ ?_, fun F hF ↦ ?_, fun K K' hK hK' he ↦ ?_⟩
  · obtain ⟨c1, -, c3⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    exact ⟨_, ⟨c1, c3.1 ((cond K).1 hc)⟩, (eqiff K _).2 rfl⟩
  · obtain ⟨K', hK', rfl⟩ := D2 F hF.1
    have hKK : (K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).comap
        (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) = K' :=
      Submodule.comap_map_eq_of_injective Φ.injective K'
    obtain ⟨-, -, c3⟩ := D1 K' hK'
    refine ⟨K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom), (exists_isCompl_comap_iff Φ _).2 (by rw [hKK]; exact hK'),
      (cond _).2 (by rw [hKK]; exact c3.2 hF.2), (eqiff _ _).2 (by rw [hKK])⟩
  · rw [ann, ann] at he
    have e := Submodule.comap_injective_of_surjective crysSurj he
    obtain ⟨-, c2, -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    obtain ⟨-, c2', -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K').1 hK')
    refine Submodule.comap_injective_of_surjective Φ.surjective ?_
    rw [← c2, ← c2', e]

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_deRhamHomology_summands_crystal : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  atlas_forward_decl GlobalTheory.LiftSys.admissible_classification
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LiftSys.summand_of_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S' hS' hN S
  obtain ⟨N, hN⟩ := hN
  obtain ⟨hinf, hfull⟩ := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const S' S
  have hS : S.Full hI := hfull hS'
  have hsup : S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    ext c
    rw [GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hS c, GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S' hρ hS' c]
  exact ⟨⟨N, (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S.K hI) N hN hsup).1 hinf.symm⟩, hsup⟩
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  atlas_forward_decl GlobalTheory.LiftSys.summand_of_full
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Twist

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

def twistHom {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] (hI : I ^ 2 = 0) (p : B →+* B₀) (hp : SemiHom π p) (α : B →ₐ[R] B') (θ : Ω[B₀⁄R₀] →+ B')
    (hsm : ∀ b w, θ (p b • w) = α b * θ w) (hmem : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b + θ (D R₀ B₀ (p b))
  map_one' := by simp
  map_mul' b c := by
    have h := mul_eq_zero_of_mem_map hI (hmem (D R₀ B₀ (p b))) (hmem (D R₀ B₀ (p c)))
    simp only [map_mul, Derivation.leibniz, map_add, hsm]
    linear_combination -h
  map_zero' := by simp
  map_add' b c := by simp only [map_add]; abel
  commutes' r := by
    simp only [SemiHom.map_algebraMap hp, Derivation.map_algebraMap, map_zero, add_zero, AlgHom.commutes]

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0)
  (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V)
  (hsm : ∀ (U V : AffOp X₀) (a : U ⟶ V) b w, θ U V a (S.p U b • w) = mp S.F a b * θ U V a w)
  (hmem : ∀ (U V : AffOp X₀) (a : U ⟶ V) w, θ U V a w ∈ I.map (algebraMap R (S.F.obj V)))
  (hid : ∀ U, θ U U (𝟙 U) = 0)
  (hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
    θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))))

def twistF : AffOp X₀ ⥤ CommAlgCat.{0} R where
  obj := S.F.obj
  map {U V} a := CommAlgCat.ofHom (twistHom hI (S.p U) (S.semi U) (mp S.F a) (θ U V a) (hsm U V a) (hmem U V a))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦ by
    change mp S.F (𝟙 U) b + θ U U (𝟙 U) (D R₀ _ (S.p U b)) = b
    rw [hid, AddMonoidHom.zero_apply, add_zero, mp_id])
  map_comp {U V W} a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ by
    change mp S.F (a ≫ b) c + θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (mp S.F a c + θ U V a (D R₀ _ (S.p U c))) +
        θ V W b (D R₀ _ (S.p V (mp S.F a c + θ U V a (D R₀ _ (S.p U c)))))
    have h0 : S.p V (θ U V a (D R₀ _ (S.p U c))) = 0 := (S.ker V _).2 (hmem U V a _)
    rw [map_add (S.p V), h0, add_zero, hcomp, mp_comp, map_add]
    abel)

def twistSys : Sys I π s₀ where
  F := twistF S hI θ hsm hmem hid hcomp
  p := S.p
  semi := S.semi
  nat {U V} a b := by
    change S.p V (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) = _
    rw [map_add, (S.ker V _).2 (hmem U V a _), add_zero]
    exact S.nat a b
  surj := S.surj
  ker := S.ker
  smooth := S.smooth

def ev {S' : Sys I π s₀} (v : GlobForm s₀ →+ Z1 S'.F) {U V : AffOp X₀}
    (a : U ⟶ V) : GlobForm s₀ →+ S'.F.obj V where
  toFun w := (v w).1 U V a
  map_zero' := by simp
  map_add' w w' := by simp

end GlobalTheory.LiftSys.Twist

namespace GlobalTheory.LiftSys

open Twist

theorem exists_twist : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S v hv hs
  have hex : ∀ (U V : AffOp X₀) (a : U ⟶ V), ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V,
      (∀ b w, θ (S.p U b • w) = mp S.F a b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R (S.F.obj V))) ∧
        ∀ w : GlobForm s₀, θ (w.1 U) = (v w).1 U V a := fun U V a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U _ _ (S.p U) (S.semi U) (S.surj U) (S.ker U) (mp S.F a)
      (ev v a) (fun r w ↦ by show (v (π r • w)).1 U V a = r • (v w).1 U V a; rw [hs]; rfl) (fun w ↦ hv w U V a)
  choose θ hθ huniq using hex
  have hsm := fun U V a ↦ (hθ U V a).1
  have hmem := fun U V a ↦ (hθ U V a).2.1
  have hglob := fun U V a ↦ (hθ U V a).2.2
  have hid : ∀ U, θ U U (𝟙 U) = 0 := fun U ↦ (huniq U U (𝟙 U) 0
    ⟨fun b w ↦ by simp, fun w ↦ by simp, fun w ↦ by rw [AddMonoidHom.zero_apply, Z1.id]⟩).symm
  have hcomp' : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]),
      θ U W (a ≫ b) x = mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x) := by
    intro U V W a b
    let ψ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj W :=
      AddMonoidHom.mk' (fun x ↦ mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x)) (fun x y ↦ by
        simp only [map_add]; abel)
    have e : ψ = θ U W (a ≫ b) := by
      refine huniq U W (a ≫ b) ψ ⟨fun c x ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩
      · show mp S.F b (θ U V a (S.p U c • x)) + θ V W b (p1 (OAff s₀) a (S.p U c • x)) =
          mp S.F (a ≫ b) c * (mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x))
        rw [hsm, oneFormsMapOfFunctorMorphism_smul, ← S.nat, hsm, map_mul, mp_comp, mul_add]
      · exact Ideal.add_mem _ (algHom_mem_map I (mp S.F b) (hmem U V a x)) (hmem V W b _)
      · show mp S.F b (θ U V a (w.1 U)) + θ V W b (p1 (OAff s₀) a (w.1 U)) = (v w).1 U W (a ≫ b)
        rw [← w.2 a, hglob, hglob, Z1.comp]
    intro x
    rw [← e]
    rfl
  have hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
      θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
        mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))) := by
    intro U V W a b c
    rw [hcomp', p1_D, S.nat]
  let S' := twistSys S hI θ hsm hmem hid hcomp
  let Φ : S.LocIso S' := ⟨fun _ ↦ AlgEquiv.refl, fun _ _ ↦ rfl⟩
  refine ⟨S', Φ, θ, fun U V a ↦ ⟨fun b w ↦ ?_, fun b ↦ ?_, hmem U V a⟩, fun w U V a ↦ hglob U V a w⟩
  · show θ U V a (S.p U b • w) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) * θ U V a w
    rw [hsm, add_mul, mul_eq_zero_of_mem_map hI (hmem U V a _) (hmem U V a _), add_zero]
  · show θ U V a (D R₀ _ (S.p U b)) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) - mp S.F a b
    rw [add_sub_cancel_left]

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_squareZeroSmoothLiftSystem_by_derivationCocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  atlas_forward_decl GlobalTheory.LiftSys.exists_twist
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

def Sys.cocyclesInIdealExtensions {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : Submodule R (Z1 S.F) where
  carrier := {z | S.IsIdealValuedLiftSystemCocycle z}
  add_mem' {a b} ha hb U V f := by
    change a.1 U V f + b.1 U V f ∈ _
    exact Ideal.add_mem _ (ha U V f) (hb U V f)
  zero_mem' U V f := Ideal.zero_mem _
  smul_mem' r z hz U V f := by
    change r • z.1 U V f ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hz U V f)

theorem exists_sys_of_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hR S' hF hN K hN' hsup
  obtain ⟨N, hN⟩ := hN

  have lin := GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) K N hN hsup
  obtain ⟨hKinf, u, hu, hu0, hall⟩ := lin.2 hN'
  have hKN : IsCompl K N := lin.1 hKinf
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀

  have fadd : ∀ (c1 c2 : Cr hI π s₀) (w1 w2 : GlobForm s₀), FormOf hI hk c1 w1 → FormOf hI hk c2 w2 → FormOf hI hk (c1 + c2) (w1 + w2) := by
    rintro c1 c2 w1 w2 ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    exact ⟨f1 + f2, by rw [map_add, map_add, h1, h2], by rw [map_add, Submodule.coe_add, e1, e2]⟩
  have fsmul : ∀ (r : R) (c : Cr hI π s₀) (w : GlobForm s₀), FormOf hI hk c w → FormOf hI hk (r • c) (π r • w) := by
    rintro r c w ⟨f, h, e⟩
    exact ⟨π r • f, by rw [map_smul, h, map_smulₛₗ], by rw [map_smul, Submodule.coe_smul, e]⟩
  have fzero : FormOf hI hk (0 : Cr hI π s₀) 0 := ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; rfl⟩
  have hwd : ∀ (c1 c2 : S'.K hI) (w : GlobForm s₀), FormOf hI hk c1.1 w → FormOf hI hk c2.1 w → u c1 = u c2 := by
    rintro c1 c2 w ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    have hz : cmpForm s₀ (f1 - f2) = 0 := Subtype.ext (by rw [map_sub, Submodule.coe_sub, e1, e2, sub_self]; rfl)
    have hcl := (hG.inj _).2 hz
    rw [map_sub, h1, h2, ← map_sub] at hcl
    have hm := (hR.2 _).1 hcl
    have := hu0 (c1 - c2) (by rw [Submodule.coe_sub]; exact hm)
    rwa [map_sub, sub_eq_zero] at this
  have hex : ∀ c ∈ S'.K hI, ∃ w : GlobForm s₀, FormOf hI hk c w := by
    intro c hc
    have h1 := (ksup S' hR hF c).1 (Submodule.mem_sup_left hc)
    rw [hodgeFiltration_eq_range] at h1
    obtain ⟨f, hf⟩ := h1
    exact ⟨(cmpForm s₀ f).1, f, hf, rfl⟩
  have hexF : ∀ w : GlobForm s₀, ∃ c : S'.K hI, FormOf hI hk c.1 w := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c0, hc0⟩ := hR.1 (Form.cl s₀ f)
    have hm : c0 ∈ S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (ksup S' hR hF c0).2 (by rw [hc0, hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨⟨k, hk'⟩, f, ?_, hf⟩
    rw [← hc0, map_add, (hR.2 i).2 hi, add_zero]
  choose cw hcw using hexF

  let v : GlobForm s₀ →+ CatCoh.H1 S'.F :=
    { toFun := fun w ↦ -S'.r hI (u (cw w))
      map_zero' := by
        rw [hwd (cw 0) 0 0 (hcw 0) fzero, map_zero, map_zero, neg_zero]
      map_add' := fun a b ↦ by
        rw [hwd (cw (a + b)) (cw a + cw b) (a + b) (hcw _) (fadd _ _ _ _ (hcw a) (hcw b)), map_add, map_add,
          neg_add] }
  have hvdef : ∀ w, v w = -S'.r hI (u (cw w)) := fun _ ↦ rfl
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    rw [hvdef, hvdef, hwd (cw (π r • w)) (r • cw w) _ (hcw _) (fsmul r _ _ (hcw w)), map_smul, map_smul, smul_neg]
  have hW : ∀ r, π r = 0 → ∀ m ∈ S'.cocyclesInIdealExtensions, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := by rw [← hk]; exact hr
    apply Subtype.ext
    funext U V a
    change r • m.1 U V a = 0
    rw [Algebra.smul_def]
    have := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj V)) hrI) (hm U V a)
    rw [← sq, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  have trans' := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀
  have hq : ∀ w, ∃ m ∈ S'.cocyclesInIdealExtensions, CatCoh.H1.mk S'.F m = v w := by
    intro w
    obtain ⟨z, z', hz, hmk, -, -⟩ := (trans' S' S' (Sys.LocIso.refl S')).2.2 (-(u (cw w))) (neg_mem (hu (cw w)).1)
    exact ⟨z, hz, by rw [hmk, map_neg]; rfl⟩
  obtain ⟨u', hu's, hu'W, hu'q⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj (Z1 S'.F)
    (CatCoh.H1 S'.F) S'.cocyclesInIdealExtensions hW (CatCoh.H1.mk S'.F) v hv hq
  obtain ⟨S'', Φ, θ, hdef, hθ⟩ := GlobalTheory.T.exists_twist_squareZeroSmoothLiftSystem_by_derivationCocycle R R₀ I hI π hπ hk X₀ s₀ hG.par S' u' hu'W hu's

  have hle : K ≤ S''.K hI := by
    intro k hk'
    obtain ⟨c, rfl⟩ := hall k hk'
    obtain ⟨w, hw⟩ := hex c.1 c.2
    obtain ⟨zw, -, hzw⟩ := (trans' S' S'' Φ).1 (u' w) (hu'W w)
    have hmain := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S' S'' Φ θ hdef c.1 c.2 w hw zw
      (fun U V a ↦ (hzw U V a).trans (hθ w U V a).symm)
    obtain ⟨z, z2, hzI, hz1, hz2, hzz⟩ := (trans' S' S'' Φ).2.2 (u c) (hu c).1
    have heq : u c = u (cw w) := hwd c (cw w) w hw (hcw w)
    have hsum : CatCoh.H1.mk S'.F (z + u' w) = 0 := by
      rw [map_add, hz1, hu'q w, hvdef, heq, add_neg_cancel]
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (z + u' w)
      (S'.cocyclesInIdealExtensions.add_mem hzI (hu'W w)) hsum
    have h2 : CatCoh.H1.mk S''.F (z2 + zw) = 0 := by
      refine CatCoh.H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
      funext U V a
      rw [(trans' S' S'' Φ).2.1 g hgI U V a, hg]
      change Φ.φ V (z.1 U V a + (u' w).1 U V a) = z2.1 U V a + zw.1 U V a
      rw [map_add, hzz, hzw]
    rw [map_add] at h2
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [Sys.K, LinearMap.mem_ker, map_sub, hmain, ← hz2, h3, sub_neg_eq_add, neg_add_cancel]

  have kinf := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const
  have hF'' : S''.Full hI := (kinf S' S'').2 hF
  have hsup'' : S''.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • ⊤ := by
    ext c
    rw [ksup S'' hR hF'' c, ksup S' hR hF c]
  have hS''N : IsCompl (S''.K hI) N :=
    (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S''.K hI) N hN hsup'').1 ((kinf S'' S').1)
  refine ⟨S'', le_antisymm ?_ hle⟩
  calc S''.K hI = (K ⊔ N) ⊓ S''.K hI := by rw [hKN.sup_eq_top, top_inf_eq]
    _ = K ⊔ N ⊓ S''.K hI := sup_inf_assoc_of_le N hle
    _ = K := by rw [inf_comm, hS''N.inf_eq_bot, sup_bot_eq]
    _ ≤ K := le_rfl

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroLiftSystem_of_summand_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  atlas_forward_decl GlobalTheory.LiftSys.exists_sys_of_summand
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Defect

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S S' : Sys I π s₀} (Φ : S.LocIso S')

abbrev al {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)

abbrev be {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)

theorem map_mem {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (f : B →ₐ[R] B')
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : f x ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (f : B →+* B') hx
  rwa [Ideal.map_map, f.comp_algebraMap] at h

theorem mul_eq_zero' (hI : I ^ 2 = 0) {B : Type} [CommRing B] [Algebra R B] {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B] at h
  simpa using h

theorem diff_mem {U V : AffOp X₀} (a : U ⟶ V) (b : S.F.obj U) :
    al Φ a b - be Φ a b ∈ I.map (algebraMap R (S'.F.obj V)) := by
  rw [← S'.ker V, map_sub, sub_eq_zero]
  change S'.p V (mp S'.F a (Φ.φ U b)) = S'.p V (Φ.φ V (mp S.F a b))
  rw [S'.nat, Φ.red, Φ.red, S.nat]

theorem ex (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) :
    ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V, IsTheta I (S.p U) (al Φ a) (be Φ a) θ :=
  (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U)
    (S.surj U) (S.ker U) (al Φ a)).1 (be Φ a) (diff_mem Φ a)

def th (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V :=
  (ex Φ hI hπ a).exists.choose

theorem th_spec (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : IsTheta I (S.p U) (al Φ a) (be Φ a) (th Φ hI hπ a) :=
  (ex Φ hI hπ a).exists.choose_spec

theorem th_comp (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V W : AffOp X₀} (a : U ⟶ V)
    (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]) :
    th Φ hI hπ (a ≫ b) x = mp S'.F b (th Φ hI hπ a x) + th Φ hI hπ b (p1 (OAff s₀) a x) := by
  let θ' : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj W :=
    ((mp S'.F b).toRingHom.toAddMonoidHom.comp (th Φ hI hπ a)) +
      (th Φ hI hπ b).comp (p1 (OAff s₀) a).toAddMonoidHom
  have hA := th_spec Φ hI hπ a
  have hB := th_spec Φ hI hπ b
  have h : IsTheta I (S.p U) (al Φ (a ≫ b)) (be Φ (a ≫ b)) θ' := by
    refine ⟨fun c w ↦ ?_, fun c ↦ ?_, fun w ↦ ?_⟩
    · change mp S'.F b (th Φ hI hπ a (S.p U c • w)) + th Φ hI hπ b (p1 (OAff s₀) a (S.p U c • w)) =
        al Φ (a ≫ b) c * (mp S'.F b (th Φ hI hπ a w) + th Φ hI hπ b (p1 (OAff s₀) a w))
      rw [hA.smul, oneFormsMapOfFunctorMorphism_smul]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.smul, map_mul]
      have hz : (mp S'.F b (al Φ a c) - al Φ b (mp S.F a c)) * th Φ hI hπ b (p1 (OAff s₀) a w) = 0 := by
        refine mul_eq_zero' hI ?_ (hB.mem _)
        have : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
        rw [this, ← map_sub]
        exact map_mem _ (diff_mem Φ a c)
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      rw [e2]
      linear_combination -hz
    · change mp S'.F b (th Φ hI hπ a (D R₀ _ (S.p U c))) + th Φ hI hπ b (p1 (OAff s₀) a (D R₀ _ (S.p U c))) =
        al Φ (a ≫ b) c - be Φ (a ≫ b) c
      rw [hA.der, p1_D]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.der, map_sub]
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      have e3 : be Φ (a ≫ b) c = be Φ b (mp S.F a c) := by
        change Φ.φ W (mp S.F (a ≫ b) c) = Φ.φ W (mp S.F b (mp S.F a c)); rw [mp_comp]
      have e4 : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
      rw [e2, e3, e4]; ring
    · exact Ideal.add_mem _ (map_mem _ (hA.mem w)) (hB.mem _)
  have := (ex Φ hI hπ (a ≫ b)).unique (th_spec Φ hI hπ (a ≫ b)) h
  exact DFunLike.congr_fun this x

def cocyc (hI : I ^ 2 = 0) (hπ : Function.Surjective π) : GlobForm s₀ →+ Z1 S'.F where
  toFun w := ⟨fun U V a ↦ th Φ hI hπ a (w.1 U), fun U V W a b ↦ by
    change th Φ hI hπ (a ≫ b) (w.1 U) = mp S'.F b (th Φ hI hπ a (w.1 U)) + th Φ hI hπ b (w.1 V)
    rw [th_comp, w.2 a]⟩
  map_zero' := Subtype.ext (by funext U V a; exact map_zero _)
  map_add' w w' := Subtype.ext (by funext U V a; exact map_add _ _ _)

theorem th_smul (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) (r : R)
    (x : Ω[Sec s₀ U.unop.1⁄R₀]) : th Φ hI hπ a (π r • x) = r • th Φ hI hπ a x := by
  rw [← algebraMap_smul (Sec s₀ U.unop.1) (π r) x, ← (S.semi U).map_algebraMap, (th_spec Φ hI hπ a).smul,
    AlgHom.commutes, ← Algebra.smul_def]

end GlobalTheory.LiftSys.Defect

theorem GlobalTheory.LiftSys.exists_defect_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  intro R R₀ _ _ I hI π hπ _ X₀ s₀ S S' Φ
  refine ⟨fun U V a ↦ Defect.th Φ hI hπ a, Defect.cocyc Φ hI hπ, fun U V a ↦ Defect.th_spec Φ hI hπ a,
    fun w U V a ↦ rfl, fun w U V a ↦ (Defect.th_spec Φ hI hπ a).mem _, fun r w ↦ ?_⟩
  refine Subtype.ext ?_
  funext U V a
  exact Defect.th_smul Φ hI hπ a r (w.1 U)
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  atlas_forward_decl GlobalTheory.LiftSys.exists_defect_cocycle
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_corr_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S S' Φ θ hθ E hEI hEs hEd

  have hext : ∀ U : AffOp X₀, ∃! η : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj U,
      (∀ b w, η (S.p U b • w) = (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) b * η w) ∧
      (∀ w, η w ∈ I.map (algebraMap R (S'.F.obj U))) ∧ ∀ w : GlobForm s₀, η (w.1 U) = E w U := fun U ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj U) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ((Pi.evalAddMonoidHom _ U).comp E)
      (fun r w ↦ by simp [hEs]) (fun w ↦ hEI w U)

  choose η hη using fun U ↦ (hext U).exists
  have hψ : ∀ U : AffOp X₀, ∃ ψ : S.F.obj U →ₐ[R] S'.F.obj U,
      IsTheta I (S.p U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ψ (-η U) := fun U ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj U) I hI π hπ (S.p U) (S.semi U) (S.surj U)
      (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)).2 (-η U)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hη U).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hη U).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ U b, ψ U b = Φ.φ U b + η U (D R₀ (Sec s₀ U.unop.1) (S.p U b)) := fun U b ↦ by
    have h := (hψ U).der b
    rw [AddMonoidHom.neg_apply] at h
    change -η U _ = Φ.φ U b - ψ U b at h
    linear_combination h
  refine ⟨ψ, fun U b ↦ ?_, fun U V a b ↦ ?_⟩
  · rw [hψv, map_add, Φ.red, (S'.ker U _).2 ((hη U).2.1 _), add_zero]
  ·
    let α : S.F.obj U →ₐ[R] S'.F.obj V := (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)
    let χ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V := θ U V a + (mp S'.F a).toAddMonoidHom.comp (η U) -
      (η V).comp (p1 (OAff s₀) a).toAddMonoidHom
    have hχ : ∀ w, χ w = θ U V a w + mp S'.F a (η U w) - η V (p1 (OAff s₀) a w) := fun _ ↦ rfl

    have hmemV : ∀ w, η V w ∈ I.map (algebraMap R (S'.F.obj V)) := (hη V).2.1
    have hdiff : ∀ c : S.F.obj U, ∀ x ∈ I.map (algebraMap R (S'.F.obj V)),
        (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) * x = α c * x := by
      intro c x hx
      have h1 := (hθ U V a).der c
      have h2 : α c - (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) ∈ I.map (algebraMap R (S'.F.obj V)) :=
        h1 ▸ (hθ U V a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj V) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hθ U V a).smul, (hη U).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← S.nat a b, (hη V).1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hθ U V a).mem w) (algHom_mem_map I _ ((hη U).2.1 w))) (hmemV _)
      · rw [hχ, hEd, amitsur_d0_apply, (hη U).2.2, ← w.2 a, (hη V).2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ U.unop.1) (S.p U b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) a (S.p U b) = S.p V (mp S.F a b) := (S.nat a b).symm
    rw [hn] at h0
    have h1 := (hθ U V a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add]
    simp only [AlgEquiv.coe_toAlgHom] at h0 h1 ⊢
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  atlas_forward_decl GlobalTheory.LiftSys.exists_corr_of_defect
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem sysHom_of_K_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S S' hF hK
  obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
  obtain ⟨θ, v, hθ, hv, hvI, hvs⟩ := GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms R R₀ I hI π hπ hk X₀ s₀ S S' Φ

  have hcl : ∀ w, H1.mk _ (v w) = 0 := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c', hc'⟩ := hρ.1 (Form.cl s₀ f)
    have hmem : c' ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀ S hρ hF c').2 (by rw [hc', hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
    have hρz : rho hI hk s₀ z = 0 := (hρ.2 z).2 hz
    have hfo : FormOf hI hk y w := ⟨f, by rw [← hc', map_add, hρz, add_zero], hf⟩
    have hm := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S S' Φ θ hθ y hy w hfo (v w) (hv w)
    have hy' : y ∈ S'.K hI := hK ▸ hy
    have h0 : S'.r hI y = 0 := hy'
    rw [h0] at hm
    exact neg_eq_zero.1 hm.symm

  let W : Submodule R (C0 S'.F) :=
    { carrier := {g | S'.IsIdealValuedLiftSystemCochain g}
      add_mem' := fun {g g'} hg hg' U ↦ Ideal.add_mem _ (hg U) (hg' U)
      zero_mem' := fun U ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg U ↦ by
        show r • g U ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hg U) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext U
    show r • m U = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj U)) hrI) (hm U)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  have hq : ∀ w, ∃ m ∈ W, d0 S'.F m = ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro w
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (v w) (hvI w) (hcl w)
    exact ⟨g, hgI, hg⟩
  have hv' : ∀ (r : R) w, ((Z1 S'.F).subtype.toAddMonoidHom.comp v) (π r • w) =
      r • ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro r w
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, hvs]
    rfl
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj
    (C0 S'.F) (C1 S'.F) W hW (d0 S'.F) _ hv' hq
  exact GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary R R₀ I hI π hπ hk X₀ s₀ hG.par S S' Φ θ hθ u hu2 hu1 (fun w U V a ↦
    (hv w U V a).symm.trans (congrFun (congrFun (congrFun (hu3 w) U) V) a).symm)

end GlobalTheory.LiftSys
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroLiftSystem_hom_of_filtration_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  atlas_forward_decl GlobalTheory.LiftSys.sysHom_of_K_eq
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem hodgeFiltration_lift_map_eq_crystalline_kernel (H : CrystallineSmoothLift) {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0)
    {π : R →+* R₀} (hπ : Function.Surjective π) (hk : RingHom.ker π = I) {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
    {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : IsPullback i s₀ s (spMap π)) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) (S : Sys I π s₀) (hP : S.Presents s i)
    (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) :
    (F1 s).map m.pull1 = S.K hI := by
  have hb := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk X X₀ s s₀ i hs hs' hs'' h m).1
  obtain ⟨e, he, -⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk X₀ s₀ S X s i h hP
  have key : ∀ c, m.pull1 c ∈ S.K hI ↔ c ∈ F1 s := fun c ↦ by
    change S.r hI (m.pull1 c) = 0 ↔ toH1O s c = 0
    rw [← he m c, LinearEquiv.map_eq_zero_iff, structureSheaf_comparison_comm]
    exact ⟨fun h0 ↦ cmpO_injective R X s (h0.trans (map_zero _).symm), fun h0 ↦ by rw [h0, map_zero]⟩
  ext x
  obtain ⟨c, rfl⟩ := hb.2 x
  constructor
  · rintro ⟨c', hc', e'⟩
    rw [← hb.1 e']
    exact (key c').2 hc'
  · intro hx
    exact ⟨c, (key c).1 hx, rfl⟩

theorem hodgeFiltration_lift_eq_comap_systemFiltration (H : CrystallineSmoothLift) (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀))
    [GrpObj A₀] (hA : IsProper A₀.hom) (hA' : GeometricallyConnected A₀.hom) (X : Over (Sp R))
    (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)) (hX : Smooth X.hom) (S : Sys I π A₀.hom)
    (hP : S.Presents X.hom i) :
    primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hpr := (GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift R R₀ π hπ hnil X A₀ i h hX hA hA').1
  have e : X.hom ≫ 𝟙 _ = X.hom := Category.comp_id _
  have h' : IsPullback i A₀.hom (X.hom ≫ 𝟙 _) (spMap π) := by rw [e]; exact h
  have hs : Smooth (X.hom ≫ 𝟙 _) := by rw [e]; exact hX
  have hs' : IsSeparated (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hs'' : QuasiCompact (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hP' : S.Presents (X.hom ≫ 𝟙 _) i := by rw [e]; exact hP
  unfold primitiveCrystalHodgeLiftClasses
  rw [hodgeFiltration_lift_map_eq_crystalline_kernel H hI hπ hk h' hs hs' hs'' S hP']

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys : CrystallineSmoothLift → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀], IsProper A₀.hom → GeometricallyConnected A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom → ∀ S : Sys I π A₀.hom, S.Presents X.hom i → primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  atlas_forward_decl GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i ∧ Surjective i ∧ Nonempty (S.Presents s i) := by
  first | exact @GlobalTheory.LiftGlue.exists_presents | exact GlobalTheory.LiftGlue.exists_presents | (intros; apply GlobalTheory.LiftGlue.exists_presents <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  first | exact @GlobalTheory.LiftSys.Glue.presents_hom | exact GlobalTheory.LiftSys.Glue.presents_hom | (intros; apply GlobalTheory.LiftSys.Glue.presents_hom <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  first | exact @GlobalTheory.LiftSys.presents_isLift | exact GlobalTheory.LiftSys.presents_isLift | (intros; apply GlobalTheory.LiftSys.presents_isLift <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLift_reduction_standard_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.LiftSys.abelianLift_facts | exact GlobalTheory.LiftSys.abelianLift_facts | (intros; apply GlobalTheory.LiftSys.abelianLift_facts <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_isCompl_ker_of_projective {R : Type} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

theorem mem_smul_top_of_tmul_eq_zero {R R₀ M : Type} [CommRing R] [CommRing R₀] [AddCommGroup M] [Module R M]
    (π : R →+* R₀) (hπ : Function.Surjective π) {I : Ideal R} (hk : RingHom.ker π = I) (x : M)
    (h : letI := π.toAlgebra; (1 : R₀) ⊗ₜ[R] x = 0) : x ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R₀) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π) • (⊤ : Submodule R M) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π))
  have h1 : E ((1 : R₀) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
    have : f.symm (1 : R₀) = Ideal.Quotient.mk _ 1 := by rw [map_one, map_one]
    change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π) (f.symm 1 ⊗ₜ[R] x) = _
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem full_and_isCompl : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  intro H HD R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg S hS
  have hpb : IsPullback i' A₀.hom A'.hom (spMap π) := h'.1
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk A₀.left A₀.hom S A'.left A'.hom i' hpb hS
  have hsm : Smooth A'.hom := hA.smooth
  haveI : IsProper A'.hom := hA.proper
  have hsep : IsSeparated A'.hom := inferInstance
  have hqc : QuasiCompact A'.hom := inferInstance
  have hw : i' ≫ A'.hom = (A₀.hom ≫ spMap π) ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id]; exact hpb.w
  let m : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' := IsMor.of_dividedPowersZeroIdeal _ hw
  have hm := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
    hsm hsep hqc hpb m).1
  have hc := H.bijective_cechDeRhamComparison_degreeOne A'.hom hsm hsep hqc
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hto⟩, hbc⟩ := HD R A' g hA hg
  have key : ∀ c, S.r hI (m.pull1 c) = e (toHO1 A'.hom (cmp1 A'.hom c)) := fun c ↦ (he1 m c).symm
  have hr : Function.Surjective (S.r hI) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := hto x
    obtain ⟨c, rfl⟩ := hc.2 w
    exact ⟨m.pull1 c, key c⟩
  haveI : Module.Projective R (GlobalTheory.CatCoh.H1 S.F) := Module.Projective.of_equiv e
  refine ⟨?_, exists_isCompl_ker_of_projective (S.r hI) hr⟩
  intro z hz
  have hz0 : S.redO.pullbackOneCocycle z = 0 := by
    refine Subtype.ext (funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_)
    exact (S.ker V _).2 (hz U V a)
  have h0 : S.redO.pull1 (H1.mk _ z) = 0 := by
    rw [CoefMap.pullCohomologyOne_class, hz0, map_zero]
  set x := e.symm (H1.mk _ z) with hxdef
  have hx0 : IsPullO hpb.w x 0 := by
    have := he2 x
    rwa [hxdef, LinearEquiv.apply_symm_apply, h0] at this
  letI := π.toAlgebra
  obtain ⟨-, -, e', he'⟩ := hbc R₀ A₀.left A₀.hom i' hpb
  have h1 : e' ((1 : R₀) ⊗ₜ[R] x) = 0 := by
    have a := he' x
    unfold IsPullO at a hx0
    exact (pairRes_injective i' A₀.hom).1 (a.symm.trans (hx0.trans (map_zero _).symm))
  have hxI : x ∈ I • (⊤ : Submodule R (HO1 A'.hom)) :=
    mem_smul_top_of_tmul_eq_zero π hπ hk x ((LinearEquiv.map_eq_zero_iff e').1 h1)
  have hzI : H1.mk _ z ∈ I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    have : H1.mk _ z = e x := by rw [hxdef, LinearEquiv.apply_symm_apply]
    rw [this]
    have hm' : e.toLinearMap x ∈ Submodule.map e.toLinearMap (I • ⊤) := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at hm'
    exact Submodule.smul_mono le_rfl le_top hm'
  have hsurjI : Submodule.map (S.r hI) (I • ⊤) = I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hr]
  rw [← hsurjI] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  exact ⟨c, hc, hcz⟩

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_presented_by_system : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  atlas_forward_decl GlobalTheory.LiftSys.full_and_isCompl
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_hodgeDeRham (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) :
    AbelianSchemeLifts := by
  intro R _ _ I hI R₀ _ π hπ hk g A₀ _ A' _ i' h' hA hg
  haveI : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ π hπ
  obtain ⟨-, -, -, -, -, -, hA₀, hg₀⟩ := GlobalTheory.T.abelianLift_reduction_standard_facts hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  have hG : Good A₀.hom := GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme hC hH R₀ A₀ g hA₀ hg₀
  have hR : RhoBC hI hk A₀.hom := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨ad1, ad2, ad3⟩ := GlobalTheory.T.admissible_deRhamHomology_summands_crystal hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨S', ⟨P'⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom A'.left A'.hom i' h'.1 hA.smooth
  obtain ⟨hF', hc'⟩ := GlobalTheory.T.abelian_scheme_presented_by_system hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg S' P'
  have core1 := GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc'
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk A₀.left A₀.hom S' hR hF'
  have fil : ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
      ∀ S : Sys I π A₀.hom, S.Presents X.hom i → schemeFil (divided₂ hI) A₀ X i h.w =
        ((S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator := fun X i h hX S P ↦
    congrArg Submodule.dualAnnihilator
      (GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys hC R R₀ I hI π hπ hk A₀ hA₀.proper hA₀.geomConnected X i h hX S P)
  refine ⟨⟨fun X i h hX ↦ ?_, fun F hF ↦ ?_⟩, fun X Y i j h k hX hY e ↦ ?_⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨hc, hs⟩ := core1 S
    obtain ⟨F, hF, e⟩ := ad1 (S.K hI) hc fun c ↦ by rw [hs]; exact ksup c
    exact ⟨F, hF, (fil X i h hX S P).trans e⟩
  · obtain ⟨K, hc, hs, e⟩ := ad2 F hF
    obtain ⟨S, rfl⟩ := GlobalTheory.T.exists_squareZeroLiftSystem_of_summand_reduction R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc' K hc
      (Submodule.ext fun c ↦ (hs c).trans (ksup c).symm)
    obtain ⟨X, s, i, h1, h2, ⟨P⟩⟩ := GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem R R₀ I hI π hπ hk A₀.left A₀.hom S
    obtain ⟨h, hX⟩ := GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents R R₀ I hI π hπ hk A₀.left A₀.hom S X s i h1 h2 P
    exact ⟨Over.mk s, i, h, hX, (fil (Over.mk s) i h hX S P).trans e⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨T, ⟨Q⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom Y.left Y.hom j k hY
    have hK : T.K hI = S.K hI := ad3 _ _ (core1 T).1 (core1 S).1
      ((fil Y j k hY T Q).symm.trans (e.symm.trans (fil X i h hX S P)))
    have hT : T.Full hI := (GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk A₀.left A₀.hom hG.const S' T).2 hF'
    obtain ⟨f, hf, hij⟩ := GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom R R₀ I hI π hπ hk A₀.left A₀.hom T S X.left X.hom i Y.left Y.hom j h Q P
      (GlobalTheory.T.exists_squareZeroLiftSystem_hom_of_filtration_eq R R₀ I hI π hπ hk A₀.left A₀.hom hG hR T S hT hK)
    haveI := hX
    have hn : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
    haveI : IsIso (Over.homMk f hf : X ⟶ Y) :=
      GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hn X Y A₀ A₀ i j h k inferInstance
        (Over.homMk f hf) (𝟙 A₀) (by simpa using hij) inferInstance
    exact ⟨asIso (Over.homMk f hf : X ⟶ Y), hij⟩

end GlobalTheory.LiftSys
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_hodgeDeRham : CrystallineSmoothLift → AbelianHodgeDeRham → AbelianSchemeLifts := by
  atlas_forward_decl GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham
end
