import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpanStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AnisotropicFiniteLengthsOfShortLatticeVector
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace

section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j := by
  first | exact @GlobalTheory.SmoothForms.hasLog_of_isLieData | exact GlobalTheory.SmoothForms.hasLog_of_isLieData | (intros; apply GlobalTheory.SmoothForms.hasLog_of_isLieData <;> assumption)
end

section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, Sm (expMap j s) φ ↔ ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => expMap j s (t i • Y i)).prod) := by
  first | exact @GlobalTheory.SmoothForms.SecondKind.main | exact GlobalTheory.SmoothForms.SecondKind.main | (intros; apply GlobalTheory.SmoothForms.SecondKind.main <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_generators_rep : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  first | exact @GlobalTheory.UnitaryLieComplexification.glRel_and_span | exact GlobalTheory.UnitaryLieComplexification.glRel_and_span | (intros; apply GlobalTheory.UnitaryLieComplexification.glRel_and_span <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  first | exact @GlobalTheory.EnvelopingExtension.exists_algHom_unitary | exact GlobalTheory.EnvelopingExtension.exists_algHom_unitary | (intros; apply GlobalTheory.EnvelopingExtension.exists_algHom_unitary <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_map_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau), Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  atlas_forward_decl GlobalTheory.EnvWords.envOf_surjective
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  first | exact @GlobalTheory.SmoothForms.RealPts.realPoints | exact GlobalTheory.SmoothForms.RealPts.realPoints | (intros; apply GlobalTheory.SmoothForms.RealPts.realPoints <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  first | exact @GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | exact GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | (intros; apply GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normInf_submultiplicative_le_adelicHeight : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧ ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  first | exact @GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | exact GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | (intros; apply GlobalTheory.SmoothForms.normInf_mul_le_and_le_height <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), DenomBound θ V := by
  first | exact @GlobalTheory.SmoothForms.denomBound | exact GlobalTheory.SmoothForms.denomBound | (intros; apply GlobalTheory.SmoothForms.denomBound <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Cover

open NumberField IsDedekindDomain Topology

theorem exists_finset_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Subgroup H) (hU : IsOpen (U : Set H)) (K : Set G) (hK : IsCompact K)
    (Ω : Set H) (hΩ : ∀ k ∈ Ω, (k : G) ∈ K) :
    ∃ S : Finset H, (∀ x ∈ S, x ∈ Ω) ∧ ∀ k ∈ Ω, ∃ x ∈ S, x⁻¹ * k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ W := by
    have : (1 : H) ∈ (U : Set H) := U.one_mem
    rw [← hWU] at this
    exact this
  have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 := by fun_prop
  have h2 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1, 1) : G × G) :=
    (hW.preimage hc).mem_nhds (by simpa using h1)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (A ∩ B)) (fun x _ => by
    have : Continuous fun y : G => x⁻¹ * y := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using ⟨hA, hB⟩))
  have hch : ∀ x : G, (∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B) → ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := fun _ h => h
  choose f hf hf' using hch
  refine ⟨(t.filter fun x => ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B).attach.image
    fun x => f x.1 (by have h := x.2; rw [Finset.mem_filter] at h; exact h.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf _ _
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht (hΩ k hk))
    have hex : ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := ⟨k, hk, hxk⟩
    refine ⟨f x hex, Finset.mem_image.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, hex⟩⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have h3 := hAB (Set.mk_mem_prod (hf' x hex).1 hxk.2)
    have h4 : (x⁻¹ * (f x hex : G))⁻¹ * (x⁻¹ * (k : G)) = (((f x hex)⁻¹ * k : H) : G) := by
      push_cast; group
    change _ ∈ (U : Set H)
    rw [← hWU]
    change _ ∈ W
    rw [← h4]
    exact h3

theorem isCompact_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {n : ℕ}
    (C : Fin n → Fin n → Set A) (hC : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : GL (Fin n) A | ∀ i j, g.1 i j ∈ C i j ∧ (g⁻¹).1 i j ∈ C i j} := by
  have h1 : IsCompact {m : Matrix (Fin n) (Fin n) A | ∀ i j, m i j ∈ C i j} :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite (hC i)
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).isCompact_preimage
    (h1.prod (h1.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, forall_and]

theorem exists_compact_denom (D : D7) (d : ℕ) (hd : 0 < d) :
    ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧ ∀ y, d • y ∈ intAE D → y ∈ C := by
  classical
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := RingOfIntegers.basis D.host.E
  let O : AddSubgroup (Af D.host.F) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers D.host.F}
      zero_mem' := fun v => zero_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      neg_mem' := fun ha v => neg_mem (ha v) }
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → Af D.host.F) →+
      Af D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := fun a => ∑ i, a i • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E))
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hφ : Continuous φ :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).fun_smul continuous_const
  have hle : intAE D ≤ (AddSubgroup.pi Set.univ fun _ => O).map φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨a, ha, x, rfl⟩
    refine ⟨fun i => b.repr x i • a, fun i _ => zsmul_mem (show a ∈ O from ha) _, ?_⟩
    change ∑ i, (b.repr x i • a) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E)) = _
    conv_rhs => rw [← b.sum_repr x]
    change _ = a ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E a) _ _).symm
  have hO : IsCompact (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      (O : Set (Af D.host.F))) :=
    isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral D.host.F
  let c : Af D.host.F := algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹
  have hcs : Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c • y :=
    (continuous_const (y := c)).fun_smul continuous_id
  refine ⟨(fun y => c • y) '' (φ '' _), (hO.image hφ).image hcs, fun y hy => ?_⟩
  refine ⟨d • y, hle hy, ?_⟩
  have : (d : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change c • d • y = y
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F), smul_smul,
    ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul, inv_mul_cancel₀ this, map_one, one_smul]

theorem exists_finset_cover : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  intro D V U hU d hd
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  obtain ⟨C, hC, hCd⟩ := exists_compact_denom D d hd
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let C' : Fin V.rank → Fin V.rank → Set (AE D) := fun i j =>
    e.symm '' ({(1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j} ×ˢ C)
  have hC' : ∀ i j, IsCompact (C' i j) := fun i j => (isCompact_singleton.prod hC).image hc
  have key : ∀ k ∈ GfC V, (∀ i j, d • finMat D.sp.cm.sig V.gram k i j ∈ intAE D) →
      ∀ i j, (matHom V k).1 i j ∈ C' i j := by
    intro k hk h i j
    refine ⟨e ((matHom V k).1 i j), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · rw [(he _).1]
      have h1 : (infHom V k).1 i j = _ := congrArg (fun g => g.1 i j) (MonoidHom.mem_ker.1 hk)
      exact h1
    · rw [(he _).2]
      exact hCd _ (h i j)
  obtain ⟨S, hS, hS'⟩ := exists_finset_of_compact (HR (AF D.host.F) D.sp.cm.sig V.gram) U hU _
    (isCompact_GL C' hC') {k : GA D V | k ∈ GfC V ∧ BddDen V d k} (fun k hk i j =>
      ⟨key k hk.1 (fun i j => (hk.2 i j).1) i j, key k⁻¹ (inv_mem hk.1) (fun i j => (hk.2 i j).2) i j⟩)
  refine ⟨S, fun k hk hb => ?_⟩
  obtain ⟨x, hx, hxk⟩ := hS' k ⟨hk, hb⟩
  exact ⟨x, hx, hxk, mul_mem (inv_mem (hS x hx).1) hk⟩

end GlobalTheory.SmoothForms.Cover
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  first | exact @GlobalTheory.SmoothForms.Cover.exists_finset_cover | exact GlobalTheory.SmoothForms.Cover.exists_finset_cover | (intros; apply GlobalTheory.SmoothForms.Cover.exists_finset_cover <;> assumption)
end

section
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_small_anisotropic_mem {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E}
    {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B₀ : ℝ} (H : Sized h Λ N ν B₀) {B : ℝ} (hB : 2 ≤ B)
    {W : Submodule E V} (hW : W ≠ ⊥) (hnd : ∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0)
    (hsp : W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}) :
    ∃ v, v ∈ Λ ∧ v ∈ W ∧ h v v ≠ 0 ∧ ν v ≤ B ^ 4 := by
  have hB1 : B ≤ B ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx0⟩ : ∃ x ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (le_bot_iff.1 (hsp.trans (Submodule.span_eq_bot.2 hc).le))
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hxy⟩ : ∃ y ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, h x y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hx0 (hnd x hx2 fun z hz => ?_)
    have : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun z hz => hc z hz
    exact this (hsp hz)
  by_cases hxx : h x x = 0
  swap
  · exact ⟨x, hx1, hx2, hxx, hx3.trans hB1⟩
  by_cases hyy : h y y = 0
  swap
  · exact ⟨y, hy1, hy2, hyy, hy3.trans hB1⟩
  refine ⟨x + h x y • y, Λ.add_mem hx1 (H.stable _ (H.int x hx1 y hy1) y hy1),
    W.add_mem hx2 (W.smul_mem _ hy2), ?_, ?_⟩
  · have : h (x + h x y • y) (x + h x y • y) = 2 * (h x y * star (h x y)) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hxx, hyy, H.symm x y,
        smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
      ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hxy (star_ne_zero.2 hxy))
  · have h0 : (0 : ℝ) ≤ B := by linarith
    have h1 : house (h x y) ≤ B * B := (H.form_le x y).trans (mul_le_mul hx3 hy3 (H.nonneg _) h0)
    have h2 : ν (h x y • y) ≤ B * B * B :=
      (H.smul_le _ _).trans (mul_le_mul h1 hy3 (H.nonneg _) (by positivity))
    have h3 : B ≤ B ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : 2 * B ^ 3 ≤ B * B ^ 3 := mul_le_mul_of_nonneg_right hB (by positivity)
    have := H.add_le x (h x y • y)
    nlinarith

theorem exists_small_frame_mem (n : ℕ) : ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B₀ : ℝ), Sized h Λ N ν B₀ →
    ∀ B : ℝ, 2 ≤ B → ∀ W : Submodule E V, Module.finrank E W = n → (∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0) →
    W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ ∧ v i ∈ W) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
      ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k := by
  induction n with
  | zero => exact ⟨0, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    refine ⟨10 * k + 4, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ?_⟩
    have hW : W ≠ ⊥ := by
      rintro rfl
      simp at hn
    have h0 : (0 : ℝ) ≤ B := by linarith
    have hB1 : (1 : ℝ) ≤ B := by linarith
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_small_anisotropic_mem H hB hW hnd hsp
    let g : W →ₗ[E] E := (h.flip v).domRestrict W
    let W' : Submodule E V := (LinearMap.ker g).map W.subtype
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x v = 0 := fun x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have hrank : Module.finrank E W' = n := by
      have h1 := g.finrank_range_add_finrank_ker
      have h2 : LinearMap.range g = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / h v v) • ⟨v, hv2⟩, ?_⟩
        rw [map_smul]
        change (c / h v v) * h v v = c
        field_simp
      rw [h2, hn, finrank_top, Module.finrank_self] at h1
      rw [Submodule.finrank_map_subtype_eq]
      omega
    let P : V →ₗ[E] V := h v v • LinearMap.id - (h.flip v).smulRight v
    have hP : ∀ x, P x = h v v • x + (-h x v) • v := fun x => by
      simp [P, sub_eq_add_neg]
    have hPW : ∀ x ∈ W, P x ∈ W' := fun x hx => by
      rw [hmem, hP]
      refine ⟨W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hv2), ?_⟩
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hnd' : ∀ y ∈ W', (∀ x ∈ W', h y x = 0) → y = 0 := fun y hy hy0 => by
      obtain ⟨hy1, hy2⟩ := (hmem y).1 hy
      refine hnd y hy1 fun x hx => ?_
      have h1 := hy0 _ (hPW x hx)
      rw [hP] at h1
      simp only [map_add, map_smulₛₗ, hy2, smul_eq_mul, mul_zero, add_zero, starRingEnd_apply] at h1
      exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 hv3)
    have hsp' : W' ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := by
      have h1 : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤
          (Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}).comap P := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨hx1, hx2, hx3⟩
        refine Submodule.subset_span ⟨?_, hPW x hx2, ?_⟩
        · rw [hP]
          exact Λ.add_mem (H.stable _ (H.int v hv1 v hv1) x hx1) (H.stable _ (H.int x hx1 v hv1).neg v hv1)
        · rw [hP]
          have a1 : house (h v v) ≤ B ^ 4 * B ^ 4 :=
            (H.form_le v v).trans (mul_le_mul hv4 hv4 (H.nonneg _) (by positivity))
          have a2 : house (-h x v) ≤ B * B ^ 4 := by
            have : house (-h x v) = house (h x v) := by simp [house]
            rw [this]
            exact (H.form_le x v).trans (mul_le_mul hx3 hv4 (H.nonneg _) h0)
          have a3 : ν (h v v • x) ≤ B ^ 4 * B ^ 4 * B :=
            (H.smul_le _ _).trans (mul_le_mul a1 hx3 (H.nonneg _) (by positivity))
          have a4 : ν ((-h x v) • v) ≤ B * B ^ 4 * B ^ 4 :=
            (H.smul_le _ _).trans (mul_le_mul a2 hv4 (H.nonneg _) (by positivity))
          have a5 : 2 * B ^ 9 ≤ B * B ^ 9 := mul_le_mul_of_nonneg_right hB (by positivity)
          calc _ ≤ _ := H.add_le _ _
            _ ≤ _ := add_le_add a3 a4
            _ = 2 * B ^ 9 := by ring
            _ ≤ B * B ^ 9 := a5
            _ = B ^ 10 := by ring
      intro x hx
      obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
      have h2 : P x ∈ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := h1 (hsp hx1)
      rw [hP, hx2, neg_zero, zero_smul, add_zero] at h2
      exact (Submodule.smul_mem_iff _ hv3).1 h2
    obtain ⟨w, hw1, hw2, hw3⟩ := ih V h Λ N ν B₀ H (B ^ 10)
      (hB.trans (le_self_pow₀ hB1 (by norm_num))) W' hrank hnd' hsp'
    have hwv : ∀ i, h (w i) v = 0 := fun i => ((hmem _).1 (hw1 i).2).2
    refine ⟨Fin.cons v w, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hv1, hv2⟩ (fun i => ?_) i
      exact ⟨(hw1 i).1, ((hmem _).1 (hw1 i).2).1⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [H.symm, hwv, star_zero]
      · intro _
        simpa using hwv i
      · intro hij
        simpa using hw2 i j fun e => hij (by rw [e])
    · intro i
      refine Fin.cases ⟨hv3, hv4.trans (pow_le_pow_right₀ hB1 (by omega))⟩ (fun i => ?_) i
      refine ⟨(hw3 i).1, (hw3 i).2.trans ?_⟩
      rw [← pow_mul]
      exact pow_le_pow_right₀ hB1 (by omega)

theorem frameSmall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  intro E _ _ _ n
  obtain ⟨k, hk⟩ := exists_small_frame_mem (E := E) n
  refine ⟨k, fun V _ _ _ h Λ N ν B hn H => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hk V h Λ N ν B H B H.two_le ⊤ (by rw [finrank_top, hn])
    (fun y _ hy => H.nondeg y fun x => hy x trivial) (by simp [H.span])
  exact ⟨v, fun i => (h1 i).1, h2, h3⟩

end GlobalTheory.SmoothForms
end

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  atlas_forward_decl GlobalTheory.SmoothForms.frameSmall
end

section
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

open Module Submodule

theorem Sized.proj_le {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
    {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B)
    {T : ℝ} (hT : 2 ≤ T) {v x : V} (hv : ν v ≤ T) (hx : ν x ≤ T) :
    ν (h v v • x - h x v • v) ≤ T ^ 4 := by
  have hneg : house (-(h x v)) = house (h x v) := by simp [house]
  have h0 : 0 ≤ T := by linarith
  have h1 : house (h v v) ≤ T * T := (H.form_le v v).trans (mul_le_mul hv hv (H.nonneg _) h0)
  have h2 : house (h x v) ≤ T * T := (H.form_le x v).trans (mul_le_mul hx hv (H.nonneg _) h0)
  have h3 : ν (h v v • x) ≤ T * T * T :=
    (H.smul_le _ _).trans (mul_le_mul h1 hx (H.nonneg _) (by positivity))
  have h4 : ν ((-(h x v)) • v) ≤ T * T * T :=
    (H.smul_le _ _).trans (by rw [hneg]; exact mul_le_mul h2 hv (H.nonneg _) (by positivity))
  rw [sub_eq_add_neg, ← neg_smul]
  have h5 : 2 * (T * T * T) ≤ T * (T * T * T) := mul_le_mul_of_nonneg_right hT (by positivity)
  refine (H.add_le _ _).trans ?_
  calc _ ≤ 2 * (T * T * T) := by linarith
    _ ≤ _ := h5
    _ = _ := by ring

theorem orthoSmall_of_anisoSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (HA : AnisoSmall E) :
    OrthoSmall E := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, 0, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, k₁, hS₁, h0₁, H₁⟩ := HA (n + 1) n.succ_ne_zero N hN
    obtain ⟨M, hM, hMS⟩ := GlobalTheory.HermClass.exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, k₂, hS₂, h0₂, H₂⟩ := ih _ (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, k₁ + (k₁ + 1) * 4 * k₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ ν B hV H
    obtain ⟨v, hv, hvS, hvν⟩ := H₁ V h Λ ν B hV H
    have hs := H.symm
    have hO := H.stable
    have hint := H.int
    have hB1 : 1 ≤ B := by linarith [H.two_le]
    have hBT : B ≤ B ^ (k₁ + 1) := le_self_pow₀ hB1 (Nat.succ_ne_zero _)
    have hT2 : 2 ≤ B ^ (k₁ + 1) := H.two_le.trans hBT
    have hvT : ν v ≤ B ^ (k₁ + 1) := hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_succ _))
    have hproj : ∀ x, ν x ≤ B → ν (h v v • x - h x v • v) ≤ (B ^ (k₁ + 1)) ^ 4 := fun x hx =>
      H.proj_le hT2 hvT (hx.trans hBT)
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    have H' : Sized (h.domRestrict₁₂ W W) Λ' (M * N) (fun w : W => ν w) ((B ^ (k₁ + 1)) ^ 4) :=
      { symm := fun x y => hs x y
        nondeg := fun y hy => Subtype.ext (H.nondeg y fun x => by
          have h1 : h y (p x) = 0 := hy (p x)
          rw [hyp] at h1
          exact (mul_eq_zero.1 h1).resolve_left ha0)
        fg := by
          apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
          exact H.fg.of_le (map_comap_le _ _)
        stable := fun c hc x hx => hO c hc x hx
        int := fun x hx y hy => hint x hx y hy
        dual := fun y hy => by
          have h1 : (N : E) • a • (y : V) ∈ Λ := H.dual _ fun x hx => by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
            exact hy _ (hpΛ x hx)
          have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
          rw [smul_smul, smul_smul] at h2
          rw [hΛ', Submodule.coe_smul]
          convert h2 using 2
          push_cast; field_simp
        two_le := hT2.trans (le_self_pow₀ (by linarith) (by norm_num))
        nonneg := fun x => H.nonneg x
        add_le := fun x y => H.add_le x y
        smul_le := fun c x => H.smul_le c x
        form_le := fun x y => H.form_le x y
        span := by
          rw [eq_top_iff]
          intro w _
          have h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤
              (span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}).comap p :=
            span_le.2 fun x hx => subset_span ⟨hpΛ x hx.1, hproj x hx.2⟩
          have h2 : p w ∈ span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4} := h1 (H.span ▸ mem_top)
          have h3 : w = a⁻¹ • p w := Subtype.ext (by
            have : h w v = 0 := w.2
            simp [hp, this, ha0])
          rw [h3]; exact smul_mem _ _ h2 }
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' _ _ hWr H'
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact ⟨Or.inl hvS, hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_add_right _ _))⟩
      | succ i =>
        refine ⟨Or.inr (huS i).1, (huS i).2.trans ?_⟩
        rw [← pow_mul, ← pow_mul, ← mul_assoc]
        exact pow_le_pow_right₀ hB1 (Nat.le_add_left _ _)

end GlobalTheory.SmoothForms
end

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], AnisoSmall E → OrthoSmall E := by
  atlas_forward_decl GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def AlgInf (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

def LieN (V : HSp D) : Type := ∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule

section Inst1

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance (V : HSp D) : NormedRing (AlgInf V) :=
  inferInstanceAs (NormedRing (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

instance (V : HSp D) : NormedAlgebra ℝ (AlgInf V) :=
  inferInstanceAs (NormedAlgebra ℝ (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

instance (V : HSp D) : FiniteDimensional ℝ (AlgInf V) :=
  inferInstanceAs (FiniteDimensional ℝ (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ))

theorem exp_algInf (V : HSp D) (X : AlgInf V) (τ : D.what₂.Tau) :
    (NormedSpace.exp X : AlgInf V) τ = NormedSpace.exp (X τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  @Pi.coe_exp D.what₂.Tau (fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) _ _ _
    (fun _ => FiniteDimensional.complete ℝ _) X τ

end Inst1

section Inst2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance (V : HSp D) : NormedAddCommGroup (LieN V) :=
  inferInstanceAs (NormedAddCommGroup (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule))

instance (V : HSp D) : NormedSpace ℝ (LieN V) :=
  inferInstanceAs (NormedSpace ℝ (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule))

end Inst2

def sigInf (V : HSp D) : AlgInf V →ₗ[ℝ] AlgInf V where
  toFun X := fun τ => (gramAt D V τ)⁻¹ * (X τ)ᴴ * gramAt D V τ
  map_add' X Y := funext fun τ => by
    change _ * (X τ + Y τ)ᴴ * _ = _ * (X τ)ᴴ * _ + _ * (Y τ)ᴴ * _
    rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := funext fun τ => by
    change _ * (c • X τ)ᴴ * _ = c • (_ * (X τ)ᴴ * _)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

def jInf (V : HSp D) : LieN V →ₗ[ℝ] AlgInf V where
  toFun X := fun τ => (X τ).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

def secInf (V : HSp D) (u : AlgInf V) : GA D V :=
  if h : ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ then h.choose else 1

def expInf (V : HSp D) : LieN V → GA D V := expMap (jInf V) (secInf θ V)

variable {θ} {V : HSp D}

theorem unit_iff (R : RealPoints θ V) (u : AlgInf V) :
    sigInf V u * u = 1 ↔ ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  refine funext_iff.trans (forall_congr' fun τ => ?_)
  change (gramAt D V τ)⁻¹ * (u τ)ᴴ * gramAt D V τ * u τ = 1 ↔ (u τ)ᴴ * gramAt D V τ * u τ = gramAt D V τ
  have h := (R.1 τ).2
  constructor
  · intro h1
    have := congrArg (gramAt D V τ * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ h, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc (u τ)ᴴ, h1, nonsing_inv_mul _ h]

theorem secInf_spec (R : RealPoints θ V) {u : AlgInf V} (hu : sigInf V u * u = 1) :
    secInf θ V u ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (secInf θ V u) = u τ := by
  have h := R.2.1 u ((unit_iff R u).1 hu)
  rw [secInf, dif_pos h]
  exact h.choose_spec

theorem isLieData (R : RealPoints θ V) : IsLieData (sigInf V) (jInf V) (secInf θ V) := by
  have anti : ∀ a b, sigInf V (a * b) = sigInf V b * sigInf V a := fun a b => funext fun τ => by
    change _ * (a τ * b τ)ᴴ * _ = (_ * (b τ)ᴴ * _) * (_ * (a τ)ᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ (R.1 τ).2]
  refine ⟨anti, funext fun τ => ?_, fun a => funext fun τ => ?_,
    fun X Y h => funext fun τ => Subtype.ext (congrFun h τ), fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (gramAt D V τ)⁻¹ * (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ (R.1 τ).2]
  · change _ * (_ * (a τ)ᴴ * _)ᴴ * _ = a τ
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, (R.1 τ).1]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ (R.1 τ).2, nonsing_inv_mul _ (R.1 τ).2, mul_one]
  · refine ⟨fun τ => ⟨X τ, ?_⟩, rfl⟩
    have h1 : (gramAt D V τ)⁻¹ * (X τ)ᴴ * gramAt D V τ = -X τ := congrFun h τ
    change (X τ)ᴴ * gramAt D V τ + gramAt D V τ * X τ = 0
    rw [← mul_nonsing_inv_cancel_left _ ((X τ)ᴴ * gramAt D V τ) (R.1 τ).2, ← mul_assoc (gramAt D V τ)⁻¹, h1, mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    funext τ
    have h1 : (Y τ).1ᴴ * gramAt D V τ + gramAt D V τ * (Y τ).1 = 0 := (Y τ).2
    change _ * (Y τ).1ᴴ * _ = -(Y τ).1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ (R.1 τ).2]
  · have hab : sigInf V (a * b) * (a * b) = 1 := by
      rw [anti, mul_assoc, ← mul_assoc (sigInf V a), ha, one_mul, hb]
    refine R.2.2.1 _ (secInf_spec R hab).1 _ (mul_mem (secInf_spec R ha).1 (secInf_spec R hb).1) fun τ => ?_
    rw [R.2.2.2.1, (secInf_spec R hab).2, (secInf_spec R ha).2, (secInf_spec R hb).2]
    rfl

theorem hasLog (R : RealPoints θ V) : HasLog (sigInf V) (jInf V) := GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData R)

theorem exp_mem_UH {n : ℕ} {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : Xᴴ * J + J * X = 0) :
    NormedSpace.exp X ∈ Formalism.QuantumDeterminants.UH J := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isExpFam_expInf (R : RealPoints θ V) : IsExpFam θ V (expInf θ V) := fun X => by
  have h := secInf_spec R (u := NormedSpace.exp (jInf V X)) ((unit_iff R _).2 fun τ => by
    rw [exp_algInf]; exact exp_mem_UH (R.1 τ).2 (X τ).2)
  exact ⟨h.1, fun τ => (h.2 τ).trans (exp_algInf V _ τ)⟩

theorem eq_expInf (R : RealPoints θ V) {e : LieInf V → GA D V} (he : IsExpFam θ V e) : e = expInf θ V :=
  funext fun X => R.2.2.1 _ (he X).1 _ (isExpFam_expInf R X).1 fun τ => by
    rw [(he X).2, (isExpFam_expInf R X).2]

theorem mem_lieAt_iff (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    X ∈ lieAt V τ ↔ X ∈ lieU (gramAt D V τ) := Iff.rfl

theorem oneP_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (t : ℝ) :
    oneP θ V τ X.1 t = expInf θ V (t • atPlace V τ X) := by
  classical
  have h0 := isExpFam_expInf R (t • atPlace V τ X)
  have h1 : IsAtTau θ V τ (NormedSpace.exp (t • X.1)) (expInf θ V (t • atPlace V τ X)) := by
    refine ⟨h0.1, ?_, fun τ' h => ?_⟩
    · rw [h0.2]; simp [atPlace]
    · rw [h0.2]; simp [atPlace, Pi.single_eq_of_ne h]
  have h : ∃ x, IsAtTau θ V τ (NormedSpace.exp (t • X.1)) x := ⟨_, h1⟩
  rw [oneP, atTau, dif_pos h]
  refine R.2.2.1 _ h.choose_spec.1 _ h1.1 fun τ' => ?_
  by_cases c : τ' = τ
  · subst c; rw [h.choose_spec.2.1, h1.2.1]
  · rw [h.choose_spec.2.2 _ c, h1.2.2 _ c]

theorem Rder_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X.1 φ = lieDer V (expInf θ V) (atPlace V τ X) φ := by
  funext g
  simp only [Rder, lieDer, oneP_eq R]

theorem lieDer_eq (X : LieInf V) (φ : GA D V → ℂ) : lieDer V (expInf θ V) X φ = Der (expInf θ V) X φ := rfl

theorem isSmoothInf_iff (φ : GA D V → ℂ) : IsSmoothInf V (expInf θ V) φ ↔ Sm (expInf θ V) φ := Iff.rfl

theorem sum_atPlace (X : LieInf V) : ∑ τ, atPlace V τ (X τ) = X := by
  classical
  convert Finset.univ_sum_single X
  rfl

theorem smooth_iff (R : RealPoints θ V) (φ : GA D V → ℂ) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ↔
    IsSmoothInf V (expInf θ V) φ := by
  have hT : Submodule.span ℝ {Y : LieN V | ∃ τ X, Y = atPlace V τ X} = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have : X = ∑ τ, (atPlace V τ (X τ) : LieN V) := (sum_atPlace X).symm
    rw [this]
    exact sum_mem fun τ _ => Submodule.subset_span ⟨τ, _, rfl⟩
  rw [isSmoothInf_iff, expInf, GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData R) (hasLog R) _ hT]
  constructor
  · intro h k Y hY g
    choose τs Xs hX using hY
    have := h k τs (fun i => (Xs i).1) (fun i => (Xs i).2) g
    simp only [oneP_eq R] at this
    simp only [hX]
    exact this
  · intro h k τs Xs hX g
    have := h k (fun i => atPlace V (τs i) ⟨Xs i, hX i⟩) (fun i => ⟨_, _, rfl⟩) g
    have e : ∀ i t, oneP θ V (τs i) (Xs i) t = expInf θ V (t • atPlace V (τs i) ⟨Xs i, hX i⟩) :=
      fun i t => oneP_eq R (τs i) ⟨Xs i, hX i⟩ t
    simp only [e]
    exact this

abbrev SmF (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) :=
  smSub (expMap (jInf V) (secInf θ V))

def opInf (R : RealPoints θ V) (X : LieInf V) : Module.End ℂ (SmF θ V) := derOp (isLieData R) (hasLog R) X

theorem opInf_coe (R : RealPoints θ V) (X : LieInf V) (φ : SmF θ V) :
    (opInf R X φ).1 = lieDer V (expInf θ V) X φ.1 := rfl

theorem opInf_add (R : RealPoints θ V) (X Y : LieInf V) : opInf R (X + Y) = opInf R X + opInf R Y :=
  derOp_add (isLieData R) (hasLog R) X Y

theorem opAt_add (R : RealPoints θ V) (τ : D.what₂.Tau) (X Y : LieAt V τ) :
    opInf R (atPlace V τ (X + Y)) = opInf R (atPlace V τ X) + opInf R (atPlace V τ Y) := by
  classical
  rw [← opInf_add, atPlace, Pi.single_add]; rfl

theorem opAt_smul (R : RealPoints θ V) (τ : D.what₂.Tau) (c : ℝ) (X : LieAt V τ) :
    opInf R (atPlace V τ (c • X)) = (c : ℂ) • opInf R (atPlace V τ X) := by
  classical
  rw [atPlace, Pi.single_smul]; exact derOp_smul (isLieData R) (hasLog R) c _

theorem opAt_bracket (R : RealPoints θ V) (τ : D.what₂.Tau) (X Y Z : LieAt V τ) (h : Z.1 = X.1 * Y.1 - Y.1 * X.1) :
    opInf R (atPlace V τ Z) = opInf R (atPlace V τ X) * opInf R (atPlace V τ Y) -
      opInf R (atPlace V τ Y) * opInf R (atPlace V τ X) := by
  classical
  refine derOp_bracket (isLieData R) (hasLog R) _ _ _ (funext fun τ' => ?_)
  change (atPlace V τ Z τ').1 = (atPlace V τ X τ').1 * (atPlace V τ Y τ').1 - (atPlace V τ Y τ').1 * (atPlace V τ X τ').1
  by_cases c : τ' = τ
  · subst c; simpa [atPlace] using h
  · simp [atPlace, Pi.single_eq_of_ne c]

theorem opAt_comm (R : RealPoints θ V) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (X : LieAt V τ) (Y : LieAt V τ') :
    Commute (opInf R (atPlace V τ X)) (opInf R (atPlace V τ' Y)) := by
  classical
  have := derOp_bracket (isLieData R) (hasLog R) (atPlace V τ X) (atPlace V τ' Y) 0 (funext fun ρ => by
    change (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (atPlace V τ X ρ).1 * (atPlace V τ' Y ρ).1 -
      (atPlace V τ' Y ρ).1 * (atPlace V τ X ρ).1
    by_cases c : ρ = τ
    · subst c; simp [atPlace, Pi.single_eq_of_ne h]
    · simp [atPlace, Pi.single_eq_of_ne c])
  rw [derOp_zero] at this
  exact sub_eq_zero.1 this.symm

theorem wordDer_eq (R : RealPoints θ V) (l : List (LieInf V)) (φ : SmF θ V) :
    wordDer V (expInf θ V) l φ.1 = ((l.map (opInf R)).prod φ).1 := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, opInf_coe, ← ih]; rfl

theorem exists_envRep (R : RealPoints θ V) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (SmF θ V),
    ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = opInf R (atPlace V τ X) :=
  GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra _ _ _ (fun X => opInf R (atPlace V τ X)) (opAt_add R τ) (opAt_smul R τ) (opAt_bracket R τ)

def envRep (R : RealPoints θ V) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (SmF θ V) := (exists_envRep R τ).choose

theorem envRep_ι (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) :
    envRep R τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = opInf R (atPlace V τ X) :=
  (exists_envRep R τ).choose_spec X

theorem envRep_envOf (R : RealPoints θ V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) :
    envRep R τ (envOf V τ w) = w.sum fun l c => c • ((l.map (atPlace V τ)).map (opInf R)).prod := by
  rw [envOf, map_finsuppSum]
  refine Finsupp.sum_congr fun l _ => ?_
  rw [map_smul, map_list_prod, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun X _ => envRep_ι R τ X

theorem envDer_eq (R : RealPoints θ V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : SmF θ V) :
    envDer V (expInf θ V) τ w φ.1 = (envRep R τ (envOf V τ w) φ).1 := by
  unfold envDer
  rw [envRep_envOf, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordDer_eq R]; rfl

theorem envRep_comm (R : RealPoints θ V) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (u : EnvAt V τ) (u' : EnvAt V τ') :
    Commute (envRep R τ u) (envRep R τ' u') := by
  obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
  obtain ⟨w', rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ' u'
  rw [envRep_envOf, envRep_envOf]
  refine Commute.sum_left _ _ _ fun l _ => Commute.sum_right _ _ _ fun l' _ => Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.list_prod_left _ _ fun a ha => Commute.list_prod_right _ _ fun b hb => ?_
  simp only [List.mem_map] at ha hb
  obtain ⟨_, ⟨X, -, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨Y, -, rfl⟩, rfl⟩ := hb
  exact opAt_comm R h X Y

theorem foldr_ofFn_eq {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (k : ℕ) :
    ∀ (f : Fin k → M → M) (a : Fin k → Module.End ℂ S), (∀ i (x : S), f i x.1 = (a i x).1) → ∀ x : S,
      (List.ofFn f).foldr (fun f acc => f acc) x.1 = ((List.ofFn a).prod x).1 := by
  induction k with
  | zero => intro f a _ x; simp
  | succ k ih =>
    intro f a h x
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply,
      ih _ _ (fun i => h i.succ), h]

theorem exists_gelf (R : RealPoints θ V) (τ : D.what₂.Tau) : ∃ c : ℕ → EnvAt V τ,
    Subalgebra.center ℂ (EnvAt V τ) = Algebra.adjoin ℂ (Set.range c) ∧
      ∀ k (φ : SmF θ V), gelf θ V τ k φ.1 = (envRep R τ (c k) φ).1 := by
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  obtain ⟨h1, h2⟩ := h (EnvAt V τ) (fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add])
    (fun c X => by
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul])
  refine ⟨_, center_eq_adjoin h1 (eq_top_iff.2 fun u _ => ?_), fun k φ => ?_⟩
  · obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
    refine Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (Subalgebra.list_prod_mem _ fun x hx => ?_) _
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
    exact Algebra.span_le_adjoin ℂ _ (h2 X)
  · rw [gelf, gelfA, map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [map_list_prod, List.map_ofFn]
    refine foldr_ofFn_eq _ _ _ _ (fun i x => ?_) φ
    simp only [Function.comp, map_add, map_smul, envRep_ι]
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl

theorem zfin_iff (R : RealPoints θ V) {φ : GA D V → ℂ} (hφ : IsSmoothInf V (expInf θ V) φ) :
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) ↔
      ∀ τ, IsZFiniteAt V (expInf θ V) τ φ := by
  choose c hc hg using exists_gelf R
  let ψ : SmF θ V := ⟨φ, hφ⟩
  constructor
  · rintro ⟨W, hW, hm, hs⟩ τ
    have key : ∀ z ∈ Algebra.adjoin ℂ (Set.range (c τ)), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
      | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
      | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
      | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
    refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    rw [show φ = ψ.1 from rfl, envDer_eq R]
    exact key _ (hc τ ▸ hw) ψ hm
  · intro h
    obtain ⟨W, hW, hm, hs⟩ := GlobalTheory.T.commuting_algebras_finite_span (SmF θ V) D.what₂.Tau
      (fun τ => (Subalgebra.center ℂ (EnvAt V τ)).map (envRep R τ))
      (by
        rintro τ τ' hne _ ⟨u, -, rfl⟩ _ ⟨u', -, rfl⟩
        exact envRep_comm R hne u u') ψ
      (fun τ => by
        have := h τ
        unfold IsZFiniteAt at this
        refine FiniteDimensional.of_injective ((SmF θ V).subtype.restrict (q := Submodule.span ℂ {ψ : GA D V → ℂ |
          ∃ w : List (LieAt V τ) →₀ ℂ, envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ) ∧
            ψ = envDer V (expInf θ V) τ w φ}) fun x hx => ?_) fun x y hxy => ?_
        · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (SmF θ V).subtype _)).2 ?_ hx)
          rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
          obtain ⟨w, rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
          exact Submodule.subset_span ⟨w, hu, (envDer_eq R τ w ψ).symm⟩
        · have h' := congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext h'))
    refine ⟨W.map (SmF θ V).subtype, inferInstance, ⟨ψ, hm, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    refine ⟨_, hs τ _ ⟨c τ k, ?_, rfl⟩ f hf, (hg τ k f).symm⟩
    rw [hc]
    exact Algebra.subset_adjoin ⟨k, rfl⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf; positivity

theorem reduction (hθ : IsInfFam θ) (R : RealPoints θ V) (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) :
    ∃ (S : Finset (GA D V)) (C : ℝ) (M : ℕ), ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧
      γ * g = x * a * k ∧ normInf θ V a ≤ C * (height θ V g : ℝ) ^ M := by
  obtain ⟨d, C, M, hd, h⟩ := GlobalTheory.T.unitary_reduction_polynomial_height_bound D θ V hθ
    (GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths _ (GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector _ (GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame _ (GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM _)))) (GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof D θ V)
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator D V U hU d hd
  obtain ⟨hm, C', hC'⟩ := GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V
  obtain ⟨-, -, -, r4, r5, r6, r7, r8⟩ := R
  refine ⟨S, C * C', M + 1, fun g => ?_⟩
  obtain ⟨γ, hγ, h1, h2⟩ := h g
  obtain ⟨k, hk, a, ha, e⟩ := r7 (γ * g)
  have e' : (γ * g)⁻¹ = k⁻¹ * a⁻¹ := by rw [e, ← r6 a ha k hk, _root_.mul_inv_rev]
  obtain ⟨x, hx, h3, h4⟩ := hS k hk fun i j => by
    have := h1 i j
    rwa [e', e, r8 _ _ ha, r8 _ _ (inv_mem ha)] at this
  refine ⟨γ, hγ, x, hx, a, ha, _, h3, h4, ?_, ?_⟩
  · rw [mul_assoc, r6 a ha _ h4, e, ← mul_assoc, mul_inv_cancel_left]
  · have h5 : normInf θ V a = normInf θ V (γ * g) := by
      unfold normInf
      rw [e', e]
      simp only [r4, r5 k hk, r5 _ (inv_mem hk), one_mul]
    rw [h5]
    refine (hm γ g).trans ((mul_le_mul h2 (hC' g) (normInf_nonneg g) ((normInf_nonneg γ).trans h2)).trans_eq ?_)
    ring

theorem wordDer_left (e : LieInf V → GA D V) {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (l : List (LieInf V)) : ∀ g, wordDer V e l φ (γ * g) = wordDer V e l φ g := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    intro g
    change lieDer V e X (wordDer V e l φ) _ = lieDer V e X (wordDer V e l φ) _
    simp only [lieDer, mul_assoc, ih]

theorem wordDer_right (R : RealPoints θ V) {φ : GA D V → ℂ} {k : GA D V} (hk : k ∈ GfC V) (h : ∀ g, φ (g * k) = φ g)
    (l : List (LieInf V)) : ∀ g, wordDer V (expInf θ V) l φ (g * k) = wordDer V (expInf θ V) l φ g := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    intro g
    change lieDer V _ X (wordDer V _ l φ) _ = lieDer V _ X (wordDer V _ l φ) _
    unfold lieDer
    congr 1
    funext t
    rw [mul_assoc, ← R.2.2.2.2.2.1 _ (isExpFam_expInf R _).1 k hk, ← mul_assoc, ih]

theorem foldr_Rder_eq (R : RealPoints θ V) (l : List (Σ τ, LieAt V τ)) (φ : GA D V → ℂ) :
    (l.map fun p => (p.1, p.2.1)).foldr (fun p f => Rder θ V p.1 p.2 f) φ =
      wordDer V (expInf θ V) (l.map fun p => atPlace V p.1 p.2) φ := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.map_cons, List.foldr_cons, ih, Rder_eq R]; rfl

theorem exists_sigma_list (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∃ l' : List (Σ τ, LieAt V τ), l = l'.map fun p => (p.1, p.2.1) := by
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons p l ih =>
    intro h
    obtain ⟨l', rfl⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    exact ⟨⟨p.1, ⟨p.2, h p List.mem_cons_self⟩⟩ :: l', rfl⟩

theorem word_mem_closure (R : RealPoints θ V) (l : List (LieInf V)) : (l.map (opInf R)).prod ∈
    AddSubmonoid.closure (Set.range fun l' : List (Σ τ, LieAt V τ) =>
      ((l'.map fun p => atPlace V p.1 p.2).map (opInf R)).prod) := by
  induction l with
  | nil => exact AddSubmonoid.subset_closure ⟨[], rfl⟩
  | cons X l ih =>
    have e : opInf R X = ∑ τ, opInf R (atPlace V τ (X τ)) := by
      conv_lhs => rw [← sum_atPlace X]
      exact map_sum (AddMonoidHom.mk' (opInf R) (opInf_add R)) _ _
    rw [List.map_cons, List.prod_cons, e, Finset.sum_mul]
    refine sum_mem fun τ _ => ?_
    generalize (l.map (opInf R)).prod = y at ih
    induction ih using AddSubmonoid.closure_induction with
    | mem y hy => obtain ⟨l', rfl⟩ := hy; exact AddSubmonoid.subset_closure ⟨⟨τ, X τ⟩ :: l', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz

theorem growth_iff (hθ : IsInfFam θ) (R : RealPoints θ V) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hφ : IsSmoothInf V (expInf θ V) φ) :
    (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) ↔
      IsUnifModerate θ V (expInf θ V) φ := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨U, hU, hUφ⟩ := ha.level
    obtain ⟨S, C₀, M, hS⟩ := reduction hθ R U hU
    let ψ : SmF θ V := ⟨φ, hφ⟩
    refine ⟨M * N, fun l => ?_⟩
    rw [show φ = ψ.1 from rfl, wordDer_eq R]
    have hl := word_mem_closure R l
    generalize (l.map (opInf R)).prod = y at hl
    induction hl using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨l', rfl⟩ := hy
      have h1 := hN (l'.map fun p => (p.1, p.2.1)) fun p hp => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact q.2.2
      rw [foldr_Rder_eq R] at h1
      choose C hC using h1
      refine ⟨(∑ x ∈ S, |C x|) * C₀ ^ N, fun g => ?_⟩
      obtain ⟨γ, hγ, x, hx, a, ha', k, hk, hk', e, hb⟩ := hS g
      beta_reduce
      rw [← wordDer_eq R, show ψ.1 = φ from rfl, ← wordDer_left (expInf θ V) (ha.left γ hγ) _ g, e, wordDer_right R hk' (hUφ k hk hk'), pow_mul, mul_assoc,
        ← mul_pow]
      refine (hC x a ha').trans (mul_le_mul ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))
        (pow_le_pow_left₀ (normInf_nonneg a) hb N) (pow_nonneg (normInf_nonneg a) N)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    | zero => exact ⟨0, fun g => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨C₁, h₁⟩ := hy
      obtain ⟨C₂, h₂⟩ := hz
      exact ⟨C₁ + C₂, fun g => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (h₁ g) (h₂ g))⟩
  · rintro ⟨N, hN⟩
    obtain ⟨M, hM⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ V
    have key : ∀ ψ : GA D V → ℂ, (∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖ψ (x * g)‖ ≤ C * normInf θ V g ^ (M * N) := by
      rintro ψ ⟨C, hC⟩ x
      obtain ⟨C', hC'⟩ := hM x
      refine ⟨|C| * C' ^ N, fun g hg => (hC _).trans ?_⟩
      rw [pow_mul, mul_assoc, ← mul_pow]
      exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
        (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)
    refine ⟨M * N, fun l hl => key _ ?_⟩
    obtain ⟨l', hl'⟩ := exists_sigma_list l hl
    rw [hl', foldr_Rder_eq R]
    exact hN _

theorem isAutFunSm_iff (hθ : IsInfFam θ) (V : HSp D) (φ : GA D V → ℂ) : IsAutFunSm θ V φ ↔ IsSmoothAutForm V φ := by
  obtain ⟨hu, hR⟩ := GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D
  have R := hR θ hθ V
  constructor
  · intro h
    have hs := (smooth_iff R φ).1 h.smooth
    refine ⟨h.toIsAutFun, ⟨θ, hθ⟩, fun θ' hθ' => ?_⟩
    obtain rfl := hu θ θ' hθ hθ'
    refine ⟨⟨_, isExpFam_expInf R⟩, fun e he => ?_⟩
    obtain rfl := eq_expInf R he
    exact ⟨hs, (zfin_iff R hs).1 h.zfin, (growth_iff hθ R h.toIsAutFun hs).1 h.growth⟩
  · rintro ⟨ha, -, h⟩
    obtain ⟨hs, hz, hg⟩ := (h θ hθ).2 _ (isExpFam_expInf R)
    exact ⟨ha, (smooth_iff R φ).2 hs, (zfin_iff R hs).2 hz, (growth_iff hθ R ha hs).2 hg⟩

variable {X : ThetaX D}

theorem afTiedSm_iff (T : ThetaTied D X) : ThetaSmoothnessCondition T ↔
    ∀ V : HSp D, V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ := by
  constructor
  · rintro ⟨⟨θ, hθ⟩, h⟩ V hV φ
    rw [← isAutFunSm_iff hθ]
    exact Set.ext_iff.1 (h θ hθ V hV) φ
  · intro h
    exact ⟨T.actR.1, fun θ hθ V hV => Set.ext fun φ => (h V hV φ).trans (isAutFunSm_iff hθ V φ).symm⟩

theorem compare (D : D7) :
    (∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, (∃! e, IsExpFam θ V e) ∧ ∀ e, IsExpFam θ V e →
      (∀ τ, lieAt V τ = lieU (gramAt D V τ)) ∧
      (∀ τ (Y : LieAt V τ) t, oneP θ V τ Y.1 t = e (t • atPlace V τ Y)) ∧
      (∀ τ (Y : LieAt V τ) φ, Rder θ V τ Y.1 φ = lieDer V e (atPlace V τ Y) φ) ∧
      (∀ τ, ∃ c : ℕ → List (LieAt V τ) →₀ ℂ,
        Subalgebra.center ℂ (EnvAt V τ) = Algebra.adjoin ℂ (Set.range fun k => envOf V τ (c k)) ∧
        ∀ k φ, IsSmoothInf V e φ → gelf θ V τ k φ = envDer V e τ (c k) φ) ∧
      (∀ φ : GA D V → ℂ, (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
        (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
          ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ↔
        IsSmoothInf V e φ) ∧
      (∀ φ, IsSmoothInf V e φ →
        ((∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) ↔
          ∀ τ, IsZFiniteAt V e τ φ)) ∧
      (∀ φ, IsAutFun V φ → IsSmoothInf V e φ →
        ((∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
          ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
            ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) ↔
          IsUnifModerate θ V e φ))) ∧
    (∀ θ, IsInfFam (D := D) θ → ∀ (V : HSp D) φ, IsAutFunSm θ V φ ↔ IsSmoothAutForm V φ) ∧
    ∀ (X : ThetaX D) (T : ThetaTied D X),
      (ThetaSmoothnessCondition T ↔ ∀ V : HSp D, V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ) ∧
      (FormsTied T ↔ ThetaSmoothnessCondition T ∧
        ∀ V : HSp D, ¬ V.SigOK → ∀ φ : GA D V → ℂ, (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ) := by
  refine ⟨fun θ hθ V => ?_, fun θ hθ => isAutFunSm_iff hθ, fun X T => ⟨afTiedSm_iff T, ?_⟩⟩
  · have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
    refine ⟨⟨_, isExpFam_expInf R, fun e he => eq_expInf R he⟩, fun e he => ?_⟩
    obtain rfl := eq_expInf R he
    refine ⟨fun _ => rfl, oneP_eq R, Rder_eq R, fun τ => ?_, smooth_iff R, fun φ => zfin_iff R,
      fun φ => growth_iff hθ R⟩
    obtain ⟨c, h1, h2⟩ := exists_gelf R τ
    choose w hw using fun k => GlobalTheory.T.enveloping_map_surjective D V τ (c k)
    refine ⟨w, by simpa only [hw] using h1, fun k φ hφ => ?_⟩
    exact (h2 k ⟨φ, hφ⟩).trans (by rw [← hw]; exact (envDer_eq R τ (w k) ⟨φ, hφ⟩).symm)
  · rw [afTiedSm_iff]
    exact ⟨fun h => ⟨fun V _ => h V, fun V _ => h V⟩, fun h V => (em V.SigOK).elim (h.1 V) (h.2 V)⟩

end GlobalTheory.SmoothForms

end
end
