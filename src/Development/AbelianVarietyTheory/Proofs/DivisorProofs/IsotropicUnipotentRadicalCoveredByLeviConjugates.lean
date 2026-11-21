import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRational
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentFrameCoords_of_mem_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  first | exact @GlobalTheory.SphEis.exists_crd_of_mem_unipRad | exact GlobalTheory.SphEis.exists_crd_of_mem_unipRad | (intros; apply GlobalTheory.SphEis.exists_crd_of_mem_unipRad <;> assumption)
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentRadical_point_with_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  first | exact @GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | exact GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | (intros; apply GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd <;> assumption)
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_coordinates_groupLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  first | exact @GlobalTheory.SphEis.crd_law | exact GlobalTheory.SphEis.crd_law | (intros; apply GlobalTheory.SphEis.crd_law <;> assumption)
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_crd_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u b₀ c₀ h
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    unfold adMat
    exact Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* _))
  have hadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X + Y) = adMat F X + adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  have hsub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X - Y) = adMat F X - adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  refine GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF u C
    (D - Z * (J₀⁻¹ * cT (σ : E →+* E) b₀) + C * c₀) (Z + C * b₀) h.onC ?_ ?_
  · rw [h.onZ, hadd, hmul]
  · rw [h.onD, hadd, hsub, hmul, hmul, hmul]
    rfl

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rationalPoints_of_unipotentCoords_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  atlas_forward_decl GlobalTheory.SphEis.mem_ratPts_of_crd_rat
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isCompact_of_crd_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun p =>
    adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)
  have key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c) := by
    intro u b c h
    have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
        adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
      have := congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum
      simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
    calc (matHom _ σ J u).1 = (matHom _ σ J u).1 * 1 := (Matrix.mul_one _).symm
      _ = Φ (b, c) := by
        rw [← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z),
          ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]
  have hsig := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1 := continuous_fst
    have h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2 := continuous_snd
    have hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1 :=
      continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose
    exact ((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))
  have hadj : Continuous (adjA σ J) := by
    have : Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X :=
      (continuous_id.matrix_map hsig).matrix_transpose
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  let S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)
  let ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))
  have hψ : Continuous ψ := hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))
  have hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)
  refine ⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩
  intro u b c h hb hc
  refine ⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩
  have e1 := key u b c h
  have e2 := adjA_mat hFr.herm u
  simp only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompact_of_unipotentCoordinates_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  atlas_forward_decl GlobalTheory.SphEis.exists_isCompact_of_crd_mem
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem cover_rect_adMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  intro F E _ _ _ _ _ σ hσ j m
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.GodementSectionReduction.cover_adele F E σ hσ
  choose Y hY h using h
  refine ⟨Ω, (C ^ m) ^ j, hΩ, fun μ =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i)).card = ∏ i, (Y (μ i)).card ^ m := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (μ i)) m).trans (le_of_eq ?_)
    simp only [bse, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul _ (μ _), mul_comm m]
  · choose x₀ y hy ω hω e using fun i k => h (μ i) (x i k)
    refine ⟨Matrix.of x₀, Matrix.of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), Matrix.of ω,
      fun i k => hω i k, ?_⟩
    ext i k
    rw [Matrix.add_apply, Matrix.add_apply, ← add_assoc]
    simp only [tor, GlobalTheory.Eis.Conv.dg, Matrix.diagonal_mul, adMat, Matrix.map_apply, Matrix.of_apply, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact e i k

end GlobalTheory.SphEis

end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_rectangularAdelicMatrices_shrunkCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  atlas_forward_decl GlobalTheory.SphEis.cover_rect_adMat
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SkewAdCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, sig_sig σ h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

theorem sigR_alg (σ : E →ₐ[F] E) (c : F) :
    sigR (AF F) σ (algebraMap F (AF F ⊗[F] E) c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ).commutes c

theorem inclR_alg (c : F) : inclR (F := F) (AF F) (algebraMap F E c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes c

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem cT_apply {A : Type} [CommRing A] (s : A →+* A) {m p : Type} (M : Matrix m p A) (i : p) (k : m) :
    cT s M i k = s (M k i) := rfl

theorem cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (j : ℕ) : ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  classical
  haveI := hσ.1
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hσ _ _ _ hΩ₀ hcov j
  set s := sigR (AF F) σ with hs_def
  set hh : AF F ⊗[F] E := algebraMap F (AF F ⊗[F] E) 2⁻¹ with hh_def
  have h2 : hh * 2 = 1 := by
    rw [hh_def, ← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hsh : s hh = hh := sigR_alg σ _
  have hss : ∀ z, s (s z) = z := sigR_sigR σ hσ
  have hsi : ∀ e, s (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := sigR_inclR σ
  let sk : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    fun z => Matrix.of fun i k => hh * (z i k - s (z k i))
  have sk_skew : ∀ z, cT s (sk z) = -sk z := fun z => by
    ext i k
    simp only [cT_apply, sk, Matrix.of_apply, Matrix.neg_apply, map_mul, map_sub, hsh, hss]
    ring
  have hcont : Continuous fun p : (AF F ⊗[F] E) × (AF F ⊗[F] E) => hh * (p.1 - s p.2) :=
    continuous_const.mul (continuous_fst.sub ((continuous_sigR σ).comp continuous_snd))
  refine ⟨_, C, (hΩ.prod hΩ).image hcont, fun μ => ?_⟩
  obtain ⟨Y, hY, hc⟩ := h μ
  have hd : ∀ i, s ((GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i) = (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := fun i => by
    rw [map_pow, hs_def, GlobalTheory.Eis.Conv.sigR_halfE]
  have htor : (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    simp [tor, GlobalTheory.Eis.Conv.dg]
  have htor' : cT s (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    rw [htor]
    ext i k
    rw [cT_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik; simp [hd]
    · simp [hik, Ne.symm hik]
  refine ⟨Y.image sk, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)), ?_, fun x hx => ?_⟩
  · simp only [bse, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact sk_skew z
  · obtain ⟨S₀, y, hy, ω, hω, e⟩ := hc x hx
    set c : E := algebraMap F E 2⁻¹ with hc_def
    have hσc : σ c = c := σ.commutes _
    refine ⟨Matrix.of fun i k => c * (S₀ i k - σ (S₀ k i)), ?_, sk y, Finset.mem_image_of_mem _ hy, sk ω, sk_skew ω,
      fun i k => ⟨(ω i k, ω k i), ⟨hω i k, hω k i⟩, rfl⟩, ?_⟩
    · ext i k
      simp only [cT_apply, Matrix.of_apply, Matrix.neg_apply, AlgHom.coe_toRingHom, map_mul, map_sub, hσc,
        sig_sig σ hσ]
      ring
    · rw [htor', htor]
      ext i k
      have hx1 : s (x k i) = - x i k := by
        have := congrFun (congrFun hx i) k
        rwa [cT_apply, Matrix.neg_apply] at this
      have e1 := congrFun (congrFun e i) k
      have e2 := congrArg s (congrFun (congrFun e k) i)
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_add, map_mul,
        hsi, hd] at e1 e2
      rw [hx1] at e2
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adMat, Matrix.map_apply,
        Matrix.of_apply, sk, map_mul, map_sub, inclR_alg]
      rw [hc_def, inclR_alg, ← hh_def]
      linear_combination hh * e1 - hh * e2 - x i k * h2
end GlobalTheory.SkewAdCover
end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  atlas_forward_decl GlobalTheory.SkewAdCover.cover
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.SphericalEisensteinCover

theorem isCompact_entries {A : Type} [TopologicalSpace A] (a b : ℕ) {Ω : Set A} (hΩ : IsCompact Ω) :
    IsCompact {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} := by
  have e : {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} =
      (Set.univ.pi fun _ => Set.univ.pi fun _ => Ω : Set (Matrix (Fin a) (Fin b) A)) :=
    Set.ext fun ω => ⟨fun h i _ k _ => h i k, fun h i k => h i trivial k trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ

variable {k A : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A] (s : A →+* A)

theorem cT_add {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M + N) = cT s M + cT s N := by
  ext; simp [cT]

theorem cT_neg {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (-M) = -cT s M := by
  ext; simp [cT]

theorem cT_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M - N) = cT s M - cT s N := by
  ext; simp [cT]

theorem cT_smul (hk : ∀ (c : k) x, s (c • x) = c • s x) {a b : ℕ} (c : k) (M : Matrix (Fin a) (Fin b) A) :
    cT s (c • M) = c • cT s M := by
  ext; simp [cT, hk]

theorem cT_cT (hs : ∀ x, s (s x) = x) {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (cT s M) = M := by
  ext; simp [cT, hs]

variable {j m : ℕ} (K : Matrix (Fin m) (Fin m) A)

theorem cT_pair (hs : ∀ x, s (s x) = x) (hK : cT s K = K) (u v : Matrix (Fin j) (Fin m) A) :
    cT s (u * (K * cT s v)) = v * (K * cT s u) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT s hs, hK, Matrix.mul_assoc]

theorem skew_rest (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (X y p : Matrix (Fin j) (Fin m) A) (c : Matrix (Fin j) (Fin j) A)
    (hc : c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p))) = 0) :
    cT s (c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) =
    -(c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) := by
  have hcc : cT s c = -c - (X + (y + p)) * (K * cT s (X + (y + p))) := by
    calc cT s c = (c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p)))) - c - (X + (y + p)) * (K * cT s (X + (y + p))) := by abel
      _ = _ := by rw [hc]; abel
  simp only [cT_add, cT_sub, cT_smul s hk, cT_pair s K hs hK, hcc]
  simp only [cT_add, cT_pair s K hs hK, Matrix.mul_add, Matrix.add_mul, smul_add, neg_add, sub_eq_add_neg]
  module

theorem rel_half (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (b : Matrix (Fin j) (Fin m) A) (z : Matrix (Fin j) (Fin j) A) (hz : cT s z = -z) :
    (z - (2⁻¹ : k) • (b * (K * cT s b))) + cT s (z - (2⁻¹ : k) • (b * (K * cT s b))) + b * (K * cT s b) = 0 := by
  rw [cT_sub, cT_smul s hk, cT_pair s K hs hK, hz]
  module

theorem final_eq (X y p : Matrix (Fin j) (Fin m) A) (c r z ws : Matrix (Fin j) (Fin j) A)
    (hR : c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p) = r + (z + ws)) :
    (-((2⁻¹ : k) • (X * (K * cT s X))) - r) + c - (-X) * (K * cT s (X + (y + p))) =
      (z - (2⁻¹ : k) • (y * (K * cT s y))) + (ws - (2⁻¹ : k) • (p * (K * cT s p))) - y * (K * cT s p) := by
  have h := sub_eq_zero.2 hR
  rw [← sub_eq_zero]
  rw [← h, Matrix.neg_mul]
  module

end GlobalTheory.SphEis.SphericalEisensteinCover

namespace GlobalTheory.SphEis

open GlobalTheory.SphEis.SphericalEisensteinCover in

theorem cover_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr lv hlv
  classical
  have hcm := hFr.cm
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hcm x)
  have hk : ∀ (c : F) x, sigR (AF F) σ (c • x) = c • sigR (AF F) σ x := fun c x =>
    map_smul (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) c x
  have hsc : Continuous (sigR (AF F) σ) := by
    have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => rfl
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _

  have hJ₀ : cT (σ : E →+* E) J₀ = J₀ := Matrix.ext fun i k => hFr.herm₀.1 i k
  have hJ₀i : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
    have hu : IsUnit J₀.det := IsUnit.mk0 _ hFr.herm₀.2
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ₀]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  have hK : cT (sigR (AF F) σ) (adMat F J₀⁻¹) = adMat F J₀⁻¹ := congrArg (adMat F) hJ₀i

  set K : Matrix (Fin m) (Fin m) (AF F ⊗[F] E) := adMat F J₀⁻¹ with hKdef
  have hplus : ∀ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), plus σ J₀ b = K * cT (sigR (AF F) σ) b := fun b => rfl
  obtain ⟨Ω₁, B₁, hΩ₁, hrect⟩ := GlobalTheory.T.cover_rectangularAdelicMatrices_shrunkCompact F E σ hcm j m
  obtain ⟨Ω₂, B₂, hΩ₂, hskew⟩ := GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact F E σ hcm j
  set S₁ : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₁} with hS₁
  set S₂ : Set (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₂} with hS₂
  have hS₁c : IsCompact S₁ := isCompact_entries j m hΩ₁
  have hS₂c : IsCompact S₂ := isCompact_entries j j hΩ₂
  have hcont : ∀ i k, Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k := fun i k => by
    have h1 : Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        q.1 * (K * cT (sigR (AF F) σ) q.1) :=
      continuous_fst.matrix_mul (continuous_const.matrix_mul (continuous_fst.matrix_map hsc).matrix_transpose)
    have hsm : Continuous fun x : AF F ⊗[F] E => (2⁻¹ : F) • x := by
      simp only [Algebra.smul_def]; exact continuous_const.mul continuous_id
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    exact ((continuous_apply_apply i k).comp continuous_snd).sub (hsm.comp (h1.matrix_elem i k))
  set Ω₃ : Set (AF F ⊗[F] E) := Ω₁ ∪ ⋃ (i : Fin j) (k : Fin j),
    (fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k) '' (S₁ ×ˢ S₂) with hΩ₃
  have hΩ₃c : IsCompact Ω₃ :=
    hΩ₁.union (isCompact_iUnion fun i => isCompact_iUnion fun k => (hS₁c.prod hS₂c).image (hcont i k))
  obtain ⟨V, hV, hVmem⟩ := GlobalTheory.T.exists_isCompact_of_unipotentCoordinates_mem F E σ n J j m C D Z J₀ hFr Ω₃ hΩ₃c
  refine ⟨V, B₁ * B₂, hV, fun μ => ?_⟩

  obtain ⟨Y₁, hY₁, hcov₁⟩ := hrect μ
  obtain ⟨Y₂, hY₂, hY₂sk, hcov₂⟩ := hskew μ
  have crd2 := GlobalTheory.T.exists_unipotentRadical_point_with_coords F E σ n J j m C D Z J₀ hFr
  have hrel : ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (z : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) z = -z →
      (z - (2⁻¹ : F) • (b * plus σ J₀ b)) + cT (sigR (AF F) σ) (z - (2⁻¹ : F) • (b * plus σ J₀ b)) +
        b * plus σ J₀ b = 0 :=
    fun b z hz => rel_half (sigR (AF F) σ) K hs hk hK b z hz
  let f : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → GAd σ J := fun q =>
    if hq : cT (sigR (AF F) σ) q.2 = -q.2 then Classical.choose (crd2 q.1 _ (hrel q.1 q.2 hq)) else 1
  have hf : ∀ b z, cT (sigR (AF F) σ) z = -z → f (b, z) ∈ unipRad σ J C ∧
      Crd σ J C D Z J₀ (f (b, z)) b (z - (2⁻¹ : F) • (b * plus σ J₀ b)) := by
    intro b z hz
    simp only [f, dif_pos hz]
    exact Classical.choose_spec (crd2 b _ (hrel b z hz))
  refine ⟨(Y₁ ×ˢ Y₂).image f, ?_, ?_, fun u hu => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul hY₁ hY₂ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hY₁)).trans (le_of_eq ?_)
    simp only [add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  · intro y hy
    obtain ⟨⟨b, z⟩, hq, rfl⟩ := Finset.mem_image.1 hy
    exact (hf b z (hY₂sk z (Finset.mem_product.1 hq).2)).1
  obtain ⟨b, c, hbc, hcond⟩ := GlobalTheory.T.exists_unipotentFrameCoords_of_mem_isotropicUnipotentRadical F E σ n J j m C D Z J₀ hFr u hu
  obtain ⟨x₀, y, hy, ω, hω, hb⟩ := hcov₁ b
  set t := tor F E fun i => (μ i : ℤ) with ht
  have hcond' : c + cT (sigR (AF F) σ) c + (adMat F x₀ + (y + t.1 * ω)) *
      (K * cT (sigR (AF F) σ) (adMat F x₀ + (y + t.1 * ω))) = 0 := by
    rw [← hb]; exact hcond
  have hRsk := skew_rest (sigR (AF F) σ) K hs hk hK (adMat F x₀) y (t.1 * ω) c hcond'
  obtain ⟨x₁, hx₁, z, hz, ωs, hωs, hωsΩ, hR⟩ := hcov₂ _ hRsk

  let c₀ : Matrix (Fin j) (Fin j) E := -((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) - x₁
  have hneg : adMat F (-x₀) = -adMat F x₀ := by ext; simp
  have hc₀ : adMat F c₀ = -((2⁻¹ : F) • (adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)))) - adMat F x₁ := by
    have e1 : adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) = adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)) := by
      simp only [adMat, Matrix.map_mul]; rfl
    have e2 : adMat F ((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) =
        (2⁻¹ : F) • adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) :=
      Matrix.map_smul _ _ (fun a => map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (2⁻¹ : F) a) _
    have e3 : ∀ P Q : Matrix (Fin j) (Fin j) E, adMat F (P - Q) = adMat F P - adMat F Q := fun P Q => by ext; simp
    have e4 : ∀ P : Matrix (Fin j) (Fin j) E, adMat F (-P) = -adMat F P := fun P => by ext; simp
    simp only [c₀]
    rw [e3, e4, e2, e1]
  have hx₁' : cT (sigR (AF F) σ) (adMat F x₁) = -adMat F x₁ := by
    show adMat F (cT (σ : E →+* E) x₁) = _
    rw [hx₁]; ext; simp
  have hγrel : adMat F c₀ + cT (sigR (AF F) σ) (adMat F c₀) + adMat F (-x₀) * plus σ J₀ (adMat F (-x₀)) = 0 := by
    rw [hc₀, hneg, hplus]
    simp only [cT_sub, cT_neg, cT_smul _ hk, cT_pair _ K hs hK, hx₁', Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    module
  obtain ⟨γ, hγU, hγC⟩ := crd2 (adMat F (-x₀)) (adMat F c₀) hγrel
  have hγrat := GlobalTheory.T.mem_rationalPoints_of_unipotentCoords_rational F E σ n J j m C D Z J₀ hFr γ (-x₀) c₀ hγC

  obtain ⟨w, hwU, hwC⟩ := crd2 ω (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) (hrel ω ωs hωs)
  have hwV : w ∈ V := hVmem w ω _ hwC (fun i k => Or.inl (hω i k))
    (fun i k => Or.inr (Set.mem_iUnion₂.2 ⟨i, k, ⟨(ω, ωs), ⟨hω, hωsΩ⟩, rfl⟩⟩))

  have hy'mem : f (y, z) ∈ (Y₁ ×ˢ Y₂).image f := Finset.mem_image_of_mem f (Finset.mem_product.2 ⟨hy, hz⟩)
  obtain ⟨hy'U, hy'C⟩ := hf y z (hY₂sk z hz)

  have law := GlobalTheory.T.unipotentRadical_coordinates_groupLaw F E σ n J j m C D Z J₀ hFr lv hlv
  have h1 := (law γ u (adMat F (-x₀)) (adMat F c₀) b c hγC).1 hbc
  have hcj := (law w w ω _ 0 0 hwC).2.2 t
  have h2 := (law (f (y, z)) _ y _ _ _ hy'C).1 hcj
  have eb : adMat F (-x₀) + b = y + t.1 * ω := by rw [hb, hneg]; abel
  have ec : adMat F c₀ + c - adMat F (-x₀) * plus σ J₀ b =
      (z - (2⁻¹ : F) • (y * plus σ J₀ y)) + t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 -
        y * plus σ J₀ (t.1 * ω) := by
    have hconj : t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 =
        t.1 * ωs * cT (sigR (AF F) σ) t.1 - (2⁻¹ : F) • ((t.1 * ω) * plus σ J₀ (t.1 * ω)) := by
      simp only [hplus, Formalism.UG.cT_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hconj, hc₀, hneg, hb]
    simp only [hplus]
    exact final_eq (sigR (AF F) σ) K (adMat F x₀) y (t.1 * ω) c (adMat F x₁) z (t.1 * ωs * cT (sigR (AF F) σ) t.1) hR
  rw [eb, ec] at h1
  have heq := (law (γ * u) _ _ _ 0 0 h1).2.1 h2
  refine ⟨γ, hγrat, hγU, f (y, z), hy'mem, w, hwV, hwU, ?_⟩
  rw [heq]
  simp only [mul_assoc]

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicUnipotentRadical_covered_by_levi_conjugates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  atlas_forward_decl GlobalTheory.SphEis.cover_unipRad
end
