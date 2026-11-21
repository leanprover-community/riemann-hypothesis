import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CoeConjEquivSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumns

section
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem reduce_gl_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) (j : ℕ) : ∃ (L : Set (GL (Fin j) (AF F ⊗[F] E))) (B : ℝ), IsCompact L ∧
    ∀ α : GL (Fin j) (AF F ⊗[F] E), ∃ (δ : GL (Fin j) E) (l : Fin j → ℤ), ∃ c ∈ L,
      bc (inclR (F := F) (AF F)) δ * α = tor F E l * c ∧
      (absE F E (Matrix.GeneralLinearGroup.det α) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ :=
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  GlobalTheory.GodementSectionReduction.reduction_GL_diagonalUnitPowers_compact (inclR (F := F) (AF F)) GlobalTheory.Doubling.continuous_absE
    (fun u => GlobalTheory.Doubling.absE_inclR u) (by positivity)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (GlobalTheory.Eis.Conv.red_gl _ _ _ hc j)

theorem reduce_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hl
  obtain ⟨L, B, hL, hR⟩ := reduce_gl_cm hF.cm j
  refine ⟨lv '' L, B, hL.image hl.cont, fun p β hp => ?_⟩
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR β
  have h1 := hl.rat δ
  generalize bc (inclR (F := F) (AF F)) δ = u at h1 hred
  refine ⟨lv u, h1, ⟨⟨u.1, fun _ _ h => absurd h (lt_irrefl _), hl.onC u⟩,
    (u⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), by rw [← map_inv]; exact hl.onC u⁻¹⟩,
    lv u * p * lv (u * β)⁻¹, ?_, l, lv c, ⟨c, hc, rfl⟩, ?_, hle⟩
  · change _ * _ = _
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hl.onC, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (adMat F C), hp, ← Matrix.mul_assoc, hl.onC, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.1, ← Units.val_mul, Units.mul_inv, Matrix.mul_one]
  · rw [mul_assoc _ (lv _) (lv c), ← map_mul, ← hred, map_inv, inv_mul_cancel_right]

end GlobalTheory.SphEis

end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_leviGL_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  atlas_forward_decl GlobalTheory.SphEis.reduce_levi
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

theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  atlas_forward_decl GlobalTheory.SphEis.exists_bound_exponents
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviSection_commute_of_fixes_isotropicColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  first | exact @GlobalTheory.SphEis.lv_comm_of_fix_cols | exact GlobalTheory.SphEis.lv_comm_of_fix_cols | (intros; apply GlobalTheory.SphEis.lv_comm_of_fix_cols <;> assumption)
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem measure_fund_le_card_mul_of_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  intro G _ _ _ _ _ _ _ _ N Λ _ ν DN b κ V Y hν hD hV hconj hY hcov
  have hVm : MeasurableSet V := hV.isClosed.measurableSet
  have hconjm : Measurable fun u : N => b * (u : G) * b⁻¹ :=
    (measurable_const.mul measurable_subtype_coe).mul measurable_const
  have hS₀m : MeasurableSet {u : N | b * (u : G) * b⁻¹ ∈ V} := hconjm hVm
  have hVNm : MeasurableSet {u : N | (u : G) ∈ V} := measurable_subtype_coe hVm
  have hS₀ : ν {u : N | b * (u : G) * b⁻¹ ∈ V} = κ * ν {u : N | (u : G) ∈ V} := by
    have h := hconj (V.indicator 1) (measurable_one.indicator hVm)
    have e1 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) (b * u * b⁻¹))
        = {u : N | b * (u : G) * b⁻¹ ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    have e2 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) u) = {u : N | (u : G) ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    rw [e1, e2, lintegral_indicator hS₀m, lintegral_indicator hVNm] at h
    simpa using h
  have hΛN : Countable (Λ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Λ.subgroupOf N => (⟨(x : N), x.2⟩ : Λ)) ?_
    intro x y h
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun z : Λ => (z : G)) h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (Λ.subgroupOf N)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (Λ.subgroupOf N) ν
  let T : G → Set N := fun y => {v : N | b * (y⁻¹ * (v : G)) * b⁻¹ ∈ V}
  have hle : ν DN ≤ ν (⋃ y ∈ Y, T y) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun u => ?_)
    obtain ⟨γ, hγΛ, hγN, y, hy, w, hw, heq⟩ := hcov u u.2
    refine ⟨⟨⟨γ, hγN⟩, (Subgroup.mem_subgroupOf).2 hγΛ⟩, Set.mem_biUnion hy ?_⟩
    show b * (y⁻¹ * (γ * (u : G))) * b⁻¹ ∈ V
    rw [heq]
    convert hw using 1
    group
  have hT : ∀ y ∈ Y, ν (T y) = κ * ν {u : N | (u : G) ∈ V} := by
    intro y hy
    have hyN : y⁻¹ ∈ N := N.inv_mem (hY y hy)
    have : T y = (fun v : N => (⟨y⁻¹, hyN⟩ : N) * v) ⁻¹' {u : N | b * (u : G) * b⁻¹ ∈ V} := by
      ext v; simp [T, mul_assoc]
    rw [this, measure_preimage_mul, hS₀]
  refine hle.trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [Finset.sum_congr rfl hT, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  atlas_forward_decl GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover
end

section
open MeasureTheory

namespace GlobalTheory.ConjugationEquivalence

def conjEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * u * b⁻¹, (h u).1 u.2⟩
  invFun u := ⟨b⁻¹ * u * b, (h _).2 (by simpa [mul_assoc] using u.2)⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

end GlobalTheory.ConjugationEquivalence
end

section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

def conjNormalEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N := GlobalTheory.ConjugationEquiv.conjEquiv N b h

end GlobalTheory.ResLine
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem lintegral_conj_eq_const_mul :
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure N) (b : G), IsClosed (N : Set G) → ν.IsHaarMeasure → (∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) → ∃ κ : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N ν b hN hν h
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let e := GlobalTheory.ResLine.conjNormalEquiv N b h
  haveI : (ν.map e).IsHaarMeasure := e.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map e) ν
  have he : Measurable e := e.continuous.measurable
  refine ⟨(Measure.haarScalarFactor (ν.map e) ν : ℝ≥0∞), fun g hg => ?_⟩
  have hg' : Measurable fun u : N => g u := hg.comp measurable_subtype_coe
  have h1 := lintegral_map (μ := ν) hg' he
  rw [hc, lintegral_smul_measure] at h1
  exact h1.symm

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_conj_normalizer_eq_const_mul_haar : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure N) (b : G), IsClosed (N : Set G) → ν.IsHaarMeasure → (∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) → ∃ κ : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν := by
  atlas_forward_decl GlobalTheory.SphEis.lintegral_conj_eq_const_mul
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

namespace GlobalTheory.Packing

theorem mem_smul_smul_iff {G : Type} [Group G] (Λ : Subgroup G) (γ : Λ) (t x : G) (U : Set G) :
    x ∈ γ • (t • U) ↔ t⁻¹ * ((γ : G)⁻¹ * x) ∈ U := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
  simp [Subgroup.smul_def, smul_eq_mul]

theorem packing_count : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  intro G _ _ _ _ _ _ _ _ Γ Λ _ μ D U hΛΓ hdisc hHaar hD hU
  have hUc : IsCompact (U * U⁻¹) := hU.mul hU.inv
  have hfin : (U * U⁻¹ ∩ (Γ : Set G)).Finite := hdisc _ hUc
  refine ⟨hfin.toFinset.card, ?_⟩
  intro T S hTΓ hTdist hS hSinv hTS
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hmeasA : ∀ (γ : Λ) (t : G), MeasurableSet (γ • (t • U)) := by
    intro γ t
    have : γ • (t • U) = (fun y => t⁻¹ * ((γ : G)⁻¹ * y)) ⁻¹' U := by
      ext y; rw [mem_smul_smul_iff]; rfl
    rw [this]
    exact hUm.preimage (continuous_const.mul (continuous_const.mul continuous_id)).measurable
  have hsubS : ∀ (γ : Λ), ∀ t ∈ T, γ • (t • U) ⊆ S := by
    intro γ t ht y hy
    rw [mem_smul_smul_iff] at hy
    have h1 := hSinv (γ : G) γ.2 _ (hTS t ht _ hy)
    simpa [mul_assoc] using h1
  set ν := μ.restrict (S ∩ D) with hν
  have key : ∀ t ∈ T, μ U = ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := by
    intro t ht
    rw [← measure_smul μ t U, hD.measure_eq_tsum (t • U)]
    refine tsum_congr fun γ => ?_
    rw [lintegral_indicator_one (hmeasA γ t), hν, Measure.restrict_apply (hmeasA γ t)]
    congr 1
    ext y
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hsubS γ t ht h1, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  have hpt : ∀ x : G, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
      ≤ (hfin.toFinset.card : ℝ≥0∞) := by
    intro x
    classical
    have hswap : ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = ∑' γ : Λ, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x := by
      first
      | exact (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      | exact (tsum_sum fun _ _ => ENNReal.summable).symm
      | exact (ENNReal.tsum_finsetSum _ _).symm
    rw [hswap, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hbool : ∑ γ ∈ s, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = (((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card : ℝ≥0∞) := by
      rw [Finset.card_filter, Finset.sum_product]
      push_cast
      simp only [Set.indicator_apply, Pi.one_apply]
    rw [hbool]
    have hcard : ((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card
        ≤ hfin.toFinset.card := by
      set P := (s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U)) with hPdef
      have memP : ∀ p : Λ × G, p ∈ P → p.2 ∈ T ∧ x ∈ p.1 • (p.2 • U) := by
        intro p hp
        rw [hPdef, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨hp.1.2, hp.2⟩
      rcases P.eq_empty_or_nonempty with hP | ⟨p₀, h₀⟩
      · rw [hP]; exact Nat.zero_le _
      obtain ⟨ht₀, hx₀⟩ := memP p₀ h₀
      rw [mem_smul_smul_iff] at hx₀
      refine Finset.card_le_card_of_injOn
        (fun p : Λ × G => (p₀.2⁻¹ * (p₀.1 : G)⁻¹) * ((p.1 : G) * p.2)) ?_ ?_
      · intro p hp
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        obtain ⟨ht, hx⟩ := memP p hp'
        rw [mem_smul_smul_iff] at hx
        show _ ∈ (hfin.toFinset : Set G)
        rw [Set.Finite.coe_toFinset]
        refine ⟨?_, ?_⟩
        · refine Set.mem_mul.2 ⟨_, hx₀, (p.2⁻¹ * ((p.1 : G)⁻¹ * x))⁻¹, ?_, ?_⟩
          · rw [Set.mem_inv, inv_inv]; exact hx
          · group
        · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hTΓ _ ht₀)) (Γ.inv_mem (hΛΓ p₀.1.2)))
            (Γ.mul_mem (hΛΓ p.1.2) (hTΓ _ ht))
      · intro p hp q hq hpq
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        have hq' : q ∈ P := by first | exact Finset.mem_coe.1 hq | exact hq
        have hpT := (memP p hp').1
        have hqT := (memP q hq').1
        have h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2 := mul_left_cancel hpq
        have e : q.2 * p.2⁻¹ = (q.1 : G)⁻¹ * p.1 := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have htt : p.2 = q.2 := hTdist _ hpT _ hqT (e ▸ Λ.mul_mem (Λ.inv_mem q.1.2) p.1.2)
        have hg : (p.1 : G) = q.1 := by
          rw [htt] at h1; exact mul_right_cancel h1
        exact Prod.ext (Subtype.ext hg) htt
    exact_mod_cast hcard
  calc (T.card : ℝ≥0∞) * μ U = ∑ t ∈ T, μ U := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t ∈ T, ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := Finset.sum_congr rfl key
    _ = ∫⁻ x, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x ∂ν := by
      rw [lintegral_finset_sum']
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_tsum]
        exact fun γ => ((measurable_one.indicator (hmeasA γ t))).aemeasurable
      · intro t _
        exact (Measurable.ennreal_tsum fun γ => measurable_one.indicator (hmeasA γ t)).aemeasurable
    _ ≤ ∫⁻ _x, (hfin.toFinset.card : ℝ≥0∞) ∂ν := lintegral_mono hpt
    _ = (hfin.toFinset.card : ℝ≥0∞) * μ (S ∩ D) := by
      rw [lintegral_const, hν, Measure.restrict_apply_univ]

end GlobalTheory.Packing
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing_count_inequivalent_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  atlas_forward_decl GlobalTheory.Packing.packing_count
end

section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_translate_shell_le_div_modulus : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  first | exact @GlobalTheory.ResLine.modulus_mul_measure_shell_le | exact GlobalTheory.ResLine.modulus_mul_measure_shell_le | (intros; apply GlobalTheory.ResLine.modulus_mul_measure_shell_le <;> assumption)
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix Pointwise
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_le_mul_of_unip_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  intro G _ _ _ _ _ _ _ _ N M Λ Γ Q _ ν π DN DM μ D V W H hΛΓ hΛQ hQ hQd hdisc hμ hD hV hW
  haveI := H.haarN
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  have hU0 : μ U ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩) (measure_mono interior_subset)).ne'
  have hUt : μ U ≠ ⊤ := hUc.measure_ne_top
  obtain ⟨k, hk⟩ := GlobalTheory.T.packing_count_inequivalent_discreteSubgroup G Γ Λ μ D U hΛΓ hdisc hμ hD hUc
  obtain ⟨B₀, hB₀t, hB₀⟩ := GlobalTheory.T.measure_translate_shell_le_div_modulus G N M Λ ν π DN DM H μ D hμ hD (W * U) (hW.mul hUc)
  have hνV : ν {u : N | (u : G) ∈ V} ≠ ⊤ :=
    (H.closedN.isClosedEmbedding_subtypeVal.isCompact_preimage hV).measure_ne_top
  have hDN0 : ν DN ≠ 0 := GlobalTheory.ResLine.Inhab.semiLat_ne_zero H
  have hDNt : ν DN ≠ ⊤ := H.finN
  refine ⟨(ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a Y T haM haN hY hcov hTΓ hTsep hTQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.lintegral_conj_normalizer_eq_const_mul_haar G N ν a⁻¹ H.closedN H.haarN (fun u => by rw [inv_inv]; exact haN u)
  let S : Set G := (Q : Set G) * (a • (W * U))
  have hSc : IsClosed S := hQ.mul_right_of_isCompact ((hW.mul hUc).smul a)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSinv : ∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S := by
    intro γ hγ x hx
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨γ * q, Q.mul_mem (hΛQ hγ) hq, y, hy, mul_assoc _ _ _⟩
  have hTS : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ S := by
    intro t ht u hu
    obtain ⟨q, hq, w, hw, rfl⟩ := hTQ t ht
    have hm : a • (w * u) ∈ a • (W * U) := Set.smul_mem_smul_set (Set.mul_mem_mul hw hu)
    refine Set.mem_mul.2 ⟨q, hq, a • (w * u), hm, ?_⟩
    simp only [smul_eq_mul, mul_assoc]
  have hpack := hk T S hTΓ hTsep hSm hSinv hTS
  have hshell : κ * μ (S ∩ D) ≤ B₀ := by
    refine hB₀ a⁻¹ κ (fun m hm => (show Commute a m from haM m hm).inv_left) hκ S hSm fun x hx => ?_
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.1 hy
    obtain ⟨u, hu, m, hm, rfl⟩ := hQd q hq
    refine ⟨a⁻¹ * u * a, (haN u).1 hu, m, hm, c, hc, ?_⟩
    have e : m * a = a * m := (haM m hm).symm
    simp only [smul_eq_mul, mul_assoc]
    rw [← mul_assoc m a c, e, mul_assoc a m c]
  have hcover := GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover G N Λ ν DN a⁻¹ κ V Y H.haarN H.domN hV hκ hY fun u hu => by
    obtain ⟨γ, hγ, hγN, y, hy, w, hw, e⟩ := hcov u hu
    exact ⟨γ, hγ, hγN, y, hy, w, hw, by rw [inv_inv]; exact e⟩
  have key : ν DN * (T.card * μ U) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := calc
    ν DN * (T.card * μ U) ≤ (Y.card * (κ * ν {u : N | (u : G) ∈ V})) * (T.card * μ U) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * (κ * (T.card * μ U)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * (κ * (k * μ (S ∩ D))) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * k * (κ * μ (S ∩ D)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * k * B₀ := by gcongr
    _ = Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := by ring
  have hc0 : ν DN * μ U ≠ 0 := mul_ne_zero hDN0 hU0
  have hct : ν DN * μ U ≠ ⊤ := ENNReal.mul_ne_top hDNt hUt
  have hX : ν {u : N | (u : G) ∈ V} * k * B₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hνV (ENNReal.natCast_ne_top k)) hB₀t
  have h1 : (T.card : ℝ≥0∞) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)) := by
    rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc (T.card : ℝ≥0∞) * (ν DN * μ U) = ν DN * (T.card * μ U) := by ring
      _ ≤ _ := key
  have hfin : ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U) ≠ ⊤ := (ENNReal.div_lt_top hX hc0).ne
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) h1
  rw [mul_comm]
  simpa [ENNReal.toReal_mul] using h2

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  atlas_forward_decl GlobalTheory.SphEis.card_le_mul_of_unip_cover
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  first | exact @GlobalTheory.SphEis.frame_facts | exact GlobalTheory.SphEis.frame_facts | (intros; apply GlobalTheory.SphEis.frame_facts <;> assumption)
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem semiLat_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ →
    ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C))
      (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))),
      SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ H
  have key : ∀ {P : Subgroup (GAd σ J)}, P ≤ fixG σ J C →
      (ratPts σ J ⊓ fixG σ J C).subgroupOf P = (ratPts σ J).subgroupOf P := fun h => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩
  obtain ⟨hC, -, cM, cN, hN, hP, hd, hn, -⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ H
  haveI := locallyCompact_unipRad H.cm H.herm hC
  obtain ⟨ν, DN, hν, hDN, h1⟩ := exists_mass_one (cocompact_unipRad H.cm H.herm hC)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := cM.locallyCompactSpace
  have hDM := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom
    ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) Measure.haar
  refine ⟨ν, Measure.haar, DN, _,
    { closedN := cN
      closedM := cM
      norm := fun x hx u hu => (hn x (hP hx.1) u).1 hu
      disj := hd
      dec := ?_
      haarN := hν
      haarM := inferInstance
      domN := by rw [key hN]; exact hDN
      domM := by rw [key inf_le_left]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J j m C D Z J₀ H _ _ inferInstance hDM }⟩
  rintro γ ⟨hγ, hf⟩
  obtain ⟨u, hu, x, hx, e, hr⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ H γ hf
  refine ⟨u, hu, x, hx, ⟨?_, hN hu⟩, ⟨hr hγ, hx.1⟩, e⟩
  have : u = γ * x⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFixatorOfColumns_isSemidirectLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C)) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  atlas_forward_decl GlobalTheory.SphEis.semiLat_fixG
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem compact_inter_ratPts_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)),
    IsCompact K → (K ∩ ratPts σ J).Finite := by
  intro F E _ _ _ _ _ σ n J K hK
  have hd : DiscreteTopology (ratPts σ J) := inferInstance
  have hcl : IsClosed ((ratPts σ J : Subgroup (GAd σ J)) : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  exact (hK.inter_right hcl).finite
    (IsDiscrete.mono (isDiscrete_iff_discreteTopology.2 hd) Set.inter_subset_right)

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_compact_inter_unitaryRationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)), IsCompact K → (K ∩ ratPts σ J).Finite := by
  atlas_forward_decl GlobalTheory.SphEis.compact_inter_ratPts_finite
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_ratPts_fixG_tor_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  obtain ⟨-, hQc, -, -, hNQ, hQP, -, hnorm, hpar⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ hF
  obtain ⟨V, B₁, hV, hcov⟩ := GlobalTheory.T.isotropicUnipotentRadical_covered_by_levi_conjugates F E σ n J j m C D Z J₀ hF lv hlv
  obtain ⟨ν, π, DN, DM, hSL⟩ := GlobalTheory.T.rationalFixatorOfColumns_isSemidirectLattice F E σ n J j m C D Z J₀ hF
  let Λ : Subgroup (GAd σ J) := ratPts σ J ⊓ fixG σ J C
  haveI : DiscreteTopology Λ := inferInstance
  haveI : Countable Λ := inferInstance
  have hDom := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Λ (Measure.haar : Measure (GAd σ J))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup (GAd σ J) (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D) Λ (ratPts σ J) (fixG σ J C)
    ν π DN DM Measure.haar _ V W hSL inf_le_left inf_le_right hQc
    (fun q hq => by
      obtain ⟨u, hu, x, hx, e, -⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ hF q hq
      exact ⟨u, hu, x, hx, e⟩)
    (fun K hK => GlobalTheory.T.finite_compact_inter_unitaryRationalPoints F E σ n J K hK) inferInstance hDom hV hW
  refine ⟨B * B₁, fun μ T hT hdist hform => ?_⟩
  set a := lv (tor F E fun i => (μ i : ℤ)) with ha
  obtain ⟨Y, hYc, hYN, hYcov⟩ := hcov μ
  have haP : a ∈ parFlag σ J C (fun _ => 0) := hpar a _ (hlv.onC _)
  have h1 := hB a Y T
    (fun x hx => (GlobalTheory.T.leviSection_commute_of_fixes_isotropicColumns F E σ n J j m C D Z J₀ hF lv hlv _ x hx))
    (fun u => by
      have := hnorm a⁻¹ (inv_mem haP) u
      simpa only [inv_inv] using this)
    hYN
    (fun u hu => by
      obtain ⟨γ, hγ, hγN, y, hy, w, hw, -, e⟩ := hYcov u hu
      exact ⟨γ, ⟨hγ, hNQ hγN⟩, hγN, y, hy, w, hw, e⟩)
    hT
    (fun t ht t' ht' h => hdist t ht t' ht' h.2)
    hform
  calc (T.card : ℝ) ≤ B * Y.card := h1
    _ ≤ B * (B₁ * ∏ i, bse F ^ ((m + j) * μ i)) := mul_le_mul_of_nonneg_left hYc hB0
    _ = B * B₁ * ∏ i, bse F ^ ((m + j) * μ i) := by ring

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  atlas_forward_decl GlobalTheory.SphEis.card_ratPts_fixG_tor_le
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

noncomputable section

namespace GlobalTheory.SphEis.Summ

theorem tor_add (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {j : ℕ}
    (μ : Fin j → ℕ) (m₀ : ℕ) :
    tor F E (fun i => (μ i : ℤ) + -(m₀ : ℤ)) = tor F E (fun i => (μ i : ℤ)) * tor F E (fun _ => -(m₀ : ℤ)) :=
  Units.ext (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))

theorem summable_absDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht
  classical
  have hb : 1 < bse F := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hb0 : 0 < bse F := one_pos.trans hb
  have hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0) := fun g hg =>
    ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by
      rw [Matrix.mul_one]; exact inv_mem hg⟩
  obtain ⟨W, B, hW, hR⟩ := GlobalTheory.T.reduction_leviGL_isotropicFrame F E σ n J j m C D Z J₀ hF lv hlv
  choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)
  have hWK : IsCompact (W * K) := hW.mul hK
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK
  have hl : ∀ i r, -(m₀ : ℤ) ≤ l i r := fun i =>
    hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by
      have := mul_mem (hγ i) (hx i)
      rwa [e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ) :=
    ⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ)) := ⟨_, rfl⟩
  have hW' : IsCompact ((fun g => a * g) '' (W * K)) := hWK.image (continuous_mul_left a)
  obtain ⟨N, hN⟩ := GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'
  have hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i)) := fun i => by
    rw [e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]
    simp only [mul_assoc]
  have hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i' := fun i i' h => hi i i' (by
    have h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))
  refine GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht
    (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle i).trans (le_of_eq ?_)
    rw [mul_assoc, hμ]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hc : (S.image fun i => γ i * x i).card = S.card :=
      Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by
        rw [← h, mul_inv_cancel]
        exact one_mem _)
    rw [← hc]
    refine hN μ' _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      exact mul_mem (hγ i) (hx i)
    · intro s hs s' hs' h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs'
      rw [hinj i i' h]
    · intro s hs
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩

end GlobalTheory.SphEis.Summ

end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_absDet_rational_points_godement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  atlas_forward_decl GlobalTheory.SphEis.Summ.summable_absDet
end
