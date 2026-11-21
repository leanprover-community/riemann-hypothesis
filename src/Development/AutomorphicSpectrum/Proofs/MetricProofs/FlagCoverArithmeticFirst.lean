import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointInPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFrameCompatibility
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesValueAtPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem exists_flags_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F z hz hF hG
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have hch : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0])
  obtain ⟨c, hc, hcb, hc1⟩ : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (∀ k : NonPluckerBlocks M.blk, c k.1 * basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → c k = 1 := by
    refine ⟨fun k => if hk : ∀ p, M.blk p ≠ some k then (basePart M.blk z ⟨⟨k, hk⟩, F.c ⟨k, hk⟩⟩)⁻¹ else 1,
      fun k => ?_, fun k => ?_, fun p k hp => ?_⟩
    · by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [dif_pos hk]
        exact inv_ne_zero (hch ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact one_ne_zero
    · simp only [dif_pos k.2]
      exact inv_mul_cancel₀ (hch k)
    · have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      simp only [dif_neg hk]
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz
  have hb₁ : basePart M.blk z₁ = fun q => (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z q := rfl
  have hT := StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc k.1)
  have hI : mCoordIdeal (basePart M.blk z₁) = mCoordIdeal (basePart M.blk z) := by
    rw [hb₁]
    exact hT.1
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by rw [hI]; exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := hcb
  obtain ⟨h, -, hh, hs⟩ := (h3 F hF z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk z₁) = valAt M.x s (basePart M.blk z) := fun s => by
    rw [hb₁]
    exact (hT.2 (h1 z hz)).2 s
  refine ⟨h, hh, fun p k hp => ?_⟩
  obtain ⟨a, ha, hm⟩ := hs p k hp
  refine ⟨a, ha, fun m => ?_⟩
  have e := hm m
  simp only [hval] at e
  have e' : z₁ ⟨k, m⟩ = z ⟨k, m⟩ := by
    show c k * z ⟨k, m⟩ = z ⟨k, m⟩
    rw [hc1 p k hp, one_mul]
  rw [e'] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_diag_frame_change : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F w H hF hb hG hH hP
  have hne : ∀ k : NonPluckerBlocks M.blk, w ⟨k.1, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap (basePart M.blk w) (X ⟨k, F.c k⟩) = 0
    have : basePart M.blk w ⟨k, F.c k⟩ = 0 := h0
    rw [mConeMap, aeval_X, this, map_zero, zero_mul])
  let c : K → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, F.c ⟨k, hk⟩⟩)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos hk]; exact inv_ne_zero (hne ⟨k, hk⟩)
    · simp only [c, dif_neg hk]; exact one_ne_zero
  let z₀ : (Σ k, ι k) → ℂ := fun q => c q.1 * w q
  let c' : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hc' : ∀ k, c' k ≠ 0 := fun k => hc k.1
  have eb : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k => c' q.1 * basePart M.blk w q := rfl
  obtain ⟨hI, hm⟩ := StepW.TorusAct.main _ _ M.Ω M.x (basePart M.blk w) c' hc'
  obtain ⟨hb₀, hval⟩ := hm hb
  rw [← eb] at hI hb₀ hval
  have hflag : M.IsFlagOf F z₀ H := by
    refine ⟨fun k => ?_, hH, fun p k hp => ?_⟩
    · show c k.1 * w ⟨k.1, F.c k⟩ = 1
      simp only [c, dif_pos k.2]
      exact inv_mul_cancel₀ (hne k)
    · obtain ⟨a, ha, hw⟩ := hP p k hp
      refine ⟨a, ha, fun m => ?_⟩
      have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      show c k * w ⟨k, m⟩ = _
      simp only [c, dif_neg hk, one_mul]
      rw [hw m, CovMap.LocImg.plk]
      simp only [hval]
  have hG₀ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [hI]; exact hG
  have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) :=
    (((GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.2 F hF z₀ hb₀ hG₀ hflag.1).2 ⟨H, hflag⟩)
  have ho : SameOrbit z₀ w := ⟨c, hc, rfl⟩
  have ho' : SameOrbit w z₀ := ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), by
    funext q
    exact (inv_mul_cancel_left₀ (hc q.1) _).symm⟩
  exact ⟨mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ho' hz₀, z₀, ho, ⟨c', hc', rfl⟩, hflag⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diag_frame_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt.main <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_two_frames_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem base_orbit {σ : Type} {blk : σ → Option K} {z₁ z : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (basePart blk z₁) (basePart blk z) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b₁ b : (Σ k, ι' k) → ℂ} (h : SameOrbit b₁ b) :
    SameOrbit (b₁ ∘ v) (b ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hv.2.2.1 q]

theorem ideal_orbit {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b) : mCoordIdeal b₁ = mCoordIdeal b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact StepW.TorusAct.mCoordIdeal_torus c hc b

theorem valAt_orbit {x : (Σ k, ι k) → Ω} {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b)
    (hb : b ∈ mcPts (mCoordIdeal x)) (s : Ω) : valAt x s b₁ = valAt x s b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ((StepW.TorusAct.main K ι Ω x b c hc).2 hb).2 s

end Orbit

theorem img_spec (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j)
    (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F₀' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F₀ : FrameData ι Ψ N M.Ω M.blk) (hz : z ∈ mcPts (mCoordIdeal y')) (hF' : M'.IsFrame F₀') (hF : M.IsFrame F₀)
    (hg' : M'.GoodAt F₀' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F₀ (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) :
    img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) ∧ IsImg Cv z (img Cv F₀' F₀ z) := by
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨h₀, hh₀, hz₀⟩ := GlobalTheory.T.exists_block_diag_frame_change K' ι' Φ' y' Ψ N j M' F₀' z hz hF' hg'
  have hT₀ := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F₀' F₀ hb hF' hF hg' hg
  have hH₀ : ∀ τ, IsBlockDiag j (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ) ∧
      (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ).det ≠ 0 := fun τ =>
    ⟨(hT₀ τ).1.mul (hh₀ τ).1, by rw [det_mul]; exact mul_ne_zero (hT₀ τ).2 (hh₀ τ).2⟩
  have hform := GlobalTheory.T.flag_cover_frames_value_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F₀' F₀ h₀ hb hF' hF hg' hg
    (fun τ => (hh₀ τ).1) hz₀
  have hwb : basePart M.blk (img Cv F₀' F₀ z) = basePart M'.blk z ∘ Cv.v := img_base Cv F₀' F₀ z
  have hw : img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) :=
    (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F₀ (img Cv F₀' F₀ z) _ hF (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg) hH₀
      (by rw [hwb]; exact hform)).1
  refine ⟨hw, ?_⟩
  intro z₁ h1 F' F hF1' hF1 hg1' hg1 h hfl
  have hbo : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) := base_orbit h1
  have hbov := comp_orbit Cv.block hbo
  rw [ideal_orbit hbo] at hg1'
  rw [ideal_orbit hbov] at hg1
  have htrans : ∀ τ, Cv.trans F' F (basePart M'.blk z₁) τ = Cv.trans F' F (basePart M'.blk z) τ := fun τ => by
    ext a c
    exact valAt_orbit hbo hb _
  obtain ⟨-, hhinv, hflag⟩ := hfl
  have hpl : ∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k',
      plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) =
        a * plk M' F₀' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h₀ p.1) := fun p k' hp => by
    obtain ⟨a, ha, e⟩ := hflag p k' hp
    obtain ⟨a₀, ha₀, e₀⟩ := hz₀ p k' hp
    obtain ⟨c, hc, rfl⟩ := h1
    refine ⟨a⁻¹ * c k' * a₀, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (hc k')) ha₀, fun m' => ?_⟩
    have e1 := e m'
    have e2 := e₀ m'
    have e3 : ∑ I, valAt M'.x (F'.u ⟨k', m'⟩ I) (basePart M'.blk fun p => c p.1 * z p) *
        minorIJ (h p.1) I (stepCols N j p.2) = plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) :=
      Finset.sum_congr rfl fun I _ => by rw [valAt_orbit hbo hb]
    rw [e3] at e1
    simp only at e1
    rw [e2] at e1
    field_simp
    linear_combination -e1
  have hind := GlobalTheory.T.flag_cover_two_frames_comparison K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F₀' F F₀ h h₀ hb hF1' hF' hF1 hF hg1' hg' hg1 hg
    (fun τ => (hhinv τ).1) (fun τ => (hh₀ τ).1) hpl
  have hT := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hb hF1' hF1 hg1' hg1
  obtain ⟨-, z₀, o1, o2, fl⟩ := GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F (img Cv F₀' F₀ z)
    (fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) hF1 (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg1)
    (fun τ => ⟨(hT τ).1.mul (hhinv τ).1, by rw [det_mul]; exact mul_ne_zero (hT τ).2 (hhinv τ).2⟩)
    (fun p k hp => by
      obtain ⟨a₁, ha₁, e₁⟩ := hform p k hp
      obtain ⟨a₂, ha₂, e₂⟩ := hind p k hp
      refine ⟨a₁ * a₂⁻¹, mul_ne_zero ha₁ (inv_ne_zero ha₂), fun m => ?_⟩
      rw [e₁ m, hwb, e₂ m]
      field_simp)
  refine ⟨z₀, o1, Cj.sameOrbit_trans (hwb ▸ o2) (Cj.sameOrbit_symm hbov), ?_⟩
  simp only [htrans]
  exact fl

theorem local_img : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ z hz
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  refine ⟨V, f, hV, hzV, hf, fun z' hz' => ?_⟩
  obtain ⟨g1, g2, e⟩ := hs z' hz'
  rw [e]
  exact img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z' F' F hz'.2 hF' hF g1 g2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end
