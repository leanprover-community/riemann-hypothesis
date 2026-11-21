import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DixmierMalliavinLie
import BuildAid.ForwardExisting

section
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory.MatLie

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}

def transChart (φ : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d))) (a : G) :
    OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d)) :=
  (Homeomorph.mulLeft a⁻¹).toOpenPartialHomeomorph.trans φ

variable (φ : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin d)))

@[simp] theorem transChart_apply (a x : G) : transChart φ a x = φ (a⁻¹ * x) := rfl

@[simp] theorem transChart_symm_apply (a : G) (y : EuclideanSpace ℝ (Fin d)) :
    (transChart φ a).symm y = a * φ.symm y := by
  simp [transChart, Homeomorph.mulLeft_symm]

@[simp] theorem transChart_source (a : G) : (transChart φ a).source = {x | a⁻¹ * x ∈ φ.source} := by
  ext x; simp [transChart]

@[simp] theorem transChart_target (a : G) : (transChart φ a).target = φ.target := by
  ext y; simp [transChart]

def chartedSpace (h1 : (1 : G) ∈ φ.source) : ChartedSpace (EuclideanSpace ℝ (Fin d)) G where
  atlas := Set.range (transChart φ)
  chartAt := transChart φ
  mem_chart_source a := by simp [h1]
  chart_mem_atlas a := ⟨a, rfl⟩

end GlobalTheory.MatLie
end
end

section
section
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory

theorem glue_smooth_of_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c →
    HasCompactSupport f →
    (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧
      ∀ g, c g ∈ V → f g = Φ (c g)) →
    ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  intro H _ X _ _ _ c f hc hf hloc
  choose V hVo hcV Φ hΦ hfΦ using hloc
  have hs : IsClosed (c '' tsupport f) := (hf.isCompact.image hc).isClosed
  have hcov : c '' tsupport f ⊆ ⋃ a, V a := by
    rintro _ ⟨a, -, rfl⟩
    exact Set.mem_iUnion.2 ⟨a, hcV a⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov
  refine ⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    refine χ.contDiffAt_finsum fun a hy => ?_
    exact (hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))
  · intro g
    have hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g := by
      intro a
      by_cases h0 : χ a (c g) = 0
      · simp [h0]
      · have hmem : c g ∈ V a := hχ a (subset_tsupport _ h0)
        rw [hfΦ a g hmem]
    simp only [hterm]
    by_cases hg : g ∈ tsupport f
    · rw [← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]
    · have : f g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [this]

end GlobalTheory
end
end

open GlobalTheory.Orb
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  atlas_forward_decl GlobalTheory.glue_smooth_of_compactSupport
end
