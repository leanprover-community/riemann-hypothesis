module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry

noncomputable section

section Quot

variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ))

attribute [local instance] MvPolynomial.gradedAlgebra

def quotGrading : ℕ → Submodule ℂ (MvPolynomial σ ℂ ⧸ I) :=
  fun d => (homogeneousSubmodule σ ℂ d).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap

theorem quot_gradedAlgebra (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    Nonempty (GradedAlgebra (quotGrading I)) := by
  classical
  have hgm : SetLike.GradedMonoid (quotGrading I) :=
    { one_mem := ⟨1, SetLike.one_mem_graded (homogeneousSubmodule σ ℂ), map_one (Ideal.Quotient.mkₐ ℂ I)⟩
      mul_mem := by
        rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, SetLike.mul_mem_graded hf hg, map_mul (Ideal.Quotient.mkₐ ℂ I) f g⟩ }
  have hproj : ∀ i, (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j) ≤
      LinearMap.ker (GradedAlgebra.proj (homogeneousSubmodule σ ℂ) i) := by
    intro i
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro g hg
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ hg hj]
  have hint : DirectSum.IsInternal (quotGrading I) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      rintro x ⟨f, hf, rfl⟩ hx
      have hx' : (Ideal.Quotient.mkₐ ℂ I).toLinearMap f ∈
          (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap := by
        simp only [Submodule.map_iSup]
        exact hx
      obtain ⟨g, hg, hgf⟩ := hx'
      have hfg : f - g ∈ I := by
        rw [← Ideal.Quotient.eq]
        exact hgf.symm
      have hcomp := (hI.mem_iff (homogeneousSubmodule σ ℂ)).mp hfg i
      have hgi : (DirectSum.decompose (homogeneousSubmodule σ ℂ) g i : MvPolynomial σ ℂ) = 0 := by
        have := hproj i hg
        rwa [LinearMap.mem_ker, GradedAlgebra.proj_apply] at this
      rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, hgi, sub_zero,
        DirectSum.decompose_of_mem_same _ hf] at hcomp
      show Ideal.Quotient.mk I f = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    · have htop : (⨆ i, homogeneousSubmodule σ ℂ i) = ⊤ :=
        (DirectSum.Decomposition.isInternal (homogeneousSubmodule σ ℂ)).submodule_iSup_eq_top
      unfold quotGrading
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective ℂ I
  exact ⟨{ hgm, hint.chooseDecomposition with }⟩

end Quot

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

@[reducible] def segreGraded {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    GradedAlgebra (segreGrading P) :=
  Classical.choice (quot_gradedAlgebra _ (segreIdeal_isHomogeneous hP))

end

end ReciprocityTheory.AnForm.R
