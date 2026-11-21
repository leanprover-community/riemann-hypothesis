import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType

section
open Finset

namespace GlobalTheory.HermitianFormFacts

theorem main : ∀ {ι : Type} [inst : Fintype ι] {n : ℕ} (w : ι → Fin n → ℂ),
    ∏ v : ι, GlobalTheory.GaussMean.gauss (w v) ≤ Real.exp (-‖w‖ ^ (2 : ℕ)) := by
  intro ι _ n w
  set S : ℝ := ∑ v : ι, ∑ i, ‖w v i‖ ^ 2 with hS
  have hprod : ∏ v : ι, GlobalTheory.GaussMean.gauss (w v) = Real.exp (-S) := by
    unfold GlobalTheory.GaussMean.gauss
    rw [← Real.exp_sum, hS, ← Finset.sum_neg_distrib]
  rw [hprod, Real.exp_le_exp, neg_le_neg_iff]
  have hS0 : 0 ≤ S := by positivity
  have hle : ‖w‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖w v i‖ ^ 2 ≤ ∑ j, ‖w v j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖w v j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ S := Finset.single_le_sum (f := fun u => ∑ j, ‖w u j‖ ^ 2) (fun u _ => by positivity) (Finset.mem_univ v)
  calc ‖w‖ ^ 2 ≤ Real.sqrt S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = S := Real.sq_sqrt hS0

end GlobalTheory.HermitianFormFacts
end

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
end
end
