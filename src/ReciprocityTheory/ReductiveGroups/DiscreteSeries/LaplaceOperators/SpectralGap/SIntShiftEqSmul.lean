import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.MeasurableIndicatorNormSq

section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem continuous_lmulM' {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def ptsOf {k r : ℕ} (U : Set (Mat k r)) : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ U}

def ptsGroup {k r : ℕ} {U : Set (Mat k r)} (hU : Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) : Group (ptsOf U) where
  mul a b := ⟨(Matrix.of a.1 * Matrix.of b.1 : Mat k r), hU.mul_mem (Matrix.of a.1) a.2 (Matrix.of b.1) b.2⟩
  one := ⟨(1 : Mat k r), hU.one_mem⟩
  inv a := ⟨((Matrix.of a.1)⁻¹ : Mat k r), hU.inv_mem (Matrix.of a.1) a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1) (hU.unit (Matrix.of a.1) a.2))

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem sInt_shift_eq_smul {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [CompleteSpace Vp] (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (f g : Mat k r → ℂ) (c₁ : ℂ)
    (hfg : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = c₁ * g y) (ξ : Vp) (x₀ x : Mat k r)
    (hx₀ : x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    sInt μW μN ψ π (fun y => f (x₀⁻¹ * y)) ξ x = c₁ • sInt μW μN ψ π (fun y => g (x₀⁻¹ * y)) ξ x := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  unfold sInt
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hfg _ (mul_mem_UH' (inv_mem_UH' hx₀) (mul_mem_UH' (mul_mem_UH' hp1.1 hp2.1) hx)), mul_smul]



end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
