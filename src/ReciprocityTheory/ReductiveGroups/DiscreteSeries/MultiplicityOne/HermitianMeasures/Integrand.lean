import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.PsiGen

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

end frob

theorem ig_uh_mul {k r : ℕ} {a b : Lap.Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem ig_ellA_continuous (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous fun g : Lap.Mat k r => Formalism.MainNotions.S.ellA k r z g a := by
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    refine continuous_finset_sum _ (fun j _ => ?_)
    exact Continuous.mul (by exact (continuous_apply j).comp (continuous_apply _)) continuous_const

theorem ig_psiGen_continuous (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ =>
      continuous_const.mul (ig_ellA_continuous k r z a)))))

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem ig_ae_mem {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  have := hW.1; have := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem integrand_aesm (hCW : ClosedW) (hCN : ClosedN) {z : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ)
    {π : Lap.Mat k r → (Vp →L[ℂ] Vp)} (hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π)
    {μW μN : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN)
    {f : Lap.Mat k r → ℂ} (hf : ContinuousOn f (UH (Hpk k r))) (ξ : Vp) {x : Lap.Mat k r}
    (hx : x ∈ UH (Hpk k r)) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => f (Matrix.of p.1 * Matrix.of p.2 * x) •
      Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  set S : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} with hS
  have hc1 : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Lap.Mat k r) := continuous_fst
  have hc2 : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 : Lap.Mat k r) := continuous_snd
  have hSc : IsClosed S := ((hCW k r z).closed.preimage hc1).inter ((hCN k r).closed.preimage hc2)
  have hae : ∀ᵐ p ∂(μW.prod μN), p ∈ S := ig_ae_mem hW hN
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  apply ContinuousOn.aestronglyMeasurable _ hSc.measurableSet
  apply ContinuousOn.smul
  · refine hf.comp ((hc1.mul hc2).mul continuous_const).continuousOn ?_
    intro p hp
    exact ig_uh_mul (ig_uh_mul hp.1.1 hp.2.1) hx
  · unfold Lap.chiInv
    apply ContinuousOn.smul
    · exact (continuous_star.comp ((ig_psiGen_continuous k r z c).comp hc2)).continuousOn
    · have hinv : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Lap.Mat k r)⁻¹) S := by
        intro p hp
        apply ContinuousAt.continuousWithinAt
        refine (continuousAt_matrix_inv _ ?_).comp hc1.continuousAt
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ ((hCW k r z).unit _ hp.1).ne_zero
      exact (hπ.2.2 ξ).comp hinv (fun p hp => (hCW k r z).inv_mem _ hp.1)

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end
