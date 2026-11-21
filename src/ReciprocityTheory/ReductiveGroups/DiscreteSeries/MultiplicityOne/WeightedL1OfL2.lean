import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MeasurableBetGm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproB

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def orbL (D : RealPlaceData k r Wp Wp) (f : Mt k r → ℝ≥0∞) (x : Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, f (Gm p x) ∂(D.μW.prod D.μN)

theorem fold_par (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) : ∫⁻ x, f x ∂D.μG = ∫⁻ x, orbL D f x ∂ν := by
  rw [hν f hf]
  refine lintegral_congr fun x => ?_
  have hm : Measurable (fun s : Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
    hf.comp (measurable_rmul_mt (Matrix.of x))
  exact lintegral_map hm measurable_sP

theorem measurable_orbL (D : RealPlaceData k r Wp Wp) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) : Measurable (orbL D f) := by
  have sW := sigmaFinite_of_haarOn D.haarW
  have sN := sigmaFinite_of_haarOn D.haarN
  exact (hf.comp measurable_Gm).lintegral_prod_left'

theorem orbL_inv (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) {q : Mt k r × Mt k r}
    (hq : (Matrix.of q.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of q.2 : Mat k r) ∈ Nset k r) (x : Mt k r) :
    orbL D f (Gm q x) = orbL D f x := by
  have hT := shL_mp D (beFacts_of h D) hq.1 hq.2
  unfold orbL
  rw [← hT.lintegral_comp (f := fun p => f (Gm p x)) (hf.comp (measurable_Gm_fst x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S D] with p hp
  congr 1
  show (Matrix.of p.2 * Matrix.of p.1 : Mat k r) * ((Matrix.of q.2 * Matrix.of q.1) * Matrix.of x) =
    (Matrix.of p.2 * (Matrix.of p.1 * Matrix.of q.2 * (Matrix.of p.1)⁻¹)) * (Matrix.of p.1 * Matrix.of q.1) * Matrix.of x
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.of p.1 : Mat k r)⁻¹, gv_inv_mul hp.1.1, Matrix.one_mul]

theorem fold_inv (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    {u f : Mt k r → ℝ≥0∞} (hu : Measurable u) (hf : Measurable f)
    (hinv : ∀ p : Mt k r × Mt k r, (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r →
      ∀ x, u (Gm p x) = u x) :
    ∫⁻ x, u x * f x ∂D.μG = ∫⁻ x, u x * orbL D f x ∂ν := by
  rw [fold_par D hν (fun x => u x * f x) (hu.mul hf)]
  refine lintegral_congr fun x => ?_
  unfold orbL
  rw [← lintegral_const_mul (u x) (f := fun p => f (Gm p x)) (hf.comp (measurable_Gm_fst x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S D] with p hp
  rw [hinv p hp x]

def wt (x : Mt k r) : ℝ≥0∞ := bcPow (2 * AB k r) x

theorem measurable_wt : Measurable (wt (k := k) (r := r)) := bc_measurable_pow _

theorem gnInt_of (h : UnitaryGroupStructuralFacts) : GNIntSharp := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, -⟩, -⟩ := id h
  exact hGI


theorem key (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {ν : Measure (Mt k r)} (hν : Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν)
    {u : Mt k r → ℝ≥0∞} (hu : Measurable u)
    (hinv : ∀ p : Mt k r × Mt k r, (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r →
      ∀ x, u (Gm p x) = u x) :
    ∫⁻ x, u x * wt x ∂D.μG ≤
      (∫⁻ x, u x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ x, orbL D wt x * wt x ∂D.μG) ^ (1 / 2 : ℝ) := by
  have hN := measurable_orbL D (measurable_wt (k := k) (r := r))
  rw [fold_inv D hν hu measurable_wt hinv,
    fold_inv D hν hN measurable_wt (fun p hp x => orbL_inv h D measurable_wt hp x)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hu.aemeasurable hN.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
  simpa only [sq] using hH

def WeightedL1Bound (D : RealPlaceData k r Wp Wp) (X : SigData k r) (E : Submodule ℂ X.Hs) (B : X.Hs →ₗ[ℂ] Wp) : Prop :=
  ∃ C : ℝ, ∀ v ∈ E,
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖) D.μG ∧
      ∫ y : Mt k r, gN (Matrix.of y) ^ (-(2 * AB k r)) * ‖B (X.σ (Matrix.of y) v)‖ ∂D.μG ≤ C * ‖v‖

theorem closed_GV (h : UnitaryGroupStructuralFacts) : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact (hCG k r).closed

theorem aesm_of_contOn (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {F : Type} [NormedAddCommGroup F]
    [SecondCountableTopologyEither (Mt k r) F] {f : Mat k r → F} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun y : Mt k r => f (Matrix.of y)) D.μG := by
  have hf' : ContinuousOn (fun y : Mt k r => f (Matrix.of y)) {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := hf
  have hm := hf'.aestronglyMeasurable (μ := D.μG) (closed_GV h).measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm


end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
