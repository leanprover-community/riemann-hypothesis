module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergenceStatement

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SqFubini

def eY (d : ℕ) : ((Fin d → ℂ) × ℂ) ≃ᵐ (Fin (d + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm

theorem eY_apply {d : ℕ} (x : (Fin d → ℂ) × ℂ) : eY d x = Fin.cons x.2 x.1 := by
  first | rfl | (simp [eY, MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eY, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eY_measurePreserving (d : ℕ) : MeasurePreserving (eY d) volume volume :=
  (Measure.measurePreserving_swap).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm

def eW (d : ℕ) : ((Fin d → ℂ) × (ℂ × ℂ)) ≃ᵐ (Fin (d + 2) → ℂ) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ)
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem eW_apply {d : ℕ} (x : (Fin d → ℂ) × (ℂ × ℂ)) :
    eW d x = Fin.cons x.2.1 (Fin.cons x.2.2 x.1) := by
  first | rfl | (simp [eW, MeasurableEquiv.prodComm, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eW, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eW_measurePreserving (d : ℕ) : MeasurePreserving (eW d) volume volume :=
  ((Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc volume volume volume)).trans
    (((MeasurePreserving.id volume).prod
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem fubini_piece {Y P Z : Type*} [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure P) (ρ : Measure Z) [SFinite μ] [SFinite ν]
    (e : (Y × P) ≃ᵐ Z) (he : MeasurePreserving e (μ.prod ν) ρ) (B : Set Y) (S : Set Z)
    (hS : e ⁻¹' S = B ×ˢ Set.univ) (F : Z → ℝ) (hF : IntegrableOn F S ρ) :
    IntegrableOn (fun y => ∫ p, F (e (y, p)) ∂ν) B μ ∧
      ∫ z in S, F z ∂ρ = ∫ y in B, ∫ p, F (e (y, p)) ∂ν ∂μ := by
  have h1 : IntegrableOn (F ∘ e) (B ×ˢ Set.univ) (μ.prod ν) := by
    rw [← hS]
    exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hF
  have h2 : ∫ z in S, F z ∂ρ = ∫ x in B ×ˢ Set.univ, F (e x) ∂(μ.prod ν) := by
    rw [← hS]
    exact (he.setIntegral_preimage_emb e.measurableEmbedding F S).symm
  constructor
  · have h3 : Integrable (F ∘ e) ((μ.restrict B).prod (ν.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact h1
    simpa [IntegrableOn, Function.comp_def] using h3.integral_prod_left
  · rw [h2]
    simpa [Function.comp_def] using setIntegral_prod (F ∘ e) h1

theorem fibre_sum {d k : ℕ} (B : Set (Fin d → ℂ)) (F : ℕ → (Fin (d + 2) → ℂ) → ℝ)
    (H : (Fin (d + 1) → ℂ) → ℝ) (κ : ℝ)
    (hF : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B})
    (hH : IntegrableOn H {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B})
    (hpt : ∀ y ∈ B, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
      κ * ∫ a : ℂ, H (Fin.cons a y))
    (hB : MeasurableSet B) :
    ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B}, F i z =
      κ * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B}, H z := by
  have hSW : (eW d) ⁻¹' {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eW_apply]
  have hSY : (eY d) ⁻¹' {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eY_apply]
  have hW := fun i (hi : i < k) => fubini_piece volume volume volume (eW d) (eW_measurePreserving d) B _ hSW
    (F i) (hF i hi)
  have hY := fubini_piece volume volume volume (eY d) (eY_measurePreserving d) B _ hSY H hH
  simp only [eW_apply, eY_apply] at hW hY
  rw [hY.2, Finset.sum_congr rfl fun i hi => (hW i (Finset.mem_range.1 hi)).2,
    ← integral_finsetSum _ fun i hi => (hW i (Finset.mem_range.1 hi)).1, ← integral_const_mul]
  exact setIntegral_congr_fun hB fun y hy => hpt y hy

theorem ae_ne (d : ℕ) : ∀ᵐ z : Fin (d + 2) → ℂ, z 0 ≠ z 1 := by
  let L : (Fin (d + 2) → ℂ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 0) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 1)
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (d + 2) → ℂ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L, LinearMap.mem_ker, Pi.single_apply] at h1
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin (d + 2) → ℂ)) (LinearMap.ker L) hs
  refine measure_mono_null ?_ h0
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
  simp [L, LinearMap.mem_ker, hz]

theorem isC2At_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {σ : Type} [Fintype σ]
    (c : σ → ℝ) (P : σ → LocPot X) (x : X) (h : ∀ a, IsTwiceDifferentiableAt A (P a) x) : IsTwiceDifferentiableAt A (sumPot c P) x := by
  intro j hj
  have : (sumPot c P).φ x ∘ (A.chart j).symm =
      fun y => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) y := rfl
  rw [this]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (h a j hj)

end SqFubini

namespace SqFubini

def EW {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k i : ℕ) :
    Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
  let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i
  fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))

def EY {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k : ℕ) :
    Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
  fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)

end SqFubini

end GlobalTheory.CompanionTheory.Ar.PB
