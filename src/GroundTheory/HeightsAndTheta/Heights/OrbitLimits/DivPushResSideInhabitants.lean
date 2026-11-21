import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularFibre
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory ReciprocityTheory.AnForm.M

def PushForwardOpen.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (O : Set X),
    IsOpen O →
    (∀ x ∈ O, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    (∀ j, ∀ᵐ u, u ∈ (A.chart j).target → (A.chart j).symm u ∉ O → locDens A Φ j u = 0) →
    (∀ᵐ y, (q ⁻¹' {y} ∩ O).Finite) →
    ∀ g : X → ℝ, MIntegrable A Φ g →
      Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x) ∧
        mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRegularDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val → IsClosed V →
    (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def PushForwardOpen.projLineAffineCoordinate : OnePoint ℂ → Fin 1 → ℂ := fun x _ => crd0 x

def PushForwardOpen.finitePlane : Set (OnePoint ℂ) := Set.range ((↑) : ℂ → OnePoint ℂ)

theorem PushForwardOpen.det_fderiv_oneVariable_ne_zero {F : ℂ → ℂ} {d : ℂ} {w : Fin 1 → ℂ}
    (hF : HasDerivAt F d (w 0)) (hd : d ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v : Fin 1 → ℂ => fun _ : Fin 1 => F (v 0)) w :
      (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0 := by
  have h : HasFDerivAt (fun v : Fin 1 → ℂ => fun _ : Fin 1 => F (v 0))
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) w :=
    hasFDerivAt_pi.2 fun _ => hF.hasFDerivAt.comp w (hasFDerivAt_apply 0 w)
  rw [h.fderiv, ← LinearMap.det_toMatrix', Matrix.det_unique]
  simpa [LinearMap.toMatrix'_apply] using hd

theorem PushForwardOpen.hyps_inhabited :
    (∀ i : Fin 1, IsPotential p1 ((fun _ : Fin 1 => fsPot) i)) ∧
    IsOpen PushForwardOpen.finitePlane ∧
    (∀ x ∈ PushForwardOpen.finitePlane, ∀ j, x ∈ (p1.chart j).source →
      AnalyticAt ℂ (PushForwardOpen.projLineAffineCoordinate ∘ (p1.chart j).symm) (p1.chart j x) ∧
        LinearMap.det (fderiv ℂ (PushForwardOpen.projLineAffineCoordinate ∘ (p1.chart j).symm) (p1.chart j x) :
          (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0) ∧
    (∀ j, ∀ᵐ u, u ∈ (p1.chart j).target → (p1.chart j).symm u ∉ PushForwardOpen.finitePlane →
      locDens p1 (fun _ : Fin 1 => fsPot) j u = 0) ∧
    (∀ᵐ y, (PushForwardOpen.projLineAffineCoordinate ⁻¹' {y} ∩ PushForwardOpen.finitePlane).Finite) ∧
    MIntegrable p1 (fun _ : Fin 1 => fsPot) (fun _ => (1 : ℝ)) := by
  refine ⟨fun _ => projLine_isSmoothPotential, OnePoint.isOpen_range_coe, ?_, ?_, ?_,
    mIntegrableCont p1 _ (fun _ => projLine_isSmoothPotential) _ continuous_const⟩
  · rintro _ ⟨z, rfl⟩ j hj
    fin_cases j
    · have e : PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtZero.symm =
          fun v : Fin 1 → ℂ => fun _ : Fin 1 => id (v 0) := rfl
      change AnalyticAt ℂ (PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtZero.symm) (projectiveLineChartAtZero z) ∧
        LinearMap.det (fderiv ℂ (PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtZero.symm) (projectiveLineChartAtZero z) :
          (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0
      rw [e]
      exact ⟨projLine_analyticAt_const_apply_zero _, PushForwardOpen.det_fderiv_oneVariable_ne_zero (hasDerivAt_id _)
        one_ne_zero⟩
    · have hz : z ≠ 0 := fun h => hj (by rw [h])
      have e : PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtInfinity.symm =
          fun v : Fin 1 → ℂ => fun _ : Fin 1 => (v 0)⁻¹ := by
        funext v i
        simp [PushForwardOpen.projLineAffineCoordinate]
      have hw : (projectiveLineChartAtInfinity (z : OnePoint ℂ)) 0 ≠ 0 := by
        simp [projLineChart1_apply, hz]
      change AnalyticAt ℂ (PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtInfinity.symm) (projectiveLineChartAtInfinity z) ∧
        LinearMap.det (fderiv ℂ (PushForwardOpen.projLineAffineCoordinate ∘ projectiveLineChartAtInfinity.symm) (projectiveLineChartAtInfinity z) :
          (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0
      rw [e]
      exact ⟨projLine_analyticAt_const_inv_apply_zero hw, PushForwardOpen.det_fderiv_oneVariable_ne_zero (hasDerivAt_inv hw)
        (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hw)))⟩
  · intro j
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 1 → ℂ))] with u hu _ hO
    exfalso
    fin_cases j
    · exact hO ⟨u 0, rfl⟩
    · refine hu (Set.mem_singleton_iff.2 (funext fun i => ?_))
      rw [Subsingleton.elim i 0]
      by_contra h
      exact hO (projLineChart1_symm_mem_range.2 h)
  · refine Filter.Eventually.of_forall fun y => Set.Subsingleton.finite ?_
    rintro _ ⟨h1, a, rfl⟩ _ ⟨h2, b, rfl⟩
    have ha : a = y 0 := congrFun (Set.mem_singleton_iff.1 h1) 0
    have hb : b = y 0 := congrFun (Set.mem_singleton_iff.1 h2) 0
    rw [ha, hb]


abbrev ProjRegular.pointV : Set ProjectiveLineResolution.res.X := {((0 : ℂ) : OnePoint ℂ)}

instance ProjRegular.instUniquePointV : Unique ProjRegular.pointV :=
  Set.uniqueSingleton _

def ProjRegular.projFirstCoordinate : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) :=
  LinearMap.pi fun _ : Fin 1 =>
    LinearMap.proj (R := ℂ) (φ := fun _ : ((k : Unit) → PBlk 2 k) => ℂ) (fun _ => 0)

theorem ProjRegular.analyticAt_of_zero_dim {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : (Fin 0 → ℂ) → F) (u : Fin 0 → ℂ) : AnalyticAt ℂ f u := by
  have e : f = fun _ => f u := funext fun v => congrArg f (Subsingleton.elim v u)
  rw [e]
  exact analyticAt_const

theorem ProjRegular.holoMap_pointV :
    HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val :=
  ⟨continuous_subtype_val, fun _ _ u _ => ProjRegular.analyticAt_of_zero_dim _ u⟩

theorem ProjRegular.projFirstCoord_segre_lift_ne_zero :
    ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 := by
  intro x hx
  obtain rfl : x = ((0 : ℂ) : OnePoint ℂ) := hx
  intro h
  have h0 := congrFun h 0
  change ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.lift ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ))) 0
    = 0 at h0
  rw [ProjectiveLineResolution.lift_coe] at h0
  simp [ProjRegular.projFirstCoordinate, segre] at h0

theorem ProjRegular.hyps_inhabited :
    HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val :=
  ProjRegular.holoMap_pointV

theorem ProjRegularFibre.hyps_inhabited :
    HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val ∧ IsClosed ProjRegular.pointV ∧
      ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 :=
  ⟨ProjRegular.holoMap_pointV, isClosed_singleton, ProjRegular.projFirstCoord_segre_lift_ne_zero⟩

theorem ProjRegularDens.hyps_inhabited :
    (∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine (PBlk 2)) j)) ∧
      HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val ∧
      IsClosed ProjRegular.pointV ∧
      ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 :=
  ⟨fun j => j.elim0, ProjRegular.holoMap_pointV, isClosed_singleton, ProjRegular.projFirstCoord_segre_lift_ne_zero⟩




end GroundTheory.Heights₂.Heights.Targets
end
end
