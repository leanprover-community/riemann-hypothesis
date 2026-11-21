import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  have := hc.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this

end GlobalTheory.CompanionTheory.SqIntFD
end
end

section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.PosNormFD

theorem posNorm : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.PosNorm := by
  intro E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  have hc : Continuous φ.1 := GlobalTheory.CuspRep.IsAutForm.continuous hA
  have hl := GlobalTheory.DiscreteUnit.left_latticeGL hA hS
  by_contra h0
  have h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0 := by simpa using h0
  have hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2 := hc.enorm.measurable.pow_const 2
  have hz := (lintegral_eq_zero_iff hm).1 h0'
  have hSo : IsOpen {g | φ.1 g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hSo.measurableSet]
    refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
    have hg' : φ.1 g ≠ 0 := hg
    simpa [hg'] using hg'
  have hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : φ.1 (γ⁻¹ • x) = φ.1 x := hl _ (γ⁻¹).2 x
    simp only [Set.mem_setOf_eq, e]
  have hS0 := h𝓕.measure_zero_of_invariant _ hinv hSF
  have hemp := (hSo.measure_eq_zero_iff μ).1 hS0
  refine hne (Subtype.ext (funext fun g => ?_))
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.1 hemp g) hg

end GlobalTheory.CompanionTheory.PosNormFD
end

section
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem sqMass_ne_top_and_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
      ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
        (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  intro E _ _ _ N _ _ μ _ F hF φ hA hS hne
  exact ⟨(GlobalTheory.CompanionTheory.SqIntFD.sqIntAt E N μ F hF φ hA hS).ne,
    (GlobalTheory.CompanionTheory.PosNormFD.posNorm E N μ F hF φ hA hS hne).ne'⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_norm_finite_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
    (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FinDisc.sqMass_ne_top_and_ne_zero
end
