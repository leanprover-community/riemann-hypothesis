import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement

section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]

omit [CompleteSpace H₁] [CompleteSpace FF] in

theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]

omit [CompleteSpace H₁] [CompleteSpace FF] in

theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩


end GlobalTheory.Contr

end
end

section
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.T.fockVectors_overVacuum_isometry

end GlobalTheory
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  atlas_forward_decl GlobalTheory.vacuumFock_all_records
end

section
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  GlobalTheory.T.thetaVacuumCharacters_realPlaces

end GlobalTheory
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  atlas_forward_decl GlobalTheory.vacChar_of_record
end

section
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  atlas_forward_decl GlobalTheory.modelsAreCoverSeries_of_hypotheses
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.Published GlobalTheory.Chain.RealIt

namespace GlobalTheory.Chain.ItPairObj

theorem exists_record (hD : DiscreteSeriesCover) (hH : HarishChandraModules) :
    ∃ X : ProvA, ChosenSeries X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X := by
  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)
  have a1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have a2 : admH2 X := GlobalTheory.JointHarm.fock_polynomials X
  have a3 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX
  have a5 : admQ5 X := hH.admQ5_of_harishChandraModules X
  have a6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have a7 : admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have a8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have a4 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8
  have h1 := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨X, hX, h1, GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩

theorem itPair_of_rows (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  obtain ⟨X, hX, h1, h2⟩ := exists_record hD hH
  exact itPair D X hX h1 h2 hF hV hB hC

theorem itPair_holds (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7) : ItPair D :=
  itPair_of_rows hD hH D (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D) (GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D) (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) GlobalTheory.Contr.contraction

end GlobalTheory.Chain.ItPairObj
end
