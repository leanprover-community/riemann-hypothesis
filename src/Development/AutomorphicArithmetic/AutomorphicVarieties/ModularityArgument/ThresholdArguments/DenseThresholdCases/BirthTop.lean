import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.FinOrdKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ValIffMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.IndAutLOfAutCsP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Sp4In
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.Loc2
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDominantEvaluation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalZetaOfAnnulusFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIntegrandIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Smooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitivePointwiseBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralAbsoluteBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodUnipotentThirdPart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodUnipotentSecondPart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G0
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeOfVariablesIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParsevalBoundOfInnerNe
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.RotationScalingMulVecSnd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivZeroOut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightRegularity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateQuadraticWeightTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondWeightIntegralBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFixedDeterminantTerm
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.MellinTransforms.UnfoldA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMulSupportBnd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GaugeC
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulReal
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.BndMeas
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulBLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurePreservingMixedSpaceReal
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.ContinuousUnipotentTranslatesHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.smoothLie
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.InverseLowerLeftStandardElement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConverseTheoremUnipotentExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementarySubgroupInvariance
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConverseTheoremConstantTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConverseTheoremCuspidality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerExpansionUnipotent
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.OrderedCechToCatCochainsOneApplyValueAtSubset
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.InverseLowerLeftNeZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.growthAd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.RsOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.EulOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FinsumOfIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HeightVanishingHypotheses
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FinOrderOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HypothesesZ''
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVREGOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistRealSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpSol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthEG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaUnramifiedOfKillsRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuDefsA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContDelta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AutomorphyRankFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGIndAutCs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AlgPosOfExpo
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSphOfUnrW

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
namespace UpperTheory.V.Sd.EG
section Norm
variable {l : ℕ} [hl : Fact l.Prime]
private theorem root_small {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have hx := norm_root hl.out.ne_zero h
  have hy : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])
  have e := add_pow_prime_eq hl.out (x - 1) 1
  rw [sub_add_cancel, h, one_pow] at e
  set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS
  have hs : ‖S‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S)) := by linear_combination -e
  have h3 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, e2, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3
variable (l) in
private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu
private theorem cong_mul {a u : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hu : u ∈ U l) : Cong (a * u) a := by
  have e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1) := by push_cast; ring
  unfold Cong
  rw [e, norm_mul, ha, one_mul]
  exact hu
private theorem resSum_of {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ)
    (ht : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s)‖ < 1)
    (hd : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s‖ < 1) : ResSum ρ ![1, Φ] := by
  intro s i
  have e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) =
      C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X +
        C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s) := by
    rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]
    ring
  rw [← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]
  refine small_add ?_ ?_
  · split_ifs
    · rw [norm_neg]; exact ht s
    · simp
  · split_ifs
    · exact hd s
    · simp
private theorem trace_inv {K : Type} [Field K] (g : GL (Fin 2) K) (d : Kˣ) (h : Matrix.GeneralLinearGroup.det g = d⁻¹) :
    ((d : K) • (g : Matrix (Fin 2) (Fin 2) K)).trace = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  have h1 := congrArg Units.val h
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
  rw [Matrix.coe_units_inv, Matrix.inv_def, h1, Ring.inverse_unit, inv_inv, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [add_comm]
end Norm
section Gal
variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem dec_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {γ : G ℚ Ω}
    (hγ : IsFrob A (normV v) γ) (K : Subgroup (G ℚ Ω)) (hI : Ine (F := ℚ) A ≤ K) (hK : γ ∈ K) :
    Dec (F := ℚ) A ≤ K.topologicalClosure := by
  haveI : IsGalois ℚ Ω := {}
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  refine le_trans (le_sInf ?_) key.ge
  rintro N ⟨hNo, hN⟩
  have h := (Subgroup.le_topologicalClosure _).trans hN
  exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)
private theorem above_of {ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hρ : Continuous ρ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn ρ (Dec (F := ℚ) A) κ) (hI : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1)
    (hF : ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A (normV v) (σ : G ℚ Ω) → κ 0 σ ∈ U l) (s : ↥(Dec (F := ℚ) A)) :
    κ 0 s * κ 1 s = Matrix.GeneralLinearGroup.det (ρ s) ∧ κ 0 s ∈ U l := by
  obtain ⟨g, hg⟩ := hκ
  constructor
  · have e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← e]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
    simp
  · obtain ⟨γ, hγ⟩ := exists_isFrob hv
    have h1 := dec_le hv hγ (((U l).comap (κ 0)).map (Dec (F := ℚ) A).subtype)
      (fun t ht => ⟨⟨t, ht.1⟩, by
        show κ 0 _ ∈ U l
        rw [hI _ ht]; exact one_mem _, rfl⟩)
      ⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2
    have hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1 :=
      ((continuous_apply 0).comp ((continuous_apply 0).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const
    have h2 := closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1}) (by
      rintro _ ⟨t, ht, rfl⟩
      show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1
      rw [(hg t).2]
      exact ht) (isClosed_small hc) h1
    show ‖_‖ < 1
    rw [← (hg s).2]
    exact h2
private theorem core (P : _root_.UpperTheory.V.Af.HypothesesH') (hl2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {φ θ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = φ * θ) (hθ : θ ^ l = 1) :
    ∃ ρ, EisRep ι φ θ k ρ := by
  obtain ⟨c, π, r, H, htr⟩ := _root_.UpperTheory.V.Sd.EG.exists_ordinary_form_trace_near_one_add_cyc P ι hk hN hχ g hg hm
  have hθU : ∀ s, θ s ∈ U l := fun s => root_small (by
    have := DFunLike.congr_fun hθ s
    rw [MonoidHom.pow_apply] at this
    rw [← Units.val_pow_eq_pow_val, this]; rfl)
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD
  set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDΦ : ∀ s, D s = Φ s * θ s := fun s => by simp [hD, hΦ, mul_assoc]
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    have := congrArg norm (hDv s)
    rwa [norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one] at this
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1 := fun s => by
    rw [hDΦ]; exact cong_mul (hΦn s) (hθU s)
  have hdr : ∀ s, Matrix.GeneralLinearGroup.det (r s) = (D s)⁻¹ := fun s => by
    refine (DFunLike.congr_fun H.det s).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv]
    rfl
  have hdet : ∀ s, (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    rw [tw_val, Matrix.det_smul, ← Matrix.GeneralLinearGroup.val_det_apply, hdr, Fintype.card_fin, sq, mul_assoc, Units.mul_inv, mul_one]
  have SF := shapeFacts l (G ℚ Ω) 2 r D
  have hc0 : Continuous fun s => (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    simp only [tw_val]
    exact hDc.smul (Units.continuous_val.comp H.cont)
  have halg := (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results P.toClassicalTheorems ℚ Ω l ι).1 ((k - 1 : ℕ) : ℤ) (φ * θ) (hm ▸ dirG_open _)
  rw [zpow_natCast] at halg
  refine ⟨tw r D, Units.continuous_iff.2 ⟨hc0, ?_⟩, SF.2.2.2.2.2 (_root_.UpperTheory.V.Sd.ordinary_irreducible_of_printed_hida P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H),
    _root_.UpperTheory.V.Sd.twist_real_selfDual P.toClassicalTheorems ℚ Ω l ι 2 r D halg ⟨π, H.reg, H.att⟩, MonoidHom.ext fun s => Units.ext (hdet s),
    resSum_of _ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩
  · simp only [← map_inv]
    exact hc0.comp continuous_inv
  · have := small_add (htr s) (hcong s)
    rw [tw_val, trace_inv _ _ (hdr s), ← map_inv]
    convert this using 2
    ring
  · rw [hdet]; exact hcong s
  · refine (shapeFacts l (G ℚ Ω) 2 _ 1).2.1 _ _ _ (Equiv.swap 0 1) (SF.1 _ _ (_root_.UpperTheory.V.Z.Win.RR.ordAway_a_alt P ℚ Ω l ι _ _ _ _ _ _ _ H A hA))
      fun i s hs => ?_
    have h1 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l A).2.2.2 hA hs
    have h2 : D s = (φ * θ) s := by
      rw [hD, MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, one_mul]
    fin_cases i
    · show 1 = ((φ * θ) s)⁻¹ * D s
      rw [h2, inv_mul_cancel]
    · show (φ * θ) s = 1 * D s
      rw [h2, one_mul]
  · obtain ⟨w, hw, hwl, hmem⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A l hl.out hA
    obtain ⟨κ, hκ, hI, hFr⟩ := _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_printsH P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H w hmem A hw
    have hI0 : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1 := fun s hs => (hI 0 s hs).trans (zpow_zero _)
    have key := above_of H.cont hw hκ hI0 fun σ hσ => by
      have h1 : κ 0 σ⁻¹ * cycBar ℚ Ω l (σ : G ℚ Ω) ^ (0 : ℤ) ∈ U l := hFr σ hσ
      rwa [zpow_zero, mul_one, map_inv, inv_mem_iff] at h1
    have h1 : ∀ s : ↥(Dec (F := ℚ) A), κ 1 s * D s = (κ 0 s)⁻¹ := fun s => by
      rw [eq_inv_iff_mul_eq_one, mul_comm, ← mul_assoc, (key s).1, hdr, inv_mul_cancel]
    refine ⟨_, SF.2.2.1 _ κ hκ, fun i s hs => ?_, fun i s => ?_⟩
    · fin_cases i
      · have h2 : (φ * θ) s = 1 := hm ▸ dirG_unr _ (not_over hl.out hA hN) hs
        show κ 0 s * D s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)
        rw [hI0 s hs, one_mul, hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply,
          show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      · show κ 1 s * D s = cycBar ℚ Ω l s ^ (0 : ℤ)
        rw [h1, hI0 s hs, inv_one, zpow_zero]
    · fin_cases i
      · show Cong (κ 0 s * D s) (Φ s)
        rw [hDΦ, mul_comm, mul_assoc]
        exact cong_mul (hΦn s) (mul_mem (hθU s) (key s).2)
      · show Cong (κ 1 s * D s) 1
        rw [h1]
        exact inv_mem (key s).2
private theorem dirG_dvd {O : Type} [CommRing O] {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (χ : DirichletCharacter O M) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ ((((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N).val : ℕ) : ZMod M) := by
  rw [dirG_val, ← (Chr.clsFacts ℚ Ω N).2.1 M h, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
private theorem dirG_ne_one {M : ℕ} [NeZero M] {O : Type} [CommRing O] {χ : DirichletCharacter O M} (h : Chr.dirG ℚ Ω χ ≠ 1) : M ≠ 1 := by
  rintro rfl
  refine h (MonoidHom.ext fun s => ?_)
  rw [Chr.dirG, MonoidHom.comp_apply, Subsingleton.elim (Chr.cls ℚ Ω 1 s) 1, map_one, MonoidHom.one_apply]
end Gal
private theorem exists_mul {M w : ℕ} [NeZero (M * w)] (φ : DirichletCharacter ℂ M) (θ : DirichletCharacter ℂ w) :
    ∃ χ : DirichletCharacter ℂ (M * w), ∀ n : ℕ, χ (n : ZMod (M * w)) = φ (n : ZMod M) * θ (n : ZMod w) := by
  refine ⟨DirichletCharacter.changeLevel (dvd_mul_right M w) φ * DirichletCharacter.changeLevel (dvd_mul_left w M) θ, fun n => ?_⟩
  by_cases h : n.Coprime (M * w)
  · have h' : IsCoprime (n : ℤ) ((M * w : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' φ (dvd_mul_right M w) h'
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' θ (dvd_mul_left w M) h'
    rw [Int.cast_natCast, Int.cast_natCast] at h1 h2
    rw [MulChar.mul_apply, h1, h2]
  · rw [MulChar.map_nonunit _ (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h'))]
    rw [Nat.coprime_mul_iff_right, not_and_or] at h
    rcases h with h | h
    · rw [φ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), zero_mul]
    · rw [θ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), mul_zero]
end UpperTheory.V.Sd.EG
open UpperTheory.V.Sd.EG in
theorem UpperTheory.V.Sd.propEG_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropEG := by
  intro P l hl Ω _ _ _ ι c hc N w φ θ hx hs hφ
  obtain ⟨M, _, φ₀, hMN, hφp, rfl⟩ := dirOf l Ω ι N hx.pos φ hs.1
  obtain ⟨w', _, θ₀, hw, -, hθ⟩ := dirOf l Ω ι w hx.prime.pos θ hx.mu
  obtain rfl : w' = w := ((Nat.dvd_prime hx.prime).1 hw).resolve_left (dirG_ne_one (hθ ▸ hx.ne))
  haveI : NeZero N := ⟨hx.pos.ne'⟩
  haveI : NeZero (M * w') := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w')⟩
  haveI : Fact w'.Prime := ⟨hx.prime⟩
  obtain ⟨χ, hχ⟩ := exists_mul φ₀ θ₀
  have hne : θ₀ ≠ 1 := by
    rintro rfl
    refine hx.ne (hθ.trans ?_)
    ext s
    rw [dirG_val]
    simp
  have hpow : θ₀ ^ l = 1 := by
    ext u
    obtain ⟨s, rfl⟩ := (Chr.clsOnto Ω w').1 u
    have h1 := congrArg Units.val (DFunLike.congr_fun hx.pow s)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hθ, dirG_val] at h1
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    apply ι.symm.injective
    rw [map_pow, map_one]
    exact h1
  have hdvd : l ∣ w' - 1 := by
    have h1 : orderOf θ₀ = l := orderOf_eq_prime hpow hne
    rw [← h1, ← ZMod.card_units w']
    refine orderOf_dvd_of_pow_eq_one ?_
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hφw : φ₀ (w' : ZMod M) = 1 := by
    have hcop : w'.Coprime N := (Nat.Prime.coprime_iff_not_dvd hx.prime).2 hx.wN
    obtain ⟨s, hs1⟩ := (Chr.clsOnto Ω N).1 (ZMod.unitOfCoprime w' hcop)
    have h1 : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ ^ w' := fun ζ hζ => by
      rw [Chr.cls_spec N s ζ hζ, hs1, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod w' hζ]
    have h2 := congrArg Units.val (hs.2 s h1)
    rw [dirG_val, cls_pow (hcop.coprime_dvd_right hMN) fun ζ hζ => h1 ζ (by
      obtain ⟨d, rfl⟩ := hMN
      rw [pow_mul, hζ, one_pow])] at h2
    apply ι.symm.injective
    rw [map_one]
    exact h2
  have E : EDat l M w' φ₀ θ₀ χ :=
    ⟨hx.odd, lt_of_le_of_ne (NeZero.pos M) (dirG_ne_one hφ).symm, fun h => hx.cop (h.trans hMN), hφp, hx.prime, hdvd,
      fun h => hx.wN (h.trans hMN), hφw, hne, hpow, hχ⟩
  have hlN : ¬ l ∣ M * w' := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl.out).1 hd with hd | hd
    · exact E.cop hd
    · have h1 : l ∣ w' - (w' - 1) := Nat.dvd_sub hd hdvd
      have := hx.prime.pos
      rw [show w' - (w' - 1) = 1 by omega] at h1
      exact hl.out.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨k₀, hk₀⟩ := propE l ι M w' φ₀ θ₀ χ E
  refine ⟨max k₀ 3, fun k hk hpar => ?_⟩
  obtain ⟨g, hg⟩ := hk₀ k (le_of_max_le_left hk) (by
    have h1 := congrArg Units.val hpar
    rw [dirG_val, (Chr.clsFacts ℚ Ω M).2.2.2.1 c hc, Units.val_neg, Units.val_one] at h1
    apply ι.symm.injective
    rw [map_pow, map_neg ι.symm, map_one ι.symm]
    simpa using h1)
  refine core P hx.odd ι (le_of_max_le_right hk) hlN (ePrim l M w' φ₀ θ₀ χ E) g hg ?_ hx.pow
  ext s
  rw [hθ, MonoidHom.mul_apply, Units.val_mul, dirG_dvd dvd_rfl, dirG_dvd (dvd_mul_right M w'), dirG_dvd (dvd_mul_left w' M)]
  simp only [MulChar.ringHomComp_apply]
  rw [hχ, map_mul]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V.Z.Bc
open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.HV UpperTheory.V.Lit
theorem hypothesesZ' (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Bc.HypothesesZ' := ⟨hH.toClassicalTheorems, _root_.UpperTheory.V.Sd.propEG_of_printsH hH, _root_.UpperTheory.V.Z.Bc.upSol_of_alt hH.toClassicalTheorems hH.cyc⟩
end UpperTheory.V.Z.Bc
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl
private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous
private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F
private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero
end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
open UpperTheory.V.Cu.RankFourTensorSourceAtPrime in
theorem UpperTheory.V.Cu.tower_is_initial_of_ok :
    UpperTheory.V.Cu.AlNe → UpperTheory.V.Cu.WtsOf4 → UpperTheory.V.Cu.IrrOf4 → UpperTheory.V.Cu.AutOf4 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
      (d : UpperTheory.V.Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → OffW d.ι d.K' d.ρ (UpperTheory.V.Cu.tenB d.ρ₁ d.τ) →
      T.IsSeedAlt d.ι ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))) := by
  intro hne hW hI hA Ω _ _ _ l _ d T hT hok hrw
  have hi := hI Ω l d T hT hok
  obtain ⟨π, h1, h2⟩ := hA Ω l d T hT hok hi
  obtain ⟨U, j, hU, hj⟩ := d.tw.wt
  have hm := d.tau.pos
  have hk := d.big
  let φ : G ℚ Ω →* (Qbar l)ˣ := (toB d.δ)⁻¹ ^ 2 * cycBar ℚ Ω l ^ j
  have hle : U ≤ φ.ker := fun g hg => by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hg)
    rw [map_pow, map_zpow] at this
    have e : toB d.δ g ^ 2 = cycBar ℚ Ω l g ^ j := this.trans (congrArg (· ^ j) (toB_chi d.c g))
    show (toB d.δ g)⁻¹ ^ 2 * cycBar ℚ Ω l g ^ j = 1
    rw [← e, inv_pow, inv_mul_cancel]
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : Finite (G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle hU)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨hi, _, ((toB d.δ).comp (resQ T.L))⁻¹, π, -j, φ.ker.index, fun i => ?_,
    hW Ω l d T U j hU hj, ((cont_delta d).comp (cont_res T.L)).inv, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,
    ⟨(d.k : ℤ) - 1 + d.m, by simp <;> ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' h1 (autOf4W hne Ω l d T hT hok hi hrw π h1 h2), h2⟩
  · fin_cases i
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
    · exact ⟨(d.k : ℤ) - 1 - 2 * d.m, by omega, by simp <;> ring⟩
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
  · have := φ.ker.pow_index_mem (resQ T.L s)
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [neg_neg]
    exact this
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu in
theorem UpperTheory.V.Cu.fourth_initial_of_rank_four_data : AlNe → _root_.UpperTheory.V.Cu.TauExAlt → RankFourAutomorphyOfTensor → RhoExP → TwEx4 → PairOf4 → ResOf4 → ContOf4 → EntOf4 → OverOf4 → WtsOf4 → IrrOf4 →
    AutOf4 → _root_.UpperTheory.V.Af.Hypotheses' → PropEGP → _root_.UpperTheory.V.Cu.SeedIVAlt := by
  intro hne hTau hAQ hRho hTw hPair hRes hCont hEnt hOver hWts hIrr hAut hH hP Ω _ _ _ l _ c D T₀ hc hok h4 ι 𝔞
  have hg : D.Good := hc.1
  obtain ⟨K', _, hq⟩ := h4.quad
  have hfix : ∀ (T : Tower D) (g : G T.F Ω), resQ T.F g ∈ T.F.fixingSubgroup := fun T g x => g.commutes x
  have hg0 : resQ T₀.F T₀.g0 ∉ K'.fixingSubgroup := by
    intro hm
    have h1 := hq.on _ hm
    apply hok.dist 0 1 (by decide)
    have h2 : residue c.O (((chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 1 (resQ T₀.F T₀.g0))⁻¹) ^ (1 : ℤ) *
        (chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 2 (resQ T₀.F T₀.g0))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = 1 := h1
    rw [zpow_one, zpow_zero, mul_one] at h2
    have h3 := congrArg (· * residue c.O (chi D T₀.pr 1 (resQ T₀.F T₀.g0) : c.O)) h2
    simp only [← map_mul, ← Units.val_mul, inv_mul_cancel_right, one_mul] at h3
    exact h3
  obtain ⟨m, c₀, κ, hκ⟩ := hTau hH Ω l ι K' hg.l_odd hq.deg hq.imag hq.disc hq.split ⟨D.cc, hg.isCC⟩ _ hg0
  obtain ⟨w, θ, k, ρ, c₁, h, ρ₁, x, hw, hsp, hθl, hθm, hB, hk, hE, ⟨hI, hrw⟩, h₀, hM⟩ :=
    hRho hP Ω l c D T₀ hc hok h4 ι (2 * (m * 9) + 3) c₀
  obtain ⟨j, j1, j9, hj⟩ := hAQ Ω l ι K' hq.deg hq.imag ρ hE.cont hE.aut hI hrw _ m c₁ κ hg0 (hκ c₁ h₀ 1 le_rfl)
  obtain ⟨τ, s, hτ⟩ := hκ c₁ h₀ j j1
  obtain ⟨δ, hδ⟩ := hTw Ω l c D T₀ hc k (by omega) hk
  have hbig : 2 * (m * j) + 3 ≤ k := le_trans (by have := Nat.mul_le_mul_left m j9; omega) hB
  obtain ⟨hunr, hdies⟩ := UpperTheory.theta_unramified_of_kills_roots_of_unity Ω l w hw θ hθl hθm
  let d : Dat Ω l := ⟨ι, c, D, T₀, hc, hok, K', hq, k, m * j, hbig, hk, δ, hδ, θ, ρ, hE, hI, c₁, h, ρ₁, x, hM, τ, s, κ ^ j, hτ,
    (hj ρ₁ τ s hM.iso hτ).1, w, hw, hsp, hunr⟩
  have hf : ∀ y ∈ maximalIdeal c₁.O, 𝔞.red c₁ y = 0 := fun y hy =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c₁) y hy)
  have hred : 𝔞.red c = (𝔞.red c₁).comp (inc h) := RingHom.ext fun y => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h y).symm
  have hle : T₀.Le T₀ := ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩
  obtain ⟨r1, r2, -, r3⟩ := hRes Ω l d T₀ hle {w} 𝔞.k (𝔞.red c₁) hf
  refine ⟨w, (d.Q T₀).map (𝔞.red c₁), hw, hsp, ⟨?_, ?_, (hCont Ω l d T₀).2 _ _ hf⟩, r2,
    fun T hT tok hd => ⟨c₁, h, d.Q T, ⟨?_, (hCont Ω l d T).1, ?_, ?_⟩, hOver Ω l d T hT _ _ hf,
      (hRes Ω l d T hT ∅ 𝔞.k (𝔞.red c₁) hf).2.2.1, hEnt Ω l d T hT tok _ _ hf⟩⟩
  · rw [hred]
    exact hPair Ω l d T₀ hle hok {w} 𝔞.k (𝔞.red c₁) (fun g _ => r3 g) fun A hA g hg =>
      hunr A (fun p hp => hA p (Finset.mem_insert_of_mem hp)) hg
  · rw [hred]
    exact r1
  · have := hPair Ω l d T hT tok ∅ c₁.O (RingHom.id _) (fun g hg => hM.det g (hdies T.F hd hg)) fun A _ g _ =>
      hdies T.F hd (hfix T g)
    have e : (d.Q T).map (RingHom.id c₁.O) = d.Q T := by
      ext <;> rfl
    rwa [e, RingHom.id_comp] at this
  · exact (hRes Ω l d T hT ∅ _ (residue c₁.O) fun y hy => (residue_eq_zero_iff _).2 hy).1
  · exact _root_.UpperTheory.V.Cu.tower_is_initial_of_ok hne hWts hIrr hAut Ω l d T hT tok (hj ρ₁ τ s hM.iso hτ).2
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Cu
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem as_infOf (M : Multiset ℂ) (h2 : M.card = 2) (hz : ∀ z ∈ M, ∃ k : ℤ, z = (k : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2) :
    ∃ a b : ℤ, M = infOf ![a, b] ∧ M = {(a : ℂ) + 1 / 2, (b : ℂ) + 1 / 2} := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h2
  obtain ⟨a, rfl⟩ := hz x (by simp)
  obtain ⟨b, rfl⟩ := hz y (by simp)
  have e : ∀ a : ℤ, (a : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 = ((a + 1 : ℤ) : ℂ) + 1 / 2 := fun a => by push_cast; ring
  refine ⟨a + 1, b + 1, ?_, by rw [e, e]⟩
  have : (Finset.univ : Finset (Fin 2)).val = {0, 1} := rfl
  rw [infOf, this, e, e]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1 <;> [skip; congr 1] <;> push_cast <;> ring
private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (h : IsIrr r) : IsIrr (tw r κ) := by
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hi => h.2.2 W hW fun s v hv => ?_⟩
  have := W.smul_mem (((κ s)⁻¹ : kˣ) : k) (hi s v hv)
  rw [tw_val, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at this
  exact this
private theorem irr_tw_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (φ : Γ' →* Γ)
    (h : IsIrr (r.comp φ)) : IsIrr ((tw r κ).comp φ) :=
  irr_tw (r.comp φ) (κ.comp φ) h
private theorem tw_one {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (s : Γ) (h : r s = 1) (h' : κ s = 1) :
    tw r κ s = 1 := Units.ext (by rw [tw_val, h, h']; simp)
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Cu.rank_four_automorphy_of_tensor_of_base_change_of_induction (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : Z.InvariantSubmoduleMonicPolynomial.E.IndAutCs) (hP : PolOf4) (hB : BadOfW) : RankFourAutomorphyOfTensor := by
  intro Ω _ _ _ l _ ι K' _ h2 hc ρ hρ ⟨π, hreg, hatt⟩ hio hrw g0 m c₁ κ hg0 ⟨τ₀, s₀, h₀⟩
  haveI : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have RK := resFacts ℚ K' Ω l 2 ρ
  obtain ⟨P₀, reg₀, att₀, -⟩ := hQ ℚ K' Ω l ι h2 ρ π hρ hreg hatt (RK.2.2.2.1.1 (hio _ RK.2.1))
  obtain ⟨j, j1, j9, hj⟩ := Cu2.goodJ K' h2 P₀ reg₀ m (by simpa using h₀.pos)
  refine ⟨j, j1, j9, fun ρ₁ τ s hiso hτ => ?_⟩
  suffices key : ∀ (L : IntermediateField ℚ Ω) [NumberField L] [IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
      IsIrr ((tenB ρ₁ τ).comp (resQ L)) → IsAutC ι ((tenB ρ₁ τ).comp (resQ L)) ∧ AllW ι ((tenB ρ₁ τ).comp (resQ L)) from
    ⟨fun L _ _ a b c d => (key L a b c d).1, fun L _ _ a b c d => (key L a b c d).2⟩
  intro L _ _ hLa hkL hgood hL
  obtain ⟨art, Y, a, e, hart, hpos, hlad, ha, ha'⟩ := hτ.alg
  obtain ⟨N, N', hN, hN', -, hnd, hint⟩ := hj Y a e hpos ha ha'
  have att₁ := Cq.attTwist K' Ω l ι 2 _ P₀ att₀ art Y a (κ ^ j) hart hlad
  have hind := Cu2.tenInd Ω l ι K' h2 ρ g0 (m * j) c₁ (κ ^ j) ρ₁ τ s hiso hτ
  obtain ⟨a₁, a₂, e₁, f₁⟩ := as_infOf N (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN, CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inl hz))
  obtain ⟨b₁, b₂, e₂, f₂⟩ := as_infOf N' (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN', CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inr hz))
  have hinj : Function.Injective ![![a₁, a₂] 0, ![a₁, a₂] 1, ![b₁, b₂] 0, ![b₁, b₂] 1] := by
    rw [f₁, f₂] at hnd
    simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, add_left_inj, Int.cast_inj, not_or] at hnd
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; omega)
  have hemb : ∀ φ : K' →+* ℂ, φ = e ∨ φ = ComplexEmbedding.conjugate e := fun φ => by
    classical
    by_contra hw
    push Not at hw
    have hne : e ≠ ComplexEmbedding.conjugate e := fun h => IsTotallyComplex.complexEmbedding_not_isReal e (ComplexEmbedding.isReal_iff.2 h.symm)
    have h3 : ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ)).card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hw.1, hw.2, hne, rfl⟩
    have h4 := Finset.card_le_univ ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ))
    rw [NumberField.Embeddings.card K' ℂ, h2] at h4
    omega
  have reg₁ : (CG.mk (P₀.twist Y)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => by
    have key : ∀ (M : Multiset ℂ), (P₀.twist Y).HasInfChar φ M → M ≤ N + N' →
        ((CG.mk (P₀.twist Y)).infChar φ).Nodup ∧ ∀ z ∈ (CG.mk (P₀.twist Y)).infChar φ, ∃ k : ℤ, z = (k : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
      intro M hM hle
      rw [CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hM]
      refine ⟨Multiset.nodup_of_le hle hnd, fun z hz => ?_⟩
      obtain ⟨k, rfl⟩ := hint z (Multiset.mem_of_le hle hz)
      exact ⟨k + 1, by push_cast; ring⟩
    rcases hemb φ with rfl | rfl
    · exact key N hN (Multiset.le_add_right _ _)
    · exact key N' hN' (Multiset.le_add_left _ _)
  haveI : FiniteDimensional ℚ K' := NumberField.to_finiteDimensional
  haveI : FiniteDimensional ℚ L := NumberField.to_finiteDimensional
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = K' ⊔ L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup K' L
  haveI : NumberField M := {}
  have hEM : K' ≤ M := hM ▸ le_sup_left
  have hLM : L ≤ M := hM ▸ le_sup_right
  letI : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra K' M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ K' M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra L _
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ K' := { finrank_eq_two' := h2 }
  haveI hK : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ K' L ‹_› ‹_› hK hLa
  haveI : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[K'] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dM : Module.finrank L M = 2 := deg_two K' L _ hM h2 hkL
  have RM := resFacts K' M Ω l 2 (ρ.comp (galEmb ℚ K' Ω))
  have hirrM : IsIrr ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    irr_tw_comp _ _ _ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  obtain ⟨P, regP, att, inf⟩ := hS K' M Ω l ι _ (P₀.twist Y) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont) reg₁ att₁ hirrM
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois L M := IsAbelianGalois.tower_top ℚ _ _
  have hc0 : Continuous (tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont
  have hcont : Continuous ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) := hc0.comp RM.1
  haveI : IsCMField K' := IsCMField.of_isAbelianGalois K'
  have hW : AllW ι ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H ℚ K' M Ω h2 l ι ρ (κ ^ j) hρ hrw ⟨hτ.kcont, art, Y, a, hart, hpos, hlad⟩ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  have hbad : Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L P := by
    refine hB Ω l ι K' L M hM ρ _ P hgood hcont
      (UpperTheory.solvable_polarized_restriction K' M Ω l ι 2 _ (hP Ω l ι K' h2 hc ρ hρ ⟨π, hreg, hatt⟩ g0 _ c₁ _ τ s hτ)) regP att
      hW fun A hA u hu h1 => ?_
    have h3 : τ (resQ K' (galEmb K' M Ω u)) = 1 :=
      hτ.unr A hA _ ⟨hu.1, hu.2⟩ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => (galEmb K' M Ω u).commutes ⟨y, hy⟩)
    have h4 : (κ ^ j) (galEmb K' M Ω u) = 1 := Units.ext (by rw [hτ.val, h3]; simp)
    have h6 : galEmb ℚ K' Ω (galEmb K' M Ω u) = resQ M u := AlgEquiv.ext fun _ => rfl
    have h5 : (ρ.comp (galEmb ℚ K' Ω)) (galEmb K' M Ω u) = 1 := by rw [MonoidHom.comp_apply, h6, h1]
    rw [MonoidHom.comp_apply]
    exact tw_one (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j) (galEmb K' M Ω u) h5 h4
  refine (fun h1 h2 => And.intro (hI L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd L M Ω dM l ι P _ att (hW P regP att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨t, t', hne, q, q'⟩ := two_emb dM ψ
    have hd : t.comp (algebraMap K' M) ≠ t'.comp (algebraMap K' M) := fun hp =>
      hne (hom_ext_sup K' L M hEM hLM hM.le t t' (fun x => DFunLike.congr_fun hp x) fun x => DFunLike.congr_fun (q.trans q'.symm) x)
    rcases hemb (t.comp (algebraMap K' M)) with p | p <;> rcases hemb (t'.comp (algebraMap K' M)) with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, t, t', hne, q, q', inf _ _ (p ▸ e₁ ▸ hN), inf _ _ (p' ▸ e₂ ▸ hN'), hinj⟩
    · exact ⟨_, _, t', t, hne.symm, q', q, inf _ _ (p' ▸ e₁ ▸ hN), inf _ _ (p ▸ e₂ ▸ hN'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ L s ∉ K'.fixingSubgroup := fun hu => by
      apply hs
      rw [range_galEmb]
      have : resQ L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨hu, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    refine ⟨fun g g' e => hind.on _ hs' (galEmb K' M Ω g) (galEmb K' M Ω g') ?_, fun g e => hind.off _ hs' (galEmb K' M Ω g) ?_⟩
    · have := congrArg (resQ L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ L) e
      rw [map_mul] at this
      exact this
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd
private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))
theorem central_character_of_regular_cusp (hP : _root_.UpperTheory.V.Af.Hypotheses') {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    (hreg : π.IsRegAlg) (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B) :
    ∃ ω : HChar F, (∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w) ∧ ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt hP F π
  have hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := fun w α β h => by
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec h
    have hZ := (UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2
    have h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))
  refine ⟨ω, hv, fun v => ?_⟩
  have hiso : π.Iso (π.dual.twist ω) := by
    refine hP.smoR F 2 one_le_two _ _ ?_
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
      rw [← hv w α β hB, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
  obtain ⟨m, hm, -, hz⟩ := hreg v
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
  obtain ⟨i, hi⟩ := hz x (by simp)
  obtain ⟨j, hj⟩ := hz y (by simp)
  have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at h
  refine ⟨i + j + 1, ?_⟩
  push_cast at hi hj ⊢
  linear_combination hi + hj - h / 2
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Ws UpperTheory.V.Cu UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix
open private charEig_cyc_inv algSat_eq from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
open private diagR infDiag_eqR diagR_mk ev_notMem from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
private theorem algPos_of_expo (ω : HChar ℚ) (h : ∀ v, ∃ n : ℤ, TR.expo ω v = n) : ∃ a, IsAlgPos ω a := by
  obtain ⟨n, hn⟩ := h default
  refine ⟨fun _ => n, fun k hk => ?_⟩
  letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩
  have hk0 : (0 : ℝ) < ((k : ℚ) : ℝ) := hk (Rat.castHom ℝ)
  have hv : ∀ v, diagR ℚ (k : ℚ) v = ((k : ℚ) : ℝ) := fun v =>
    eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp (diagR ℚ)) (k : ℚ)
  have e : Units.map (diagR ℚ).toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ) :=
    Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)
  have e2 := TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)
  rw [← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0] at e2
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]
  exact e2
private theorem det_sat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = ((x * y : ℂˣ) : ℂ) * q := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, algSat_eq, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]
private theorem det_alg (P : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (ha : IsAutR ι ρ) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp ρ) := by
  obtain ⟨π, hreg, hatt⟩ := ha
  obtain ⟨ω, hω, hint⟩ := _root_.central_character_of_regular_cusp P.toClassicalTheorems π hreg (hatt.2.mono fun w ⟨B, hB, _⟩ => ⟨B, hB⟩)
  obtain ⟨a, hal⟩ := algPos_of_expo ω hint
  obtain ⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι hal
  have hch : IsCharOf ι ω μ := ⟨hμ, art, a, hart, hal, hL⟩
  obtain ⟨hcc, χ, art', a', h'⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l)
    ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩
  have H := (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).2.1
  have h1 : Af.IsAlgChar ι (cycBar ℚ Ω l) := ⟨χ, hcc, art', a', h'⟩
  have h2 := (H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1
  have key : (fun s : G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) =
      fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l) := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and (ev_notMem (K := ℚ) l)))
      (Units.continuous_val.comp (hc.comp continuous_inv)).matrix_det
      (Units.continuous_val.comp ((hμ.mul hcc.inv).comp continuous_inv)) ?_
    intro v hv _ A hA σ hσ
    obtain ⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩ := not_not.1 hv
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    apply ι.injective
    rw [MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, (charEig_cyc_inv ι v h4 A hA).2 σ hσ,
      ← hω v x y hB, ← det_sat _ _ _ _ e2]
    exact ι.toRingHom.map_det _
  have e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹ := MonoidHom.ext fun s => Units.ext (by
    have := congrFun key s⁻¹
    simp only [inv_inv] at this
    exact this)
  rw [e]
  exact h2
private theorem conj_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem conj_off {Ω : Type} [Field Ω] [CharZero Ω] (K' : IntermediateField ℚ Ω) (hK : IsTotallyComplex K') {c : G ℚ Ω}
    (hc : IsConjEl c) : c ∉ K'.fixingSubgroup := by
  intro h
  obtain ⟨j, hj⟩ := hc
  refine InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω))))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  exact (hj x).symm.trans (congrArg j (h x))
private theorem pair_plane {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem kap_anti {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {K' : IntermediateField ℚ Ω} [NumberField K'] {g0 : G ℚ Ω} {m : ℕ} {c₁ : Coef l} {κ : G K' Ω →* (Qbar l)ˣ}
    {τ : G ℚ Ω →* Sd.S3.M2 c₁.O} {s} (hτ : TauDat ι K' g0 m c₁ τ s κ) {c : G ℚ Ω} (hc : c ∉ K'.fixingSubgroup) {g g' : G K' Ω}
    (h : resQ K' g' = c * resQ K' g * c⁻¹) : (κ g : Qbar l) * κ g' = 1 := by
  have hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 := fun x => by
    have h := congrFun (congrFun (hτ.form x) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hg : resQ K' g ∈ K'.fixingSubgroup := fun y => g.commutes y
  have e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g) := by
    rw [h, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hg' : resQ K' g' ∈ K'.fixingSubgroup := fun y => g'.commutes y
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 0) 1
  have f1 := hf c
  have f2 := hf (resQ K' g)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2
  have key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1 := by
    generalize τ (resQ K' g) 0 0 = a at *
    generalize τ (resQ K' g) 0 1 = b at *
    generalize τ (resQ K' g') 0 0 = a' at *
    generalize τ (resQ K' g') 0 1 = b' at *
    generalize τ c 0 0 = p at *
    generalize τ c 0 1 = q at *
    linear_combination (a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1
  rw [hτ.val g, hτ.val g']
  exact_mod_cast congrArg (fun z : c₁.O => (z : Qbar l)) key
theorem UpperTheory.V.Cu.polOf4_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Cu.PolOf4 := by
  intro P Ω _ _ _ l _ ι K' _ _ hK ρ hρ ha g0 m c₁ κ τ s hτ
  obtain ⟨c, hc⟩ := conj_ex Ω
  let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J * ρ c⁻¹, det_alg P ι ρ hρ ha,
    fun a b h h' => auSign _ a b h h', hc, fun g g' h => ?_⟩
  have h' : resQ K' g' = c * resQ K' g * c⁻¹ := h
  have hk := kap_anti hτ (conj_off K' hK hc) h'
  have e : ρ c⁻¹ * ρ (resQ K' g') = ρ (resQ K' g) * ρ c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (ρ c⁻¹).val * (ρ (resQ K' g')).val = (ρ (resQ K' g)).val * (ρ c⁻¹).val := congrArg Units.val e
  have hp : (ρ (resQ K' g)).valᵀ * J.val * (ρ (resQ K' g)).val = (ρ (resQ K' g)).val.det • J.val := pair_plane _
  have hd : (((Matrix.GeneralLinearGroup.det.comp ρ).comp (resG ℚ K' Ω) g : (Qbar l)ˣ) : Qbar l) = (ρ (resQ K' g)).val.det := rfl
  rw [hd, tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul, ← Matrix.smul_mul, ← hp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk, one_smul]
  simp only [Matrix.mul_assoc, e']
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Cu UpperTheory.V.Z.Bc
namespace UpperTheory.V.Z.Win.Birth
theorem seed2_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Sd.Seed2Alt := _root_.UpperTheory.V.Z.Bc.second_initial_of_prints (_root_.UpperTheory.V.Z.Bc.hypothesesZ' hH) (_root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH hH) (_root_.UpperTheory.V.Z.Win.Birth.propEGP_of_printsH hH)
theorem fourth_initial_of_prints_h (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Cu.SeedIVAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Cu.fourth_initial_of_rank_four_data alNe _root_.UpperTheory.V.Cu.tauEx' (_root_.UpperTheory.V.Cu.rank_four_automorphy_of_tensor_of_base_change_of_induction hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc))
      (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt hA indCs) (_root_.UpperTheory.V.Cu.polOf4_alt hH) (badOfW Z.InvariantSubmoduleMonicPolynomial.E.splitOfDec Z.InvariantSubmoduleMonicPolynomial.E.unrOfIne (_root_.UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt hH)))
    (Cu2.rhoExP Cu2.exists_weight_four_auxiliary_characters Cu2.phiFacts Cu2.modEx4) twEx4 pairOf4 resOf4 contOf4 entOf4 overOf4 wtsOf4
    (irrOf4_of alNe) (autOf4_of alNe) hA (_root_.UpperTheory.V.Z.Win.Birth.propEGP_of_printsH hH)
end UpperTheory.V.Z.Win.Birth
end
end
