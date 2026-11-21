import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspaces
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ScalAtZeroOfLiftMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfHyp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EwfMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem star_eC (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (σ : D.what₂.LL →+* ℂ) (g : G) :
    starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
  unfold RealDat.eC
  rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  rw [inv_one] at h1
  simp only [map_mul, map_div₀, map_natCast]
  rw [h2, ← h1]

theorem integral_levelGroupAction_pairing_invariant {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (𝓕 : Set (GA D V))
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hk : ∃ κ, IsLevelLift V β L g0 κ) (F S : GA D V → ℂ)
    (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) (hS : ∀ γ ∈ GQ V, ∀ g, S (γ * g) = S g)
    (hi : IntegrableOn (fun g => star (F g) * S g) 𝓕 μ) :
    IntegrableOn (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) 𝓕 μ ∧
      ∫ g in 𝓕, star (actG0 V β L g0 F g) * actG0 V β L g0 S g ∂μ = ∫ g in 𝓕, star (F g) * S g ∂μ := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨hcpt, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
  have ha : ‖(levChi V β (flagL L) hk.choose)⁻¹‖ = 1 := by
    rw [norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
  have hmap : Measure.map (fun g => g * hk.choose) μ = μ :=
    GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
  set a := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
  have haa : star a * a = 1 := by
    have : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, ha]; norm_num
  have key : (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) =
      fun g => star (F (g * hk.choose)) * S (g * hk.choose) := by
    funext g
    simp only [actG0, dif_pos hk]
    rw [star_mul', ← ha_def]
    linear_combination (star (F (g * hk.choose)) * S (g * hk.choose)) * haa
  rw [key]
  exact GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 _ hmap (fun g => star (F g) * S g)
    (fun γ hγ g => by simp only [hF γ hγ g, hS γ hγ g]) hi

end GlobalTheory.EwfMove

noncomputable section

namespace GlobalTheory.EwfMove

theorem integral_eWf_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hX i σ v Φ hΦ hi y
  obtain ⟨hinj, hrange, hip⟩ := hC.models.HW i σ
  obtain ⟨h1, h2⟩ := hC.models.νW i
  haveI := h1.1
  have hgW := hC.models.gW
  have hL : ∀ z : (R.HW i σ).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (R.HW i σ).e z (fun ρ => v ρ) (γ * g) = (R.HW i σ).e z (fun ρ => v ρ) g := fun z =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ _
      ((hrange.le : _ ≤ R.Wall i σ) (LinearMap.mem_range_self _ z)) _).1
  have hS : ∀ (g : G) (z : (R.HW i σ).H), (R.HW i σ).e z (fun ρ => v ρ) =
      actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e (R.gW i σ g⁻¹ z) (fun ρ => v ρ)) := by
    intro g z
    have e := congrArg (fun T : MMap (R.MW i σ) => T (fun ρ => v ρ)) (hgW i σ g (R.gW i σ g⁻¹ z))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hper : ∀ g : G,
      IntegrableOn (fun h => star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h) (R.fdW i) (R.νW i) ∧
      ∫ h in R.fdW i, star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h ∂(R.νW i) =
      ∫ h in R.fdW i, star (Φ h) * (R.HW i σ).e (R.gW i σ g⁻¹ y) (fun ρ => v ρ) h ∂(R.νW i) := by
    intro g
    by_cases hk : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ
    · rw [hS g y]
      exact integral_levelGroupAction_pairing_invariant _ _ _ _ _ h2 hk Φ _ hΦ (hL _) (hi _)
    · have h0 : ∀ z : (R.HW i σ).H, (R.HW i σ).e z (fun ρ => v ρ) = 0 := fun z => by
        rw [hS g z]
        simp only [actG0, dif_neg hk]
      constructor
      · simp only [h0, Pi.zero_apply, mul_zero]
        exact integrableOn_zero
      · simp only [h0, Pi.zero_apply, mul_zero]
  have eL : ∀ h, star (R.eWf i σ Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h =
      ∑ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) *
        (star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h) := by
    intro h
    simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, star_sum, star_mul', Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_assoc]
    rfl
  have eR : ∀ h, star (Φ h) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) h =
      ∑ g, RealDat.eC (A := A) σ g * (star (Φ h) * (R.HW i σ).e (R.gW i σ g y) (fun ρ => v ρ) h) := by
    intro h
    simp only [GlobalTheory.LiftLower.projH, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  simp only [eL, eR]
  rw [integral_finset_sum _ fun g _ => ((hper g).1.const_mul _),
    integral_finset_sum _ fun g _ => ((hi (R.gW i σ g y)).const_mul _)]
  simp only [integral_const_mul, (hper _).2, star_eC hX]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

end GlobalTheory.EwfMove
end
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_goodProjector_move_petersson : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  atlas_forward_decl GlobalTheory.EwfMove.integral_eWf_move
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaLeftW

theorem thetaKernel_leftInvariant_rationalUnitary : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i χS χT ω hW φ hφ h γ hγ g
  unfold Datum.thetaKO
  have e : (h, γ * g) = ((1 : GA D (Vc D i)), γ) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hφ)

end GlobalTheory.ThetaLeftW
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  atlas_forward_decl GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicRestrict

theorem ext_restrict {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W)
    (hΨ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) (h : GA D V) :
    c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  set h₀ := GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h) with eh₀
  have m₀ : h₀ ∈ GfC V := GlobalTheory.AdelicScalar.finLift_mem V _
  have s₀ : finHom V h₀ = finHom V h :=
    congrArg Subtype.val (GlobalTheory.AdelicScalar.finLift_spec V ((finHom V).rangeRestrict h))
  set k := h₀⁻¹ * h with ek
  have hk1 : finHom V k = 1 := by rw [ek, map_mul, map_inv, s₀, inv_mul_cancel]
  have hkE : Lev.finE V k = 1 := by
    unfold Lev.finE
    rw [MonoidHom.comp_apply, hk1, map_one]
  have hkL : Lev.finE V k ∈ lev D.sp.cm V.gram β L := by rw [hkE]; exact Subgroup.one_mem _
  have hχ : Lev.levChi V β L k = 1 := by
    unfold Lev.levChi
    rw [hkE]
    have := map_one (levChar D.sp.cm V.gram β L)
    have e : levFn β L 1 = (levChar D.sp.cm V.gram β L 1 : ℂˣ) := rfl
    rw [e, this]
    rfl
  have hlaw := hΨ 1 (Subgroup.one_mem _) k hkL h₀
  have eh : 1 * h₀ * k = h := by rw [ek, one_mul, mul_inv_cancel_left]
  rw [eh, hχ, one_smul] at hlaw
  change c.ρ h⁻¹ (Ψ (GlobalTheory.AdelicScalar.finLift V ((finHom V).rangeRestrict h))) = Ψ h
  rw [← eh₀, hlaw]
  have hρ : c.ρ h⁻¹ = c.ρ k⁻¹ := by
    rw [← eh, one_mul, _root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem m₀), mul_one]
  rw [hρ]

end GlobalTheory.AdelicRestrict

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_restriction_finitePoints_eq : ∀ {D : D7} {V : HSp D} (c : CoefA V), c.Is → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W), (∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h, Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) → ∀ h : GA D V, c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  atlas_forward_decl GlobalTheory.AdelicRestrict.ext_restrict
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAdjoint

theorem inner_eq_integral {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hH : R.models_HW)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (a b : (R.HW i σ).H) :
    inner ℂ a b = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) *
      ∫ g in R.fdW i, star ((R.HW i σ).e a (fun ρ => v ρ) g) * (R.HW i σ).e b (fun ρ => v ρ) g ∂(R.νW i) := by
  obtain ⟨-, -, hip⟩ := hH i σ
  have hc := ipM_spec (R.MW i σ) (R.νW i) (R.fdW i) _ _
    (GlobalTheory.LiftLower.IsMultIP₂ (R.HW i σ) (N := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) hip a b)
  rw [hip, ipAt, (hc (fun ρ => v ρ) (fun ρ => v ρ)).2]
  congr 1
  rw [Finset.prod_eq_one, mul_one]
  intro ρ _
  rw [inner_self_eq_norm_sq_to_K, hv ρ]
  simp

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint

theorem integrableOn_theta {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hI : GlobalTheory.LiftRows.InnerProductFormulaC R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (hL : GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io)
    (hM : IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0))
    (U : MMap (R.MW i σ)) (hU : U ∈ R.Wall i σ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (h : GA D (Vc D i))
    (Q : PolF D (Wc D i).rank (Vc D i).rank) :
    IntegrableOn (fun g => Datum.thetaKO ω h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f Q) * starRingEnd ℂ (U (fun ρ => v ρ) g))
      (R.fdW i) (R.νW i) := by
  obtain ⟨μ, 𝓧, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  obtain ⟨⟨Fr, hFr⟩, h2⟩ := (hL.1.models.νW i).1.2.2 R.θ hL.1.models.inf
  obtain ⟨mR, hmR⟩ := (h2 Fr hFr).1
  exact (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL _ _ hM μ 𝓧 hμ Fr hFr mR hmR U hU U hU v v Q Q).1 h

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

set_option maxHeartbeats 400000 in

theorem adjoint_eq_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hX hS hI hF hZ hR i σ s m μ' η' ω B f₀ f c io H hL hM hy hH v hv thP th hT hP y h w

  have hC : GlobalTheory.Hk3.Core R F := hL.1
  have hω := hL.2.2.2.2.2.1
  have hpt := hL.2.2.2.2.2.2.2.2.1
  have hc : c.Is := hL.2.2.2.2.2.2.2.2.2.1
  have hio := hL.2.2.2.2.2.2.2.2.2.2
  have hKc : starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := GlobalTheory.AdelicScalar.ptL R i σ B f (io (PiTensorProduct.tprod ℂ v))
  have hφ : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ w) := fun w => hpt _
  have hinf : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w) := fun u hu w => hio.1 u hu _ w
  have hlev : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)), ∀ w,
      ω (κ, 1) (φ w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) κ)⁻¹ • φ w :=
    fun κ hκ w => hS i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL κ hκ _
  have hWall : ∀ y' : (R.HW i σ).H, (R.HW i σ).e y' ∈ R.Wall i σ := fun y' =>
    GlobalTheory.AdelicScalar.HMod_mem (hC.models.HW i σ) y'
  have hth : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) *
      starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) := fun y' w h =>
    integrableOn_theta R F hI i σ s m μ' η' ω B f₀ f c io hL hM _ (hWall y') v h (io (PiTensorProduct.tprod ℂ v) w)
  have hth' : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => star (Datum.thetaKO ω h g (φ w)) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := fun y' w h => by
    have h1 := hth y' w h
    have h2 : IntegrableOn (fun g => starRingEnd ℂ (Datum.thetaKO ω h g (φ w) *
        starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g))) (R.fdW i) (R.νW i) :=
      h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1) (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.congr h2 (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hcls : ∀ u g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j))) := by
    intro u g
    refine (hT.eq _ _ _).trans ?_
    exact GlobalTheory.AdelicScalar.theta_classSum hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev hM hy (GlobalTheory.AdelicScalar.HMod_mem hH u) g
  have hφw : ∀ w, φ w = ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w) := fun w => rfl
  clear_value φ
  have hex := GlobalTheory.AdelicScalar.exists_upVec hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev (R.νW i) (R.fdW i)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ)) (hth _)
  have hΨ := hex.choose_spec.1
  have hlaw := hex.choose_spec.2
  have hzex := GlobalTheory.AdelicScalar.HMod_onto hH (GlobalTheory.AdelicScalar.upVec_mem c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw)
  have hz := hzex.choose_spec
  have hinv : ∀ u, ∀ γ ∈ GQ (Wc D i), ∀ g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) (γ * g) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g := by
    intro u γ hγ g
    refine (hcls u (γ * g)).trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcls u g).symm)
    exact congrArg _ (GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ R i _ _ ω hω _ (hφ _) _ γ hγ g)
  have eF : ∀ u (y' : (R.HW i σ).H), (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) = fun g =>
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        (star (Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j)))) * (R.HW i σ).e y' (fun ρ => v ρ) g) := by
    intro u y'
    funext g
    refine (congrArg (fun t => star t * (R.HW i σ).e y' (fun ρ => v ρ) g) (hcls u g)).trans ?_
    simp only [star_sum, Finset.sum_mul, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hintF : ∀ u (y' : (R.HW i σ).H), IntegrableOn (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u)
      (PiTensorProduct.tprod ℂ v) g) * (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := by
    intro u y'
    have hsum := integrable_finset_sum (μ := (R.νW i).restrict (R.fdW i)) Finset.univ fun j _ =>
      (hth' y' (H.e u ((R.B.L i A.μ0).pres.y j)) (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j))).const_mul
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹
    exact hsum.congr (Filter.Eventually.of_forall fun g => (congrFun (eF u y') g).symm)
  have hpair : ∀ u, ∫ g in R.fdW i, star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) = inner ℂ u hzex.choose := by
    intro u
    refine (congrArg (fun F => ∫ g in R.fdW i, F g ∂(R.νW i)) (eF u (GlobalTheory.LiftLower.projH R i σ y))).trans ?_
    refine (integral_finset_sum _ fun j _ => (hth' _ _ _).const_mul _).trans ?_
    refine Eq.trans ?_ (hH.2.2 u hzex.choose).symm
    refine Eq.trans ?_ (congrArg (Bridge.adInner _ _ _ (H.e u)) hz).symm
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (integral_const_mul _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ (inner_conj_symm _ _)
    refine Eq.trans ?_ (congrArg (starRingEnd ℂ) (hΨ _ _)).symm
    unfold GlobalTheory.AdelicScalar.l2 Lift.pet
    refine Eq.trans ?_ integral_conj
    refine congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) (funext fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hadj : LinearMap.adjoint th y = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hzex.choose := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : (fun g => star ((R.HW i σ).e (th u) (fun ρ => v ρ) g) * (R.HW i σ).e y (fun ρ => v ρ) g) =
        fun g => star (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v)) g) *
          (R.HW i σ).e y (fun ρ => v ρ) g :=
      funext fun g => congrArg (fun t : GA D (Wc D i) → ℂ => star (t g) * (R.HW i σ).e y (fun ρ => v ρ) g) (hP u v)
    refine (LinearMap.adjoint_inner_right th u y).trans ?_
    refine (inner_eq_integral R hC.models.HW i σ v hv (th u) y).trans ?_
    refine Eq.trans ?_ (inner_smul_right _ _ _).symm
    refine congrArg _ (Eq.trans ?_ (hpair u))
    refine (congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) e1).trans ?_
    exact GlobalTheory.T.integral_goodProjector_move_petersson R F hC hX i σ v _ (hinv u) (hintF u) y
  have e3 : c.ext (H.e (LinearMap.adjoint th y)) h = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hex.choose h := by
    refine (congrArg (fun x => c.ext (H.e x) h) hadj).trans ?_
    simp only [map_smul, Pi.smul_apply]
    exact congrArg _ ((congrArg (fun x => c.ext x h) hz).trans
      (GlobalTheory.T.extend_restriction_finitePoints_eq c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw h))
  refine (congrArg (fun a => inner ℂ a w) e3).trans ?_
  refine (inner_smul_left _ _ _).trans ?_
  refine congrArg₂ (· * ·) hKc ?_
  exact (hΨ h w).trans (congrArg (fun p => GlobalTheory.AdelicScalar.l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g p)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ))) (hφw w))

end GlobalTheory.ConjAdjoint
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  atlas_forward_decl GlobalTheory.ConjAdjoint.adjoint_eq_upLift
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftGram

theorem inner_eq_sum_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hirr hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν hy hH v hv U₁ hU₁ U₂ hU₂
    z₁ z₂ h₁ h₂ ι _ b
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  refine (GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)).elim fun μ h0 => h0.elim fun 𝓧 hμ => ?_
  have h5 := (hd.1.models.νW i).1.2.2 R.θ hd.1.models.inf
  refine h5.1.elim fun Fr hFr => (h5.2 Fr hFr).1.elim fun mR hmR => ?_
  have hint : ∀ k, IntegrableOn (fun h =>
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h)) (R.fdV i A.μ0) (R.νV i A.μ0) := fun k =>
    (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hd _ _ hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v v
      (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  have hx := fun z => (SetLike.ext_iff.mp hH.2.1 _).mp (LinearMap.mem_range_self H.e z)
  have e1 := GlobalTheory.AdelicScalar.integral_eq_classSum (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m) hν hy
    (fun h => inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h)) fun γ hγ k hk x =>
      (congrArg₂ (inner ℂ) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₁) hγ k hk x) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₂) hγ k hk x)).trans
        (GlobalTheory.AdelicScalar.inner_law c.ρ hc.2.1 (GlobalTheory.AdelicScalar.norm_levChi _ _ k) _ _ _)
  simp only [GlobalTheory.AdelicScalar.ext_finLift c hc] at e1
  rw [hH.2.2 z₁ z₂]
  unfold Bridge.adInner
  rw [← e1]
  have e2 : ∀ h, inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h) = ∑ k,
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h) := fun h =>
    (b.sum_inner_mul_inner _ _).symm.trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) (h₁ h (b k))
      ((inner_conj_symm _ _).symm.trans (congrArg (starRingEnd ℂ) (h₂ h (b k)))))
  refine (congrArg (fun F => ∫ h in R.fdV i A.μ0, F h ∂(R.νV i A.μ0)) (funext e2)).trans ?_
  exact integral_finsetSum _ fun k _ => hint k

end GlobalTheory.LiftGram

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  atlas_forward_decl GlobalTheory.LiftGram.inner_eq_sum_upLift
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.UnitCoefIP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _hirr _hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν _hy _hH v hv ev
  have hC := hd.1
  obtain ⟨⟨μ, 𝓧⟩, hμ⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  obtain ⟨⟨Fr, hFr⟩, hFr2⟩ := (hC.models.νW i).1.2.2 R.θ hC.models.inf
  obtain ⟨mR, hmR⟩ := (hFr2 Fr hFr).1
  choose δ _hδpos hδ' using hδ i σ
  have hδv : ∀ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ :=
    fun ρ => (hδ' ρ Fr hFr (mR ρ) (hmR ρ) (v ρ) (hv ρ)).2
  have hW := GlobalTheory.LiftScalarL.inner_HW R hC.models.HW i σ
  set N : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos fun ρ _ => by
      have := one_le_dimK i σ ρ
      positivity
    exact_mod_cast this.ne'
  by_cases h0 : typePart R i σ A.μ0 R.triv ev = ⊥
  · refine ⟨0, fun y₁ hy₁ y₂ w _ => ?_⟩
    have e1 : y₁ = 0 := by
      rw [← GlobalTheory.LiftLower.typePart_base hC.lev, h0] at hy₁
      exact (Submodule.mem_bot ℂ).1 hy₁
    subst e1
    simp [l2, Lift.pet, upLift, petW]
  · obtain ⟨Bf, -, -, -, hK⟩ := hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev h0
    refine ⟨(((R.νV i A.μ0) (R.fdV i A.μ0)).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) *
      ((Nat.card R.triv.H : ℂ) * (Datum.nrm2 μ 𝓧 f : ℂ) *
        (GlobalTheory.LFun.LSD D (finS R A.μ0) Bf μ' ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R A.μ0) : ℂ)))) / N,
      fun y₁ hy₁ y₂ w hw => ?_⟩
    have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hC.models.HW i σ)
    have hw' : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hy' : y₁ ∈ typePart R i σ A.μ0 R.triv ev := by
      rw [GlobalTheory.LiftLower.typePart_base hC.lev]; exact hy₁
    have hK1 := hK _ (Submodule.mem_comap.1 hy') _ (hm y₂)
    have hIP := isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂
    have key := GlobalTheory.LiftScalarL.l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) hIP _ hK1 v δ hδv w hw'
    refine key.trans ?_
    rw [hW y₁ y₂]
    field_simp

end GlobalTheory.UnitCoefIP

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_innerProductFormula_unitCoefficient : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  atlas_forward_decl GlobalTheory.UnitCoefIP.exists_scalar
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_gW (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : (R.HW i σ).H) :
    ⟪R.gW i σ g x, R.gW i σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨R.gW i σ g, GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ g⟩ x y

theorem adjoint_projH (hC : GlobalTheory.Hk3.Core R F) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (GlobalTheory.LiftLower.projH R i σ) = GlobalTheory.LiftLower.projH R i σ := by
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
    intro g
    unfold RealDat.eC
    rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← inner_gW hC i σ g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem projH_projH (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    GlobalTheory.LiftLower.projH R i σ (GlobalTheory.LiftLower.projH R i σ x) = GlobalTheory.LiftLower.projH R i σ x := by
  classical
  have h1 : ∀ g, ∑ a, RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g) = RealDat.eC (A := A) σ g := by
    intro g
    unfold RealDat.eC
    conv_rhs => rw [← idemOf_mul_self A.X hX]
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [map_mul]
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl fun g _ => by rw [← h1 g, Finset.sum_smul]]
  rw [Finset.sum_comm (f := fun g a => (RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g)) • R.gW i σ g x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_nbij' (fun g => a * g) (fun g => a⁻¹ * g) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply, mul_comm]

theorem eq_of_ext {V : HSp D} {c : CoefA V} (hc : c.Is) {H : HMod (Bridge.Gf V → c.W)} (hinj : Function.Injective H.e) {z z' : H.H}
    (h : ∀ x w, inner ℂ (c.ext (H.e z) x) w = inner ℂ (c.ext (H.e z') x) w) : z = z' := by
  refine hinj (funext fun u => ?_)
  have e : c.ext (H.e z) (GlobalTheory.AdelicScalar.finLift V u) = c.ext (H.e z') (GlobalTheory.AdelicScalar.finLift V u) :=
    ext_inner_right ℂ fun w => h _ w
  exact (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z) u).symm.trans (e.trans (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z') u))

end GlobalTheory.ConjScalarProof

namespace GlobalTheory.ConjScalarProof
set_option maxHeartbeats 1000000 in
open GlobalTheory.LiftLower in

theorem conjScalarAt_of_sourceLevelLaw_fock_zeta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hCore hX hSL hIPF hFC hFZ hRC
  intro gramR c0R c0L hT i σ hσ μ' η' c c₁ H j th hD ev
  have hμ := hD.1
  have hη := hD.2.1
  have hf := hD.2.2.1
  have hL := hD.2.2.2
  have hL2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hL
  obtain ⟨ω, hL3⟩ := hL2
  obtain ⟨f₀, f, B, io, thP, hL4⟩ := hL3
  have hLD := hL4.1
  have hP := hL4.2
  have h38 := GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum R F hCore gramR c0R c0L hT i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hLD
  obtain ⟨s, m, h39⟩ := h38
  have hC := h39.1
  have hν := h39.2.1
  have hy := h39.2.2.1
  have hH := h39.2.2.2
  have hth := hLD.2.2.2
  have hio := hC.2.2.2.2.2.2.2.2.2.2
  have hc : c.Is := hC.2.2.2.2.2.2.2.2.2.1
  have hv0 := hio.2.2
  let v := hv0.choose
  have hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 := hv0.choose_spec.choose_spec.1
  let K : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)
  have hKdef : K = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := rfl
  have hK0 : K ≠ 0 := by
    rw [hKdef, Finset.prod_ne_zero_iff]
    intro ρ _
    have h1 := GlobalTheory.AdelicScalar.one_le_dimK i σ ρ
    exact_mod_cast (show (dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) ≠ 0 by positivity)
  have hKc : starRingEnd ℂ K = K := by
    rw [hKdef, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  have hadj : ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W), inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w = K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h :=
    GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv thP th hth hP
  have hpp : ∀ y, projH R i σ (projH R i σ y) = projH R i σ y := projH_projH hX i σ
  have hsa : LinearMap.adjoint (projH R i σ) = projH R i σ := adjoint_projH hCore hX i σ
  have hinj : Function.Injective H.e := hH.1
  have hadjP : ∀ y, LinearMap.adjoint th (projH R i σ y) = LinearMap.adjoint th y := fun y =>
    eq_of_ext (V := Vc D i) (c := c) (H := H) hc hinj fun x w =>
      (hadj (projH R i σ y) x w).trans ((congrArg (fun z => K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e z fun ρ => v ρ) x) (hpp y)).trans (hadj y x w).symm)
  have hfix : ∀ u, projH R i σ (th u) = th u := fun u => ext_inner_right ℂ fun y =>
    (LinearMap.adjoint_inner_right (projH R i σ) (th u) y).symm.trans
      ((congrArg (fun A => inner ℂ (th u) (A y)) hsa).trans ((LinearMap.adjoint_inner_right th u (projH R i σ y)).symm.trans
        ((congrArg (inner ℂ u) (hadjP y)).trans (LinearMap.adjoint_inner_right th u y))))
  have hW : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => GlobalTheory.AdelicScalar.HMod_mem (hCore.models.HW i σ) y
  have hz : ∀ y h w, inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := by
    intro y h w
    have e1 : c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) = K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) :=
      (congrArg c.ext (H.e.map_smul K⁻¹ _)).trans (c.ext.map_smul K⁻¹ _)
    have e2 : starRingEnd ℂ K⁻¹ = K⁻¹ := by simp only [map_inv₀, hKc]
    calc inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w
        = inner ℂ (K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) h) w := congrArg (fun Fn => inner ℂ (Fn h) w) e1
      _ = starRingEnd ℂ K⁻¹ * inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w := inner_smul_left _ _ _
      _ = K⁻¹ * (K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h) := by simp only [e2, hadj y h w]
      _ = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := inv_mul_cancel_left₀ hK0 _
  have hG := GlobalTheory.T.exists_scalar_innerProductFormula_unitCoefficient R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv ev
  let C := hG.choose
  have hC2 := hG.choose_spec
  let b := stdOrthonormalBasis ℂ c.W
  have key : ∀ u, th u ∈ partH R i σ ev → ∀ y₂,
      inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by
    intro u hu y₂
    have e1 := GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv
      _ (hW (projH R i σ (th u))) _ (hW (projH R i σ y₂)) _ _ (hz (th u)) (hz y₂) b
    have hu' : projH R i σ (th u) ∈ partH R i σ ev := (hfix u).symm ▸ hu
    have e2 : inner ℂ (projH R i σ (th u)) (projH R i σ y₂) = inner ℂ (th u) y₂ :=
      (congrArg (fun z => inner ℂ z (projH R i σ y₂)) (hfix u)).trans
        ((congrArg (fun A => inner ℂ (th u) (A y₂)) hsa.symm).trans
          ((LinearMap.adjoint_inner_right (projH R i σ) (th u) y₂).trans (congrArg (fun z => inner ℂ z y₂) (hfix u))))
    have e4 : inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂) =
        (Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂) := by
      refine e1.trans ?_
      rw [Finset.sum_congr rfl fun k _ => hC2 _ hu' (projH R i σ y₂) (b k) (b.orthonormal.1 k), e2, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    have e3 : ∀ y, LinearMap.adjoint th y = K • (K⁻¹ • LinearMap.adjoint th y) := fun y =>
      (smul_inv_smul₀ hK0 _).symm
    calc inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂)
        = inner ℂ (K • (K⁻¹ • LinearMap.adjoint th (th u))) (K • (K⁻¹ • LinearMap.adjoint th y₂)) :=
          congrArg₂ (inner ℂ) (e3 _) (e3 _)
      _ = starRingEnd ℂ K * (K * inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂)) :=
          (inner_smul_left _ _ _).trans (congrArg (fun z => starRingEnd ℂ K * z) (inner_smul_right _ _ _))
      _ = K * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂))) :=
          (congrArg (fun z => starRingEnd ℂ K * (K * z)) e4).trans
            (congrArg (fun k => k * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂)))) hKc)
      _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by ring
  refine ⟨(K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re, fun u hu => ?_⟩
  by_cases h0 : th u = 0
  · simp only [h0, map_zero, smul_zero]
  have hre : (((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) := by
    have e0 : ((‖LinearMap.adjoint th (th u)‖ : ℝ) : ℂ) ^ 2 = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * ((‖th u‖ : ℝ) : ℂ) ^ 2 :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint th (th u))).symm.trans
        ((key u hu (th u)).trans (congrArg (fun z => (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * z) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (th u))))
    have hn : ((‖th u‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 h0)
    have e' : (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) = ((‖LinearMap.adjoint th (th u)‖ ^ 2 / ‖th u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hn]
      exact e0.symm
    exact (congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) e').trans ((congrArg (fun r : ℝ => (r : ℂ)) (Complex.ofReal_re _)).trans e'.symm)
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (th (LinearMap.adjoint th (th u))) y = inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y) :=
        (LinearMap.adjoint_inner_right th _ y).symm
    _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y := key u hu y
    _ = inner ℂ ((((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) • th u) y :=
      (congrArg (fun z => z * inner ℂ (th u) y) ((Complex.conj_ofReal _).trans hre)).symm.trans (inner_smul_left _ _ _).symm

end GlobalTheory.ConjScalarProof
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatum_lift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  atlas_forward_decl GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZPartEig

theorem heckePolyOf_coeff {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) {k : ℕ} (hk : k ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff k = (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k := by
  classical
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem heckePolyOf_val_eq {L : Type} [Field L] [CharZero L] (n q : ℕ) (hq : q ≠ 0) (a b : ℕ → L)
    (h : Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b) {k : ℕ} (hk : k ≤ n) : a k = b k := by
  have e := congrArg (fun p => Polynomial.coeff p k) h
  simp only [heckePolyOf_coeff n q _ hk] at e
  have hne : ((-1 : L) ^ k * (q : L) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne e

theorem apply_of_mem_maxGen {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : K →+* ℂ) (j : V →ₛₗ[σ] H) (T : Module.End K V)
    (N : Module.End ℂ H) (hN : Commute N (LinearMap.adjoint N)) (hj : ∀ f, j (T f) = N (j f)) (c : K) (f : V)
    (hf : f ∈ T.maxGenEigenspace c) : N (j f) = σ c • j f := by
  have key : ∀ (k : ℕ) (g : V), j (((T - c • (1 : Module.End K V)) ^ k : Module.End K V) g) =
      (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hj, map_smulₛₗ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h0 : (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j f)) = 0 := by rw [← key, hk, map_zero]
  have hmem : j f ∈ N.maxGenEigenspace (σ c) := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, h0⟩
  rw [GlobalTheory.NormalFamily.maxGenEigenspace_eq hN] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OpLab (R : RealDat3 D A3 Ks) (i : Fin D.R.m) : (A3.liftI i A3.A.μ0).OpIx → Pl D.host.E → List ℤ → Prop :=
  Sum.elim
    (fun k P d => R.pl ((A3.A.fam.L i A3.A.μ0).pl k.1) = P ∧ k.2 ≤ (Vc D i).rank ∧ d = splitLab (Vc D i).rank k.2)
    (fun k P d => R.plI ((A3.liftI i A3.A.μ0).plI k.1) = P ∧ Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 ∧
      d = GlobalTheory.Hk3.labIn (Vc D i).rank k.2)

theorem opLab_ops (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h) :
    ∀ idx P d, OpLab R i idx P d → GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧
      ∀ f, R.jV i A3.A.μ0 ((A3.liftI i A3.A.μ0).opAll idx f) = h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) := by
  have hlev := hC.base.lev
  have hfam := hC.base.fam
  have hmod := hC.base.models
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.1
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨⟨Q, hQ⟩, s'⟩) P d hc
  · obtain ⟨rfl, hk, rfl⟩ := hc
    refine ⟨((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hlev).2.2.2 hfam A3.A.μ0 P' hP').1, fun f => ?_⟩
    exact (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hlev hfam hmod).2 i A3.A.μ0 h hh ⟨P', hP'⟩ k hk f
  · obtain ⟨rfl, hs, rfl⟩ := hc
    have hty : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 →
        GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 (R.plI k.1) ∧ Formalism.DivisionValues.conjPl (R.plI k.1) = R.plI k.1 ∧
          (GlobalTheory.Hk3.labIn (Vc D i).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
      ⟨(c3 A3.A.μ0 k.1 k.1.2).1, (c3 A3.A.μ0 k.1 k.1.2).2,
        ((GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
    refine ⟨(c3 A3.A.μ0 Q hQ).1, fun f => ?_⟩
    exact (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hlev hfam hmod i A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D i).rank k.2) (A3.heckeLI i A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) hty (hC.inert.hL i A3.A.μ0).some (⟨Q, hQ⟩, s') hs).2.2.2 h hh f

theorem exists_opLab (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d → ∃ idx, OpLab R i idx P d := by
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.2.1
  intro P d hg hr
  rcases hr with ⟨hc, k, hk, rfl⟩ | ⟨hc, hl⟩
  · obtain ⟨P0, hP0, rfl⟩ := (c3 P hg).2 hc
    exact ⟨Sum.inl (⟨P0, hP0⟩, k), rfl, hk, rfl⟩
  · obtain ⟨Q, hQ, rfl⟩ := (c3 P hg).1 hc
    obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.LabChar.labels_char (Vc D i) _ d).1 hl
    obtain ⟨s', h1, h2, h3, rfl⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank d).1 ⟨hlen, hpw, hdual hc⟩
    exact ⟨Sum.inr (⟨Q, hQ⟩, s'), rfl, ⟨h2, h3, h1⟩, rfl⟩

theorem opLab_val_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) :
    ∀ idx P d, OpLab R i idx P d → ∀ y y', (A3.liftI i A3.A.μ0).HasRes3 q y → (A3.liftI i A3.A.μ0).HasRes3 q y' →
      y idx = y' idx := by
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨Q, s'⟩) P d hc y y' hy hy'
  · obtain ⟨-, hk, -⟩ := hc
    have hq : (A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩ ≠ 0 := by
      show A3.A.q P' ≠ 0
      rw [((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.base.lev).2.2.2 hC.base.fam A3.A.μ0 P' hP').2.2]
      exact fun h0 => (R.pl P').ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y (Sum.inl (⟨P', hP'⟩, j))) =
        Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y' (Sum.inl (⟨P', hP'⟩, j))) :=
      (hy.1 ⟨P', hP'⟩).trans (hy'.1 ⟨P', hP'⟩).symm
    have hk' : k ≤ (A3.A.fam.L i A3.A.μ0).n := by
      have e2 : (A3.A.fam.L i A3.A.μ0).n = A3.A.r + A3.A.t := rfl
      rw [e2, ← R.B.rankL i]; exact hk
    exact heckePolyOf_val_eq _ _ hq _ _ e hk'
  · exact (hy.2 (Q, s')).trans (hy'.2 (Q, s')).symm

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thetaLiftPoint_mem_jointEigenspace_of_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : (R.toCx3 F).H3W F.cr false) (i : Fin D.R.m)
    (p : A3.fam3.base3.Ix) (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL)
    (hx : (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p) :
    F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1) := by
  have hZ := (hW i p x).2 hx
  have h2 : (A3.A.fam.L i A3.A.μ0).vE (A3.A.fam.lvlA F.P0 F.ψ0) *ᵥ
      ((A3.A.fam.L i A3.A.μ0).zE (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) *ᵥ x) ∈
      ((A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1)).map
        ((A3.A.fam.L i A3.A.μ0).S.basis.equivFun : (A3.A.fam.L i A3.A.μ0).S.Forms →ₗ[D.what₂.LL] _) := hZ
  obtain ⟨g, hg, hge⟩ := Submodule.mem_map.1 h2
  convert hg using 1
  rw [← LinearEquiv.symm_apply_apply (A3.A.fam.L i A3.A.μ0).S.basis.equivFun g]
  erw [hge]
  rfl

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def eigVal (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) (P : Pl D.host.E) (d : List ℤ) :
    D.what₂.LL :=
  if hx : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d then hx.1.choose hx.2.choose else 0

theorem eig_of_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ))
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h)
    (hn : GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0) h) (f : (A3.A.fam.L i A3.A.μ0).S.Forms)
    (hf : f ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d →
      h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) = D.what₂.embLL (eigVal R i q P d) • R.jV i A3.A.μ0 f := by
  let E : Submodule ℂ (R.HV i A3.A.μ0).H :=
    ⨅ (P : Pl D.host.E) (d : List ℤ) (_ : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ RelLab (Vc D i) P d),
      (h P (Finsupp.single d 1)).eigenspace (D.what₂.embLL (eigVal R i q P d))
  have hle : (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q ≤ E.comap (R.jV i A3.A.μ0) := by
    unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
    refine iSup₂_le fun y hy g hg => ?_
    rw [Submodule.mem_comap]
    simp only [E, Submodule.mem_iInf]
    rintro P d ⟨hgd, hr⟩
    have hex : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d :=
      ⟨⟨y, hy⟩, exists_opLab R F hC i P d hgd hr⟩
    have ha : eigVal R i q P d = hex.1.choose hex.2.choose := by
      unfold eigVal
      rw [dif_pos hex]
    have ha' : eigVal R i q P d = y hex.2.choose :=
      ha.trans (opLab_val_eq R F hC i q _ P d hex.2.choose_spec _ _ hex.1.choose_spec hy)
    have hop := opLab_ops R F hC i h hh _ P d hex.2.choose_spec
    have hN : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) :=
      (congrArg (Commute (h P (Finsupp.single d 1))) (hn.2 P hop.1 (Finsupp.single d 1))).mpr (hn.1 P P hop.1 hop.1 _ _)
    have key := apply_of_mem_maxGen D.what₂.embLL (R.jV i A3.A.μ0) ((A3.liftI i A3.A.μ0).opAll hex.2.choose) _ hN hop.2
      (y hex.2.choose) g (Formalism.L2.Col.eigAt_le (A3.liftI i A3.A.μ0).opAll y hex.2.choose hg)
    exact Module.End.mem_eigenspace_iff.2 (key.trans (congrArg (fun c => D.what₂.embLL c • R.jV i A3.A.μ0 g) ha'.symm))
  intro P d hg hr
  have e1 := hle hf
  rw [Submodule.mem_comap] at e1
  simp only [E, Submodule.mem_iInf] at e1
  exact Module.End.mem_eigenspace_iff.1 (e1 P d ⟨hg, hr⟩)

theorem points_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s _hOk hC hW i p
  obtain ⟨h, hh, hn⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models).2 i A3.A.μ0
  refine ⟨eigVal R i (A3.fam3.tr3 i p.1), fun x hx => ?_⟩
  have hm := thetaLiftPoint_mem_jointEigenspace_of_part R F hW i p x hx
  intro P d hg hr
  have e1 := eig_of_mem R F hC i _ h hh hn _ hm P d hg hr
  have e2 := hh P hg (Finsupp.single d 1) (R.jV i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x))
  exact e2.symm.trans ((congrArg (R.HV i A3.A.μ0).e e1).trans (map_smul _ _ _))

end GlobalTheory.ZPartEig
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  atlas_forward_decl GlobalTheory.ZPartEig.points_eig
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjScalarCoord

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)

theorem wC_cpt (j : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
        (R.FW j).j (sgAt D.what₂.embLL v) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      ((∑ k, cj (twAt D.what₂.embLL v) (v.embedding (c k)) •
        (⟨R.toRealDat.bC F.lv2 b j _ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) :
        (R.HW j (sgAt D.what₂.embLL v)).H) := rfl
  rw [e, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, emb_eq D.what₂.embLL v, cj_cj, LinearMap.map_smulₛₗ, smul_comm]
  rfl

theorem sqrt_ne : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'

theorem liftWeight_complexPoint_eq_twist (j : Fin D.R.m) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      (R.FW j).j (sg0 D A3.A) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • ((Tw.out (s := twAt D.what₂.embLL A3.A.v0)
        ((R.toCx3 F).wC b j A3.A.v0 (cpt A3.A.v0.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL A3.A.v0)) : (R.HW j (sgAt D.what₂.embLL A3.A.v0)).H) := rfl
  rw [e, wC_cpt, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem inner_wC (j : Fin D.R.m) {v : InfinitePlace D.what₂.LL} (hv : v ≠ A3.A.v0) (c c' : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      (Nat.card (F.lv2.lvl b).P : ℂ)⁻¹ * ⟪(R.FW j).j v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b j k),
        (R.FW j).j v.embedding (∑ k, c' k • R.toRealDat.bL F.lv2 b j k)⟫_ℂ := by
  have hs : sgAt D.what₂.embLL v = v.embedding := if_neg (R.hv0 ▸ hv)
  have ht : twAt D.what₂.embLL v = false := if_pos hs.symm
  have e : ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      cj (twAt D.what₂.embLL v) ⟪((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H),
        ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c')) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H)⟫_ℂ := rfl
  rw [e, wC_cpt, wC_cpt, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (RealDat.nP_pos (F := F.lv2) b).le, hs]
  generalize twAt D.what₂.embLL v = s at ht
  subst ht
  simp only [cj, RealDat.nP, Bool.false_eq_true, if_false]
  simp only [cond_false, RingHom.id_apply, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem tC_cpt (cr : Crd A3.fam3.amb3 F.fc) (j : Fin D.R.m) (t : T0)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ j t) → D.what₂.LL) :
    (R.toCx3 F).tC cr b j t (cpt A3.fam3.base3.v0.embedding x) =
      (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t (cr.toL (R.toCx3 F).zs b j t x)) := by
  conv_rhs => rw [← (Pi.basisFun D.what₂.LL _).sum_repr x]
  simp only [CxData.tC, lin_apply, map_sum, map_smul, LinearMap.map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply, cpt,
    RingHom.id_apply]

theorem liftMat_isRatLift_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).H5 F.cr false → (R.toCx3 F).RATth F.cr false → ∀ i, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R.toRealDat i (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k)) ∧ ∀ v, v ≠ A3.A.v0 → ∀ x y, ⟪(R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)), (R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))⟫_ℂ = ((Nat.card F.P0 : ℕ) : ℂ)⁻¹ * ⟪(R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k), (R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y) k • R.toRealDat.bL F.lv2 false i k)⟫_ℂ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hR i
  refine ⟨fun x => ?_, fun v hv x y => ?_⟩
  · show (R.FW i).j (sg0 D A3.A) _ = _
    refine (liftWeight_complexPoint_eq_twist R F false i _).symm.trans ?_
    have h1 := ((R.toCx3 F).key_lift F.cr false hT hR i A3.A.μ0 x).trans (tC_cpt R F false F.cr i A3.A.μ0 x)
    exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) h1
  · rw [inner_wC R F false i hv]
    rfl

end GlobalTheory.ConjScalarCoord
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarOff

section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le' {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem jV_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (t : T0) :
    ∀ z ∈ (R.toCx3 F).Zl j t, R.jV j t z ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) := by
  intro z hz
  have hx1 := range_adjoint_smul_le' (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hz
  exact (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t z)).1 hx1

end SlopeTestRemainingChoices

theorem galD_base : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  intro hHowe hCRL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hC hEx hCS hψ fw hBar hIo hPins hRow0 hPT hU hfacts
  obtain ⟨h5, hrat, h3w, hprov⟩ := hfacts
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  intro j v hv p
  obtain ⟨a, ha⟩ := GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField R F s hOk hC h3w j p
  have hOne := hPT j hU (hRow0 j)
  have hHerm : Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A3.A.fam.L j A3.A.μ0).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0))
      ((A3.A.fam.L j A3.A.μ0).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0)) := hprov j
  have hBH : BlockHyp (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.lifts j A3.A.μ0⟩
  have hfE := GlobalTheory.QuotRational.fE_mem_cmMax _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) A3.A.v0 s hBH hHerm
  obtain ⟨l, hl⟩ := GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces hHowe hCRL T R.toRealDat κ v₀ O F.lv2 _ hcore.1 hψ hCS fw hBar hIo hU hPins j hOne
    (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE (jV_mem_range R F j A3.A.μ0) v.embedding a
  have hmaj := (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE).1 v
  have hco := GlobalTheory.ConjScalarCoord.liftMat_isRatLift_inner R F h5 hrat j
  have hS : ∀ x, (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p → ∀ y,
      ⟪(R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)),
        (R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec y))⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x y := by
    intro x hx y
    have e1 := hco.2 v hv x y
    have e2 := hl x (F.cr.toL (R.toCx3 F).zs false j A3.A.μ0 y) _ _ (ha x hx) (hco.1 x) (hco.1 y)
    have e3 := hmaj x y
    rw [e1, e2]
    erw [e3]
    exact mul_left_comm _ _ _
  intro x hx y
  by_cases hP : R.PartAt F j p v
  · have e : R.lam3 j A3.A.μ0 p v = l := hC.scal.off j p v l hv hP hS
    exact (hS x hx y).trans (congrArg (fun t : ℝ => (t : ℂ) * _) e.symm)
  · have h0 := GlobalTheory.ScalarConjugation.maj_eq_zero _ v x y (by by_contra hn; exact hP ⟨x, hx, hn⟩)
    exact (hS x hx y).trans ((mul_eq_zero_of_right _ h0).trans (mul_eq_zero_of_right _ h0).symm)

end GlobalTheory.ConjScalarOff
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  atlas_forward_decl GlobalTheory.ConjScalarOff.galD_base
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalConjRow

theorem galD_of_inputs : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.SourceLevelLawC R.toRealDat F.lv2 → GlobalTheory.LiftRows.InnerProductFormulaC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FockCoefficientC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FiniteZetaL R.toRealDat F.lv2 → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro hH D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx h1 h2 h3 h4 hph hstd fw hbar hio hom hone hpt hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  exact GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel hH GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s hOk hC hEx
    (GlobalTheory.T.conjugateDatum_lift_scalar_of_innerProductFormula R.toRealDat F.lv2 core hOk.ok2.irr h1 h2 h3 h4
      (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R.toRealDat F.lv2 core))
    hstd fw hbar hio hom hone hpt hun
    (GlobalTheory.scalConj_base_facts R F s hOk hsep hC hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum)

end GlobalTheory.ScalConjRow
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_baseLevel_of_howeUnramifiedCorrespondence : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.SourceLevelLawC R.toRealDat F.lv2 → GlobalTheory.LiftRows.InnerProductFormulaC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FockCoefficientC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FiniteZetaL R.toRealDat F.lv2 → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  atlas_forward_decl GlobalTheory.ScalConjRow.galD_of_inputs
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ScalConj.scalarConjRow : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro pI hH pD _ pBZ _ _ pU pW _ D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx hP
  exact GlobalTheory.T.conjugate_baseLevel_of_howeUnramifiedCorrespondence hH T R F κ v₀ O s hOk hsep hC hEx
    (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law GlobalTheory.SingleBlock.localIntegralSingleBlock R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses pD pW pI R.toRealDat F.lv2 hP)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula (GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral) R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue pD pBZ pU R.toRealDat F.lv2)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_method_consequence : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ScalConj.scalarConjRow | exact GlobalTheory.ScalConj.scalarConjRow | (intros; apply GlobalTheory.ScalConj.scalarConjRow <;> assumption)
end
