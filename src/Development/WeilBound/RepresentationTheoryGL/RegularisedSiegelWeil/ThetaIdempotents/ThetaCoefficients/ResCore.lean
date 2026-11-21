import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpEx
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajor
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MatGExt
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.GenK
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixW
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LRowTotal
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExt
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxId
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EisMeasTop
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LNullSing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemExTrans
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongrOverOfFrame
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularStab
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ProjKComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ContinuousHermitianInnerSelf
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FromColsSmulApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendByZeroHermitianVal
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoef
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFourierPt
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.JstTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenOfRightInvariant
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRel
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfInv
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCore

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

abbrev thM (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : Matrix (Fin r) (Fin r) D.host.E) :
    Measure (Fin r → Fin V.rank → AE D) :=
  GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = T}

theorem thInt (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable Φ (thM V μH 𝓕 T) := by
  classical
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  let b := Module.finBasis D.host.F D.host.E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf D.host.F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV D.host.F
  have : BorelSpace (Ainf D.host.F) := ⟨rfl⟩
  have : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), BorelSpace (Fv D.host.F v) :=
    fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Ainf D.host.F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf D.host.F hCM.1) b laminf hinf.1 r
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Fv D.host.F v)
    (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v) b (lam v) (hlam v).1 r
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (thM V μH 𝓕 T) 1
      (minf (hermOf (Ainf D.host.F) D.sp.cm.sig T hT)) (fun v => m v (hermOf (Fv D.host.F v) D.sp.cm.sig T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero D.host.F D.host.E D.sp.cm.sig hCM r V.rank V.gram hJ (by omega) T hT hdet _ b laminf lam hinf hlam
      μH 𝓕 hμH h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b Φ hΦ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard D.host.F D.host.E V.rank r _ b _ 1 _ _ hEu
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R],
      IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det := by
    intro R _ _
    have h : (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det = HeckeCharacterZeroLocus.SiegelWeilU.inclR R T.det :=
      ((HeckeCharacterZeroLocus.SiegelWeilU.inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR R)
  have hP : ∀ i, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i)) (thM V μH 𝓕 T) := by
    intro i
    obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b laminf hinf
      minf hminf _ (hu _) (φ i) (hφ i)
    have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b v (lam v)
      (hlam v) (m v) (hm v) (hermOf (Fv D.host.F v) D.sp.cm.sig T hT) (hu _) (A i v) (hA i v).1 (hA i v).2
    exact (hS₁ (S ∪ S₁) Finset.subset_union_right (φ i) hφm hφi.self_of_nhds (A i) (fun v => (hfin v).1)
      (fun v => (hfin v).2) (fun v hv => hAl i v fun h => hv (Finset.mem_union_left _ h))).1
  have hΦe : Φ = fun X => ∑ i, GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i) X := funext hsum
  rw [hΦe]
  exact integrable_finsetSum _ fun i _ => hP i

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace PositivityTheory.Rg.Rsw.L.LatticeFibreBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archBump [IsTotallyReal F] {M n : ℕ} (C : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hC : IsCompact C) :
    ∃ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ ∧ ∀ Y ∈ C, φ Y = 1 := by
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  obtain ⟨ρ, hρ⟩ := (hC.image eV.continuous).isBounded.subset_closedBall 0
  let β : ContDiffBump (0 : Fin N → ℝ) :=
    ⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩
  show ((β (eA Y) : ℝ) : ℂ) = 1
  have hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)
  rw [β.one_of_mem_closedBall hm, Complex.ofReal_one]

omit [NumberField F] [NumberField E] in
theorem repr_natCast_mul' {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem scaled_cpt_open {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧
      IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} ∧
      IsOpen {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu
  have hNu : (N : Fv F v ⊗[F] E) * u = 1 := by
    rw [hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i :=
    fun c => continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} =
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v := by
    ext Y
    constructor
    · intro hY
      refine ⟨_, hY, ?_⟩
      funext a i
      show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
      rw [← mul_assoc, mul_comm u, hNu, one_mul]
    · rintro ⟨Z, hZ, rfl⟩
      show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v
      simpa only [← mul_assoc, hNu, one_mul] using hZ
  exact ⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩

omit [NumberField E] in

theorem scaled_eq_lat {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hv : (algebraMap F (Af F) ((N : F)⁻¹)) v ∈ v.adicCompletionIntegers F) :
    {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = latV b v := by
  have hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F := by
    have h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹) :=
      (evalV F v).commutes _
    rwa [h] at hv
  have hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) N, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F := by
    intro c
    constructor
    · intro h
      have := mul_mem hw h
      rwa [← mul_assoc, hwN, one_mul] at this
    · exact fun h => mul_mem (natCast_mem _ N) h
  ext Y
  simp only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]

theorem finCpt_of_integrable (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (n : ℕ) (h2n : 2 * n < M) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hν : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := F) (E := E) Φ → Integrable Φ ν) :
    IsFiniteMeasureOnCompacts ν := by
  classical
  have : IsTotallyReal F := hCM.1
  refine ⟨fun K hK => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨N, R, hN, -, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hCM _ b n M).2 K hK
  obtain ⟨hcInf, -, -, hlat, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM _ b n M
  obtain ⟨φ, hφ, hφ1⟩ := archBump (projInf '' K) (hK.image hcInf)
  let A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  let y : Af F := algebraMap F (Af F) ((N : F)⁻¹)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  have hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => scaled_cpt_open b v N hN (hlat v)
  have hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v := fun v hv =>
    scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))
  have hΦ := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl
  have hint := hν _ hΦ
  have h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := by
    intro X hX
    have e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1 := by
      unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
      rw [hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem
        (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]
    simp [e1]
  calc ν K ≤ ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := measure_mono h1
    _ = 1 * ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := (one_mul _).symm
    _ ≤ ∫⁻ X, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ ∂ν := mul_meas_ge_le_lintegral₀ hint.1.enorm 1
    _ < ⊤ := hint.2

end PositivityTheory.Rg.Rsw.L.LatticeFibreBump

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

theorem thFin (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsFiniteMeasureOnCompacts (thM V μH 𝓕 T) :=
  PositivityTheory.Rg.Rsw.L.LatticeFibreBump.finCpt_of_integrable D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) r hr _ fun Φ hΦ =>
      thInt V hr μH 𝓕 hμH h𝓕 T hT hdet Φ hΦ

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_hermitian_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
    μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ T : Matrix (Fin n) (Fin n) E, (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta | exact GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta <;> assumption)
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

open GlobalTheory.CompanionTheory.SiegelND in

theorem tupOf_act (V : HSp D) (h : GA D V) (X : Fin r → Fin V.rank → AE D) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h X) = mm (mt V h) (tupOf X) := by
  ext i a
  rfl

open GlobalTheory.CompanionTheory.SiegelND in

theorem ip_tupOf (V : HSp D) (X : Fin r → Fin V.rank → AE D) :
    ip V (tupOf X) (tupOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X := by
  ext a b
  exact (GlobalTheory.CompanionTheory.SiegelND.hR_tup V (tupOf X) (tupOf X) a b).symm

open GlobalTheory.CompanionTheory.SiegelND in

def tupE (D : D7) (m r : ℕ) : (Fin r → Fin m → AE D) ≃ᵐ Mx D m r where
  toFun := tupOf
  invFun := tupInv
  left_inv := tupInv_tupOf
  right_inv := tupOf_tupInv
  measurable_toFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupOf.measurable
  measurable_invFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupInv.measurable

open GlobalTheory.CompanionTheory.SiegelND in

theorem finE {m : ℕ} (ν : Measure (Fin r → Fin m → AE D)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (ν.map (tupE D m r)) := by
  refine ⟨fun K hK => ?_⟩
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D m r) ⁻¹' K = tupInv '' K := by
    ext X
    exact ⟨fun hX => ⟨tupOf X, hX, rfl⟩, fun ⟨y, hy, hyX⟩ => by subst hyX; exact hy⟩
  rw [hs]
  exact (hK.image continuous_tupInv).measure_lt_top

open GlobalTheory.CompanionTheory.SiegelND in

theorem suppE (V : HSp D) (T : Matrix (Fin r) (Fin r) D.host.E) (ν : Measure (Fin r → Fin V.rank → AE D))
    (h : ν {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ = 0) :
    ν.map (tupE D V.rank r) {x | ip V x x ≠ rat T} = 0 := by
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D V.rank r) ⁻¹' {x | ip V x x ≠ rat T} ⊆
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ := by
    intro X hX h0
    apply hX
    change ip V (tupOf X) (tupOf X) = rat T
    rw [ip_tupOf]
    exact h0
  exact measure_mono_null hs h

open GlobalTheory.CompanionTheory.SiegelND in

theorem invE (V : HSp D) (ν : Measure (Fin r → Fin V.rank → AE D)) (h : GA D V)
    (hm : Measurable (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h : (Fin r → Fin V.rank → AE D) → _))
    (hν : ν.map (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h) = ν) :
    (ν.map (tupE D V.rank r)).map (fun x => mm (mt V h) x) = ν.map (tupE D V.rank r) := by
  set e := tupE D V.rank r
  have hg : Measurable fun x : Mx D V.rank r => mm (mt V h) x := by
    have : (fun x : Mx D V.rank r => mm (mt V h) x) =
        e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h ∘ e.symm :=
      funext fun x => (tupOf_act V h (tupInv x)).symm
    rw [this]
    exact e.measurable.comp (hm.comp e.symm.measurable)
  have hc : (fun x : Mx D V.rank r => mm (mt V h) x) ∘ e = e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h :=
    funext fun X => (tupOf_act V h X).symm
  rw [Measure.map_map hg e.measurable, hc, ← Measure.map_map e.measurable hm, hν]

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.SiegelND in
theorem _root_.PositivityTheory.Rg.Rsw.L.fibEx : FibEx := by
  intro D r V hr ψ hψ θ hθ μ hμ lam hlam b₀ hb₀
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (b₀.1 b a) = b₀.1 a b := fun a b => by
    have := congrFun (congrFun b₀.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hCM (AF D.host.F)
  have := hB r V.rank
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact _ _ D.sp.cm.sig hCM V.rank V.gram hJ (AF D.host.F)
  obtain ⟨ac, -, -, -⟩ := hact r
  have hTI := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ μH 𝓕 hμH h𝓕 r b₀.1
  have hfin := thFin V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀
  refine ⟨(thM V μH 𝓕 b₀.1).map (tupE D V.rank r), finE _, suppE V b₀.1 _ hTI.2,
    fun h => invE V _ h (ac.comp (continuous_const.prodMk continuous_id)).measurable (hTI.1 h), fun φ hφ => ?_⟩
  have hSB := GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ
  have hI := thInt V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀ _ hSB
  refine ⟨(tupE D V.rank r).measurableEmbedding.integrable_map_iff.2 hI, ?_⟩
  rw [hW φ b₀, (tupE D V.rank r).measurableEmbedding.integral_map]
  exact GlobalTheory.T.siegel_weil_hermitian_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb μH 𝓕 hμH h𝓕 _ hSB
    b₀.1 hT hb₀

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThetaPoisson GlobalTheory.CompanionTheory.ThetaInv GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

def SetW (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) : Prop :=
  IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ IsInfFam θ ∧ (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) ∧ IsWeilSch ψ χ θ V μ ω

theorem theta_levi_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨-, hχ, -, -, hω⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hS.2.2.2.2.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), psi_unip_rat hS.1, one_mul]

theorem theta_weyl_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨hψ, -, hθ, ⟨𝓕, hμ⟩, hω⟩ := hS
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (Φ : schwartzA θ V.rank n) (γ : G D n) (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi_w hS g a hg Φ)
    (fun g b hg Φ => theta_unip_w hS g b hg Φ) (fun g hg Φ => theta_weyl_w hS g hg Φ)
  exact hle hγ Φ

theorem covar_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (γ : G D n) (hγ : γ ∈ GF D n) (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n) (hΨ : Ψ.1 = Heisenberg₂ ψ V v Φ.1) :
    (ω γ Ψ).1 = Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1 := by
  obtain ⟨-, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat GlobalTheory.CompanionTheory.BruhatCell.bruhat D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem partial_fourier_second_term {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (Φ : schwartzA θ V.rank n) (r : ℕ) (hr : r ≤ n) (μr : Measure (Mx D V.rank r))
    (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E) (hc : IsCompl c a)
    (b : HermE D r) (γ : G D n) (hγ : γ ∈ GF D n)
    (hmat : mat γ = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D)) :
    (ω γ Φ).1 0 = J ψ V μr (pull c Φ.1) b := by
  obtain ⟨hψ, -, hθ, ⟨𝓕, hcov⟩, -⟩ := id hS
  have hinv : mat γ * mat γ⁻¹ = 1 := mat_mul_inv' γ
  rw [GlobalTheory.T.eisenstein_vanishing D ψ hψ θ hθ V n μ 𝓕 hcov (ω γ Φ).1 (ω γ Φ).2,
    ← GlobalTheory.T.eisenstein_unfolding_second_term D ψ hψ θ hθ V n r hr μ 𝓕 hcov μr hμr c a hc b Φ.1 Φ.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [← hmat]
  have hΨ := GlobalTheory.T.eisenstein_heisenberg_schwartz D ψ hψ θ hθ V n (HMul.hMul (zy y) (mat γ)) Φ.1 Φ.2
  have h1 := covar_w hS γ hγ (HMul.hMul (zy y) (mat γ)) Φ
    ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ rfl
  have h2 := thetaInv_w hS ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ γ hγ
  have hv : HMul.hMul (HMul.hMul (zy y) (mat γ)) (mat γ⁻¹) = zy y := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hv] at h1
  rw [h1] at h2
  exact h2

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

abbrev ee (hn : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr hn)

abbrev ff (hn : r + t = n) : Fin t ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))

theorem ee_inl_val (hn : r + t = n) (k : Fin r) : (ee hn (Sum.inl k) : ℕ) = k := by simp [ee]
theorem ee_inr_val (hn : r + t = n) (k : Fin t) : (ee hn (Sum.inr k) : ℕ) = r + k := by simp [ee]
theorem ff_inl_val (hn : r + t = n) (k : Fin t) : (ff hn (Sum.inl k) : ℕ) = k := by simp [ff]
theorem ff_inr_val (hn : r + t = n) (k : Fin r) : (ff hn (Sum.inr k) : ℕ) = t + k := by simp [ff]

theorem ext_ee (hn : r + t = n) {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (h : ∀ s s', M (ee hn s) (ee hn s') = N (ee hn s) (ee hn s')) : M = N := by
  ext i j
  simpa using h ((ee hn).symm i) ((ee hn).symm j)

theorem bl_ee {R : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (s s' : Fin r ⊕ Fin t) :
    bl hn a b c d (ee hn s) (ee hn s') = Matrix.fromBlocks a b c d s s' := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem blockRowSubstitution_one {R : Type} [CommRing R] (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, Matrix.fromBlocks_one, Matrix.one_apply, Matrix.one_apply]
  simp only [(ee hn).injective.eq_iff]

theorem bl_add {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.add_apply, bl_ee, bl_ee, bl_ee, ← Matrix.add_apply, Matrix.fromBlocks_add]

theorem block_neg {R : Type} [CommRing R] (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    -bl hn a b c d = bl hn (-a) (-b) (-c) (-d) := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.neg_apply, bl_ee, bl_ee, ← Matrix.neg_apply, Matrix.fromBlocks_neg]

theorem block_map {R S : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (f : R → S) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [bl, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem one_sub_bl {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 1 = bl hn 1 0 0 0 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem eId_eq {K : Type} [Field K] (hn : r + t = n) : eId K n r = bl hn 1 0 0 0 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, eId, Matrix.diagonal_apply]
  simp only [(ee hn).injective.eq_iff]
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp [Matrix.one_apply, ee_inl_val, ee_inr_val]

theorem cT_blk4 {K : Type} [Field K] (σ : K →+* K) (A B C E : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose]

def wE {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (1 - e) e (-e) (1 - e)

theorem cT_one {K : Type} [Field K] (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT]

theorem cT_sub {K : Type} [Field K] (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) : cT σ (A - B) = cT σ A - cT σ B := by
  have h : (A - B).map σ = A.map σ - B.map σ := by ext; simp
  rw [cT, cT, cT, h, Matrix.transpose_sub]

theorem cT_neg {K : Type} [Field K] (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) : cT σ (-A) = -cT σ A := by
  have h : (-A).map σ = -A.map σ := by ext; simp
  rw [cT, cT, h, Matrix.transpose_neg]

theorem block_matrix_map {R S : Type} (A B C E : Matrix (Fin n) (Fin n) R) (f : R → S) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  simp only [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem wE_unit {K : Type} [Field K] (σ : K →+* K) (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) (hσ : cT σ e = e) :
    IsUnit (wE e).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE e) := by
  have h1 : e * (1 - e) = 0 := by rw [Matrix.mul_sub, he, Matrix.mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [Matrix.sub_mul, he, Matrix.one_mul, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_zero]
  constructor
  · refine Matrix.isUnit_det_of_right_inverse (B := blk4 (1 - e) (-e) e (1 - e)) ?_
    rw [wE, submatrix_fromBlocks_mul, ← block_matrix_one]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      sub_add_cancel, neg_add_cancel]; try abel)
  · unfold IsUnitary
    rw [wE, cT_blk4, cT_sub, cT_one, hσ, cT_neg, hσ, PositivityTheory.GramSchwartzFunctions.EC.Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_add_cancel, neg_add_cancel]; try abel)

def πe (hn : r + t = n) : Equiv.Perm (Fin n) := (ff hn).symm.trans ((Equiv.sumComm _ _).trans (ee hn))

theorem πe_ff_inl (hn : r + t = n) (k : Fin t) : πe hn (ff hn (Sum.inl k)) = ee hn (Sum.inr k) := by
  rw [πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inl (hn : r + t = n) (k : Fin r) : (πe hn).symm (ee hn (Sum.inl k)) = ff hn (Sum.inr k) := by
  rw [Equiv.symm_apply_eq, πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inr (hn : r + t = n) (k : Fin t) : (πe hn).symm (ee hn (Sum.inr k)) = ff hn (Sum.inl k) := by
  rw [Equiv.symm_apply_eq, πe_ff_inl]

def Pm (K : Type) [Field K] (hn : r + t = n) : Matrix (Fin n) (Fin n) K := (1 : Matrix (Fin n) (Fin n) K).submatrix (πe hn) id

theorem permutation_matrix_transpose {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ = (1 : Matrix (Fin n) (Fin n) K).submatrix id (πe hn) := by
  simp [Pm, Matrix.transpose_submatrix]

theorem Pm_mul_alt {K : Type} [Field K] (hn : r + t = n) : Pm K hn * (Pm K hn)ᵀ = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (πe hn) (Equiv.refl _) (πe hn)
  simpa using this

theorem T_mul_Pm {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ * Pm K hn = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id
  simpa using this

theorem conj_Pm {K : Type} [Field K] (hn : r + t = n) (M : Matrix (Fin n) (Fin n) K) :
    (Pm K hn)ᵀ * M * Pm K hn = M.submatrix (πe hn).symm (πe hn).symm := by
  have e1 : M = (M.submatrix (πe hn).symm id).submatrix (πe hn) id := by ext; simp
  have e2 : M.submatrix (πe hn).symm id = (M.submatrix (πe hn).symm (πe hn).symm).submatrix id (πe hn) := by ext; simp
  rw [permutation_matrix_transpose, Pm]
  nth_rewrite 1 [e1]
  rw [Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) _ id (πe hn) id, Matrix.one_mul, Matrix.submatrix_id_id, e2,
    Matrix.submatrix_mul_equiv _ (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id, Matrix.mul_one, Matrix.submatrix_id_id]

theorem eId_conj {K : Type} [Field K] (hn : r + t = n) :
    (Pm K hn)ᵀ * eId K n t * Pm K hn = bl hn 0 0 0 1 := by
  rw [conj_Pm]
  refine ext_ee hn fun s s' => ?_
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp only [bl_ee, Matrix.submatrix_apply, πe_symm_ee_inl, πe_symm_ee_inr] <;>
    rw [eId, Matrix.diagonal_apply] <;>
    simp [(ff hn).injective.eq_iff, ff_inl_val, ff_inr_val, Matrix.one_apply] <;> simp [Fin.ext_iff] <;> omega

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

theorem block_mul₂ {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' = bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem cT_bl {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) (a : Matrix (Fin r) (Fin r) K) (b : Matrix (Fin r) (Fin t) K)
    (c : Matrix (Fin t) (Fin r) K) (d : Matrix (Fin t) (Fin t) K) :
    cT σ (bl hn a b c d) = bl hn (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.cT
  rw [block_map]
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_zero {K : Type} [Field K] (σ : K →+* K) {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  simp [cT]

theorem first_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0 * bl hn 1 0 0 0 = bl hn 1 0 0 0 ∧
      cT σ (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) = bl hn 1 0 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

theorem second_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1 * bl hn 0 0 0 1 = bl hn 0 0 0 1 ∧
      cT σ (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1) = bl hn 0 0 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

theorem Pm_map {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : (Pm K hn).map σ = Pm K hn := by
  rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem cT_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn) = (Pm K hn)ᵀ := by
  rw [cT, Pm_map]

theorem cT_PmT {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn)ᵀ = Pm K hn := by
  rw [cT, Matrix.transpose_map, Pm_map, Matrix.transpose_transpose]

theorem repMat_zero {K : Type} [Field K] (σ : K →+* K) {p : ℕ} (a : Matrix (Fin n) (Fin n) K) :
    repMat σ (0 : Matrix (Fin p) (Fin p) K) a = wr K n p * mA σ a := by
  have h0 : (PositivityTheory.GramSchwartzFunctions.EC.extB (n := n) (0 : Matrix (Fin p) (Fin p) K)) = 0 := by
    ext i j
    simp [PositivityTheory.GramSchwartzFunctions.EC.extB]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.repMat, h0, PositivityTheory.GramSchwartzFunctions.EC.nB, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one, Matrix.mul_one]

theorem mA_one {K : Type} [Field K] (σ : K →+* K) : mA σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_one, inv_one, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]

theorem mA_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : mA σ (Pm K hn) = blk4 (Pm K hn) 0 0 (Pm K hn) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_Pm, Matrix.inv_eq_left_inv (Pm_mul_alt (K := K) hn)]

theorem key3 {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * repMat σ (0 : Matrix (Fin t) (Fin t) K) (Pm K hn) = wE (bl hn 0 0 0 1) := by
  have hc := eId_conj (K := K) hn
  have h1 : (Pm K hn)ᵀ * (1 - PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = 1 - bl hn 0 0 0 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, T_mul_Pm, hc]
  have h2 : (Pm K hn)ᵀ * (-PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = -bl hn 0 0 0 1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hc]
  rw [repMat_zero, mA_Pm, ← Matrix.mul_assoc]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.wr, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h2, hc]
  rfl

theorem gQ_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ) := by
  have hinv : blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * blk4 (Pm K hn) 0 0 (Pm K hn) = 1 := by
    rw [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [T_mul_Pm, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  refine ⟨Matrix.isUnit_det_of_right_inverse hinv, ?_⟩
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary PositivityTheory.GramSchwartzFunctions.EC.Jm
  rw [cT_blk4, cT_PmT, cT_zero]
  simp only [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Pm_mul_alt, Matrix.one_mul, neg_zero]

theorem wr_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wr K n r).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wr K n r) := by
  have h : PositivityTheory.GramSchwartzFunctions.EC.wr K n r = wE (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) := by
    rw [← eId_eq hn]
    rfl
  rw [h]
  exact wE_unit σ _ (first_block_hermitian_idempotent σ hn).1 (first_block_hermitian_idempotent σ hn).2

theorem second_block_weyl_unitary {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)).det ∧
      IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)) :=
  wE_unit σ _ (second_block_hermitian_idempotent σ hn).1 (second_block_hermitian_idempotent σ hn).2

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t a : ℕ}

def c₁ (D : D7) (hn : r + t = n) : Matrix (Fin r) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inl k)) id

def c₃ (D : D7) (hn : r + t = n) : Matrix (Fin t) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inr k)) id

theorem jn_ee (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (s : Fin r ⊕ Fin t) :
    jn hn x v i (ee hn s) = Matrix.fromCols x v i s := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]

theorem mul_c₁ (hn : r + t = n) (y : Mx D a r) : mm y ((c₁ D hn).map (incA D)) = jn hn y 0 := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₁, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem mul_c₃ (hn : r + t = n) (y : Mx D a t) : mm y ((c₃ D hn).map (incA D)) = jn hn 0 y := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₃, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem compl_c₁ (hn : r + t = n) : IsCompl (c₁ D hn) 1 := by
  refine ⟨by simp, fun i hi => ?_⟩
  have : ee hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ee_inl_val hn _)
  simp only [c₁, this]
  rfl

theorem compl_c₃ (hn : r + t = n) : IsCompl (c₃ D hn) (Pm D.host.E hn) := by
  refine ⟨Matrix.isUnit_det_of_right_inverse (Pm_mul_alt hn), fun i hi => ?_⟩
  have h1 : ff hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ff_inl_val hn _)
  have h2 : πe hn i = ee hn (Sum.inr ⟨i, hi⟩) := by
    have := πe_ff_inl hn ⟨i, hi⟩
    rwa [h1] at this
  funext j
  simp only [Pm, c₃, Matrix.submatrix_apply]
  rw [h2]

theorem linInd_c₁ (hn : r + t = n) : LinearIndependent D.host.E (c₁ D hn) := by
  have h : c₁ D hn = (Pi.basisFun D.host.E (Fin n)) ∘ (fun k => ee hn (Sum.inl k)) := by
    funext k j
    simp [c₁, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h]
  exact (Pi.basisFun D.host.E (Fin n)).linearIndependent.comp _
    (fun k k' h => Sum.inl_injective ((ee hn).injective h))

theorem jn_mul_bl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (A : Mx D r r) (B : Mx D r t) (C : Mx D t r)
    (E : Mx D t t) :
    HMul.hMul (jn hn x v) (bl hn A B C E) = jn hn (x * A + v * C) (x * B + v * E) := by
  simp only [jn, bl]
  rw [show (Matrix.fromCols x v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm =
    (Matrix.fromCols x v).submatrix id (⇑(finSumFinEquiv.trans (finCongr hn)).symm) from rfl,
    Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) : jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  simp only [Matrix.add_apply, jn_ee]
  rcases s with k | k <;> simp

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar GlobalTheory.CompanionTheory.ThetaPoisson

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

theorem mem_gf_of {γ : G D n} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (hu : IsUnit g.det)
    (hU : IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (PositivityTheory.GramSchwartzFunctions.EC.Jm D.host.E n) g)
    (h : mat γ = g.map (incA D)) : γ ∈ GF D n := by
  obtain ⟨γ₀, h0, e⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 g hu hU
  rwa [mat_injective' (e.trans h.symm)] at h0

theorem one_sub_bl' {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 0 = bl hn 0 0 0 1 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem mat_w (hn : r + t = n) (M : Maps D hn) : mat M.w = (wr D.host.E n r).map (incA D) := by
  have hm : (-1 : Matrix (Fin r) (Fin r) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [M.w_mat, wr, eId_eq hn, block_matrix_map, one_sub_bl', block_neg]
  simp [block_map, hm]

theorem mat_emb (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = (wE (bl hn (0 : Matrix (Fin r) (Fin r) D.host.E) 0 0 1)).map (incA D) := by
  have hm : (-1 : Matrix (Fin t) (Fin t) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [M.emb_mat w 0 1 (-1) 0 hw, wE, one_sub_bl, block_neg, block_matrix_map]
  simp [block_map, hm]

theorem mat_emb' (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = blk4 (bl hn 1 0 0 0) (bl hn 0 0 0 1) (bl hn 0 0 0 (-1)) (bl hn 1 0 0 0) :=
  M.emb_mat w 0 1 (-1) 0 hw

theorem adj_Pm (hn : r + t = n) : adj ((Pm D.host.E hn).map (incA D)) = (Pm D.host.E hn)ᵀ.map (incA D) := by
  have h1 : (Pm D.host.E hn).map (incA D) = (1 : Mx D n n).submatrix (πe hn) id := by
    rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [adj, Matrix.transpose_map, h1, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]

def uP (D : D7) (hn : r + t = n) : GL (Fin n) D.host.E := ⟨(Pm D.host.E hn)ᵀ, Pm D.host.E hn, T_mul_Pm hn, Pm_mul_alt hn⟩

theorem mat_gQ {γ : G D n} (hn : r + t = n) (h : mat γ = (blk4 (Pm D.host.E hn)ᵀ 0 0 (Pm D.host.E hn)ᵀ).map (incA D)) :
    mat γ = blk4 ((uP D hn).1.map (incA D)) 0 0 (adj (((uP D hn)⁻¹).1.map (incA D))) := by
  rw [h, block_matrix_map]
  show blk4 _ _ _ _ = blk4 _ _ _ (adj ((Pm D.host.E hn).map (incA D)))
  rw [adj_Pm]
  simp [uP]

def xz {m : ℕ} (X : Mx D m n) : Mx D m (n + n) :=
  Matrix.of fun i k => Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm k)

theorem xPart_xz {m : ℕ} (X : Mx D m n) : xPart (xz X) = X := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem yPart_xz {m : ℕ} (X : Mx D m n) : yPart (xz X) = 0 := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem heis_xz (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (X : Mx D V.rank n) (F : Mx D V.rank n → ℂ) :
    PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V (xz X) F 0 = F X := by
  simp [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, xPart_xz, yPart_xz, GlobalTheory.StdUnn.inner, halfTr]

theorem trace_inner_jn (V : HSp D) (hn : r + t = n) (x x' : Mx D V.rank r) (v v' : Mx D V.rank t) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x' v')) = Matrix.trace (ip V x x') + Matrix.trace (ip V v v') := by
  simp only [Matrix.trace, Matrix.diag, GlobalTheory.StdUnn.inner, ip, mm]
  rw [← (ee hn).sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, jn_ee, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr]

theorem psi_ip_symm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (x y : Mx D V.rank t) :
    ψ (trA (Matrix.trace (ip V x y))) = ψ (trA (Matrix.trace (ip V y x))) := by
  have hs := pairing_symm (n := t) (isHermND_gram V) ψ x y
  have e : ∀ a b : Mx D V.rank t, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ a b = ψ (trA (Matrix.trace (ip V a b))) :=
    fun a b => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
      rfl
  rw [← e, ← e, hs]

theorem levi_zero {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (g : G D n) (u : GL (Fin n) D.host.E)
    (hg : mat g = blk4 (u.1.map (incA D)) 0 0 (adj ((u⁻¹).1.map (incA D)))) (F : schwartzA θ V.rank n) :
    (ω g F).1 0 = F.1 0 := by
  obtain ⟨-, hχ, -, -, hω⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) u
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det u) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (u⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) u)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  rw [hω.levi g a' hg' F, h1, h2]
  simp [npow]

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

def h0 (D : D7) (p : ℕ) : HermE D p := ⟨0, by simp⟩

theorem j_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {p : ℕ} (y : Mx D V.rank p) :
    ψ (halfTr (Matrix.trace (HMul.hMul ((h0 D p).1.map (incA D)) (GlobalTheory.StdUnn.inner V y y) : Mx D p p))) = 1 := by
  simp [h0, halfTr]

theorem clause1 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μr : Measure (Mx D V.rank r)) (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) (Φ : schwartzA θ V.rank n) :
    (ω M.w Φ).1 0 = ∫ x, Φ.1 (jn hn x 0) ∂μr := by
  have hmat : mat M.w = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D r).1 1).map (incA D) := by
    rw [h0, repMat_zero, mA_one, Matrix.mul_one, mat_w]
  have hγ : M.w ∈ GF D n := mem_gf_of _ (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_w hn M)
  rw [partial_fourier_second_term hS Φ r (by omega) μr hμr (c₁ D hn) 1 (compl_c₁ hn) (h0 D r) M.w hγ hmat]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  exact congrArg Φ.1 (mul_c₁ hn y)

theorem clause2 {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hn : r + t = n) (Φ : schwartzA θ V.rank n) :
    (fun x => Φ.1 (jn hn x 0)) ∈ schwartzA θ V.rank r := by
  have := GlobalTheory.T.pullback_schwartz_linear_independent D θ hθ V.rank r n (c₁ D hn) (linInd_c₁ hn) Φ.1 Φ.2
  convert this using 1
  funext x
  exact congrArg Φ.1 (mul_c₁ hn x).symm

theorem clause3 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μt : Measure (Mx D V.rank t)) (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    (w : G D t) (hw : IsW w) (x : Mx D V.rank r) (v₀ : Mx D V.rank t) :
    (ω (M.emb w) Φ).1 (jn hn x v₀) = ∫ v, Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V v₀ v))) ∂μt := by
  have hγ : M.emb w ∈ GF D n := mem_gf_of _ (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_emb hn M w hw)
  obtain ⟨γQ, hQ, hmQ⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 _ (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2
  have hγ' : γQ⁻¹ * M.emb w ∈ GF D n := (GF D n).mul_mem ((GF D n).inv_mem hQ) hγ
  have hmat' : mat (γQ⁻¹ * M.emb w) =
      (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) := by
    have h1 : mat γQ * (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) =
        mat (M.emb w) := by
      rw [hmQ, ← Matrix.map_mul, h0, key3, mat_emb hn M w hw]
    rw [mat_mul', ← h1, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have hψ := hS.1
  have hθ := hS.2.2.1
  have hΨm := GlobalTheory.T.eisenstein_heisenberg_schwartz D ψ hψ θ hθ V n (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1 Φ.2
  let Ψ : schwartzA θ V.rank n := ⟨Heisenberg₂ ψ V (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1, hΨm⟩
  have hc := covar_w hS (M.emb w) hγ (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ Ψ rfl
  have hv : HMul.hMul (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) (mat (M.emb w)⁻¹) = xz (jn hn x v₀) := by
    rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]
  rw [hv] at hc
  have step1 : (ω (M.emb w) Φ).1 (jn hn x v₀) = (ω (M.emb w) Ψ).1 0 := by rw [hc, heis_xz]
  have step2 : (ω (M.emb w) Ψ).1 0 = (ω (γQ⁻¹ * M.emb w) Ψ).1 0 := by
    conv_lhs => rw [show M.emb w = γQ * (γQ⁻¹ * M.emb w) by group]
    rw [map_mul, Module.End.mul_apply]
    exact levi_zero hS γQ (uP D hn) (mat_gQ hn hmQ) _
  rw [step1, step2, partial_fourier_second_term hS Ψ t (by omega) μt hμt (c₃ D hn) (Pm D.host.E hn) (compl_c₃ hn) (h0 D t) _ hγ' hmat']
  have hx : xPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn x 0 := by
    rw [mat_emb' hn M w hw, x_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hy : yPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn 0 v₀ := by
    rw [mat_emb' hn M w hw, y_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hip1 : ∀ {a b : ℕ} (z : Mx D V.rank b), ip V (0 : Mx D V.rank a) z = 0 := fun z => by simp [ip, mm, adj]
  have hip2 : ∀ {a b : ℕ} (z : Mx D V.rank a), ip V z (0 : Mx D V.rank b) = 0 := fun z => by simp [ip, mm]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  show PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V _ Φ.1 _ = _
  rw [show (HMul.hMul y ((c₃ D hn).map (incA D)) : Mx D V.rank n) = jn hn 0 y from mul_c₃ hn y]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, jn_add, trace_inner_jn, trace_inner_jn, hip1, hip1, hip2]
  simp only [Matrix.trace_zero, zero_add, add_zero, halfTr, map_zero, mul_zero]
  rw [psi_ip_symm, mul_comm]

end PositivityTheory.Rg.Rsw.L.LPartFT

namespace PositivityTheory.Rg.Rsw.L

theorem partFT : PartFT := by
  intro D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt Φ
  have hS : LPartFT.SetW D n V ψ χ θ μ ω := ⟨hψ, hχ, hθ, hμ, hω⟩
  exact ⟨LPartFT.clause1 hS hn M μr hμr Φ, LPartFT.clause2 hθ hn Φ,
    fun w hw x v₀ => LPartFT.clause3 hS hn M μt hμt Φ w hw x v₀⟩

end PositivityTheory.Rg.Rsw.L
end
end

section
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := GlobalTheory.T.split_place_rank_cut_of_alternative (GlobalTheory.T.alternative_local_computation_of_components GlobalTheory.T.iwasawa_decomposition_statement GlobalTheory.T.height_bound_statement GlobalTheory.T.uniform_boundedness_statement GlobalTheory.T.compactness_statement GlobalTheory.T.positivity_statement)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := GlobalTheory.T.jacquet_piatetski_bound_holds D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact GlobalTheory.T.section_eigenfunction_maximal_compact D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
end

section
theorem PositivityTheory.Rg.Rsw.resCore : PositivityTheory.Rg.Rsw.ResCore :=
  open PositivityTheory.Rg.Rsw in
  have i := PositivityTheory.Rg.Rsw.L.idemEx
  have ge := PositivityTheory.Rg.Rsw.L.goodEv i
  have be := PositivityTheory.Rg.Rsw.L.bumpEx i
  have wm := PositivityTheory.Rg.Rsw.L.wMaj
  have tp := PositivityTheory.Rg.Rsw.L.thProd wm
  have rt := PositivityTheory.Rg.Rsw.L.rowTotal i be
  have fw := PositivityTheory.Rg.Rsw.L.fixW i PositivityTheory.Rg.Rsw.L.genK wm
  have ns := PositivityTheory.Rg.Rsw.L.nullSing i
  have t2 := GlobalTheory.CompanionTheory.ColumnSplitting.main i PositivityTheory.Rg.Rsw.L.latBound GlobalTheory.CompanionTheory.QKAvg.qk PositivityTheory.Rg.Rsw.L.ikSch
  have em := PositivityTheory.Rg.Rsw.Em.eisMeas i be (PositivityTheory.Rg.Rsw.L.major i ge be) fw (PositivityTheory.Rg.Rsw.L.fixTh i PositivityTheory.Rg.Rsw.L.geng PositivityTheory.Rg.Rsw.L.genK) tp (PositivityTheory.Rg.Rsw.Cell.muCell htExist i)
    PositivityTheory.Rg.Rsw.L.fibEx (GlobalTheory.CompanionTheory.RCellP.rcell wm PositivityTheory.Rg.Rsw.L.partFT) PositivityTheory.Rg.Rsw.L.posExt (PositivityTheory.Rg.Rsw.L.approxId i)
  have mi := PositivityTheory.Rg.Rsw.L.muId i ge be tp em ns (GlobalTheory.CompanionTheory.OrbUniq.uniq_of_trans i ns (GlobalTheory.CompanionTheory.RgTrans.idemEx_trans i)) (GlobalTheory.CompanionTheory.RswNoFrame.noFrame i) t2 (PositivityTheory.Rg.Rsw.L.toS i)
  have ci := GlobalTheory.CompanionTheory.RkCoef.target polar resMu mapsExist cfFJ pcBound pcFc rSec htExist tp rt wm PositivityTheory.Rg.Rsw.L.ikSch t2 mi
  have tb := PositivityTheory.Rg.Rsw.L.thBdd wm PositivityTheory.Rg.Rsw.L.latBound PositivityTheory.Rg.Rsw.L.wa1
  have cl := PositivityTheory.Rg.Rsw.L.cutLow PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1
  have ie := (fun _ _ _ => PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.GenG → PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.IkEq) PositivityTheory.Rg.Rsw.L.geng wm PositivityTheory.Rg.Rsw.L.ikSch
  have tc := PositivityTheory.Rg.Rsw.L.thCoef PositivityTheory.Rg.Rsw.L.latBound
  PositivityTheory.Rg.Rsw.L.resCore polar cfFJ i ge fw wm (GlobalTheory.CompanionTheory.Jp.jPos_of_idemEx i) (PositivityTheory.Rg.Rsw.L.cfRel htExist) PositivityTheory.Rg.Rsw.L.cfInv cl
    (PositivityTheory.Rg.Rsw.L.cutId polar cfFJ ci tc PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1 PositivityTheory.Rg.Rsw.L.cfInv tb cl PositivityTheory.Rg.Rsw.L.ikSch ie wm) tb tc PositivityTheory.Rg.Rsw.L.ikSch ie
end
