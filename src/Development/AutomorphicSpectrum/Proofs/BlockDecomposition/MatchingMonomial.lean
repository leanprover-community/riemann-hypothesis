import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSchwartzAOfIsMonoFock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.RationalHermitianCountable.CountableRatHerm
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatAtIsCO
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarLatticeUnipotentIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem npow_inv (x : ℝ≥0) (t : ℂ) : (((((x : ℝ))⁻¹ : ℝ)) : ℂ) ^ (-t) = npow x t := by
  have harg : Complex.arg ((x : ℝ) : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg x)]
    exact Real.pi_pos.ne
  unfold npow
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

theorem npow_add_of (x : ℝ≥0) (hx : x ≠ 0) (s t : ℂ) : npow x (s + t) = npow x s * npow x t := by
  unfold npow
  exact Complex.cpow_add _ _ (by exact_mod_cast hx)

theorem jtR_hermTo (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (φ : Mx D V.rank n → ℂ)
    (b : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
      (fun X => φ (tupOf X)) (hermTo b) = Jt ψ V μ φ b := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  haveI : IsTopologicalAddGroup (Mx D V.rank n) := k1
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  unfold PositivityTheory.PfSWUS.Loc.jtR Jt
  rw [integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hg : gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
    ext a c
    exact hR_tup V y y a c
  change φ y * ψ (PositivityTheory.PfSWUS.Loc.trPair _ b.1 (gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y))) = _
  rw [hg]
  rfl

theorem trace_pull (a : GL (Fin n) (AE D)) (B : Mx D n n) (b : hermA D n) :
    Matrix.trace (HMul.hMul (adj a.1 * B * a.1) (pull a b).1 : Mx D n n) = Matrix.trace (HMul.hMul B b.1 : Mx D n n) := by
  have h1 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul]
    have : a.1 * (a⁻¹).1 = 1 := by simp
    rw [this]
    simp [adj]
  have h2 : a.1 * (a⁻¹).1 = 1 := by simp
  show Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1)) = Matrix.trace (B * b.1)
  calc Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1))
      = Matrix.trace (adj a.1 * (B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1)) * adj a.1) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * b.1 * (adj (a⁻¹).1 * adj a.1)) := by
        rw [h2]
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = Matrix.trace (B * b.1) := by rw [h1, Matrix.mul_one]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem mono_mem (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ)
    (hθ : IsInfFam θ) (hl : ∀ τ, l τ ≠ 0) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hφ : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s ∧ φ ∈ schwartzA θ V.rank n := by
  refine ⟨?_, GlobalTheory.CompanionTheory.IfrAdd.mem_schwartzA_of_isMonoFock hθ hl hs hφ⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := hφ
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    have h1 := GlobalTheory.CompanionTheory.IfrAdd.mem_SB_of_isPureFin bs (Φf := fun X => g fun i j => X j i) (Φv := gv) hp
    have h2 := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) h1
    exact ⟨h2.1, h2.2⟩
  exact Submodule.subset_span ⟨_, g, hg, rfl⟩

theorem sect_w (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (hω : IsWeilSch ψ χ θ V μ ω) (nb : hermA D n → G D n) (hnb : IsNMap nb) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0)
    (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b * 1) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  rw [mul_one]
  unfold sect Jt
  congr 1
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, adj]
  show (ω (nb b) Φ).1 y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V 0 y))) = _
  rw [h0, hω.unip (nb b) b.1 (hnb b)]
  simp [mul_comm]

theorem jt_pull (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n))
    (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (φ : Mx D V.rank n → ℂ) (a : GL (Fin n) (AE D))
    (b : hermA D n) :
    Jt ψ V μ φ (pull a b) = npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) *
      Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b := by
  have hr0 : absA D (Matrix.GeneralLinearGroup.det a) ≠ 0 :=
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have key := GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a
    (fun x => φ x * ψ (halfTr (Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V x x) : Mx D n n))))
  have e : ∀ y : Mx D V.rank n, Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1)) : Mx D n n) =
      Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D n n) := by
    intro y
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    have hin : GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1) = adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1 := by
      unfold GlobalTheory.StdUnn.inner
      rw [adj_mul]
      simp only [Matrix.mul_assoc]
    rw [hin]
    show Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y)
    calc Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1))
        = Matrix.trace ((a⁻¹).1 * (b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1)) * (a⁻¹).1) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y * (a.1 * (a⁻¹).1)) := by
          rw [h1]
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y) := by rw [h2, Matrix.mul_one]
  unfold Jt
  simp only [e] at key
  rw [key, ← mul_assoc]
  have : npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) = 1 := by
    unfold npow
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hr0), add_neg_cancel, Complex.cpow_zero]
  rw [this, one_mul]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.ThetaGlue
variable {D : D7} {n : ℕ}

theorem ifrB_eq_meanC (D : D7) (r : ℕ) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (φ : Mx D V.rank r → ℂ) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (β : HermE D r) (hβ : β.1.det ≠ 0) :
    IfrB V ν φ β = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
      (HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) (fun X => φ (tupOf X))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig (HSpace.gram V) X = β.1}) := by
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  rw [hS]
  exact hI

def pullE (a : GL (Fin n) (AE D)) : hermA D n ≃+ hermA D n where
  toFun := pull a
  invFun := pull a⁻¹
  left_inv b := by
    apply Subtype.ext
    show (a⁻¹⁻¹).1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj (a⁻¹⁻¹).1 = b.1
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    rw [inv_inv]
    calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
        = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv b := by
    apply Subtype.ext
    show (a⁻¹).1 * ((a⁻¹⁻¹).1 * b.1 * adj (a⁻¹⁻¹).1) * adj (a⁻¹).1 = b.1
    have h1 : adj a.1 * adj (a⁻¹).1 = 1 := (astar a).inv_val
    have h2 : (a⁻¹).1 * a.1 = 1 := by simp
    rw [inv_inv]
    calc (a⁻¹).1 * (a.1 * b.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * b.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    apply Subtype.ext
    show (a⁻¹).1 * (x.1 + y.1) * adj (a⁻¹).1 = (a⁻¹).1 * x.1 * adj (a⁻¹).1 + (a⁻¹).1 * y.1 * adj (a⁻¹).1
    rw [Matrix.mul_add, Matrix.add_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_pull (a : GL (Fin n) (AE D)) : Continuous (pull a) := by
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const)).subtype_mk _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) (hF : Integrable F lam) : Integrable (fun b => F (pull a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
  haveI := hl
  have hc : Continuous (pullE a) := continuous_pull a
  have hc' : Continuous (pullE a).symm := continuous_pull a⁻¹
  let M : hermA D n ≃ₜ hermA D n := { toEquiv := (pullE a).toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI hH : (lam.map (pullE a)).IsAddHaarMeasure := (pullE a).isAddHaarMeasure_map lam hc hc'
  have e := Measure.isAddLeftInvariant_eq_smul (lam.map (pullE a)) lam
  have h1 : Integrable F (lam.map (pullE a)) := by
    rw [e]
    exact hF.smul_measure ENNReal.coe_ne_top
  have hemb : MeasurableEmbedding (pullE a) := M.measurableEmbedding
  exact hemb.integrable_map_iff.1 h1

end GlobalTheory.CompanionTheory.MM
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM

theorem isPlaces_of_hasRealPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ → HasRealPar ψ θ l → PositivityTheory.SiegelWeilFormula.Gen.IsPlaces D.sp.cm.sig ψ θ l ∧ Nonempty D.what₂.Tau := by
  intro D ψ θ l hψ hθ hl
  refine ⟨⟨fun τ => GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ),
    GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D) (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ,
    fun τ z => GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) z,
    fun τ => GlobalTheory.CompanionTheory.IfrAdd.realPar_ne_zero hψ hθ hl τ, hl⟩, ?_⟩
  exact D.eTau.nonempty_congr.2 inferInstance

end GlobalTheory.CompanionTheory.MM
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.CartFrames

open Matrix
open scoped ComplexOrder

theorem herm_eig {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ * (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 ∧
    (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ = 1 ∧
    A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← Matrix.star_eq_conjTranspose]
    exact h

theorem posDef_factor {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ} (hP : P.PosDef) :
    ∃ B C : Matrix (Fin k) (Fin k) ℂ, Bᴴ * B = P ∧ B * C = 1 ∧ C * B = 1 := by
  obtain ⟨h1, h2, h3⟩ := herm_eig hP.isHermitian
  set U : Matrix (Fin k) (Fin k) ℂ := (hP.isHermitian.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set d := hP.isHermitian.eigenvalues with hd
  have hpos : ∀ i, 0 < d i := hP.eigenvalues_pos
  let r : Fin k → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simpa [r] using (Real.sqrt_pos.2 (hpos i)).ne'
  have hrr : ∀ i, star (r i) * r i = (d i : ℂ) := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
  have hdiag : diagonal r * diagonal (fun i => (r i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hr0 i)
  have hdiag' : diagonal (fun i => (r i)⁻¹) * diagonal r = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hr0 i)
  refine ⟨diagonal r * Uᴴ, U * diagonal (fun i => (r i)⁻¹), ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    calc U * diagonal (star r) * (diagonal r * Uᴴ) = U * (diagonal (star r) * diagonal r) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => (d i : ℂ)) * Uᴴ := by
          rw [diagonal_mul_diagonal]; congr 3; funext i; exact hrr i
      _ = P := h3.symm
  · calc diagonal r * Uᴴ * (U * diagonal fun i => (r i)⁻¹)
        = diagonal r * (Uᴴ * U) * diagonal (fun i => (r i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hdiag]
  · calc U * diagonal (fun i => (r i)⁻¹) * (diagonal r * Uᴴ)
        = U * (diagonal (fun i => (r i)⁻¹) * diagonal r) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdiag', Matrix.mul_one, h2]

theorem exists_frame {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    ∃ (ε : Fin k → Bool) (f : GL (Fin k) ℂ),
      (f.1)ᴴ * G * f.1 = diagonal (PositivityTheory.Rg.Sw.sgn ε) ∧ (f.1)ᴴ * (G * s) * f.1 = 1 := by
  obtain ⟨hss, hiso, hP⟩ := h
  obtain ⟨B, C, hBB, hBC, hCB⟩ := posDef_factor hP

  have hPs : (G * s) * s = G := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  have hsP : sᴴ * (G * s) = G := by rw [← Matrix.mul_assoc]; exact hiso
  have hCtBt : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]

  have hHh : (B * s * C).IsHermitian := by
    have e : (B * s * C)ᴴ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by
      rw [conjTranspose_mul, conjTranspose_mul]
      calc Cᴴ * (sᴴ * Bᴴ) = Cᴴ * (sᴴ * Bᴴ) * (B * C) := by rw [hBC, Matrix.mul_one]
        _ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by simp only [Matrix.mul_assoc]
    show (B * s * C)ᴴ = B * s * C
    rw [e, hBB, hsP, ← hPs, ← hBB]
    calc Cᴴ * (Bᴴ * B * s) * C = (Cᴴ * Bᴴ) * (B * s * C) := by simp only [Matrix.mul_assoc]
      _ = B * s * C := by rw [hCtBt, Matrix.one_mul]
  have hHH : (B * s * C) * (B * s * C) = 1 := by
    calc (B * s * C) * (B * s * C) = B * s * (C * B) * s * C := by simp only [Matrix.mul_assoc]
      _ = B * (s * s) * C := by rw [hCB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hss, Matrix.mul_one, hBC]
  obtain ⟨h1, h2, h3⟩ := herm_eig hHh
  set V : Matrix (Fin k) (Fin k) ℂ := (hHh.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hV
  set l := hHh.eigenvalues with hl
  set H := B * s * C with hH

  have hHV : H * V = V * diagonal (fun i => (l i : ℂ)) := by
    conv_lhs => rw [h3]
    calc V * diagonal (fun i => (l i : ℂ)) * Vᴴ * V = V * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

  have hsq : diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ)) = 1 := by
    calc diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ))
        = (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) := by
          rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (l i : ℂ)) * Vᴴ) * (V * diagonal (fun i => (l i : ℂ))) := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * H * (H * V) := by rw [← h3, hHV]
      _ = Vᴴ * (H * H) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, h1]
  have hl2 : ∀ i, l i = 1 ∨ l i = -1 := fun i => by
    have e := congrFun (congrFun hsq i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, Matrix.one_apply_eq] at e
    have e' : l i * l i = 1 := by exact_mod_cast e
    exact mul_self_eq_one_iff.mp e'
  have hsgn : PositivityTheory.Rg.Sw.sgn (fun i => decide (0 < l i)) = fun i => (l i : ℂ) := by
    funext i
    rcases hl2 i with e | e <;> simp [PositivityTheory.Rg.Sw.sgn, e]
  let f : GL (Fin k) ℂ := ⟨C * V, Vᴴ * B, by
    calc C * V * (Vᴴ * B) = C * (V * Vᴴ) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hCB], by
    calc Vᴴ * B * (C * V) = Vᴴ * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, Matrix.mul_one, h1]⟩
  have hf : f.1 = C * V := rfl
  have hfP : (f.1)ᴴ * (G * s) * f.1 = 1 := by
    rw [hf, conjTranspose_mul, ← hBB]
    calc Vᴴ * Cᴴ * (Bᴴ * B) * (C * V) = Vᴴ * (Cᴴ * Bᴴ) * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCtBt, hBC, Matrix.mul_one, Matrix.mul_one, h1]
  have hsf : s * f.1 = f.1 * diagonal (fun i => (l i : ℂ)) := by
    rw [hf]
    calc s * (C * V) = (C * B) * s * C * V := by rw [hCB, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = C * (H * V) := by rw [hH]; simp only [Matrix.mul_assoc]
      _ = C * V * diagonal (fun i => (l i : ℂ)) := by rw [hHV, Matrix.mul_assoc]
  refine ⟨fun i => decide (0 < l i), f, ?_, hfP⟩
  rw [hsgn]
  calc (f.1)ᴴ * G * f.1 = (f.1)ᴴ * ((G * s) * s) * f.1 := by rw [hPs]
    _ = (f.1)ᴴ * (G * s) * (s * f.1) := by simp only [Matrix.mul_assoc]
    _ = ((f.1)ᴴ * (G * s) * f.1) * diagonal (fun i => (l i : ℂ)) := by
        rw [hsf]; simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => (l i : ℂ)) := by rw [hfP, Matrix.one_mul]

theorem exists_frames : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ), PositivityTheory.SiegelWeilFormula.Gen.IsFrames (HSpace.gram V) θ ε fr ∧ ∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1 := by
  intro D V θ s hθ hs
  choose ε fr h1 h2 using fun τ => exists_frame (hs τ)
  refine ⟨ε, fr, fun τ => ?_, h2⟩
  have e : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) (HSpace.gram V)).map (θ τ) = gramAt D V τ := by
    ext a b
    exact (hθ τ).1 _
  rw [e]
  exact h1 τ

end GlobalTheory.CompanionTheory.CartFrames
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PfSWUS.MonoSplit

theorem main : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ) (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (c : ℂ), Nonempty D.what₂.Tau → (∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1) → ∃ P : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ, evalPoly (MvPolynomial.monomial e c) z * gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.evX (P τ) (((fr τ)⁻¹).1 * z τ) * PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
  classical
  intro D n V l s fr e c hne hfr
  obtain ⟨τ0⟩ := hne
  obtain ⟨PG, hPG⟩ : ∃ PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ τ,
      PG τ = MvPolynomial.C (if τ = τ0 then c else 1) *
        ∏ k ∈ e.support, (if k.1 = τ then PositivityTheory.PfSWUS.SwSpanR.lz (fr τ).1 k.2 else 1) ^ (e k) :=
    ⟨_, fun τ => rfl⟩
  refine ⟨PG, fun z => ?_⟩
  have hinv : ∀ τ, (fr τ).1 * ((fr τ)⁻¹).1 = 1 := fun τ => Units.mul_inv (fr τ)
  have hZ : ∀ τ, (fr τ).1 * (((fr τ)⁻¹).1 * z τ) = z τ := fun τ => by
    rw [← Matrix.mul_assoc, hinv τ, Matrix.one_mul]

  have hG : gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
    unfold gauss PositivityTheory.Rg.Sw.gs
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [PositivityTheory.PfSWUS.SwSpanR.trace_frame (fr τ).1 ((fr τ)⁻¹).1 _ _ (hinv τ) (hfr τ),
      PositivityTheory.PfSWUS.SwSpanR.trace_ct_mul_self]
    push_cast
    ring

  have hP : evalPoly (MvPolynomial.monomial e c) z =
      ∏ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) := by
    set f : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℂ := fun k =>
      if k.2.2.2 then (starRingEnd ℂ) (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 with hf
    have hτ : ∀ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) =
        (if τ = τ0 then c else 1) * ∏ k ∈ e.support, (if k.1 = τ then f k else 1) ^ (e k) := fun τ => by
      rw [hPG τ]
      simp only [PositivityTheory.Rg.Sw.evX, map_mul, MvPolynomial.eval_C, map_prod, map_pow]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases h : k.1 = τ
      · subst h
        rw [if_pos rfl, if_pos rfl]
        have := PositivityTheory.PfSWUS.SwSpanR.evX_lz (fr k.1).1 (((fr k.1)⁻¹).1 * z k.1) k.2
        unfold PositivityTheory.Rg.Sw.evX at this
        rw [this, hZ k.1, hf]
        simp only [starRingEnd_apply]
      · rw [if_neg h, if_neg h, map_one]
    simp only [hτ]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ τ0, if_pos (Finset.mem_univ _),
      Finset.prod_comm]
    unfold evalPoly
    rw [MvPolynomial.eval_monomial]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [ite_pow, one_pow]
    rw [Finset.prod_ite_eq Finset.univ k.1, if_pos (Finset.mem_univ _)]
    simp only [hf, ite_pow]
  rw [hP, hG, ← Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PfSWUS.MonoSplit
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LatStd

open NumberField IsDedekindDomain Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem map_comp_apply_evalV (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
        (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp; rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem eventually_matV_mem_intLoc {n : ℕ} (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a c, PositivityTheory.SiegelWeilFormula.Gen.matV v h a c ∈ intLoc F E v :=
  eventually_all.2 fun a => eventually_all.2 fun c => by
    filter_upwards [eventually_map_evalV_mem_intLoc
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (h a c))] with v hv
    change Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) (h a c) ∈ _
    rw [map_comp_apply_evalV]
    exact hv

omit [NumberField E] in

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    (hh : h * h' = 1) : PositivityTheory.SiegelWeilFormula.Gen.matV v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  have e := map_mul (AlgHom.mapMatrix (m := Fin n) (Algebra.TensorProduct.map
    ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E))) h h'
  rw [hh, map_one] at e
  exact e.symm

omit [NumberField E] in

theorem mulVec_mem_intLoc {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {M : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)}
    (hM : ∀ a c, M a c ∈ intLoc F E v) {x : Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : ∀ c, x c ∈ intLoc F E v)
    (a : Fin n) : M.mulVec x a ∈ intLoc F E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun c _ => mul_mem (hM a c) (hx c)

theorem eventually_map_latLoc_eq_latO {n d : ℕ} {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} (hh : h * h' = 1)
    (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      (((latLoc F (stdLattice E n) v).toAddSubgroup.map
        (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v h)).toAddMonoidHom : AddSubgroup _) :
          Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  filter_upwards [GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr bs, eventually_matV_mem_intLoc h,
    eventually_matV_mem_intLoc h'] with v hb h1 h2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := mem_latLoc_stdLattice.1 hx
    intro a k
    refine (hb _).1 ?_ k
    exact mulVec_mem_intLoc h1 hx' a
  · intro hy
    have hy' : ∀ a, y a ∈ intLoc F E v := fun a => (hb _).2 (hy a)
    refine ⟨(PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y,
      mem_latLoc_stdLattice.2 (mulVec_mem_intLoc h2 hy'), ?_⟩
    change (PositivityTheory.SiegelWeilFormula.Gen.matV v h).mulVec ((PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y) = y
    rw [Matrix.mulVec_mulVec, matV_mul_eq_one v hh, Matrix.one_mulVec]

theorem latAt_eq_latO : ∀ (D : D7) (n : ℕ) (h : GL (Fin n) (AE D)) (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E), ∀ᶠ v in Filter.cofinite, ((latAt h.1 v : AddSubgroup _) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  intro D n h d bs
  have hh : h.1 * (h⁻¹).1 = 1 := by simp
  exact eventually_map_latLoc_eq_latO hh bs

end GlobalTheory.CompanionTheory.MM.LatStd
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PureTwist

open IsDedekindDomain

def twistT {A : Type} [CommRing A] {n M : ℕ} (m : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    Fin n → Fin M → A :=
  fun j i => ∑ k, Y k i * m k j

theorem twistT_twistT {A : Type} [CommRing A] {n M : ℕ} {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1)
    (Y : Fin n → Fin M → A) : twistT m' (twistT m Y) = Y := by
  funext j i
  simp only [twistT, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hm : ∀ k, ∑ l, m k l * m' l j = (1 : Matrix (Fin n) (Fin n) A) k j := fun k => by
    rw [← h, Matrix.mul_apply]
  simp [hm, Matrix.one_apply]

def twistH {A : Type} [CommRing A] [TopologicalSpace A] [ContinuousMul A] [ContinuousAdd A] {n M : ℕ}
    {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1) (h' : m' * m = 1) :
    (Fin n → Fin M → A) ≃ₜ (Fin n → Fin M → A) where
  toFun := twistT m
  invFun := twistT m'
  left_inv := twistT_twistT h
  right_inv := twistT_twistT h'
  continuous_toFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const
  continuous_invFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

def intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

theorem repr_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x ⊗ₜ[F] e) k = x * algebraMap F R (b.repr e k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    x = ∑ k, (Algebra.TensorProduct.basis R b).repr x k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem eventually_adele (t : HeckeCharacterZeroLocus.SiegelWeilU.Af F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v t ∈ v.adicCompletionIntegers F := by
  exact t.2

theorem eventually_const (c : F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F := by
  filter_upwards [eventually_adele (F := F) (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Af F) c)] with v hv
  rwa [AlgHom.commutes] at hv

theorem sum_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {ι : Type} (s : Finset ι) (f : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ intE b v) :
    ∑ i ∈ s, f i ∈ intE b v := by
  intro k
  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => h i hi k

theorem mul_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {x y : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : x ∈ intE b v) (hy : y ∈ intE b v) : x * y ∈ intE b v := by
  simp only [intE, Set.mem_ofPred_eq] at hx hy ⊢
  intro k
  rw [eq_sum_tmul b x, eq_sum_tmul b y, Finset.sum_mul_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum, Finsupp.finsetSum_apply, repr_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  exact mul_mem (mul_mem (hx i) (hy j)) (hc i j k)

theorem eventually_mul_closed (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j k
  exact eventually_const _

theorem eventually_mem_intE (b : Module.Basis (Fin d) F E) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) x ∈ intE b v := by
  have hall : ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ k,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (HeckeCharacterZeroLocus.SiegelWeilU.sndA F
        ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr x k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun k => eventually_adele _
  filter_upwards [hall] with v hv
  rw [eq_sum_tmul b x]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
  refine sum_mem_intE b v _ _ fun k _ => ?_
  intro k'
  rw [repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with hk
  · subst hk
    rw [map_one, mul_one]
    exact hv _
  · rw [map_zero, mul_zero]
    exact zero_mem _

theorem eventually_matV_mem (b : Module.Basis (Fin d) F E) {n : ℕ}
    (h : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k j, PositivityTheory.SiegelWeilFormula.Gen.matV v h k j ∈ intE b v := by
  simp only [Filter.eventually_all]
  intro k j
  filter_upwards [eventually_mem_intE b (h k j)] with v hv
  simpa [PositivityTheory.SiegelWeilFormula.Gen.matV] using hv

theorem twistT_mem_latV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {n M : ℕ} {m : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)} (hm : ∀ k j, m k j ∈ intE b v)
    {Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    twistT m Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v := by
  intro a i
  exact sum_mem_intE b v _ _ fun k _ => mul_mem_intE b v hc (hY k i) (hm k a)

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {h h' : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)} (e : h * h' = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.matV (E := E) v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  simp only [PositivityTheory.SiegelWeilFormula.Gen.matV]
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, e, map_one]

end Int

theorem map_evalV_finPart (D : D7) (v : HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (x : AE D) :
    Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D x) =
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
        (AlgHom.id D.host.F D.host.E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem isPureFin_twist : ∀ (D : D7) (n M d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E) (g : (Fin M → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ) (a : GL (Fin n) (AE D)), HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv → HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j)) (fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j)) := by
  intro D n M d bs g gv a H
  obtain ⟨hSB, hev, hprod⟩ := H
  have e1 : a.1 * a⁻¹.1 = 1 := a.mul_inv
  have e2 : a⁻¹.1 * a.1 = 1 := a.inv_mul
  refine ⟨fun v => ?_, ?_, fun Y => ?_⟩
  · let T := twistH (M := M) (matV_mul_eq_one v e1) (matV_mul_eq_one v e2)
    obtain ⟨hlc, hcs⟩ := hSB v
    exact ⟨hlc.comp_continuous T.continuous, hcs.comp_homeomorph T⟩
  · filter_upwards [hev, eventually_mul_closed bs, eventually_matV_mem bs a.1,
      eventually_matV_mem bs a⁻¹.1] with v hv hc hm hm'
    funext Y
    rw [hv]
    show (HeckeCharacterZeroLocus.SiegelWeilU.latV bs v).indicator 1 (twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y) = _
    have hiff : twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v ↔
        Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v := by
      constructor
      · intro hY
        have h1 := twistT_mem_latV bs v hc hm' hY
        rwa [twistT_twistT (matV_mul_eq_one v e1)] at h1
      · exact twistT_mem_latV bs v hc hm
    by_cases hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v
    · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hiff.mpr hY)]
      simp only [Pi.one_apply]
    · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hiff.mp hY)]
  · have h3 := hprod (fun j i => ∑ k, Y k i * finPart D (a.1 k j))
    dsimp only at h3 ⊢
    rw [h3]
    refine finprod_congr fun v => ?_
    congr 1
    funext j i
    simp [HeckeCharacterZeroLocus.SiegelWeilU.projV, PositivityTheory.SiegelWeilFormula.Gen.matV, map_evalV_finPart]

end GlobalTheory.CompanionTheory.PureTwist
end
end

section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.LocHaar

theorem exists_addHaar_tens (D : D7) (n : ℕ) :
    ∃ lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      ∀ v, (lamG v).IsAddHaarMeasure := by
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      ∃ μ : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
        μ.IsAddHaarMeasure := by
    intro v
    obtain ⟨tr, lc, sc, t2, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v
    obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.G5.tens_facts (F := D.host.F) (E := D.host.E)
      (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.deg2
    exact ⟨Measure.addHaar, inferInstance⟩
  choose lamG h using key
  exact ⟨lamG, h⟩

end GlobalTheory.CompanionTheory.LocHaar
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip
variable {D : D7} {n : ℕ}

theorem integral_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) :
    ∫ b, F b ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, F (pull a b) ∂lam := by
  have key := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a (fun c => F (pull a c))
  have e : ∀ c : hermA D n, pull a (cg a c) = c := fun c => Subtype.ext (by
    show (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1 = c.1
    have h1 : (a⁻¹).1 * a.1 = 1 := by simp
    calc (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * c.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = c.1 := by rw [h1, adj_mul_adj_inv, Matrix.one_mul, Matrix.mul_one])
  simp only [e] at key
  exact key

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matchMono : PositivityTheory.PfSWUS.MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hCD w hw β hβ a k hk φ hφ
  obtain ⟨hpl, hne⟩ := GlobalTheory.CompanionTheory.MM.isPlaces_of_hasRealPar D ψ θ l hS.hψ hS.hθ hS.hl
  obtain ⟨ε, fr, hfr, hfr1⟩ := GlobalTheory.CompanionTheory.CartFrames.exists_frames D V θ s hS.hθ hS.hs
  obtain ⟨hfock, hsch⟩ := mono_mem D n V θ l s φ hS.hθ hpl.ne hS.hs hφ
  obtain ⟨lamG, hlamG⟩ := GlobalTheory.CompanionTheory.LocHaar.exists_addHaar_tens D n
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφe⟩ := hφ
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.PfSWUS.MonoSplit.main D n V l s fr e c hne hfr1
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hT : ∀ x y, D.sp.cm.sig (β.1 y x) = β.1 x y := fun x y => by
    have := congrFun (congrFun β.2 x) y
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨hnb, hlam⟩ := hCD
  haveI : lam.IsAddHaarMeasure := hlam.1
  refine ⟨d, bs, θ, l, ε, fr, gAt θ a, P, lamG, latAt a.1, latAt (adj (a⁻¹).1),
    fun X => φ (HMul.hMul (tupOf X) a.1), fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j),
    fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j),
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ⟨(n : ℝ) / 2, ?_⟩, ?_⟩
  · refine
      { cm := hcm, herm := hJ, lt := hR.1, hT := hT, det := hβ, chr := hS.hψ, places := hpl, frames := hfr, haar := hlamG,
        co := fun v => ⟨GlobalTheory.CompanionTheory.MM.latAt_isCO D n a v, ?_⟩, std := ?_, pure := GlobalTheory.CompanionTheory.PureTwist.isPureFin_twist D n V.rank d bs g gv a hpure, prod := ?_,
        sdW := sdW_map V hS.hψ hμ, sdH := sdHerm_map hS.hψ hlam }
    · exact GlobalTheory.CompanionTheory.MM.latAt_isCO D n (astar a) v
    · filter_upwards [GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n a d bs, GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n (astar a) d bs] with v h1 h2
      exact ⟨h1, h2⟩
    · intro X
      have hcomp : ∀ τ, compAt θ τ (HMul.hMul (tupOf X) a.1 : Mx D V.rank n) =
          Matrix.of (fun i j => θ τ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j i)) * (gAt θ a τ).1 := by
        intro τ
        ext i j
        simp only [compAt, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
        rfl
      have hfin : (fun i j => finPart D ((HMul.hMul (tupOf X) a.1 : Mx D V.rank n) i j)) =
          fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j) := by
        funext i j
        simp only [Matrix.mul_apply, map_sum, map_mul]
        rfl
      show φ (HMul.hMul (tupOf X) a.1) = PositivityTheory.SiegelWeilFormula.Gen.phiInf θ l fr (gAt θ a) P (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
        (g fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j))
      rw [hφe]
      simp only []
      rw [hP, hfin]
      congr 1
      unfold PositivityTheory.SiegelWeilFormula.Gen.phiInf PositivityTheory.SiegelWeilFormula.Gen.crd
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hcomp τ, Matrix.mul_assoc]
  · intro z hz
    obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
    haveI : IsTopologicalAddGroup (Mx D n n) := i1
    haveI : SecondCountableTopology (Mx D n n) := i3
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
    haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    set r := absA D (Matrix.GeneralLinearGroup.det a) with hr
    have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
    have hS' : Std D n V ψ χ θ μ ω H l s ν (⟨φ, hsch⟩ : schwartzA θ V.rank n) := { hS with hΦ := hfock }
    have hF0 : Integrable (fun b : hermA D n => sect ω H (⟨φ, hsch⟩ : schwartzA θ V.rank n) z (w * nb b * 1)) lam :=
      (PositivityTheory.PfSWUS.HUnfold.unfold D n V ψ χ θ μ ω H l s ν _ hS' hR nb lam 𝓖 ⟨hnb, hlam⟩ w hw β hβ z hz 1).1
    have hF : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam :=
      hF0.congr (Filter.Eventually.of_forall fun b => sect_w D n V ψ χ θ μ ω H hS.hω nb hnb w hw ⟨φ, hsch⟩ z b)
    have hFp := integrable_pull D n lam hlam.1 a _ hF
    have hch : Continuous fun b : hermA D n =>
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      have h := continuous_chi hS.hψ (-(β.1.map (incA D)))
      exact h.congr fun b => chi_neg_left ψ _ b
    have hcn : ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 :=
      fun b => hS.hψ.2.1 _
    have hrm : npow r (V.rank : ℂ) ≠ 0 := by
      unfold npow
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hr0 (by exact_mod_cast h.1)

    have hR1 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
        Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) lam := by
      have h1 : Integrable (fun b : hermA D n => (npow r (V.rank : ℂ))⁻¹ *
          (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b))) lam := hFp.const_mul _
      have h2 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b) lam := by
        refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
        show (npow r (V.rank : ℂ))⁻¹ * (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b)) = _
        rw [jt_pull D n V ψ μ 𝓕 hμ φ a b, ← hr, mul_left_comm (npow (H (w * nb (pull a b))) (z - s0 V n)),
          inv_mul_cancel_left₀ hrm]
      refine h2.mono (h2.aestronglyMeasurable.mul hch.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun b => ?_)
      rw [norm_mul, hcn, mul_one]
    have hwhI : ∀ b : hermA D n,
        PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1))
          (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)))
          (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z (hermTo b) =
        npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
          ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      intro b
      unfold PositivityTheory.SiegelWeilFormula.Gen.whI
      have e1 := GlobalTheory.T.local_haar_lattice_unipotent_integral D n θ hS.hθ H hS.hH nb hnb w hw a lamG hlamG b
      have e2 := jtR_hermTo V ψ μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b
      have e3 : (z - ((V.rank : ℂ) - n) / 2) = z - s0 V n := by
        unfold s0
        ring
      show ((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 : ℝ) : ℂ) ^
          (-(z - ((V.rank : ℂ) - n) / 2)) * _ * _ = _
      rw [e1, e3, npow_inv, e2]
      rfl
    let Mh : hermA D n ≃ₜ HermR (AF D.host.F) D.sp.cm.sig n :=
      { toEquiv := ⟨hermTo, hermFrom, hermFrom_hermTo, hermTo_hermFrom⟩
        continuous_toFun := continuous_hermTo
        continuous_invFun := continuous_hermFrom }
    have hemb : MeasurableEmbedding (hermTo (D := D) (r := n)) := Mh.measurableEmbedding
    constructor
    · exact hemb.integrable_map_iff.2 (hR1.congr (Filter.Eventually.of_forall fun b => (hwhI b).symm))
    · refine Eq.trans ?_ (congrArg (fun t => npow r ((V.rank : ℂ) - n) * t)
        (integral_map_of (hermTo (D := D) (r := n)) hermFrom hermFrom_hermTo hermTo_hermFrom hermTo_add continuous_hermTo
        continuous_hermFrom lam _)).symm
      beta_reduce
      rw [integral_congr_ae (Filter.Eventually.of_forall fun b => hwhI b)]
      show ∫ b, npow (H (w * nb b * k)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) b.1 : Mx D n n))) ∂lam = _
      rw [integral_pull D n lam hlam.1 a]
      have hcong : ∀ b : hermA D n, npow (H (w * nb (pull a b) * k)) (z - s0 V n) * Jt ψ V μ φ (pull a b) *
          ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) (pull a b).1 : Mx D n n))) =
          npow r (V.rank : ℂ) * (npow (H (w * nb (pull a b))) (z - s0 V n) *
            Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
            ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) := by
        intro b
        rw [GlobalTheory.CompanionTheory.PfSWUS.height_mul_K hS.hH _ hk, jt_pull D n V ψ μ 𝓕 hμ φ a b, trace_pull, ← hr]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hcong), integral_const_mul, ← mul_assoc]
      congr 1
      rw [sub_eq_add_neg, npow_add_of r hr0, mul_comm]
  · intro μH 𝓕H hμH hF
    exact congrArg (fun t => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) * t)
      (ifrB_eq_meanC D n V ν hS.hν _ μH 𝓕H hμH hF β hβ)
end GlobalTheory.CompanionTheory.MM
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_monomial : PositivityTheory.PfSWUS.MatchMono := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MM.matchMono
end
end
