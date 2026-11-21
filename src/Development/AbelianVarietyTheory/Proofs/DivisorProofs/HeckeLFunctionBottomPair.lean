import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeVacuumReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIteratedQuotientIntegralFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsParamVecOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  atlas_forward_decl GlobalTheory.NormRatio.exists_ipPair_one
end

section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes : ∀ {D : D7} (V : HSp D) (n : ℕ) (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n), V.gram = 1 → V.rank = n → GlobalTheory.BotFormula.IsFinPt V g x →
  IsSelfDualC V (stdLat V) ∧ (x ∈ intG D n ↔ g ∈ openOff V (stdLat V) ∅) := by
  first | exact @GlobalTheory.NormRatio.selfDual_and_mem_intG_iff | exact GlobalTheory.NormRatio.selfDual_and_mem_intG_iff | (intros; apply GlobalTheory.NormRatio.selfDual_and_mem_intG_iff <;> assumption)
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section
namespace GlobalTheory.RatioConst

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont Formalism.L2.Pj in

theorem rcoef_one_const {D : D7} {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    GlobalTheory.Core.Rk.IP.rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]

theorem integral_const_coef : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  intro D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0
  have hF := hX.1
  haveI := hF.haarA
  set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef
  have hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k := by
    intro g
    obtain ⟨h, hh, k, hk, rfl⟩ := Formalism.IndefR.TopMult.ga_decomp g
    rw [← hF.rangeA] at hh
    obtain ⟨x, rfl⟩ := hh
    exact ⟨x, k, hk, rfl⟩
  have hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1 := by
    intro k hk v
    show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1
    rw [← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]
    exact GlobalTheory.AdelicU.proj_ofInf _ _ v _
  have hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1 := by
    intro k hk
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom X.A k = 1 from hk, map_one]
  have hmem : ∀ x k S, k ∈ GinfC X.A →
      (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S) := by
    intro x k S hk
    simp only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]
  have hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    by_cases hx : x ∈ intG D P.a
    · rw [Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]
    · rw [Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))),
        h0 x hx ((hmem x k Sf hk).1 hg) k hk]
  have hKsub : K ⊆ openOff X.A (stdLat X.A) Sf := fun g hg v _ => hg v (Finset.notMem_empty v)
  have hKm : MeasurableSet K := (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet
  have hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet
  have hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A)) := by
    ext g
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]
  have hKvol : X.m K = 1 := by
    rw [hKeq]; exact GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1
  have hKc : IsCompact K := by
    have hG : IsCompact (GinfC X.A : Set (GA D X.A)) :=
      GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA
    refine (hF.levA.2.mul hG).of_isClosed_subset ?_ ?_
    · rw [hKeq]; exact Subgroup.isClosed_of_isOpen _ hF.levA.1
    · intro g hg
      obtain ⟨x, k, hk, rfl⟩ := hdec g
      rw [hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one] at hg
      refine Set.mul_mem_mul ?_ hk
      exact Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩
  obtain ⟨hcont, hpos, -⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha
  refine ⟨fun s => ?_, ?_⟩
  · let F : GA D X.A → ℂ := fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g)
        (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)
    have hFc : Continuous F := by
      refine (continuous_const.mul ?_).mul continuous_const
      simp only [GlobalTheory.Doubling.npow]
      refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_
      exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)
    have hI : Integrable (K.indicator F) X.m :=
      (integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)
    refine hI.integrableOn.congr_fun (fun g hg => ?_) hSm
    have hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ) := by
      exact rcoef_one_const X.m g
    simp only [integrand, hr, hw g hg]
    by_cases hgK : g ∈ K
    · simp [Set.indicator_of_mem hgK, F]
    · simp [Set.indicator_of_notMem hgK]
  · rw [setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]
    simp

end GlobalTheory.RatioConst
end
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  atlas_forward_decl GlobalTheory.RatioConst.integral_const_coef
end

section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_spherical_off_modulus : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
    IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf φ := by
  first | exact @GlobalTheory.NormRatio.SphCoset.sph | exact GlobalTheory.NormRatio.SphCoset.sph | (intros; apply GlobalTheory.NormRatio.SphCoset.sph <;> assumption)
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.SphMove

theorem isSphOff_om : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  intro D ψ A B χA χB om hW LA LB hA hB Sf g hg f hf hsph
  have hmv : GlobalTheory.FinPl.Moves A g LA LA (fun v => v ∉ Sf) :=
    (GlobalTheory.QLawPf.moves_iff_forall hA _ g).2 fun v hv =>
      (GlobalTheory.StMoves.moves_iff_stabLoc A LA hA.1.fg v g).2 (hg v hv)
  have hmi : GlobalTheory.FinPl.Moves A g⁻¹ LA LA (fun v => v ∉ Sf) := GlobalTheory.StMoves.moves_inv hmv
  have hm1 : GlobalTheory.FinPl.Moves B (1 : GA D B)⁻¹ LB LB (fun v => v ∉ Sf) := by
    intro y _
    rw [inv_one, show mt B (1 : GA D B) = 1 from rfl, Matrix.one_mulVec]
  have key : ∀ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf),
      actO A B g⁻¹ (1 : GA D B)⁻¹ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf) :=
    fun u hu => GlobalTheory.MidVacLat.actO_mem_latO hA hA hB hB hmi hm1 hu
  have step : ∀ w, heisO ψ A B (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f = f →
      heisO ψ A B w (om (g, 1) f) = om (g, 1) f := by
    intro w hw
    have h := hW.om_heis g 1 (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f hf
    rw [hw, GlobalTheory.MidVacLat.actO_actO_inv] at h
    exact h.symm
  refine ⟨fun u hu => step _ ?_, fun e he u hu hh => step _ ?_⟩
  · rw [GlobalTheory.MidVacLat.actO_two_nsmul]
    exact hsph.1 _ (key u hu)
  · exact hsph.2 e he _ (key u hu) (GlobalTheory.MidVacLat.isHalf_actO _ _ hh)

end GlobalTheory.SphMove
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  atlas_forward_decl GlobalTheory.SphMove.isSphOff_om
end

section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) (ν : Formalism.L2.Host.HChar D.host.E),
  IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) → ChrEq χ ν := by
  first | exact @GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | exact GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | (intros; apply GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.Core.Rk.TrivCoef
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NuOffPair

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  intro D T L sc μ₀ hL hF G t i j χ hχ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ sfB G t → (nuH G t i j).UnrAt w := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw (GlobalTheory.BottomIPData.mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
    have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
      hw (e ▸ GlobalTheory.BottomIPData.under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
    have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hv
    have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hv (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt w := by
      by_contra hn
      rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
      · exact hQ w hq rfl
      · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
    rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv
  have hram : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ sfB G t → ¬ (nuH G t i j).UnrAt w := by
    intro w hw
    by_cases h0 : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · exact GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j w h0
    · unfold GlobalTheory.BottomIPData.sfB at hw
      obtain ⟨P, hP, hPw⟩ := Finset.mem_image.1 hw
      have hP' : P ∈ L.Q t := by
        unfold locPl GlobalTheory.ChiGrid.Places.W0 at hP
        rcases Finset.mem_union.1 hP with h | h
        · exfalso
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
          apply h0
          rw [← hPw, G.pl.under_w hv]
          exact hv
        · exact h
      have := GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w P hP' hPw h0
      have e0 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
        mul_div_mul_right_eq_div _ _ _
      rwa [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)] at this
  refine ⟨fun w hw => (GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w).2 (hunr w ?_), fun Λ hΛ s => ?_⟩
  · exact hw
  have hT : GlobalTheory.CMVal.TrivOnF (nuH G t i j) := by
    have h := ((L.C.isMu0 j).triv.mul (hL.xi_triv t)).mul (G.ch.triv _ hm.1 hm.2).inv
    rw [nuH, div_eq_mul_inv]
    exact h
  have hu : ∀ w, GlobalTheory.LFun.UnrAt χ⁻¹ w ↔ (nuH G t i j)⁻¹.UnrAt w := fun w => by
    rw [GlobalTheory.UnrCharZeta.unrAt_inv, ← GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w]
    exact ⟨fun h => inv_inv χ ▸ h.inv, fun h => h.inv⟩
  have hfam : GlobalTheory.LFun.charFam χ⁻¹ = GlobalTheory.LFun.heckeFam (nuH G t i j)⁻¹ := funext fun w => by
    by_cases h : (nuH G t i j)⁻¹.UnrAt w
    · rw [GlobalTheory.LFun.heckeFam_of_unrAt h, GlobalTheory.LFun.charFam, if_pos ((hu w).2 h), GlobalTheory.LFun.val_inv,
        GlobalTheory.LFun.val_eq_of_chrEq hχ, GlobalTheory.UnrCharZeta.val_inv]
    · rw [GlobalTheory.LFun.heckeFam_of_not_unrAt h, GlobalTheory.LFun.charFam, if_neg (mt (hu w).1 h)]
  have hΛ' := GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF D.host.E (nuH G t i j) Λ hT hΛ
  have hr' : ∀ w ∈ GlobalTheory.LFun.above D.host.E ((sfB G t : Finset (FinPl D)) : Set (FinPl D)),
      ¬ (nuH G t i j)⁻¹.UnrAt w := fun w hw h =>
    hram w hw ((GlobalTheory.UnrCharZeta.unrAt_inv _ w).1 h)
  have heq : GlobalTheory.Cont.EqRight Λ (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) := ⟨1, fun z hz => by
    change Λ z = GlobalTheory.LFun.eulerProd _ (GlobalTheory.LFun.charFam χ⁻¹) z
    rw [hfam]
    exact (GlobalTheory.SqStep.heckeL_eq_of_ram hr' hΛ' hz).symm⟩
  exact (GlobalTheory.Cont.holValueAt_self (σ := s.re - 1) (fun z _ => hΛ.1.analyticAt z) (by linarith)).congr heq

end GlobalTheory.NuOffPair
end
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  atlas_forward_decl GlobalTheory.NuOffPair.main
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.CosetNorm

open Formalism.MainNotions.TaylorLogMetric (VC tor0 La Iop U al YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt La0 Wd wdPh Crv)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := by
  have e : symplO S T x y + symplOH S T y x = symplOH S T x y := by
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
    unfold symplOH
    rw [GlobalTheory.OrientedHeis.symplO_skew x y]
    linear_combination (-symplO S T x y) * h2
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, e, add_comm]

theorem heisO_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_heisO_eq_zero {ΛS : Lat S} {ΛT : Lat T} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {u u' : WO S T}
    (hu : u.map (infPart D) = 0) (hu' : u'.map (infPart D) = 0) (hn : u - u' ∉ latO S T ΛS ΛT fun _ => True) :
    GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f) = 0 := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have h0 : (u - u').map (infPart D) = 0 := by
    funext i j
    have a : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    have b : infPart D (u' i j) = 0 := congrFun (congrFun hu' i) j
    show infPart D (u i j - u' i j) = 0
    rw [RingHom.map_sub, a, b, sub_self]
  rw [h1 _ h0] at hn
  push_neg at hn
  obtain ⟨l, hl, hne⟩ := hn
  obtain ⟨ε, hε, hεf⟩ := h3 f hv l hl
  have t1 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu
  have t2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu'
  have e := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 t1 t2 l
  rw [heisO_comm l u, heisO_comm l u', hεf f hv, heisO_smul, heisO_smul, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left,
    GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right] at e
  have hεε : ε * starRingEnd ℂ ε = 1 := by rcases hε with rfl | rfl <;> simp
  have n1 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplO S T l u'))
  have e2 : ψ (symplO S T (u - u') l) * ψ (symplO S T l u) = ψ (symplO S T l u') := by
    rw [← AddChar.map_add_eq_mul, GlobalTheory.OrientedHeis.symplO_skew u l, GlobalTheory.OrientedHeis.symplO_skew u' l]
    congr 1
    have : symplO S T (u - u' + u') l = symplO S T (u - u') l + symplO S T u' l := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]
    rw [sub_add_cancel] at this
    linear_combination -this
  refine (mul_eq_zero.1 (?_ : (ψ (symplO S T (u - u') l) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hne)
  set I := GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f)
  set A := ψ (symplO S T (u - u') l)
  set B := ψ (symplO S T l u)
  set C := ψ (symplO S T l u')
  linear_combination (-A) * e + (ε * starRingEnd ℂ C * starRingEnd ℂ ε * I) * e2 +
    (C * starRingEnd ℂ C * I) * hεε + I * n1

theorem ip_sum (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (h : ι → WO S T → ℂ) (c : ℂ) (ht : ∀ i, IsThetaFunO ψ S T (h i))
    (ha : ∀ i, a i * starRingEnd ℂ (a i) = 1)
    (ho : ∀ i j, i ≠ j → GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) = 0) (hc : ∀ i, GlobalTheory.Ker.ipO μ 𝓕 (h i) (h i) = c) :
    GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) = s.card * c := by
  have e : ∀ w, (∑ i ∈ s, a i • h i) w * starRingEnd ℂ ((∑ i ∈ s, a i • h i) w) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w)) := fun w => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hi : ∀ i j, Integrable (fun w => (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w))) (μ.restrict 𝓕) :=
    fun i j => Integrable.const_mul (GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (ht i) (ht j)) _
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) := by
    unfold GlobalTheory.Ker.ipO
    simp only [e]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e2, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hj => by rw [ho i j hj.symm, mul_zero], ha, hc, one_mul]

theorem selfDual_stdLat (hS : S.gram = 1) : IsSelfDualC S (stdLat S) := by
  convert GlobalTheory.Ker.Base.selfDualC_stdL hS using 1
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL, stdLat, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h trivial)
    rw [← hb]
    exact b.2
  · exact Submodule.mem_one.2 ⟨⟨x i, h⟩, rfl⟩

theorem reads_sum {θ : InfFam D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}
    {ι : Type} (s : Finset ι) {G : ι → VC D a d → ℂ} {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem finPt_sub {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z z' : Matrix (Fin d) (Fin a) D.host.E) :
    finPt hS hT r (z - z') = finPt hS hT r z - finPt hS hT r z' := by
  unfold finPt
  rw [← AddMonoidHom.map_sub]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply]
  ring_nf

theorem pt_sub_mem {a d : ℕ} (δ : ℂ) {z z' : Matrix (Fin d) (Fin a) D.host.E} (h : z - z' ∈ YYl D (stdL D a) (stdL D d)) :
    pt D (tor0 D ⊤ δ) δ z - pt D (tor0 D ⊤ δ) δ z' ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, h, ?_⟩
  funext τ i j
  simp only [pt, embV, tor0, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub]
  ring

set_option maxHeartbeats 1000000 in

theorem ip_cosetVec : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ hf₀ hsph hφ ν 𝓕 hcov
  have hset := hX.setup
  have hψ := hset.std
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ P.crv 𝔪 hG.1 (Ideal.isCoprime_iff_sup_eq.2 hG.2.1) P.a P.d
  have hpts := fun y hy => GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ P.crv 𝔪 hG.1 (a := P.a) (d := P.d) y hy
  unfold cosetVec at hφ
  generalize La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d) = L at hidx hpts hφ
  have hne : ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index ≠ 0 := by rw [hidx]; positivity
  haveI : Finite (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  letI : Fintype (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := Fintype.ofFinite _
  choose z hz _ using fun q : L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L => hpts _ (Quotient.out q).2
  have hlv : IsLatVac (heisO X.ψ X.A X.B) (latO X.A X.B (stdLat X.A) LB fun _ => True) f₀ := by
    have e : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by funext v; simp
    rw [← e]
    exact hsph
  have hfin : ∀ y, (finPt X.rkA X.rkB r y).map (infPart D) = 0 := fun y => GlobalTheory.VacUnique.finRat_inf _ _ _
  have hrd := GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hset
  set n := ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index with hn
  have eI : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) L P.e0 = ((Real.sqrt (n : ℝ) : ℂ))⁻¹ •
      ∑ q, al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) • U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) P.e0 := by
    funext y
    simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hz, ← hn]
  have hg := reads_sum Finset.univ fun q => (hrd _ _ hf₀ (z q)).smul (al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
  have hg2 := hg.smul ((Real.sqrt (n : ℝ) : ℂ))⁻¹
  rw [← eI] at hg2
  have hw := ((hrd _ _ hg2 (unitBlock D o P.a P.d)).smul
    (wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  have hsum := ip_sum hψ hcov Finset.univ (fun q => al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
    (fun q => heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (z q)) f₀) (GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀) (fun q => (hrd _ _ hf₀ (z q)).1)
    (fun q => by
      rw [al, map_zpow₀, ← mul_zpow]
      simp)
    (fun q q' hq => ip_heisO_eq_zero hψ (selfDual_stdLat hset.gS) hLB hf₀.1 hlv hcov (hfin _) (hfin _) fun h => hq (by
      rw [← finPt_sub, ← hY] at h
      have h2 := pt_sub_mem δ h
      rw [← hz, ← hz] at h2
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
      exact h2))
    fun q => GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hf₀.1 hf₀.1 _
  have hph : ∀ x : VC D P.a P.d, wdPh D (tor0 D ⊤ δ) x * starRingEnd ℂ (wdPh D (tor0 D ⊤ δ) x) = 1 := fun x =>
    GlobalTheory.HeisOrtho.mul_conj_of_norm_one (by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.norm_exp])
  have hsq : ∀ t : ℝ, 0 ≤ t → ((Real.sqrt t : ℂ))⁻¹ * starRingEnd ℂ ((Real.sqrt t : ℂ))⁻¹ = (t : ℂ)⁻¹ := fun t ht => by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have e1 := hsq n (Nat.cast_nonneg n)
  have e2 := hsq ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) (by positivity)
  have e3 := hph (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
  have e4 : ((n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1 := by
    rw [Complex.ofReal_natCast]; exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hne)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← hn] at hsum
  have eW : ∀ (x : VC D P.a P.d) G, Wd D (tor0 D ⊤ δ) x G = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G := fun _ _ => rfl
  rw [eW] at hφ
  rw [Reads.unique hφ hw]
  show GlobalTheory.Ker.ipO ν 𝓕 _ _ = _ * GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀
  rw [GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right,
    GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hg2.1 hg2.1, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, hsum,
    ← mul_assoc, e2, ← mul_assoc (wdPh _ _ _), e3, one_mul, ← mul_assoc _ (starRingEnd ℂ _), e1, ← mul_assoc _ (n : ℂ), e4, one_mul]
  push_cast
  rfl

end GlobalTheory.NormRatio.CosetNorm
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  atlas_forward_decl GlobalTheory.NormRatio.CosetNorm.ip_cosetVec
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

theorem card_transversal_mul : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  intro D 𝔪 h𝔪 hcop a a' R hR hRu
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 a

  have hker : ∀ k : ↥(intG D a), ρ k = 1 ↔ CongOne D 𝔪 (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) := by
    intro k
    constructor
    · intro h i j
      have h1 := (hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).1 (by
        rw [h]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij])
      by_cases hij : i = j
      · subst hij; simpa [Matrix.sub_apply] using h1
      · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
    · intro h
      apply Units.ext
      ext i j
      refine ((hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).2 ?_).trans ?_
      · have h1 := h i j
        by_cases hij : i = j
        · subst hij; simpa [Matrix.sub_apply] using h1
        · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
      · by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪)
      (((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) =
        ((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop a (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)

  let f : R → GL (Fin a) (𝓞 D.host.E ⧸ 𝔪) := fun r => ρ ⟨r.1, hR r.1 r.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * ⟨r', hR r' hr'⟩) = 1 := by
        rw [map_mul, map_inv]; exact inv_mul_eq_one.2 h
      have h2 : CongOne D 𝔪 (r⁻¹ * r') := (hker _).1 h1
      have h3 : CongOne D 𝔪 (r'⁻¹ * r') := by
        rw [inv_mul_cancel]
        exact (hker 1).1 (map_one ρ)
      obtain ⟨r₀, -, hu⟩ := hRu r' (hR r' hr')
      exact Subtype.ext ((hu r ⟨hr, h2⟩).trans (hu r' ⟨hr', h3⟩).symm)
    · intro g'
      obtain ⟨k, rfl⟩ := hsurj g'
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hRu k.1 k.2
      refine ⟨⟨r, hr⟩, ?_⟩
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * k) = 1 := (hker _).2 hc
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.1 h1)
  have hcard : R.card = Nat.card (GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.ofBijective f hf)]
  rw [hcard, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪 a, GlobalTheory.StdLoc.absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, locNorm]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  set q : ℝ := (Ideal.absNorm w : ℝ)
  set c := (normalizedFactors 𝔪).count w
  have e : (q ^ c) ^ (a * (a + a')) = q ^ (c * a ^ 2) * q ^ (c * a * a') := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e, mul_inv, ← mul_assoc, mul_comm (q ^ (c * a ^ 2)) _, mul_assoc, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
  ring

end GlobalTheory.NormRatio
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  atlas_forward_decl GlobalTheory.NormRatio.card_transversal_mul
end

section
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio

theorem conj_smul_le {D : D7} {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J :=
  EigUnit.conj_smul_mono D h

theorem exists_conj_place {D : D7} (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
      w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ∧
      ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w'' = w ∨ w'' = w' := by
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hp := w.isPrime
  have hpr : (D.host.conj • w.asIdeal).IsPrime := inferInstance
  have hnb : D.host.conj • w.asIdeal ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  let w' : HeightOneSpectrum (𝓞 D.host.E) := ⟨D.host.conj • w.asIdeal, hpr, hnb⟩
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv w w' := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have hiff := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w
  refine ⟨w', rfl, (hiff w').2 (Or.inr hc), fun w'' h => ?_⟩
  rcases (hiff w'').1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h1 hc)

theorem eq_top_of_eq_conj {D : D7} {𝔪 A B : Ideal (𝓞 D.host.E)} (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hA : 𝔪 ≤ A)
    (hB : 𝔪 ≤ B) (h : A = D.host.conj • B) : A = ⊤ :=
  top_le_iff.1 (hcop ▸ sup_le hA (h ▸ conj_smul_le hB))

theorem prod_Ioc_shift {M : Type} [CommMonoid M] (g : ℕ → M) (a a' : ℕ) :
    ∏ n ∈ Finset.Ioc a' (a + a'), g n = ∏ i ∈ Finset.Icc 1 a, g (a' + i) := by
  have e : Finset.Ioc a' (a + a') = (Finset.Icc 1 a).image (a' + ·) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨n - a', by omega, by omega⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; omega
  rw [e, Finset.prod_image fun x _ y _ h => by simpa using h]

theorem locIdx_mul_locNorm_mul_dSfun : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf →
    ∀ a a' : ℕ, 1 ≤ a' →
    (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  intro D 𝔪 Sf hG a a' ha'
  classical
  obtain ⟨hne, hcop, -, hS⟩ := hG
  set s : ℂ := (a' : ℂ) / 2 with hs_def
  have hs : 0 < s.re := by
    have : (1 : ℝ) ≤ a' := by exact_mod_cast ha'
    simp only [hs_def, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + a') v s with hf
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Sf f)
  have hsplitf : Set.mulIndicator {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))} f =
      Set.mulIndicator {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Sf : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Set.mem_empty_iff_false]
    by_cases hv : v ∈ Sf <;> simp [hv]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s * ∏ v ∈ Sf, f v :=
    h0.unique (h1.mul h2)
  set P := (normalizedFactors 𝔪).toFinset with hP
  have hw : ∀ I ∈ P, I.IsPrime ∧ I ≠ ⊥ ∧ 𝔪 ≤ I := by
    intro I hI
    obtain ⟨hp, hle⟩ := (Ideal.mem_normalizedFactors_iff hne).1 (Multiset.mem_toFinset.1 hI)
    exact ⟨hp, fun h => hne (le_bot_iff.1 (h ▸ hle)), hle⟩
  let W : P → HeightOneSpectrum (𝓞 D.host.E) := fun x => ⟨x.1, (hw x.1 x.2).1, (hw x.1 x.2).2.1⟩
  have hbij : ∏ v ∈ Sf, f v = ∏ x ∈ P.attach, f ((W x).under (𝓞 D.host.F)) := by
    symm
    refine Finset.prod_bij (fun x _ => (W x).under (𝓞 D.host.F)) (fun x _ => (hS _).2 ⟨W x, (hw x.1 x.2).2.2, rfl⟩)
      (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => rfl)
    · obtain ⟨w', hw', -, hall⟩ := exists_conj_place (W x)
      rcases hall (W y) hxy.symm with h | h
      · exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm
      · have h' : y.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
        exact absurd (eq_top_of_eq_conj hcop (hw y.1 y.2).2.2 (hw x.1 x.2).2.2 h') (hw y.1 y.2).1.ne_top
    · obtain ⟨w, hmw, rfl⟩ := (hS v).1 hv
      have hmem : w.asIdeal ∈ P := Multiset.mem_toFinset.2 ((Ideal.mem_normalizedFactors_iff hne).2 ⟨w.isPrime, hmw⟩)
      exact ⟨⟨w.asIdeal, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hloc : ∀ x : P, ((blockIdx (Ideal.absNorm x.1 : ℝ) ((normalizedFactors 𝔪).count x.1) a a' : ℝ) : ℂ) *
      ((((Ideal.absNorm x.1 : ℝ) ^ ((normalizedFactors 𝔪).count x.1 * a * a'))⁻¹ * glVol (Ideal.absNorm x.1 : ℝ) a : ℝ) : ℂ) *
      f ((W x).under (𝓞 D.host.F)) = 1 := by
    intro x
    obtain ⟨w', hw', hu, -⟩ := exists_conj_place (W x)
    have hne' : W x ≠ w' := by
      intro h
      have h' : x.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
      exact (hw x.1 x.2).1.ne_top (eq_top_of_eq_conj hcop (hw x.1 x.2).2.2 (hw x.1 x.2).2.2 h')
    have hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((W x).under (𝓞 D.host.F)) :=
      ⟨W x, w', hne', rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
    have hN : Ideal.absNorm ((W x).under (𝓞 D.host.F)).asIdeal = Ideal.absNorm x.1 :=
      GlobalTheory.ChainTw.TwPlaces.absNorm_under_of_ne hu.symm hne'
    have hq : (1 : ℝ) < (Ideal.absNorm x.1 : ℝ) := by
      have h1 : Ideal.absNorm x.1 ≠ 1 := fun h => (hw x.1 x.2).1.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h2 : Ideal.absNorm x.1 ≠ 0 := fun h => (hw x.1 x.2).2.1 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast (by omega : 1 < Ideal.absNorm x.1)
    have hd := GlobalTheory.ChainTw.dv_center_of_isSplit D.sp.cm.deg2 hsp a a'
    have hst := congrArg (fun r : ℝ => (r : ℂ)) (GlobalTheory.StdLoc.stdLoc_product hq ((normalizedFactors 𝔪).count x.1) a a')
    simp only [hf, hs_def, hd, hN, prod_Ioc_shift (fun n => (1 - (((Ideal.absNorm x.1 : ℕ) : ℂ) ^ n)⁻¹)) a a']
    push_cast at hst ⊢
    linear_combination hst
  rw [key]
  have hmain : (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * ∏ v ∈ Sf, f v = 1 := by
    rw [hbij, locIdx, locNorm, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_attach P,
      ← Finset.prod_attach P, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => hloc x
  linear_combination (GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s) * hmain

end GlobalTheory.NormRatio
end
end

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ a a' : ℕ, 1 ≤ a' →
  (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  atlas_forward_decl GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun
end

section
noncomputable section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type}
    (s : Finset ι) (G : ι → Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ) (f : ι → WO S T → ℂ) (h : ∀ i ∈ s, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ip_eq (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) : ip S T ν 𝓕 f g = GlobalTheory.Ker.ipO ν 𝓕 f g := rfl

theorem ip_sum_left (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 (∑ i ∈ s, f i) g = ∑ i ∈ s, ip S T ν 𝓕 (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_left hψ hν.1 hν.2.1 (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j) hg

theorem ip_sum_right (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 g (∑ i ∈ s, f i) = ∑ i ∈ s, ip S T ν 𝓕 g (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_right hψ hν.1 hν.2.1 hg (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j)

theorem isSphOff_sum {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i ∈ s, IsSphOff ψ S T LS LT Sf (f i)) : IsSphOff ψ S T LS LT Sf (∑ i ∈ s, f i) := by
  have key : ∀ u, (∀ i ∈ s, heisO ψ S T u (f i) = f i) → heisO ψ S T u (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    intro u hu
    funext w
    simp only [heisO, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => congrFun (hu i hi) w
  exact ⟨fun u hu => key _ fun i hi => (hf i hi).1 u hu, fun e he u hu hh => key _ fun i hi => (hf i hi).2 e he u hu hh⟩

theorem isSphOff_pure (hθ : IsInfFam θ) {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {f : WO S T → ℂ}
    (hf : IsSphOff ψ S T LS LT Sf f) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (p : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f p) :=
  ⟨fun u hu => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any (nsmul_mem hu 2)), hf.1 u hu],
   fun e he u hu hh => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any hu), hf.2 e he u hu hh]⟩

theorem volQ_eq_mass (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V) (h2 : Function.Injective ι) (h3 : ι.range = GfC V)
    (h4 : ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n)
    (h5 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K) (h6 : ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ intG D n)
    (h7 : Links.IsMeasDef V K μ 𝓕) : (volQ V μ : ℂ) = mass D n := by
  have h := (GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum V n ι (intG D n) K μ 𝓕 h1 h2 h3 h4 h5 h6 h7 (fun _ => 1)
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩).2.2
  simpa [GlobalTheory.AutomorphicL2Unitary.descend, volQ, mass] using h

theorem openOff_conj {V : HSp D} {L : Lat V} {Sf : Finset (FinPl D)} {a g b : GA D V} (ha : a ∈ openOff V L ∅)
    (hg : g ∈ openOff V L Sf) (hb : b ∈ openOff V L ∅) : a⁻¹ * g * b ∈ openOff V L Sf := fun v hv => by
  rw [map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem (ha v (Finset.notMem_empty v))) (hg v hv)) (hb v (Finset.notMem_empty v))

end General

section Translates

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)

theorem om_mul_one (om : GlobalTheory.Core.Rk.IP.WRep S T) (g g' : GA D S) (f : WO S T → ℂ) :
    om (g * g', 1) f = om (g, 1) (om (g', 1) f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem coef_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G) (x : G) :
    ip S T ν 𝓕 (om (ι x, 1) (∑ y ∈ R, om (ι y, 1) φ)) (∑ y ∈ R, om (ι y, 1) φ) =
      ∑ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * x * y), 1) φ) φ := by
  have hth : ∀ g : GA D S, IsThetaFunO ψ S T (om (g, 1) φ) := fun g => hom.om_pres _ _ hφ
  rw [map_sum]
  simp only [← om_mul_one]
  rw [ip_sum_left hom.std hν R _ (fun _ => hth _) ((GlobalTheory.FinWeilO.thetaSub _ _ _).sum_mem fun j _ => hth _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ip_sum_right hom.std hν R _ (fun _ => hth _) (hth _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have e : ι x * ι y = ι y' * ι (y'⁻¹ * x * y) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [ip_eq, ip_eq, ← GlobalTheory.Size.ipO_om hom hν.1 hν.2.1 (hth (ι (y'⁻¹ * x * y))) hφ (ι y', 1), ← om_mul_one, e]

theorem norm_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G)
    (h : ∀ y ∈ R, ∀ y' ∈ R, y' ≠ y → ip S T ν 𝓕 (om (ι (y'⁻¹ * y), 1) φ) φ = 0) :
    ip S T ν 𝓕 (∑ y ∈ R, om (ι y, 1) φ) (∑ y ∈ R, om (ι y, 1) φ) = (R.card : ℂ) * ip S T ν 𝓕 φ φ := by
  have h1 := coef_sum ι hom hν hφ R 1
  rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  have h2 : ∀ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * 1 * y), 1) φ) φ = ip S T ν 𝓕 φ φ := by
    intro y hy
    rw [Finset.sum_eq_single_of_mem y hy]
    · rw [mul_one, inv_mul_cancel, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    · intro y' hy' hne
      rw [mul_one]
      exact h y hy y' hy' hne
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]

theorem mem_of_conj_mem {H : Subgroup G} {a b x : G} (ha : a ∈ H) (hb : b ∈ H) (h : a⁻¹ * x * b ∈ H) : x ∈ H := by
  have := mul_mem (mul_mem ha h) (inv_mem hb)
  rwa [show a * (a⁻¹ * x * b) * b⁻¹ = x by group] at this

theorem openOff_conj_hom {L : Lat S} {Sf : Finset (FinPl D)} {a g b : G} (ha : ι a ∈ openOff S L ∅)
    (hg : ι g ∈ openOff S L Sf) (hb : ι b ∈ openOff S L ∅) : ι (a⁻¹ * g * b) ∈ openOff S L Sf := by
  rw [map_mul, map_mul, map_inv]
  exact openOff_conj ha hg hb

theorem norm_arith {A B C : ℂ} {c N e : ℕ} {n v L : ℝ} (h1 : A = (c : ℂ) * B) (h2 : B = ((N : ℂ) ^ e)⁻¹ * C) (h3 : C = n)
    (h4 : n = v) (h5 : (c : ℝ) * ((N : ℝ) ^ e)⁻¹ = L) : A = (L : ℂ) * (v : ℂ) := by
  rw [h1, h2, h3, h4, ← h5]
  push_cast
  ring

end Translates

section Exact

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D N) := fun i j => by simp

theorem vac_eq_of_reads (h : IsExact P X r) {G : Formalism.MainNotions.TaylorLogMetric.VC D P.a P.d → ℂ} {f : WO X.A X.B → ℂ} (hF : P.F = G)
    (h1 : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r G f) : X.vac = f := by
  subst hF
  exact h.read.unique h1

theorem vac_eq_sum (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) {o : ℕ}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hF : P.F = ∑ y ∈ R, P.W.Om y 1 (cosetVec P 𝔪 o)) {φ : WO X.A X.B → ℂ}
    (hφ : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ) : X.vac = ∑ y ∈ R, X.om (X.ιA y, 1) φ := by
  have h1 : ∀ y, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (P.W.Om y 1 (cosetVec P 𝔪 o)) (X.om (X.ιA y, 1) φ) := fun y => by
    have := h.reads_om hI y 1 (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o) hφ
    rwa [X.ιB.map_one] at this
  exact vac_eq_of_reads h hF (reads_sum R (fun y => P.W.Om y 1 (cosetVec P 𝔪 o)) (fun y => X.om (X.ιA y, 1) φ) fun y _ => h1 y)

theorem exists_reads_coset (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) (o : ℕ) :
    ∃ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup (cosetVec P 𝔪 o) (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o)

theorem exists_reads_vacuum (h : IsExact P X r) : ∃ f₀, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)

theorem mem_openOff (h : IsExact P X r) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∈ intG D P.a) (Sf : Finset (FinPl D)) :
    X.ιA x ∈ openOff X.A (stdLat X.A) Sf := fun v _ =>
  (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)).2.1 hx v (Finset.notMem_empty v)

theorem norm_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a)
    (hRu : ∀ k ∈ intG D P.a, ∃! y, y ∈ R ∧ CongOne D 𝔪 (y⁻¹ * k)) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) :
    ip X.A X.B ν 𝓕 (∑ y ∈ R, X.om (X.ιA y, 1) φ) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = (R.card : ℂ) * ip X.A X.B ν 𝓕 φ φ := by
  refine norm_sum X.ιA h.weil hν hφ R fun y hy y' hy' hne =>
    horth _ (mem_openOff h (mul_mem (inv_mem (hR y' hy')) (hR y hy)) Sf) fun hc => hne ?_
  have h1 : CongOne D 𝔪 (y⁻¹ * y) := by rw [inv_mul_cancel]; exact congOne_one 𝔪 _
  exact (hRu y (hR y hy)).unique ⟨hy', hc.2⟩ ⟨hy, h1⟩

theorem supp_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∉ intG D P.a)
    (hx' : X.ιA x ∈ openOff X.A (stdLat X.A) Sf) :
    ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) (∑ y ∈ R, X.om (X.ιA y, 1) φ)) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = 0 := by
  refine (coef_sum X.ιA h.weil hν hφ R x).trans ?_
  refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun y' hy' => horth _ ?_ fun hc => hx ?_
  · exact openOff_conj_hom X.ιA (mem_openOff h (hR y' hy') ∅) hx' (mem_openOff h (hR y hy) ∅)
  · exact mem_of_conj_mem (hR y' hy') (hR y hy) hc.1

theorem finite_data (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ}
    (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o) (ho : o + P.a ≤ P.d) :
    (∃ LB : Lat X.B, IsSelfDualC X.B LB ∧ IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf X.vac) ∧
    ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
      ip X.A X.B ν 𝓕 X.vac X.vac = (locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ) ∧
      ∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) X.vac) X.vac = 0 := by
  obtain ⟨R, hR, hRu, hF⟩ := hstd
  refine (exists_reads_coset h hm.1 o).elim fun φ hφ => ?_
  refine (exists_reads_vacuum h).elim fun f₀ hf₀ => ?_
  refine (GlobalTheory.T.exists_selfDualLattice_vacuumReading X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup).elim fun LB ⟨hLB, hz, hsph⟩ => ?_
  have hs₀ := hsph P.e0 P.vac.1 f₀ hf₀
  have hsd := (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA 1) 1 h.std.frame.gramA X.rkA (h.std.ptA 1)).1
  have hv := vac_eq_sum hI h hm.1 hF hφ
  have hsφ := GlobalTheory.T.thetaCosetIndicatorReading_spherical_off_modulus P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ
  have hs := isSphOff_sum R (fun y => X.om (X.ιA y, 1) φ) fun y hy =>
    GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer X.ψ X.A X.B X.χA X.χB X.om h.weil _ _ hsd hLB Sf _ (mem_openOff h (hR y hy) Sf) φ hφ.1 hsφ
  refine ⟨⟨LB, hLB, by rw [hv]; exact hs⟩, fun ν 𝓕 hν => ?_⟩
  have horth := GlobalTheory.T.cosetVector_orthogonal_translate_finite_point P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ho ν 𝓕 hν
  refine ⟨?_, fun x hx hx' => by rw [hv]; exact supp_transl h hR hφ.1 hν horth hx hx'⟩
  have h3 := GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ν 𝓕 hν
  have h4 := GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup LB hLB hz P.e0 P.vac.1 f₀ hf₀ hs₀ ν 𝓕 hν
  have h5 := GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm D 𝔪 hm.1 hm.2.1 P.a (P.d - P.a) R hR hRu
  rw [Nat.add_sub_cancel' P.a_le] at h5
  have h6 := norm_transl h hR hRu hφ.1 hν horth
  exact norm_arith (by rw [hv]; exact h6) h3 h4 P.vac.2.2.1 h5

end Exact

section Fock

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem var_injective (X : Data P) : Function.Injective X.var := by
  rintro ⟨τ, i, j⟩ ⟨τ', i', j'⟩ e
  simp only [Data.var, Prod.mk.injEq, Fin.cast_inj] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

theorem ip_fock (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) : ip X.A X.B ν 𝓕 (X.fock T) (X.fock T) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) * ip X.A X.B ν 𝓕 X.vac X.vac := by
  have h := GlobalTheory.FockIsometry.ipO_pureTensorO D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank) (fun _ => le_rfl) (fun _ => le_rfl)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) X.vac hX.2.vac_theta hX.2.vac_fock
    ν 𝓕 hν (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T)) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) := by
    rw [GlobalTheory.FockCoefReal.fockIp_eq_fock, GlobalTheory.LowRowFock.fock_rename_inj (var_injective X), ← GlobalTheory.FockCoefReal.fockIp_eq_fock]
  have e2 : ip X.A X.B ν 𝓕 X.vac X.vac = (nrm2 ν 𝓕 X.vac : ℂ) := GlobalTheory.Size.ipO_self ν 𝓕 X.vac
  exact h.trans (by rw [e, e2])

theorem ip_fock_zero (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) {g : GA D X.A} (hg : g ∈ GfC X.A) (h0 : ip X.A X.B ν 𝓕 (X.om (g, 1) X.vac) X.vac = 0) :
    ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) = 0 := by
  refine (GlobalTheory.FockCoefSplit.pair_eq_inf D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) ν 𝓕 hν 1 (one_mem _) 1 (one_mem _)
    (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))).elim fun c hc => ?_
  have h1 := hc X.vac (X.om (g, 1) X.vac) hX.2.vac_theta (hX.2.weil.om_pres _ _ hX.2.vac_theta) hX.2.vac_fock
    fun τ => GlobalTheory.FockCoefSplit.fockVac_om_fin hX.2.weil hX.2.inf hg (one_mem _) τ _ hX.2.vac_theta (hX.2.vac_fock τ)
  have h2 := GlobalTheory.FockCoefSplit.om_fin_pureTensorO hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) hg
    (one_mem (GfC X.B)) hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  rw [GlobalTheory.VacPairSchur.thetaIP_eq_ipO, GlobalTheory.VacPairSchur.thetaIP_eq_ipO, ← h2, Prod.mk_one_one, X.om.map_one,
    Module.End.one_apply, ← ip_eq, ← ip_eq, h0, mul_zero] at h1
  exact h1

theorem isFockVec_fock (hX : IsDict P X) (T : Tup D P.a P.d P.n) :
    IsFockVec X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (X.fock T) :=
  GlobalTheory.FockSph.isFockVec_pureTensorO (sS := fun _ => 1) (sT := fun _ => 1) hX.2.weil.std hX.2.inf
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB) (fun _ => 1) (fun _ => 1)
    hX.2.vac_theta hX.2.vac_fock _

theorem wcoef_fock (hX : IsDict P X) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)) (T : Tup D P.a P.d P.n)
    (g : GA D X.A) {k : GA D X.A} (hk : k ∈ GinfC X.A) : wcoef X.om ν 𝓕 (X.fock T) (X.fock T) (g * k) =
      ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) := by
  rw [wcoef, om_mul_one, GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors P X hX hX.2.infB k hk T]

end Fock

section Norm

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem petersson_eq (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (hX : IsDict P X)
    {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))} {μ₀ : Measure (GA D X.B)} (hK : IsMaxLevel X.toFrame K₀ μ₀)
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ} (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o)
    (ho : o + P.a ≤ P.d) (ha : 1 ≤ P.a) (had : P.a < P.d) (hu : GlobalTheory.LFun.UnrOff X.χB (Sf : Set (FinPl D))) (Λ : ℂ → ℂ)
    (hΛ : ∀ s, GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL X.χB⁻¹ (Sf : Set (FinPl D))) s (Λ s)) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) =
      mass D P.d * mass D P.a * ((∏ i ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - i)) /
        GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) P.a P.d (((P.d - P.a : ℕ) : ℂ) / 2)) *
        (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) *
          ((locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ))) := by
  refine (GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan P X hX ha had).elim fun cA h1 => h1.elim fun a h2 => h2.elim fun ν h3 => h3.elim fun 𝓕 hPair => ?_
  have hfd := finite_data hI h hm hstd ho
  refine hfd.1.elim fun LB hLB => ?_
  have hn := (hfd.2 ν 𝓕 hPair.covol).1
  have hs := (hfd.2 ν 𝓕 hPair.covol).2
  have hlev := fun x => GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)
  have hsph : IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf (X.fock T) := isSphOff_pure hX.2.inf hLB.2 _ _ _ _ _
  have hU : GlobalTheory.Core.Rk.IP.Unram X.ψ X.A X.B X.χB (stdLat X.A) LB Sf (X.fock T) (X.fock T) :=
    ⟨(hlev 1).1, hLB.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2, hu, hsph, hsph⟩
  have hint := GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact P X hX (hlev 1).1 (fun x => (hlev x).2) a ν 𝓕 hPair.maj Sf (X.fock T)
    (ip X.A X.B ν 𝓕 (X.fock T) (X.fock T))
    (fun x hx k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (by rw [hX.2.fixA x hx T]))
    (fun x hx hx' k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (ip_fock_zero hX hPair.covol T (h.std.ptA x).1 (hs x hx hx')))
  refine hK.meas.elim fun 𝓕₀ h𝓕₀ => hX.1.measA.elim fun 𝓕A h𝓕A => ?_
  haveI := hX.1.haarA
  haveI : μ₀.IsHaarMeasure := h𝓕₀.1.1
  have hA : GlobalTheory.Cusp.wittIndex X.A = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramA)
  have hB : GlobalTheory.Cusp.wittIndex X.B = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramB)
  have key := GlobalTheory.BottomRallis.norm_eq hP hPair hA hB (isFockVec_fock hX T) hU X.m μ₀
    ⟨((P.d - P.a : ℕ) : ℝ) / 2 - 1, by linarith, hint.1 _⟩
    (fun i => Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (X.A.rank : ℂ) / 2 - i)) fun i _ => hΛ _
  have vA := volQ_eq_mass X.A P.a X.ιA X.KA X.m 𝓕A hX.1.defA hX.1.injA hX.1.rangeA hX.1.ratA hX.1.levA hX.1.levA_iff h𝓕A
  have vB := volQ_eq_mass X.B P.d X.ιB K₀ μ₀ 𝓕₀ hX.1.defB hX.1.injB hX.1.rangeB hX.1.ratB hK.lev hK.mem_iff h𝓕₀
  have e1 := hint.2.trans ((ip_fock hX hPair.covol T).trans (congrArg _ hn))
  refine key.trans ?_
  rw [vA, vB, e1, X.rkA, X.rkB]

def normFactor (D : D7) (δ t0 : ℂ) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  (normConst D ⊤ δ a n : ℂ) * mass D d * mass D a * fockSum D a d n * (vacNorm D ⊤ δ t0 a d : ℂ) /
    GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a d (((d - a : ℕ) : ℂ) / 2)

theorem collect {c I mB mA L dS d0 F l v : ℂ} (h : I * l * d0 = dS) (h0 : d0 ≠ 0) (hS : dS ≠ 0) :
    c * I * (mB * mA * (L / dS) * (F * (l * v))) = c * mB * mA * F * v / d0 * L := by
  rw [← h] at hS ⊢
  have h1 : I ≠ 0 := fun e => hS (by rw [e]; simp)
  have h2 : l ≠ 0 := fun e => hS (by rw [e]; simp)
  field_simp

theorem norm_bottom (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) {T : Type}
    {L : LevCh D T} {sc : Consts} {μ : T} (hL : L.Is μ) (G : GridData L sc) {t : T} {i j : Fin D.R.m}
    {P' : Pair D ⊤ δ t0 Q} (hb : IsBottom G t i j (modT G t) P P') {Λ : ℂ → ℂ} (hΛ : GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ) :
    (P.norm : ℂ) = normFactor D δ t0 P.a P.d P.n *
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  have hm := goodMod_modT hL (GlobalTheory.SqTop.BotT.pde_ne_q hR).1 (GlobalTheory.SqTop.BotT.pde_ne_q hR).2 G t
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hdict := exact_dictionary P hI (isCongLevel_of_isBlockLevel hm.1 hb.lev.1)
  refine hdict.2.1.elim fun X h1 => h1.elim fun r h2 => h2.elim fun K₀ h3 => h3.elim fun μ₀ h4 => ?_
  have h5 := hdict.2.2 X r K₀ μ₀ h4.1 h4.2
  have hX := h5.1.1
  have hχ := GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse X.χB P.W.chV' P.W.ep' (nuH G t i j) hX.2.weil.hecT h4.1.chB hb.chars.2
  have hl := GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive hL hR.hF G t i j X.χB hχ
  have hT := petersson_eq hP hI h4.1 hX h4.2 hm hb.std (by rw [zero_add]; exact P.a_le) (by omega) (by omega) hl.1 Λ
    (hl.2 Λ hΛ)
  have hidx : ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = locIdx D (modT G t) P.a (P.d - P.a) :=
    GlobalTheory.StdLoc.relIndex_blockLevel P (modT G t) P.a hm.1 hm.2.1 P.a_le (hPa.symm ▸ hb.lev.1)
  have hidx' : ((P.J.relIndex (intG D P.d) : ℕ) : ℂ) = (locIdx D (modT G t) P.a (P.d - P.a) : ℂ) := by
    rw [← hidx]; rfl
  have hd := GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial D (modT G t) (sfB G t) hm P.a (P.d - P.a) (by omega)
  rw [Nat.add_sub_cancel' P.a_le] at hd
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hprod : ∏ k ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - k) =
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
    obtain ⟨u, hu⟩ := hrk.2.2.1
    have e1 : P.d = 2 * GlobalTheory.SqTop.h0 D i j := by unfold GlobalTheory.SqTop.h0; omega
    rw [← GlobalTheory.BottomRallis.prod_range_sub_eq_prod_Icc (fun s => Λ s) P.a (GlobalTheory.SqTop.h0 D i j) (GlobalTheory.SqTop.e0 D i j)
      (by unfold GlobalTheory.SqTop.h0 GlobalTheory.SqTop.e0; omega)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    rw [Nat.cast_sub P.a_le, e1]
    push_cast
    ring
  refine h5.2.2.2.2.trans ?_
  rw [Finset.sum_congr rfl fun T _ => hT T, ← Finset.mul_sum, ← Finset.sum_mul, hidx', hprod]
  exact collect hd (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)

end Norm

theorem normBig_ratio : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  intro hP hI _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 i j t t' Q Q' P P' P₁ P₁' Λ Λ' hb hb' hΛ hΛ'
  have h1 := norm_bottom hP (hI D) hR hL G hb hΛ
  have h2 := norm_bottom hP (hI D) hR hL G hb' hΛ'
  have h3 := (GlobalTheory.BottomReal.bottom_real_eq G hL hb hb').1
  have h4 : normFactor D δ t0 P.a P.d P.n = normFactor D δ t0 P₁.a P₁.d P₁.n :=
    congr (congr (congrArg (normFactor D δ t0) h3.1) h3.2.1) h3.2.2.1
  rw [h1, h2, h4]
  ring

end GlobalTheory.NormRatio
end
end
