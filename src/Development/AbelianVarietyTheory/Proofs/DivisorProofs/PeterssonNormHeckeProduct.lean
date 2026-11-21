import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisotropicRallisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGrids
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AutomorphicArithmetic.DivisorFrames.FiniteComponentMemStabilizerOfStandardSectionNeZ
import Development.AutomorphicArithmetic.DivisorFrames.StdFstActOOfMemStabilizer
import Development.AutomorphicArithmetic.DivisorFrames.IsUnitDetProdDetIdlOfMemSt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsStdFstNeZeroOfRankLe

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω where
  std := h.std
  hecS := h.hecS
  hecT := h.hecT
  resS := h.resS
  resT := h.resT
  om_pres p f hf := (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
  om_heis g k w f hf := h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_aut γ hγ γ' hγ' f hf := h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_cont f hf := h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_unit μ 𝓕 h1 h2 p f hf := h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_split e he g k h1 h2 x y h3 h4 :=
    (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
      hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) where
  rank := hX.rank
  rank' := hX.rank'
  std := hX.std
  std' := hX.std'
  stdW := hX.stdW
  is :=
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.NormBigDict

theorem normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  intro D T L sc G W i j A A' WW X hX t P ν 𝓕 hν h𝓕
  have h := hX.is
  obtain ⟨ν₁, hν₁, hfd, hint⟩ := GlobalTheory.SgnIdent.meas_sgn true A X.m X.fd h.meas.1 h.meas.2
  refine ⟨ν₁, hν₁, ?_⟩
  have hW := h.weil t
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ)
    X.rA.B X.rW.s X.rW.B (GlobalTheory.ConstRatio.theta_f h t).1 P
  set Φ := pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P with hΦd
  set om := (X.ω t).toSgn true with hom

  have hg : ∀ y : GA D WW, AutomorphicL2Unitary.LeftInv (GQ (GlobalTheory.Grid.neg A)) (fun g => thetaKO om g y Φ * (fun _ => (1 : ℂ)) g) := by
    intro y γ hγ g
    show om (γ * g, y) Φ 0 * 1 = om (g, y) Φ 0 * 1
    have e : ((γ * g, y) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (γ, 1) * (g, y) := by rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    rw [hW.om_aut γ hγ 1 (GQ WW).one_mem _ (hW.om_pres _ _ hΦ)]

  have hup : ∀ y, up om ν₁ Φ (fun _ => 1) y = X.I W.ψ W.θ t P y := by
    intro y
    haveI := hν₁
    simp only [up, AutomorphicL2Unitary.autMeasure]
    rw [integral_quotMeasure hfd]
    simp only [(hg y).descend_mk]
    simp only [mul_one]
    exact (hint fun g => thetaKO (X.ω t) g y Φ).2

  have hinv : AutomorphicL2Unitary.LeftInv (GQ WW) (up om ν₁ Φ fun _ => 1) := by
    intro γ hγ y
    rw [hup, hup]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker]
    congr 1
    funext g
    exact GlobalTheory.ThetaMean.leftInv_theta hW hΦ ((GlobalTheory.Grid.ofSgn true A).symm g) γ hγ y
  haveI := hν
  simp only [petersson, pet]
  rw [integral_quotMeasure h𝓕]
  simp only [hinv.descend_mk, hup, Complex.mul_conj, ← Complex.sq_norm]
  exact (integral_ofReal).symm

end GlobalTheory.NormBigDict

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_thetaIntegral_normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  atlas_forward_decl GlobalTheory.NormBigDict.normSq_eq_petersson
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  first | exact @GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | exact GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero | (intros; apply GlobalTheory.RowTest.BottomMeas.exists_haar_fd_volQ_ne_zero <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomPairData
variable {D : D7}

theorem sig_of_gram_one {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 ∧ (V.sig τ).1 = V.rank := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  have hq : (V.sig τ).2 = 0 := by
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
  refine ⟨hq, ?_⟩
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum, hq] at this
  omega

open GlobalTheory.Grid (neg neg_gram) in

def negFrame (A : HSp D) : CptF (neg A) := fun τ r c =>
  Sum.elim (fun _ => (0 : ℂ)) (fun k => if (k : ℕ) = (c : ℕ) then 1 else 0) r

open GlobalTheory.Grid (neg) in
theorem negFrame_inl (A : HSp D) (τ : D.what₂.Tau) (a : Fin ((neg A).sig (tauE D τ)).1) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inl a) c = 0 := rfl

open GlobalTheory.Grid (neg) in
theorem negFrame_inr (A : HSp D) (τ : D.what₂.Tau) (k : Fin ((neg A).sig (tauE D τ)).2) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inr k) c = if (k : ℕ) = (c : ℕ) then 1 else 0 := rfl

open GlobalTheory.Grid (neg neg_gram) in
theorem jpq_mul_negFrame (A : HSp D) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq ((neg A).sig (tauE D τ)).1 ((neg A).sig (tauE D τ)).2 * negFrame A τ = -negFrame A τ := by
  ext r c
  rcases r with a | b
  · rw [Matrix.neg_apply, show negFrame A τ (Sum.inl a) c = 0 from rfl, neg_zero, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun x _ => by
      rcases x with x | x
      · rw [show negFrame A τ (Sum.inl x) c = 0 from rfl, mul_zero]
      · simp [Formalism.UG.Jpq]
  · simp only [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      negFrame_inl, negFrame_inr, mul_zero, Finset.sum_const_zero, Matrix.neg_apply, Matrix.zero_apply, zero_mul, zero_add,
      Matrix.one_apply, neg_mul, ite_mul, one_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

open GlobalTheory.Grid (neg neg_gram) in
theorem negFrame_conj_mul (A : HSp D) (hg : A.gram = 1) (hA : A.SigOK) (τ : D.what₂.Tau) :
    (negFrame A τ)ᴴ * negFrame A τ = 1 := by
  obtain ⟨hq, hp⟩ := sig_of_gram_one hg hA (tauE D τ)
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  have e1 : ∀ x, star (negFrame A τ (Sum.inl x) a) * negFrame A τ (Sum.inl x) b = 0 := fun x => by
    rw [show negFrame A τ (Sum.inl x) a = 0 from rfl, star_zero, zero_mul]
  have e2 : ∀ x : Fin ((neg A).sig (tauE D τ)).2, star (negFrame A τ (Sum.inr x) a) * negFrame A τ (Sum.inr x) b =
      if (x : ℕ) = a ∧ (x : ℕ) = b then 1 else 0 := fun x => by
    rw [negFrame_inr, negFrame_inr]
    by_cases h1 : (x : ℕ) = a <;> by_cases h2 : (x : ℕ) = b <;> simp [h1, h2]
  rw [Finset.sum_eq_zero fun x _ => e1 x, zero_add, Finset.sum_congr rfl fun x _ => e2 x]
  have hk : (a : ℕ) < ((neg A).sig (tauE D τ)).2 := by
    show (a : ℕ) < (A.sig (tauE D τ)).1
    rw [hp]; exact a.2
  rw [Finset.sum_eq_single ⟨a, hk⟩]
  · by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg]; rintro ⟨-, h2⟩; exact h (Fin.ext h2)
  · intro x _ hx; rw [if_neg]; rintro ⟨h1, -⟩; exact hx (Fin.ext h1)
  · simp

open GlobalTheory.Grid (neg neg_gram) in
theorem gramAt_neg_of_gram_one {A : HSp D} (hg : A.gram = 1) (τ : D.what₂.Tau) : gramAt D (neg A) τ = -1 := by
  ext a b
  simp only [gramAt, neg_gram, hg, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn) in

theorem exists_pair {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S}
    (h : X.Is ψ θ α β νH S) (hstd : X.rA.IsStd) (hA : A.SigOK) (h1 : 1 ≤ A.rank) (h1' : 1 ≤ A'.rank) (t : T) :
    ∃ (cA : CptF (neg A)) (a : GL (Fin (neg A).rank) (AE D)) (ν : Measure (WO (neg A) WW)) (𝓕 : Set (WO (neg A) WW)),
      Pair ψ θ (neg A) WW (β t) (β t / α t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) ν 𝓕 := by
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (neg A) WW
  have hg := hstd.1
  have hgn : ∀ τ, gramAt D (neg A) τ = -1 := gramAt_neg_of_gram_one hg
  have hs : ∀ τ, X.rA.s τ = 1 := fun τ => (hstd.2.2 τ).1
  refine ⟨negFrame A, 1, ν, 𝓕, ⟨⟨h1, h1', ?_, h.isVac.2.inf, sigOK_sgn true hA, fun τ => ?_,
    fun τ => isCartanInv_sgn true _ τ (h.rigA.2.2 τ).1, fun τ => (h.rigW.2.2 τ).1, fun τ => ?_⟩, ?_, fun τ => ?_, h.weil t, hν⟩⟩
  · exact h.rank.symm
  · rw [Matrix.mul_assoc, jpq_mul_negFrame, Matrix.mul_neg, negFrame_conj_mul A hg hA, hgn]
  · show negFrame A τ * -X.rA.s τ = _
    rw [hs, jpq_mul_negFrame, Matrix.mul_neg, Matrix.mul_one]
  · intro w
    refine ⟨fun _ => false, ?_⟩
    simp only [JR, neg_gram, hg]
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rw [hgn, hs]
    simp [compAt]

open GlobalTheory.Grid (neg) in

theorem one_le_bot (i j : Fin D.R.m) : 1 ≤ botBig D i j ∧ 1 ≤ botSmall D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  have h2 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr : Odd D.R.r := by
    have := GlobalTheory.ChiGrid.odd_sLen D
    simp only [GlobalTheory.ChiGrid.sLen] at this
    exact (Nat.odd_add.1 this).2 (by decide)
  obtain ⟨w, hw⟩ := hr
  have hi := i.2
  have hj := j.2
  simp only [botBig, botSmall, rankV, GlobalTheory.ChiGrid.sLen]
  constructor <;> omega

end GlobalTheory.BottomPairData

open GlobalTheory.BottomPairData in

theorem GlobalTheory.BottomPairData.pair_data : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T, ∃ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)), Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX hA t
  have hb := one_le_bot (D := D) i j
  exact exists_pair X (GlobalTheory.BottomIPData.isBottomTri_is hX) hX.std hA (hX.rank ▸ hb.1) (hX.rank' ▸ hb.2) t

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomWitt

theorem wittIndex_eq_zero :
    GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h _
  exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram h.stdW.1)

end GlobalTheory.BottomWitt
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  atlas_forward_decl GlobalTheory.BottomWitt.wittIndex_eq_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem isFockVec_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ cS cT X.rA.B X.rW.B hf hv P

end GlobalTheory.BottomIPData

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolynomialFockThetaVector_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  atlas_forward_decl GlobalTheory.BottomIPData.isFockVec_bottom
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomCusp

theorem isAniso_neg {D : D7} {A : HSp D} (h : IsAniso A) : IsAniso (GlobalTheory.Grid.neg A) := by
  rintro r C ⟨hr, hC, h0⟩
  refine h r C ⟨hr, hC, ?_⟩
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [e, Matrix.mul_neg, Matrix.neg_mul] at h0
  exact neg_eq_zero.1 h0

theorem const_one_mem_cuspForms_of_anisotropic {D : D7} {V : HSp D} (h : IsAniso V) (θ : GlobalTheory.Mem.Th.InfF D) (A : CptF V) :
    (fun _ => (1 : ℂ)) ∈ A0 θ V A :=
  GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem one_mem_A0_of_isBottomTri : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t cA _
  exact const_one_mem_cuspForms_of_anisotropic (isAniso_neg (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.std.1)) W.θ cA

end GlobalTheory.BottomCusp
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_one_mem_cuspForms_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  atlas_forward_decl GlobalTheory.BottomCusp.one_mem_A0_of_isBottomTri
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
noncomputable section
namespace GlobalTheory.BottomIPData

theorem isParamFun_one_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc _ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t
  exact ⟨_, GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar (GlobalTheory.Grid.neg A) X.rA.Λ _
    (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) (fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2)⟩

end GlobalTheory.BottomIPData
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  atlas_forward_decl GlobalTheory.BottomIPData.isParamFun_one_bottom
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomIPData

theorem dSfun_bottom_ne_zero : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h t
  apply GlobalTheory.LFun.dSfun_ne_zero_of_re_pos
  have h2 := (GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j).1
  have hp : (0 : ℝ) < A'.rank := by rw [h.rank']; exact_mod_cast (by omega : 0 < SqNum.botSmall D i j)
  rw [show ((A'.rank : ℂ) / 2) = (((A'.rank : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  positivity

end GlobalTheory.BottomIPData
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  atlas_forward_decl GlobalTheory.BottomIPData.dSfun_bottom_ne_zero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomLVal

open GlobalTheory.LFun

private theorem par_eq_trivPar {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (S : Set (FinPl D)) (par : Fam D.host.E)
    (h : IsParamFun D.sp.cm.sig J L S (fun _ => (1 : ℂ)) par) :
    ∀ w ∉ above D.host.E S, par w = GlobalTheory.BottomRallis.trivPar (D := D) n w := by
  intro w hw
  have hx := h _ hw w rfl
  have h0 : (fun _ : GAd D.sp.cm.sig J => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  refine hx.unique ?_
  rcases hx with ⟨hs, e, he, -⟩ | ⟨hw', τ, ϖ, e, α, hϖ, he, -, -⟩
  · exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩
  · refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero _) n).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero _) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

private theorem mem_sfB (G : GridData L sc) (t : T) (v : FinPl D) :
    v ∈ GlobalTheory.BottomIPData.sfB G t ↔ v ∈ G.pl.S0 ∨ ∃ P ∈ L.Q t, P.under (𝓞 D.host.F) = v := by
  classical
  simp only [GlobalTheory.BottomIPData.sfB, GlobalTheory.FunObj.locPl, GlobalTheory.ChiGrid.Places.W0, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩ | hw, rfl⟩
    · exact Or.inl ((G.pl.under_w hu).symm ▸ hu)
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hv | ⟨P, hP, rfl⟩)
    · exact ⟨_, Or.inl ⟨v, hv, rfl⟩, G.pl.under_w hv⟩
    · exact ⟨P, Or.inr hP, rfl⟩

private theorem nuH_unrAt_iff (G : GridData L sc) (t : T) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0) : (nuH G t i j).UnrAt P ↔ (L.xiH t).UnrAt P := by
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 (by
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  refine ⟨fun hnu => ?_, fun hxi => ?_⟩
  · have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv

private theorem nuH_not_unrAt_iff {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ (nuH G t i j).UnrAt P ↔ P.under (𝓞 D.host.F) ∈ GlobalTheory.BottomIPData.sfB G t := by
  rw [mem_sfB]
  by_cases h0 : P.under (𝓞 D.host.F) ∈ G.pl.S0
  · exact iff_of_true (GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j P h0) (Or.inl h0)
  · rw [nuH_unrAt_iff G t i j P h0, hL.Q_ram t P, or_iff_right h0]
    constructor
    · rintro (h | ⟨Q, h, hc⟩)
      · exact ⟨P, h, rfl⟩
      · exact ⟨Q, h, GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc⟩
    · rintro ⟨Q, h, e⟩
      by_cases hq : Q = P
      · exact Or.inl (hq ▸ h)
      · exact Or.inr ⟨Q, h, GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D Q P e hq⟩

private theorem prod_range_sub (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

private theorem bot_ranks (D : D7) (i j : ℕ) : 1 ≤ botSmall D i j ∧ botBig D i j + botSmall D i j = 2 * h0 D i j ∧
    botBig D i j = h0 D i j + e0 D i j := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 : D.R.m < D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  simp only [h0, e0]
  omega

end GlobalTheory.BottomLVal

theorem _root_.GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par →
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
    HolValueAt (fun s => GlobalTheory.LFun.LSD D (GlobalTheory.BottomIPData.sfB G t) par (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (s + 1 / 2)) ((A'.rank : ℂ) / 2)
      (κ * GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
        ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W i j A A' WW X hX t par hpar => ?_⟩⟩
  obtain ⟨r1, r2, r3⟩ := GlobalTheory.BottomLVal.bot_ranks D i j
  rw [← hX.rank'] at r1 r2
  rw [← hX.rank] at r2 r3
  have hd := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos (E := D.host.E)
    ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank
    (s := (A'.rank : ℂ) / 2) (by
      have : (1 : ℝ) ≤ A'.rank := by exact_mod_cast r1
      simp only [Complex.div_ofNat_re, Complex.natCast_re]
      linarith)
  refine ⟨_, inv_ne_zero hd, fun Λ hΛ => ?_⟩
  rw [inv_mul_cancel₀ hd, one_mul]
  have hν : (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)⁻¹ = G.nu t i (j + 1) := by
    rw [inv_div]
    exact mul_div_mul_right_eq_div _ _ _
  have hc := chrEq_nu G t i j hL
  have hU : GlobalTheory.LFun.UnrOff (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)
      ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) := fun w hw => by
    rw [← inv_inv (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t), hν]
    exact ((GlobalTheory.LFun.unrAt_iff_of_chrEq hc w).2
      (not_not.1 (mt (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).1 hw))).inv
  obtain ⟨σ, hσ⟩ := GlobalTheory.RallisEuler.trivPar_euler _ _ A.rank hU
  have hH : Differentiable ℂ fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k) :=
    Differentiable.fun_finset_prod fun k _ => hΛ.1.comp (by fun_prop)
  refine ⟨fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k),
    ⟨Set.univ, trivial, isRightDomain_univ, fun s _ => (hH.analyticAt s).meromorphicAt,
      max σ ((A.rank : ℝ) / 2 + 1), fun s hs => ?_⟩, hH.analyticAt _, ?_⟩
  · have hs1 : σ < s.re := (le_max_left _ _).trans_lt hs
    have hs2 : (A.rank : ℝ) / 2 + 1 < s.re := (le_max_right _ _).trans_lt hs
    refine Eq.trans ?_ ((hσ hs1).trans
      (GlobalTheory.LFun.LSTw_congr (GlobalTheory.BottomLVal.par_eq_trivPar _ _ _ par hpar) _ _).symm)
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ A.rank := by exact_mod_cast Finset.mem_range.1 hk
    rw [hν, GlobalTheory.LFun.charL_eq_of_chrEq hc]
    refine (GlobalTheory.SqStep.heckeL_eq_of_ram
      (fun w hw => (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).2 hw) hΛ ?_).symm
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  · rw [← GlobalTheory.BottomLVal.prod_range_sub (fun s => Λ s) A.rank (h0 D i j) (e0 D i j) (by exact_mod_cast r3)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    have : (A.rank : ℂ) + A'.rank = 2 * (h0 D i j : ℕ) := by exact_mod_cast r2
    push_cast
    linear_combination this / 2
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

private theorem mem_bottomPairFinitePlacesBelow_of_mem_exceptional {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {v : FinPl D} (hv : v ∈ G.pl.S0) : v ∈ sfB G t := by
  classical
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl GlobalTheory.ChiGrid.Places.W0
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨_, hw, G.pl.under_w hv⟩

private theorem under_mem_sfB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ locPl G t) : w.under (𝓞 D.host.F) ∈ sfB G t := by
  classical
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨w, hw, rfl⟩

private theorem unrOff_betaB_div_alphaB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) :
    GlobalTheory.LFun.UnrOff (betaB G i j / alphaB Lc i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) := by
  classical
  intro w hw
  have hw' : w.under (𝓞 D.host.F) ∉ sfB G t := hw
  have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
  have hQ : ∀ P ∈ Lc.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
    hw' (e ▸ under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hv)
  have hμ0 : GlobalTheory.LFun.UnrAt (Lc.mu0 ((j : ℕ) + 1)) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((Lc.C.isMu0 j).unr w fun k hk => hv ?_)
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  have hξ : GlobalTheory.LFun.UnrAt (Lc.xi t) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hn
    rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ w hq rfl
    · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
  have e : betaB G i j / alphaB Lc i j t = G.ch.chi (D.R.m - i) * (Lc.mu0 ((j : ℕ) + 1) * Lc.xi t)⁻¹ := by
    unfold betaB alphaB
    rw [mul_div_mul_right_eq_div, div_eq_mul_inv]
    rfl
  rw [e]
  exact hχ.mul (hμ0.mul hξ).inv

private theorem isSphOff_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (sS : RealMat S) (sT : RealMat T)
    (BS : RealMat S) (BT : RealMat T) (LS : Lat S) (LT : Lat T) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Pset)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (FinPl D)) (hP : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ∈ Sf)
    (hpt : ∀ φ, IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  GlobalTheory.FockSph.isLatVac_pureTensorO_off hvac.2.inf BS BT hvac he hth Sf hP (fun φ => (hpt φ).1) φ

theorem _root_.GlobalTheory.T.unramifiedInnerProductData_definiteBottom_largeGrids : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, Unram W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) X.rA.Λ X.rW.Λ (GlobalTheory.BottomIPData.sfB G t) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  have hpt := GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hψ hθ cS cT X.rA.B X.rW.B hf hv
  have hs := isSphOff_pureTensorO (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.rA.Λ X.rW.Λ
    h.isVac (h.idem t) (h.fst t) (sfB G t) (fun PP hPP => under_mem_sfB G t hPP) hpt P
  exact ⟨GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1, h.rigW.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2,
    unrOff_betaB_div_alphaB G hL i j t, hs, hs⟩

end GlobalTheory.BottomIPData

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomLoc

open GlobalTheory.BottomIPData

private theorem rcoef_one {D : D7} (V : HSp D) (m : Measure (GA D V)) (hm : m.IsHaarMeasure) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ g, rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = c := by
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas V
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure m ν)
  refine ⟨((m 𝓕).toReal : ℂ), ?_, fun g => ?_⟩
  · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h𝓕'.measure_ne_zero (NeZero.ne m),
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm h𝓕').ne⟩)
  · have e : rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = ∫ _ in 𝓕, (1 : ℂ) * conj (1 : ℂ) ∂m :=
      GlobalTheory.AutomorphicL2Unitary.pet_eq h𝓕' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    rw [e]
    simp [Measure.real]

private def topPol (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ) : MvPolynomial (FVar D d a) ℂ :=
  ∏ τ, (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, Fin.castLE h i, i') : MvPolynomial (FVar D d a) ℂ)).det ^ n τ

private theorem topPol_ne_zero (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ) : topPol D h n ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.eval fun p : FVar D d a => if p.2.1.1 = p.2.2.1 then (1 : ℂ) else 0) h0
  rw [topPol, map_prod, map_zero, Finset.prod_eq_one] at this
  · exact one_ne_zero this
  · intro τ _
    rw [map_pow, RingHom.map_det]
    have e : (MvPolynomial.eval fun p : FVar D d a => if p.2.1.1 = p.2.2.1 then (1 : ℂ) else 0).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, Fin.castLE h i, i') : MvPolynomial (FVar D d a) ℂ)) = 1 := by
      ext i i'
      simp [Matrix.one_apply, Fin.ext_iff]
    rw [e, Matrix.det_one, one_pow]

private theorem substF_topPol (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ)
    (g : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g (topPol D h n) =
      (∏ τ, (g τ).det ^ n τ) • topPol D h n := by
  unfold topPol
  have key : ∀ (τ : D.what₂.Tau) (r : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (g τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ r
    rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : ℂ →+* MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ), mul_comm,
      ← Matrix.det_mul]
    congr 1
    ext1 i i'
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.CompactHowe.substF_X, Matrix.one_apply]
    rw [Finset.sum_eq_single (r i)]
    · simp [mul_comm]
    · intro b _ hb
      simp [hb]
    · simp
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, key τ (Fin.castLE h), mul_pow, map_pow]

private theorem conj_transpose_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (h : uᴴ * u = 1) :
    (((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * u * 1)⁻¹)ᵀ.map (starRingEnd ℂ) = u := by
  rw [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_eq_left_inv h]
  ext i j
  simp [Matrix.conjTranspose_apply]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}

private theorem f_theta (hX : IsBottomTri W i j X) (t : T) : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
  GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.fst t) hX.is.isVac.2.theta

private theorem f_fock (hX : IsBottomTri W i j X) (t : T) (τ : D.what₂.Tau) :
    IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) :=
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
  GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hX.is.isVac.1.1.1 hX.is.isVac.2.inf ho.infPart_eq ho.conj.infPart_eq (hX.is.fst t)
    hX.is.isVac.2.theta (f_theta hX t) (hX.is.isVac.2.fock τ)

set_option maxHeartbeats 1000000 in

private theorem real_fix (hX : IsBottomTri W i j X) (t : T) (hr : A.rank ≤ WW.rank) (n : D.what₂.Tau → ℕ)
    (hn : ∀ τ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n τ : ℚ) + (WW.rank : ℚ) / 2))
    {k : GA D (GlobalTheory.Grid.neg A)} (hk : k ∈ GinfC (GlobalTheory.Grid.neg A)) :
    (X.ω t).toSgn true (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
      (topPol D hr n)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) := by
  have h := isBottomTri_is hX
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hW := h.weil t
  have hf := f_theta hX t
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t) := fun ρ => by
    have := f_fock hX t ρ
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  have hgA : ∀ τ, gramAt D A τ = 1 := fun τ => by rw [gramAt, hX.std.1]; simp
  have hgW : ∀ τ, gramAt D WW τ = 1 := fun τ => by rw [gramAt, hX.stdW.1]; simp
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [e1, e2, e3, e4]
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ _ τ hθ hW.hecS hW.resS
  choose e he using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecS hW.resS (ha τ)
  let k₀ : GA D A := GlobalTheory.Grid.ofSgn true A k
  have hu : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A k₀))ᴴ * compAt W.θ τ (Formalism.L2.Theta.mt A k₀) = 1 := fun τ => by
    have e : (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).conjTranspose * (gramAt D A τ) * compAt W.θ τ (Formalism.L2.Theta.mt A k₀) =
      gramAt D A τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ A k₀ τ
    rwa [hgA, Matrix.mul_one] at e
  have key := GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ A WW _ _ ((X.ω t).toSgn true) hW hθ (fun _ => 1) (fun _ => 1)
    (fun τ => by rw [hgA]; simp) (fun τ => by rw [hgW]; simp) a (fun τ => (n τ : ℚ) + (WW.rank : ℚ) / 2) ha
    hn (fun τ => e τ - A.rank) (fun τ => -(n τ : ℤ))
    (fun τ => by push_cast; rw [he τ]; show _ + (A.rank : ℚ) / 2 - _ = _; ring)
    (fun τ => by push_cast; ring) (X.f t) hf hv k hk 1 (one_mem _) (topPol D hr n)
  have c1 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.JointHarm.compAt_mt_one' W.θ τ WW
  have ck : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k) = compAt W.θ τ (Formalism.L2.Theta.mt A k₀) := fun τ => rfl
  have s1 : (fun τ => (((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) *
      (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ).map (starRingEnd ℂ)) = fun _ => 1 := by
    funext τ
    show ((1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * 1).map (starRingEnd ℂ) = 1
    rw [c1, inv_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have s2 : (fun τ => (((((fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹ *
      compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k) * (fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹)ᵀ).map
        (starRingEnd ℂ)) = fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A k₀) :=
    funext fun τ => conj_transpose_inv (hu τ)
  rw [s1, s2, substF_topPol, map_smul, smul_smul, ← Finset.prod_mul_distrib] at key
  have hone : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k)).det ^ (-(n τ : ℤ)) *
      (compAt W.θ τ (Formalism.L2.Theta.mt WW 1)).det ^ (e τ - A.rank) *
        (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).det ^ n τ) = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero
    rw [ck, c1, Matrix.det_one, _root_.one_zpow, mul_one, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hne)]
  rw [hone, one_smul] at key
  exact key

private theorem exists_weights (hX : IsBottomTri W i j X) (t : T) {a b : D.what₂.Tau → ℚ}
    (h : ∀ τ, HasInfExp D (alphaB L i j t) τ (a τ) ∧ HasInfExp D (betaB G i j) τ (b τ) ∧
      2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ)) :
    ∃ n : D.what₂.Tau → ℕ, ∀ τ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n τ : ℚ) + (WW.rank : ℚ) / 2) := by
  have hW := (isBottomTri_is hX).weil t
  have hd : WW.rank = SqNum.botBig D i j + SqNum.botSmall D i j := by rw [← hX.is.rank, hX.rank, hX.rank']
  have key : ∀ τ, ∃ n : ℕ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n : ℚ) + (WW.rank : ℚ) / 2) := fun τ => by
    obtain ⟨h1, h2, h3⟩ := h τ
    have h4 := GlobalTheory.RealQuot.hasInfExp_div D _ _ τ _ _ h1 h2
    obtain ⟨e, he⟩ := GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecT hW.resT h4
    rw [← hd] at h3
    have h5 : (WW.rank : ℤ) ≤ e := by
      have : ((WW.rank : ℤ) : ℚ) ≤ (e : ℚ) := by push_cast; linarith
      exact_mod_cast this
    refine ⟨(e - WW.rank).toNat, ?_⟩
    have h6 : (((e - WW.rank).toNat : ℕ) : ℚ) = (e : ℚ) - WW.rank := by
      have := Int.toNat_of_nonneg (sub_nonneg.2 h5)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
    convert h4 using 1
    rw [h6, he]; ring
  choose n hn using key
  exact ⟨n, hn⟩

private theorem chars_unram {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (hu : GlobalTheory.LFun.UnrOff (betaB G i j / alphaB L i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)))
    (v : FinPl D) (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (betaB G i j) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (betaB G i j / alphaB L i j t) v := by
  classical
  have hS : v ∉ sfB G t := fun h => by
    obtain ⟨w, hw, e⟩ := Finset.mem_image.1 h
    exact hv w hw e
  have h0 : v ∉ G.pl.S0 := fun h => by
    have hw : G.pl.w v ∈ locPl G t := by
      unfold locPl GlobalTheory.ChiGrid.Places.W0
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
    exact hv _ hw (G.pl.under_w h)
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.ch.chi (D.R.m - i)) v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w (by rwa [hw]))
  have hη : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D L.eta v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  refine ⟨fun x a b c d => ?_, GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => hu w ?_⟩
  · rw [betaB, MonoidHom.mul_apply, MonoidHom.pow_apply, hχ x a b c d, hη x a b c d, one_pow, one_mul]
  · show w.under (𝓞 D.host.F) ∉ sfB G t
    rwa [hw]

private theorem fin_fix {μ₀ : T} (hL : L.Is μ₀) (hX : IsBottomTri W i j X) (t : T)
    (hu : GlobalTheory.LFun.UnrOff (betaB G i j / alphaB L i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)))
    {k : GA D (GlobalTheory.Grid.neg A)} (hk : k ∈ GfC (GlobalTheory.Grid.neg A)) (hk' : k ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) :
    (X.ω t).toSgn true (k, 1) (X.f t) = X.f t := by
  have h := isBottomTri_is hX
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (betaB G i j) (betaB G i j / alphaB L i j t) ((X.ω t).toSgn true) := h.weil t
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have sdW : IsSelfDualC WW X.rW.Λ := h.rigW.1
  have he := h.idem t
  have hloc : ∀ v, proj D.sp.cm.sig (GlobalTheory.Grid.neg A).gram v k ∈ stabLoc D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ v :=
    fun v => hk' v (Finset.notMem_empty v)
  have hSt : Lev.finE (GlobalTheory.Grid.neg A) k ∈ Formalism.L2.DIV.St X.rA.β :=
    (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D (GlobalTheory.Grid.neg A) X.rA.β X.rA.Λ h.rigA.2.1 k).2 hloc
  have hid : ∀ w ∈ locPl G t, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have hvac := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW sdA sdW (locPl G t) hid (GlobalTheory.LevelPlaces.under_injOn he)
    (chars_unram hL t hu) k hk 1 (one_mem _)
    ((mem_levelOpen_iff_latHat D.sp.cm.sig (GlobalTheory.Grid.neg A).gram sdA.1.fg k).1 (mem_levelOpen.2 hloc))
    ((mem_levelOpen_iff_latHat D.sp.cm.sig WW.gram sdW.1.fg 1).1 (one_mem _))
    X.vac h.isVac.2.theta h.isVac.2.lat
  have hy := UpperTheory.isUnitDet_prod_detIdl_of_mem_St D (GlobalTheory.Grid.neg A) X.rA.β (X.e t) (locPl G t) he k hSt
  have hΦ := UpperTheory.stdFst_actO_of_mem_stabilizer D (GlobalTheory.Grid.neg A) WW X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
    (X.ideal (locPl G) t) he k hSt _ hy
  have d1 : ∀ w, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) WW 1 = 1 := fun w => by
    unfold GlobalTheory.RowVacScalar.detIdl; split_ifs <;> simp
  have hc : (∏ w ∈ locPl G t, ((splitFacO (betaB G i j) (betaB G i j / alphaB L i j t)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) (GlobalTheory.Grid.neg A) k)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) WW 1) : Circle) : ℂ)) =
      (((alphaB L i j t / betaB G i j) (∏ w ∈ locPl G t,
        GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) (GlobalTheory.Grid.neg A) k) : Circle) : ℂ) := by
    rw [map_prod]
    refine Eq.trans ?_ (map_prod Circle.coeHom _ _).symm
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [d1, splitFacO, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
    rfl
  rw [hc] at hvac
  have key := GlobalTheory.SchrMove.smul_om_eq D W.ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW sdA sdW (X.e t)
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) k 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ sdA sdW h.rigA.2.1 h.rigW.2.1 k 1 hSt
      (by rw [map_one]; exact one_mem _))
    X.vac _ (X.f t) _ _ h.isVac.2.theta (h.fst t) (Circle.coe_ne_zero _) hvac hΦ
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

private theorem std_isSB (hX : IsBottomTri W i j X) (t : T) :
    IsSBHalf (X.e t) (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (alphaB L i j t / betaB G i j) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β) := by
  have h := isBottomTri_is hX
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have sdW : IsSelfDualC WW X.rW.Λ := h.rigW.1
  have he := h.idem t
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A) sdA.1 sdW.1 X.rA.β X.rW.β
  exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (h.weil' t).hecT.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW
    X.rA.β X.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) sdA.1.fg sdW.1.fg X.rA.β X.rW.β)
    ⟨K, hK, fun u hu => hC u (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_idemSum he) hu)⟩

private theorem f_ne_zero (hX : IsBottomTri W i j X) (t : T) : X.f t ≠ 0 := by
  have h := isBottomTri_is hX
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have he := h.idem t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h.fst t
  obtain ⟨x, hx⟩ := UpperTheory.exists_stdFst_ne_zero_of_rank_le D A WW X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
    (X.ideal (locPl G) t) (h.rank ▸ Nat.le_add_right _ _) he
  rw [hall Tm hTm]
  exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ (X.e t) X.vac _ Tm h.isVac.1 sdA h.rigW.1
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm
    (GlobalTheory.Core.Rk.IP.Model.isSphOff_of_vac h.isVac ∅).2.2 (std_isSB hX t) fun h0 => hx (congrFun h0 x)

private theorem pt_theta (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) :
    IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
  (GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1)
    (fun τ => (hX.is.rigW.2.2 τ).1) X.rA.B X.rW.B (f_theta hX t) (f_fock hX t) P).1

private theorem gramAt_neg (hX : IsBottomTri W i j X) (τ : D.what₂.Tau) : gramAt D (GlobalTheory.Grid.neg A) τ = -1 := by
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [gramAt, e, hX.std.1]
  ext a b
  simp [Matrix.one_apply, apply_ite]

private theorem pt_ne_zero (hX : IsBottomTri W i j X) (t : T) {P : PolF D WW.rank A.rank} (hP : P ≠ 0) :
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P ≠ 0 := by
  have h := isBottomTri_is hX
  choose pW hpW using fun τ => (h.rigW.2.2 τ).2
  have hA : ∀ τ, IsONBasis (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) (X.rA.B τ) 0 := fun τ => by
    refine ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩
    · rw [gramAt_neg hX, (hX.std.2.2 τ).2]
      ext a b
      simp [Matrix.one_apply, Matrix.diagonal_apply, apply_ite]
    · rw [(hX.std.2.2 τ).1, (hX.std.2.2 τ).2]
      ext a b
      simp [Matrix.one_apply, Matrix.diagonal_apply, apply_ite]
  have hinj := GlobalTheory.FockPolyInj.pureTensorO_injective_of_on W.ψ W.θ (GlobalTheory.Grid.neg A) WW h.isVac.1 h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B (fun _ => 0) pW hA hpW (X.f t) (f_theta hX t) (f_fock hX t) (f_ne_zero hX t)
  exact fun h0 => hP (hinj (h0.trans (map_zero _).symm))

private theorem wcoef_off (hX : IsBottomTri W i j X) (t : T) {ν : Measure (WO (GlobalTheory.Grid.neg A) WW)} {𝓕 : Set (WO (GlobalTheory.Grid.neg A) WW)}
    (hν : IsCovolOne (ratL WW (GlobalTheory.Grid.neg A)) ν 𝓕) (P : PolF D WW.rank A.rank) {g : GA D (GlobalTheory.Grid.neg A)}
    (hg : g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) (hn : g ∉ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) :
    wcoef ((X.ω t).toSgn true) ν 𝓕
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P)
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g = 0 := by
  classical
  have h := isBottomTri_is hX
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (betaB G i j) (betaB G i j / alphaB L i j t) ((X.ω t).toSgn true) := h.weil t
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have he := h.idem t
  have hint : ∀ v, (∀ PP ∈ locPl G t, PP.under (𝓞 D.host.F) ≠ v) →
      proj D.sp.cm.sig (GlobalTheory.Grid.neg A).gram v g ∈ stabLoc D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ v := fun v hv =>
    hg v fun hm => by
      obtain ⟨w, hw, e⟩ := Finset.mem_image.1 hm
      exact hv w hw e
  have hsupp := fun x hx => by_contra fun hx' => hn fun v _ =>
    (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D (GlobalTheory.Grid.neg A) X.rA.β X.rA.Λ h.rigA.2.1 g).1
      (UpperTheory.finiteComponent_mem_stabilizer_of_standardSection_ne_zero D (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
        (X.ideal (locPl G) t) sdA h.rigA.2.1 (show A.rank ≤ WW.rank from h.rank ▸ Nat.le_add_right _ _) he g hint x hx hx') v
  obtain ⟨n, a, y, h0, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D W.ψ (GlobalTheory.Grid.neg A) WW hW.std X.rA.Λ X.rW.Λ sdA h.rigW.1
    (locPl G t) (X.e t) he X.vac _ (X.f t) (std_isSB hX t) (h.fst t) g hsupp
  have k1 := GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hW.std h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (f_theta hX t) n a y (fun l => (h0 l).1) P
  have k2 := GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hW.std h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (f_theta hX t) n (fun l => conj (a l))
    (fun l => actO (GlobalTheory.Grid.neg A) WW g⁻¹ 1 (-(y l))) (fun l => (h0 l).2) P
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ hW ν 𝓕 hν _ (pt_theta hX t P) g n a y
    (k1.1.trans (by rw [h1])) (k2.1.trans (by rw [h2]; exact k2.2))

private theorem openOff_eq (hX : IsBottomTri W i j X) (Λ : Lat (GlobalTheory.Grid.neg A)) {a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)}
    (ha : IsMaj (GlobalTheory.Grid.neg A) a)
    (ha' : ∀ τ, (compAt W.θ τ a.1)ᴴ * (gramAt D (GlobalTheory.Grid.neg A) τ * (-X.rA.s τ)) * compAt W.θ τ a.1 = 1) :
    openOff (GlobalTheory.Grid.neg A) Λ ∅ = levelAll D.sp.cm.sig (GlobalTheory.Grid.neg A).gram Λ a := by
  have h1 : ∀ τ, frameInv W.θ (GlobalTheory.Grid.neg A) a τ = -1 := fun τ => by
    have h3 := ha' τ
    rw [gramAt_neg hX, (hX.std.2.2 τ).1, neg_mul_neg, Matrix.mul_one, Matrix.mul_one] at h3
    rw [frameInv, mul_eq_one_comm.1 h3, gramAt_neg hX, Matrix.one_mul]
  ext g
  rw [SetLike.mem_coe, mem_levelAll]
  refine ⟨fun hg => ⟨fun v => hg v (Finset.notMem_empty v), (placeOf_bijective D).2.forall.2 fun τ => ?_⟩,
    fun hg v _ => hg.1 v⟩
  refine (ha.mem_stabArch_iff hX.is.isVac.2.inf τ g).2 ?_
  rw [h1]
  exact Commute.neg_one_right _

end GlobalTheory.BottomLoc

open GlobalTheory.BottomIPData GlobalTheory.BottomLoc in

theorem _root_.GlobalTheory.T.definiteBottom_localDoublingIntegral_converges : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)), Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W →
  ∃ P : PolF D WW.rank A.rank, ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
    (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
      (integrand ((X.ω t).toSgn true) m νW 𝓕W X.rA.Λ a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (GlobalTheory.BottomIPData.sfB G t)) m) ∧
    ∫ g in openOff (GlobalTheory.Grid.neg A) X.rA.Λ (GlobalTheory.BottomIPData.sfB G t), wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H0 : GBig fun {_} _ Lc _ _ μ₀ _ _ _ => Lc.Is μ₀ :=
    ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ _ _ _ _ _ _ _ _ hL _ => hL⟩⟩
  refine gbig_mono (gbig_and H0 (gbig_and GlobalTheory.T.unramifiedInnerProductData_definiteBottom_largeGrids GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids)) ?_
  intro D T Lc sc G μ₀ C x b ⟨hL, H1, H2⟩ W i j A A' WW X hX t cA a νW 𝓕W hP
  have h := isBottomTri_is hX
  have hr : A.rank ≤ WW.rank := h.rank ▸ Nat.le_add_right _ _
  obtain ⟨ea, eb, hab⟩ := H2 W i j
  obtain ⟨n, hn⟩ := exists_weights hX t (hab t)
  refine ⟨topPol D hr n, fun m hm => ?_⟩
  have hU := H1 W i j A A' WW X hX t (topPol D hr n)
  have hoff := fun g => wcoef_off (g := g) hX t hP.covol (topPol D hr n)
  have hth := pt_theta hX t (topPol D hr n)
  have hne := pt_ne_zero hX t (topPol_ne_zero D hr n)
  have hfix : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, (X.ω t).toSgn true (g, 1)
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) := by
    intro g hg
    have hk := GlobalTheory.LevelNbhd.finPartG_mem_GfC (GlobalTheory.Grid.neg A) g
    have hk' : GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅ := fun v hv => by
      rw [GlobalTheory.SuppLevO.proj_finPartG]; exact hg v hv
    have e : ((g, 1) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g, 1) *
        ((GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g)⁻¹ * g, 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, real_fix hX t hr n hn (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC _ g),
      GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ WW _ _ _ hP.weil W.θ h.isVac.2.inf _ hk 1 (one_mem _) _ _ _ _ _ _
        (f_theta hX t), fin_fix hL hX t hU.unr hk hk']
  generalize pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) = Φ
    at hoff hth hne hfix ⊢
  obtain ⟨c, hc, hrc⟩ := rcoef_one (GlobalTheory.Grid.neg A) m hm
  set c₀ : ℂ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip (GlobalTheory.Grid.neg A) WW νW 𝓕W Φ Φ with hc₀
  have hc0 : c₀ ≠ 0 := by
    have h' := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hP.weil.std hth hne hP.covol
    have e : c₀ = GlobalTheory.RawLift.thetaIP νW 𝓕W Φ Φ := by
      simp only [hc₀, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, GlobalTheory.RawLift.thetaIP, mul_comm (Φ _), Complex.star_def]
    rwa [e]
  have hon : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, wcoef ((X.ω t).toSgn true) νW 𝓕W Φ Φ g = c₀ := fun g hg => by
    simp only [wcoef, hfix g hg, hc₀]
  have hK := openOff_eq hX X.rA.Λ hP.maj hP.maj_eq
  haveI : Submodule.IsLattice D.host.E X.rA.Λ := hU.sdA.1
  have hhgt : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, GlobalTheory.Core.Rk.IP.hgtL (GlobalTheory.Grid.neg A) X.rA.Λ a g = 1 := by
    rw [hK]
    intro g hg
    have := hgtAd_mul (Q := (dblSp (GlobalTheory.Grid.neg A)).gram) (L := X.rA.Λ) (a := a) (isCMExt_host D) 1
      (k := io (GlobalTheory.Grid.neg A) (g, 1)) ((ioH_mem_KAd _).2 ⟨hg, one_mem _⟩)
    simpa [GlobalTheory.Core.Rk.IP.hgtL] using this
  have hKc : IsCompact (openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) := by
    rw [hK]
    exact isCompact_levelAll (isCMExt_host D) _ _ _
  have hKo : IsOpen (openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) := GlobalTheory.Core.Rk.IP.isOpen_openOff _ _ hU.sdA _
  have hOm : MeasurableSet (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff _ _ hU.sdA _).measurableSet
  have hsub : openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅ ⊆ openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t) :=
    fun g hg v _ => hg v (Finset.notMem_empty v)
  have hI : ∀ s : ℂ, Set.EqOn (integrand ((X.ω t).toSgn true) m νW 𝓕W X.rA.Λ a Φ Φ (fun _ => 1) (fun _ => 1) s)
      ((openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅).indicator fun _ => c₀ * c) (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) := by
    intro s g hg
    by_cases hg' : g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅
    · rw [Set.indicator_of_mem hg']
      simp only [integrand, hon g hg', hhgt g hg', hrc, one_npow, mul_one]
    · rw [Set.indicator_of_notMem hg']
      simp only [integrand, hoff g hg hg', zero_mul]
  refine ⟨⟨(A'.rank : ℝ) / 2 - 1, by linarith, ?_⟩, ?_⟩
  · refine IntegrableOn.congr_fun ?_ (hI _).symm hOm
    exact ((integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hKc.measure_ne_top)).integrableOn
  · simp only [← GlobalTheory.Core.Rk.IP.integrand_sZero _ m νW 𝓕W X.rA.Λ a]
    rw [setIntegral_congr_fun hOm (hI _), setIntegral_indicator hKo.measurableSet, Set.inter_eq_right.2 hsub,
      setIntegral_const]
    refine smul_ne_zero ?_ (mul_ne_zero hc0 hc)
    exact ENNReal.toReal_ne_zero.2 ⟨(hKo.measure_pos m ⟨1, GlobalTheory.Core.Rk.IP.one_mem_openOff _ _ _⟩).ne', hKc.measure_ne_top⟩

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem data_exists : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H := gbig_and GlobalTheory.BottomPairData.pair_data (gbig_and GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom (gbig_and GlobalTheory.T.isPolynomialFockThetaVector_definiteBottom (gbig_and GlobalTheory.BottomIPData.unram_bottom (gbig_and GlobalTheory.T.const_one_mem_cuspForms_definiteBottom
    (gbig_and GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom (gbig_and GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom (gbig_and GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom GlobalTheory.T.definiteBottom_localDoublingIntegral_converges)))))))
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ W i j A A' WW X hX hA t
  obtain ⟨cA, a, νW, 𝓕W, hP⟩ := h1 W i j A A' WW X hX hA t
  obtain ⟨par, hpar⟩ := h6 W i j A A' WW X hX t
  obtain ⟨κ, hκ, hL⟩ := h8 W i j A A' WW X hX t par hpar
  obtain ⟨P, hloc⟩ := h9 W i j A A' WW X hX t cA a νW 𝓕W hP
  refine ⟨betaB G i j, betaB G i j / alphaB Lc i j t, fun τ => -X.rA.s τ, X.rW.s, cA, a, νW, 𝓕W, X.rA.Λ, X.rW.Λ,
    sfB G t, par, κ, P, hP, h2 W i j A A' WW X hX t, h3 W i j A A' WW X hX t P, h4 W i j A A' WW X hX t P,
    h5 W i j A A' WW X hX t cA hP.setting, hpar, ?_, hκ, h7 W i j A A' WW X hX t, hL, hloc⟩
  intro v _ k _ g
  rfl

end GlobalTheory.BottomIPData

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_innerProductFormula_data_definite_bottom : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  atlas_forward_decl GlobalTheory.BottomIPData.data_exists
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.RallisBottom

theorem normBig_innerProduct : GlobalTheory.FunPr.Hypotheses₂ → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, ∃ (P : PolF D WW.rank A.rank) (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)) (c : ℂ), c ≠ 0 ∧ ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s := by
  intro hPr
  obtain ⟨CF0, h⟩ := GlobalTheory.T.exists_innerProductFormula_data_definite_bottom
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩

  have hX₁ := isBottomTri_posSig hX
  obtain ⟨χA, χB, sA, sB, cA, a, νW, 𝓕W, LA, LB, Sf, par, κ, P, hP, hw, hF, hU, h1, hpar, hsph, hκ, hdS, hL, hloc⟩ :=
    h C hC D large₂ he hx hR T Lc μ₀ hμ G W i j (posSig A) A' WW (Tri.posSig X) hX₁ (sigOK_posSig hX) t
  obtain ⟨ν, 𝓕, hν, h𝓕, hvol⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero W i j (posSig A) A' WW (Tri.posSig X) hX₁
  obtain ⟨m, hm, hdict⟩ := GlobalTheory.T.definiteBottom_thetaIntegral_normSq_eq_petersson W i j (posSig A) A' WW (Tri.posSig X) hX₁ t P ν 𝓕 hν h𝓕
  obtain ⟨hs₁, hZ⟩ := hloc m hm
  obtain ⟨-, -, -, hH⟩ := GlobalTheory.T.hecke_form_anisotropic_rallis hPr D W.ψ W.θ (GlobalTheory.Grid.neg (posSig A)) WW χA χB sA sB A'.rank cA a _ νW 𝓕W hP hw LA LB Sf _ _ hF hF hU
    m ν hm hν _ h1 _ h1 par hpar hsph hs₁
  refine ⟨P, ν, 𝓕, volQ WW ν * κ * _,
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hvol) hκ) hZ, hν, h𝓕, fun Λ hΛ => ?_⟩
  show ((∫ h in 𝓕, ‖(Tri.posSig X).I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = _
  rw [hdict, hH _ (hL Λ hΛ), mul_right_comm κ, mul_div_cancel_right₀ _ hdS]
  ring

end GlobalTheory.RallisBottom
end
