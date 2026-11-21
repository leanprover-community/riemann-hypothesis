import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiterature
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsOfLiterature
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SpehInfinitesimalCharacterOfResidual
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGL
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepresentationTheoryHypotheses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfPublishedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweDualityGLOfMinguezThetaCorrespondence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PublishedInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OfStar
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegmentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeLAdicParameterAboveOfAlgebraicCharacterWD
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAbove
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveLOfRowPublished
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanCompatOfLiterature
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalParameterStableAtUnramifiedPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemInputsAtThirdPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtInputOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigISupEqTopOfSep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointStatementsOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recTExists_of_published_inputs : _root_.UpperTheory.Zero.LLC.RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → _root_.UpperTheory.Zero.LLC.RecTExists := by
  first | exact @_root_.UpperTheory.One.M.New.llOf_alt | exact _root_.UpperTheory.One.M.New.llOf_alt | (intros; apply _root_.UpperTheory.One.M.New.llOf_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
omit [IsCMField E] [Fact l.Prime] in
theorem star_guard'_alt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (k : NcW (rc (algNorm σ))) :
    (IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ UpperTheory.GalStar.Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hrc
  have e : (rc (algNorm σ)).lpDim = a := H.dim _
  have := star_guard k
  rwa [e] at this
theorem isGalU_of_props_alt {π : CuspSub E a} (χ : HChar (maximalRealSubfield E)) {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsB _root_.UpperTheory.One.M.recT π ι r wt HT) :
    _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT :=
  ⟨H.cont, H.ss, fun w hl A h rc hrc σ hσ => aw_of_away (H.away w hl A h rc hrc σ hσ), H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have k := H.above P AI T w A h O Bw hj
      ⟨fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).1,
        fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.1, fun σ hσ hs => (k.crys σ hσ hs).1⟩⟩
theorem pairU_of_star_alt (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.PairUAlt := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt χ k⟩
theorem carU_of_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.CarUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  have hpol := isPolarized_of_isCsd hc
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a (by omega) π _ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E _) (hGK E a _) hpol.dual⟩
  refine ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt _ k, fun P AI T w _ A h O _ _ _ Bw hj σ hσ rc hrc n => ?_⟩
  have b := ((k.above P AI T w A h O Bw hj).nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.2
  exact ⟨b.dim, fun _ => (away_nice b n).1, fun _ _ => (away_nice b n).2⟩
theorem field_of_starFull_alt (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : GlobalTheory.Published.LocalConverseGL)
    (_ : GlobalTheory.Published.LanglandsExhaustionGL) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.PairUAlt := _root_.UpperTheory.GalS.pairU_of_star_alt H
theorem ofDual_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.CarUAlt := _root_.UpperTheory.GalS.carU_of_star_alt hGK H
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.GalS
theorem bridgeStar_alt : GlobalTheory.Published.GelfandKazhdanDual → (_root_.UpperTheory.One.M.Row → _root_.UpperTheory.GalS.CarUAlt) ∧ (_root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.GalS.CuspUAlt) :=
  fun hGK => ⟨_root_.UpperTheory.GalS.ofDual_star_alt hGK, _root_.UpperTheory.GalS.cusp_of_pair_alt hGK⟩
end UpperTheory.GalS
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory
theorem heckeLAdicParameterAbove_of_algebraicCharacterWD_alt (H : GlobalTheory.Published.AlgebraicCharacterWD) :
    _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A h O _ _ _ Bw hj ξ hξ rc hrc
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, L⟩ := hOpn) | obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hχ hμ hL w A h O Bw hj ξ hξ a ha]
  exact (L.one ξ hξ.1).symm
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.NRows.HypothesesBridge
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  intro hBZ hBern hGeo hTD hMP hJS hFin hTSI hESS hGK hGRP hCLGD hCP hCC hArt hChA hAlg hBerger hCheb hLL
  have hCSD := _root_.UpperTheory.GalS.bridgeStar_alt hGK
  exact
    { bz := hBZ
      bern := hBern
      geo := hGeo
      unl := GlobalTheory.TotDisjUnlinked.main hTD
      mp := GlobalTheory.depthZeroJacquetInjective_of_admissible hBZ hMP
      js := hJS
      fin := hFin
      gal := hCSD.2 hGRP
      car := _root_.UpperTheory.GalS.carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)
      clo := GlobalTheory.regularAlgebraicPurity_of_clozel hCP hCC
      art := hArt
      chA := hChA
      chP := _root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt hAlg
      berger := hBerger
      cheb := hCheb }
end GlobalTheory.NRows.HypothesesBridge
end
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.published_inputs_combined_alt_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  first | exact @_root_.GlobalTheory.NRows.HypothesesBridge.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.NRows.HypothesesBridge.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.NRows.HypothesesBridge.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem localLanglandsGL_and_purity_at_member_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt → _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' → _root_.UpperTheory.Zero.LLC.RecTExists ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt := by
  intro L A
  have hL : _root_.UpperTheory.Zero.LLC.RecTExists :=
    _root_.GlobalTheory.T.recTExists_of_published_inputs L.llc L.conv L.dzi L.brauer L.chev A.art L.exh L.multi L.cos L.zel L.geo L.bz
  refine ⟨hL, ?_⟩
  have hG : GlobalTheory.GLq.Green := GlobalTheory.GreenBridge.green_of_regular L.green
  exact
    { what₂ := _root_.GlobalTheory.T.published_inputs_combined_alt_alt L.bz L.bern L.geo L.disj L.mp A.js A.fin L.temp L.seg A.gk A.gal A.car
        A.pur A.coh A.art A.chA A.chW A.berger GlobalTheory.Published.chebotarevDegreeOne' hL
      decay := A.decay
      hc := A.hc
      greenC := hG
      green := hG
      zel := L.zel
      ray := A.ray
      rayF := A.ray
      rayA := GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin A.art
      bc := _root_.UpperTheory.BaseChangeIdentities.bridge A.bc L.bern
      gen := _root_.PositivityTheory.Gud.generic_unitary_dual_GL trivial L.sq L.gen L.multi L.cos
      std := L.cos
      cheb := GlobalTheory.Published.cheb_holds
      howe := GlobalTheory.Hk3.howeUnram_holds }
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

section
theorem UpperTheory.GalS.CarUAlt.regAlg : type_of% (@UpperTheory.GalS.carU_of_regular_algebraic_purity) := @UpperTheory.GalS.carU_of_regular_algebraic_purity
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.GalOfCusp
theorem local_global_above_ell_of_cusp_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → _root_.UpperTheory.GalS.CarUAlt :=
  fun H => H.car.regAlg H.clo
end GlobalTheory.GalOfCusp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.ArchFromLit
theorem archimedean_local_langlands_compatibility_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt → _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL := by
  intro hLoc hAut hL
  exact
    { pht := GlobalTheory.PhtCompare.phtCmp
      lp := fun _ _ => ⟨⟨⟩⟩
      cg := fun _ _ _ => ⟨⟨⟩⟩ }
end GlobalTheory.ArchFromLit
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt
set_option maxHeartbeats 2000000 in
theorem locComp_of_isRc_classMapD_cenLoc : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.HeightCounting.HtCard → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → JumpsCard D'.nd D'.naut := by
  intro hL _ hH
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  refine ⟨fun _ => ∅, fun L hB _ => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hs⟩ := hB
  let b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL (withLoc L) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtInput_of l.c.tp l.mt.mt l.c.xi_eq l.c.Q_eq, big := fun _ => ∅, L := L, Sp := Sp, Au := Au, ss := hs,
      eq := rfl }
  exact _root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_of_built_alt hH b l.a.fr l.a.pht
end GlobalTheory.HeightCounting.JumpsSt
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem eventually_eigSpan_of_levelC : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => D'.nd.EigSpan := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  exact ⟨fun _ => ∅, fun L _ => eigSpan_of_record _⟩
end GlobalTheory.HeightCounting.Up
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
namespace PointStatements
section Loc
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem built_anti_alt {big big' : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)} (h : ∀ w, big' w ⊆ big w)
    (hb : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L := by
  obtain ⟨Sp, hA, hs⟩ := hb
  exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
theorem eventuallyOfBuilt_mono_withLoc {P Q : D7 → Prop} (h : ∀ L : LocAll (lay0 D), P (withLoc L) → Q (withLoc L))
    (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q :=
  let ⟨b, hb⟩ := hP; ⟨b, fun L hL => h L (hb L hL)⟩
theorem eventuallyOfBuilt_and {P Q : D7 → Prop} (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) (hQ : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q) :
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P D' ∧ Q D' := by
  classical
  obtain ⟨b1, h1⟩ := hP
  obtain ⟨b2, h2⟩ := hQ
  exact ⟨fun w => b1 w ∪ b2 w, fun L hL => ⟨h1 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_left) hL),
    h2 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_right) hL)⟩⟩
end Loc
theorem residualIrreducibleGood_of_inputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (I : _root_.GlobalTheory.NRows.LinkedInputs hL D) (R : _root_.GlobalTheory.NRows.PointConditions' D) : AutomorphicSideWildInertia.ResidualIrreducibleGood D :=
  _root_.Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime_alt D
    ⟨R.a.tieLab, _root_.GlobalTheory.AdmTame.main_alt_alt_alt D R.a.tie0 R.a.a2 R.a.a5 (_root_.GlobalTheory.TieLabAt.main_alt_alt hL D I.P).2.1⟩
    R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
end PointStatements
end GlobalTheory.HeightCounting.Up
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
namespace PointStatements
section Loc
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
end Loc
theorem aux_residual_aux42_prvZ_of_inputs {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hc : GlobalTheory.Published.HarishChandraFinite)
    (dec : GlobalTheory.Published.CuspRapidDecay) (I : _root_.GlobalTheory.NRows.LinkedInputs hL D) (hJ : JumpsCard D.nd D.naut) :
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ SumRepresentations.Conclusion42 D ∧ SumRepresentations.ConclusionZ D := by
  have R : _root_.GlobalTheory.NRows.PointConditions' D := _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard hPr hc dec hL D I hJ
  have h1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b
  exact ⟨h1.1, _root_.GlobalTheory.HeightCounting.Up.PointStatements.residualIrreducibleGood_of_inputs hL D I R, h1.2.2, (SumRepresentations.multiplicity_statement_iff_reduced D I.isot h1.2.2).2 (_root_.GlobalTheory.T.reducedMultiplicity_of_inputs hL D I R)⟩
end PointStatements
open PointStatements in
theorem ptSt_of_inputs_geometric_compat : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL := by
  intro hP hX hL
  have h := allSt_and (allSt_and (allSt_and (_root_.GlobalTheory.T.eventually_nonempty_inputs_of_level_c hL hP hX) (_root_.GlobalTheory.HeightCounting.JumpsSt.locComp_of_isRc_classMapD_cenLoc hL hP hX.ht))
    (_root_.GlobalTheory.HeightCounting.Up.eventually_eigSpan_of_levelC hL hP)) (_root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat hP hX)
  refine allSt_mono (fun K B f T w P x H l => ?_) h
  obtain ⟨⟨⟨hI, hJ⟩, hE⟩, hS⟩ := H
  refine _root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_mono_withLoc ?_ (_root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_and (_root_.GlobalTheory.HeightCounting.Up.PointStatements.eventuallyOfBuilt_and (hI l) (hJ l)) (hE l))
  rintro L ⟨⟨hI', hJ'⟩, hE'⟩
  exact ⟨fun ho => _root_.GlobalTheory.HeightCounting.Up.PointStatements.aux_residual_aux42_prvZ_of_inputs hP.what₂ hP.hc hP.decay (hI' ho).some (hJ' ho), hE', hS.1⟩
end GlobalTheory.HeightCounting.Up
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
theorem GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL := by
  intro hN hX
  have hS := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS
  obtain ⟨hLoc, hA, hCo, ⟨hToric, -, hT, -, -⟩, -⟩ := hN
  obtain ⟨hL, hPr⟩ := _root_.GlobalTheory.Mem.LiteralAutomorphy.localLanglandsGL_and_purity_at_member_alt hLoc hA
  have hRatio := GlobalTheory.ToricRatioBridge.ratioConj_of_toricRatioConjugates
    (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hT)
  obtain ⟨hkInt, hkTr, hkRead⟩ := GlobalTheory.HeckeMember.heckeInt_transform_readTie
  obtain ⟨hRS, hInt⟩ := GlobalTheory.seriesRatS_and_serInt_of_globalArtin hA.art
  have hSer : SerN := ⟨hS hRS, hInt, hkInt, hkTr, hkRead, hRatio⟩
  have hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis := by
    obtain ⟨hCheb, hDeg1, -, hTC, hCD, hTame, hAdm4, hRay⟩ :=
      GlobalTheory.twist_front_inputs (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hCo.pt) hCo.lf hCo.lt hCo.lfK hCo.ltK hCo.leK
        hA.art
    exact
      { e1 := hCheb, e2 := hTC, e3 := hCD, e4 := hTame, e5 := hCo.lf, e6 := hCo.lt, e7 := hCo.le, e8 := hCo.gf,
        e9 := hCo.ge, e10 := hCo.uo, e11 := hAdm4, e12 := hCo.gw, e13 := hRay, e14 := hDeg1, e15 := hToric,
        e16 := hSer.rat, e17 := hSer.int, e18 := hSer.hkInt, e19 := hSer.hkTr, e20 := hSer.hkRead,
        e21 := hPr.what₂.fin, e22 := hPr.what₂.gal, e23 := hPr.what₂.berger,
        e24 := _root_.GlobalTheory.GalOfCusp.local_global_above_ell_of_cusp_alt hPr.what₂,
        e25 := GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hCo.bk hCo.ltK hCo.leK }
  exact ⟨hE, hPr, hSer, hL, hPr, hSer, _root_.GlobalTheory.ArchFromLit.archimedean_local_langlands_compatibility_alt hLoc hA hL,
    _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt hPr (_root_.GlobalTheory.MtInMain.prN_sMt_alt_alt hPr) hL, _root_.GlobalTheory.HeightCounting.Up.ptSt_of_inputs_geometric_compat hPr hX hL, _root_.GlobalTheory.HeightCounting.Up.cuspParameter_at_member_alt hPr hL⟩
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL := by
  first | exact @_root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat | exact _root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat | (intros; apply _root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat <;> assumption)
end
end
end
