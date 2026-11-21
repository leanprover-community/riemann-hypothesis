import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedOfFunctor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemKLOfTrivLam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNbhd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UOfIsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleHomCompSquareZeroSection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinCohStOfCmpSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteChains
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.D2Apply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFirstCohomologyBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCohomologyComparisonSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferSumProjectionsDegreeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedFormNaturality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFunctionalTwoFormNaturality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedStOfTwoFormCohSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPairingIotaTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfRTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormComponentOfWedgeClassZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BilinearStatementWithDescentHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfStOfSpreads
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstHypercohomologyBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAndFinrankLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFieldOfField
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.EqZeroOfExteriorPowerMapAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfSmulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VbOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeFirstCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.ClosedPoints.IsClosedPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyDimensionLowerBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankOverField
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace MainStatements.Hodge.Free

structure Chapters : Prop where
  dict : DictSt
  cx : CxSt
  low : DictSt → LowSt
  htpy : CxSt → HtpySt
  qcalc : CxSt → QCalcSt
  fubini : CxSt → FubiniSt
  affacyc : CxSt → HtpySt → AffAcycSt
  descent : CxSt → HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt
  sysbc : DescentSt → LowSt → SysBCSt
  stein : SteinSt
  cot : CotSt
  par : CotSt → SteinSt → ParSt
  axo : DescentSt → LowSt → SysBCSt → SteinSt → AxOSt
  axform : CotSt → SteinSt → ParSt → AxFormSt
  cmp : CxSt → CmpSt
  fincoh : CmpSt → FinCohSt
  van : CxSt → CmpSt → VanSt
  perfnoeth : CxSt → DictSt → PerfNoethSt
  perfbase : PerfBaseSt
  perfh1 : PerfectH1BaseChange
  perfh2 : PerfectH2FromFibres
  wedgeof : LowSt → WedgeOfSt
  hopffield : CxSt → DictSt → LowSt → HopfFieldSt
  oneform : OneFormCohSt
  twoform : TwoFormCohSt
  closed : TwoFormCohSt → ClosedSt
  lift : OneFormCohSt → TwoFormCohSt → LiftSt
  alt : OneFormCohSt → TwoFormCohSt → AltSt
  hyp2 : OneFormCohSt → TwoFormCohSt → H2FieldHypothesis
  hopf : HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt → LowSt → AxOSt → HopfSt
  bi : DescentSt → LowSt → SteinSt → ParSt → AxOSt → AxFormSt → BiSt
  formbc : SteinSt → ParSt → FormBCSt
  oside : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange → PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt
  perf : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt → PerfBaseSt → PerfSt
  hopfle : CxSt → DictSt → LowSt → HopfLeSt
  h1le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe
  wedgefield2 : DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt
  noprim : DescentSt → LowSt → SteinSt → AxOSt → WedgeFieldSt → NoPrimSt
  smalllift : DescentSt → LowSt → SysBCSt → AxOSt → NoPrimSt → SmallLiftSt
  perfvb : PerfVBSt
  h1all : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle
  flatbc : DescentSt → LowSt → SysBCSt → FlatBCSt
  feweqn : FewEqSt
  stalkdim : StalkDimSt
  h1ge : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim
  h1field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim
  final : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt → GlobalTheory.Published.AbelianHodgeDeRham

theorem wedge_alt {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (h : Wedge F)
    (c : H1 F) : cup F c c = 0 := by
  obtain ⟨e, he⟩ := h
  rw [← he, (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![c, c] (i := 0) (j := 1) rfl (by decide), map_zero]

theorem Chapters.print (h : Chapters) (h₁ : GlobalTheory.SpreadingModels.SchemeModels)
    (h₂ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f)) (h₃ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f))
    (ht : PositivityTheory.ObstructionTrivialLocus.TrivLocus) (hk : PositivityTheory.ObstructionTrivialLocus.KFinite) : GlobalTheory.Published.AbelianHodgeDeRham := by
  have low := h.low h.dict
  have htpy := h.htpy h.cx
  have qc := h.qcalc h.cx
  have fub := h.fubini h.cx
  have aff := h.affacyc h.cx htpy
  have des := h.descent h.cx htpy qc fub aff
  have sbc := h.sysbc des low
  have par := h.par h.cot h.stein
  have axo := h.axo des low sbc h.stein
  have axf := h.axform h.cot h.stein par
  have cmp := h.cmp h.cx
  have hopf := h.hopf htpy qc fub aff des low axo
  have perf := h.perf h₁ h₂ h₃ des low sbc (h.fincoh cmp) (h.perfnoeth h.cx h.dict) h.perfbase
  have van := h.van h.cx cmp
  have fbc := h.flatbc des low sbc
  have h1f := h.h1field fbc (h.h1le des low h.stein van hopf (h.hopfle h.cx h.dict low))
    (h.h1ge ht hk fbc h.feweqn h.stalkdim)
  have wf := h.wedgefield2 des low h.stein h1f van hopf (h.hopffield h.cx h.dict low)
  have h1 := h.h1all des low sbc perf h.stein h1f
    (h.smalllift des low sbc axo (h.noprim des low h.stein axo wf)) h.perfvb
  obtain ⟨obc, w⟩ := h.oside des low sbc perf h.stein h1 wf hopf h.perfh1 h.perfh2 (h.wedgeof low)
  have bi := h.bi des low h.stein par axo axf
  have fr : AllAb fun _ _ A _ _ ↦ Framed (OAff A.hom) := fun R _ A _ g hA hg ↦
    ⟨h.stein R A g hA hg, (par R A g hA hg).1, (par R A g hA hg).2.1, (par R A g hA hg).2.2.1⟩
  have deg : DegenSt := fun R _ A _ g hA hg ↦
    have c := h.closed h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg)
    ⟨c, h.lift h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) c⟩
  have wh : WedgeHypSt := fun R _ A _ g hA hg ↦
    h.hyp2 h.oneform h.twoform R _ _ (fr R A g hA hg) (h1 R A g hA hg).1 (h1 R A g hA hg).2.1 (deg R A g hA hg).1
      (deg R A g hA hg).2 (w R A g hA hg)
      (h.alt h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) (deg R A g hA hg).1 (deg R A g hA hg).2
        (wedge_alt (w R A g hA hg)))
  exact h.final h.stein par h1 deg wh obc (h.formbc h.stein par)

theorem Chapters.h1Le (h : Chapters) : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  have low := h.low h.dict
  have htpy := h.htpy h.cx
  have qc := h.qcalc h.cx
  have fub := h.fubini h.cx
  have aff := h.affacyc h.cx htpy
  have des := h.descent h.cx htpy qc fub aff
  have axo := h.axo des low (h.sysbc des low) h.stein
  exact h.h1le des low h.stein (h.van h.cx (h.cmp h.cx)) (h.hopf htpy qc fub aff des low axo)
    (h.hopfle h.cx h.dict low)

end MainStatements.Hodge.Free
end

section
namespace MainStatements.Hodge.Free

theorem abelianHodgeDeRham' : Chapters where
  dict := GlobalTheory.CompanionTheory.Dict.dictSt
  cx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
  low := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt
  htpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt
  qcalc := GlobalTheory.CompanionTheory.QCalc.qCalcSt
  fubini := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
  affacyc := GlobalTheory.CompanionTheory.AffAcyc.main
  descent := GlobalTheory.CompanionTheory.Descent.descentSt
  sysbc := GlobalTheory.CompanionTheory.SysBC.sysBCSt
  stein := GlobalTheory.CompanionTheory.Hodge.stein_holds
  cot := GlobalTheory.CompanionTheory.Cot.cotSt
  par := GlobalTheory.CompanionTheory.AbForms.parSt
  axo := GlobalTheory.CompanionTheory.Axis.axOSt
  axform := GlobalTheory.CompanionTheory.AxForm.axFormSt
  cmp := GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt
  fincoh := GlobalTheory.CompanionTheory.Hodge.finCohSt_of_cmpSt
  van := GlobalTheory.CompanionTheory.Hodge.vanSt
  perfnoeth := GlobalTheory.CompanionTheory.PerfN.perfNoeth
  perfbase := GlobalTheory.CompanionTheory.PerfExt.main
  perfh1 := GlobalTheory.CompanionTheory.PerfectFirstCohomology.perfect_first_cohomology_base_change
  perfh2 := GlobalTheory.CompanionTheory.PerfectSecondCohomology.perfect_second_cohomology_from_fibres
  wedgeof := GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low
  hopffield := GlobalTheory.CompanionTheory.HopfC.hopfFieldSt
  oneform := GlobalTheory.CompanionTheory.OneFormCoh.oneFormCohSt
  twoform := GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
  closed := GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
  lift := GlobalTheory.CompanionTheory.Hodge.LiftO.lift_of_forms
  alt := GlobalTheory.CompanionTheory.HodgeAlt.altSt
  hyp2 := GlobalTheory.CompanionTheory.HypWedge.hyp2St
  hopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt
  bi := GlobalTheory.CompanionTheory.GroupLaw.bilinear_statement_with_descent_hypotheses
  formbc := GlobalTheory.CompanionTheory.Hodge.FormBC.formBC
  oside := GlobalTheory.CompanionTheory.HodgeO.oBC_wedge
  perf := GlobalTheory.CompanionTheory.PerfModels.perfSt_of_spreads
  final := GlobalTheory.CompanionTheory.HodgeAssembly.abelianHodgeDeRham_of_statements
  hopfle := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt
  h1le := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le
  wedgefield2 := GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo.wedgeField_of_field
  noprim := MainStatements.Hodge.Pf.noprim
  smalllift := GlobalTheory.CompanionTheory.SmallLift.main
  perfvb := GlobalTheory.CompanionTheory.PerfVB.perfVB
  h1all := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle.first_cohomology_vector_bundle_rank
  flatbc := GlobalTheory.CompanionTheory.Hodge.FlatBase.flatBC
  feweqn := GlobalTheory.CompanionTheory.FewEq.fewEq
  stalkdim := MainStatements.Hodge.Pf.stalkdim
  h1ge := GlobalTheory.CompanionTheory.FirstCohomologyLowerBound.first_cohomology_dimension_lower_bound
  h1field := GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField.first_cohomology_rank_over_field

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham :=
  abelianHodgeDeRham'.print GlobalTheory.CompanionTheory.NoethApprox.schemeModels GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
    GlobalTheory.CompanionTheory.TrivLoc.trivLocus GlobalTheory.CompanionTheory.KLFinite.kFinite

end MainStatements.Hodge.Free
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR FubiniStudyChowHeightFormula₂.Hdr

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Free

theorem page_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) : AbelianDeRhamPage := by
  intro R _ A _ g hA hg
  obtain ⟨⟨a1, a2, a3⟩, hw, ⟨f1, f2, f3⟩, ⟨o1, o2, -⟩, ⟨hcl, hinj, hsurj⟩, hbc⟩ := H R A g hA hg
  let i := formEquiv A.hom hcl hinj
  have hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom) := (cechHodgeFiltration_eq_range A.hom).symm
  let q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom :=
    (Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)
  refine ⟨hw, ⟨⟨a1, a2⟩, a3⟩, ⟨hcl, hinj, ⟨⟨Module.Finite.equiv i, Module.Projective.of_equiv i⟩,
      fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv i, f3]⟩,
      Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm⟩,
    ⟨by rw [hk]; exact LinearMap.exact_subtype_ker_map _, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨b1, ⟨e, he⟩, b3⟩ := hbc R' X' s' φ h
  refine ⟨b1, ?_, b3⟩
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  obtain ⟨-, -, -, -, ⟨hcl', hinj', -⟩, -⟩ := H R' (Over.mk s') g hA' hg'
  let i' := formEquiv s' hcl' hinj'
  refine ⟨(LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i'), fun c ↦ ?_⟩
  obtain ⟨c, rfl⟩ := i.surjective c
  have k : ((LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i')) (1 ⊗ₜ i c) = i' (e (1 ⊗ₜ c)) := by
    simp
  rw [k]
  exact IsPullForm.cl (ω := ⟨c, hcl ▸ trivial⟩) (ω' := ⟨e (1 ⊗ₜ c), hcl' ▸ trivial⟩) (he c)

end MainStatements.Hodge.Free
end
end

section
namespace MainStatements.Hodge.Free

theorem abelianDeRhamPage : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage := page_of_hodge abelianHodgeDeRham

end MainStatements.Hodge.Free
end
