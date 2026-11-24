module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CobApplyOfDeg
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.Spread
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AlgCoreSubOfAlgCore
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkBijective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkStrictMono
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CarImpFrel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CardOther
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfUnitaryConjugate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreAnnApply
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreApply
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsCocycleOfMapToDegreeOneTerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExpMemUJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GlRelOfBracket
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExt
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HwMapOfLowSpan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsAlt
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KExp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KhwExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KsetSubsetUjset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemUJsetOfMemKset
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MulMemUJset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumInsertErase
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WlemOfGfacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordMonomial
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZetaDegZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.D.DSIC

theorem hCAR : CAR := GlobalTheory.CompanionTheory.ChainCAR.car
theorem hFRel : FRel := GlobalTheory.CompanionTheory.DSICFRel.car_imp_frel hCAR
theorem hBdFacts : BdFacts := GlobalTheory.CompanionTheory.KoszulBd.bdFacts hCAR
theorem hGFacts : GFacts := GlobalTheory.CompanionTheory.GopEntries.gFacts
theorem hKoszul : Koszul := GlobalTheory.CompanionTheory.DSICKoszul.koszul hCAR
theorem hVerma : Verma := GlobalTheory.CompanionTheory.DSVerma.verma
theorem hCover : Cover := GlobalTheory.CompanionTheory.DSCover.cover hKoszul hVerma
theorem hCO0 : CapelliDeterminantBlockProduct := GlobalTheory.CompanionTheory.CapelliBlocks.co0
theorem hCO : CO := GlobalTheory.CompanionTheory.CasselmanOsborne.co_of hBdFacts hGFacts hCover hCO0
theorem hZetaHW : ZetaHW := GlobalTheory.CompanionTheory.ZetaHighest.zetaHW
theorem hWLem : WLem := GlobalTheory.CompanionTheory.DSICWLem.wlem_of_gfacts hGFacts
theorem hNormLt : NormLt := GlobalTheory.CompanionTheory.DSNormLt.normLt
theorem hAdj : Adj := GlobalTheory.CompanionTheory.DSChainAdj.adj
theorem hGamDom : GamDom := GlobalTheory.CompanionTheory.GamDomProof.gamDom
theorem hKHWExists : KHWExists := GlobalTheory.CompanionTheory.KHighestExists.khwExists
theorem hLowSpan : LowSpan := GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
theorem hHWMap : HWMap := GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan hLowSpan
theorem hPRV : PRV := GlobalTheory.CompanionTheory.ChainHighest.aux₃ hFRel hGFacts hGamDom hKHWExists hHWMap
theorem hAlgCore : AlgCore := algCore_of hFRel hBdFacts hCO hZetaHW hWLem hNormLt hAdj hPRV
theorem hAlgCoreSub : AlgCoreSub := GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore hAlgCore
theorem hSmLin : SmLin := GlobalTheory.CompanionTheory.DSSmLin.smLin
theorem hSmBracket : SmBracket := GlobalTheory.CompanionTheory.SmBracket.smBracket_of hSmLin
theorem hSmMod : SmMod := GlobalTheory.CompanionTheory.SmoothModule.smMod hSmLin hSmBracket
theorem hActQ : ActQ := GlobalTheory.CompanionTheory.DSCapelliAction.actQ
theorem hSpread : Spread := capelli_spread
theorem hKFinStab : KFinStab := GlobalTheory.CompanionTheory.KFinStab.kFinStab
theorem hKExp : KExp := GlobalTheory.CompanionTheory.DSICKExp.kExp
theorem hStabLink : StabLink := GlobalTheory.CompanionTheory.DSStabLink.stabLink hKExp
theorem hWtLink : WtLink := GlobalTheory.CompanionTheory.WtLinkPf.wtLink
theorem hHWofType : HWofType := GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType hStabLink hWtLink
theorem hTypeOfHW : TypeOfHW := GlobalTheory.CompanionTheory.DSKType.typeOfHW hLowSpan hStabLink hWtLink

theorem discrete_series_infinitesimal_character : PI.DSInfCharCap.DSInfCharCap :=
  dsInfCharCap_of hAlgCoreSub hSmMod hActQ hSpread CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs hKFinStab hStabLink
    hHWofType hTypeOfHW

end CompanionTheory.D.DSIC
