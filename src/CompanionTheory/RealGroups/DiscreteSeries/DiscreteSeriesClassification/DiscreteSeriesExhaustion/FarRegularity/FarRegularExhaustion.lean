module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasApplyOfScalChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantOfKHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EvaluationLiftDegreeZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FarRegOfLktUnitIneqFarNum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjROfVanKG
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjUOfInjR
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NumKG
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SubChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TotalBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VNormSqRenum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VanKGOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.RgExh.U

theorem far_regular_exhaustion : CompanionTheory.RgExh.FarReg :=
  GlobalTheory.CompanionTheory.FarRegularityLevels.farReg_of_lkt_unitIneq_farNum GlobalTheory.CompanionTheory.RgExhFarReg.lktExists GlobalTheory.CompanionTheory.RgFarRen.renumber GlobalTheory.CompanionTheory.RgExhUnit.unitIneq
    (GlobalTheory.CompanionTheory.RgCOBlock.coBlock (GlobalTheory.CompanionTheory.RgExh.injU_of_injR (GlobalTheory.CompanionTheory.RgExhInjR.injR_of_vanKG
      (GlobalTheory.CompanionTheory.RgExhVanKG.vanKG_of GlobalTheory.CompanionTheory.ClusterNum.numKG))) GlobalTheory.CompanionTheory.GenCOUP.genCOU) GlobalTheory.CompanionTheory.RgExhFar.farNum

end CompanionTheory.RgExh.U
