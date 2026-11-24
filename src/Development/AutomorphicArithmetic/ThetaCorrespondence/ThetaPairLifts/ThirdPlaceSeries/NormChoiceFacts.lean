module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
noncomputable section
namespace GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
structure CoreNormFacts (D : D7) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
structure NormChoiceFacts (D : D7) (C : NChoice D) : Prop extends toCore : _root_.GlobalTheory.NFacts.CoreNormFacts D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D
theorem CoreNormFacts.admA {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := h.adm.1.1
theorem CoreNormFacts.a3 {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L
theorem CoreNormFacts.isot {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : Rows.IsotInternal D.what₂ := h.adm.2.2
end GlobalTheory.NFacts
end
end
