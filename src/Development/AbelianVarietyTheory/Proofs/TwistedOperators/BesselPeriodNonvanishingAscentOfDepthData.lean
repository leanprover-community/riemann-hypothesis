module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTowerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodGridFramesOfDepthFixedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTowerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := GlobalTheory.T.fockConjugates_span_depth_data
  have hPart : PartFixed := GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData hD GlobalTheory.T.firstRow_data_have_depth
  GlobalTheory.T.besselPeriod_ascent_of_tower_rungs (GlobalTheory.T.existsGoodGridFrames_of_depthFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower hTot hPart)
    (GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower hTot hPart)

end GlobalTheory.Asc
