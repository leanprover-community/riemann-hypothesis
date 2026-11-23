module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Imports
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionExistenceHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FarClosed
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.IntertwinerAdjoints.Imports
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.Models
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.StepM
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.RgHe

theorem occ : Occ :=
  Dec.walk (Sl.stepL LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (SM.stepM LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (PositivityTheory.RgHe3.base LowestKTypeModel.models FrameF.frame)

end PositivityTheory.RgHe
