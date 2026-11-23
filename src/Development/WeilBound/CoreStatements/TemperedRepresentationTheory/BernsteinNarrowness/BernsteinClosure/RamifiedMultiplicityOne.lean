module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
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

namespace PositivityTheory.BernsteinRamification.Close

theorem narrowBern : PositivityTheory.BernsteinRamification.NarrowBern :=
  PositivityTheory.BernsteinRamification.narrowBern PositivityTheory.Geo.geometricLemmaFiltration

theorem kCoinv (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  PositivityTheory.BernsteinRamification.kCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hD

theorem soCoinv (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  PositivityTheory.BernsteinRamification.soCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hK

theorem ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  PositivityTheory.BernsteinRamification.ramifiedMultiplicityOne_of_geometricFiltration PositivityTheory.Geo.geometricLemmaFiltration

theorem finRam : PositivityTheory.ThK.FinRam :=
  PositivityTheory.BernsteinRamification.finRam_of_geo PositivityTheory.Geo.geometricLemmaFiltration

theorem finSplit : PositivityTheory.ThK.FinSplit :=
  PositivityTheory.BernsteinRamification.finSplit_of_geo PositivityTheory.Geo.geometricLemmaFiltration

end PositivityTheory.BernsteinRamification.Close
