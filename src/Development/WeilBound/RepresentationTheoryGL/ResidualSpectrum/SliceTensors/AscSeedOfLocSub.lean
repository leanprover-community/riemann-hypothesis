module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopGap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.CharZeroCompletion
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscAllOfRest
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsOpenStabTw
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PLocDual
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatHerm
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStep
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
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

namespace PositivityTheory.Rg.Rs

theorem ascAll_holds : AscAll := by
  exact ascAll_of_rest (slice_of dict_holds finTr_holds) pr_holds indMap_holds
    (stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds infAsc_holds
      satInd2_holds satAsc_holds satHerm_holds gap_holds)

theorem ascSeed_of_locSub (h : LocSub) : AscSeed := by
  exact ⟨ascAll_holds, C3.clause3Asc_holds h locDual_holds⟩

end PositivityTheory.Rg.Rs
