module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.RestrictAtPointHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem locSub_holds2 : LocSub := LsTop.locSub_of C3.Rap.restrictAtPoint_holds existsProj2 frobRecip_holds

theorem ascSeed_holds2 : AscSeed := ascSeed_of_locSub locSub_holds2

end PositivityTheory.Rg.Rs
