module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CharpolyNilpotence.IsNilpotentAevalCharpoly
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SliceVanOfFrob
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.Imports
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace PositivityTheory.RgUd.T.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sliceVan [CharZero k] : SliceVan (k := k) :=
  SLF.sliceVan_of_frob' PositivityTheory.PfBern.Frob.frobeniusReciprocity SLF.Un2.unimod

theorem descA [CharZero k] : DescA (k := k) := Asm.descA_of JC.jcPoly (sliceVan k)

end PositivityTheory.RgUd.T.Desc.Final
