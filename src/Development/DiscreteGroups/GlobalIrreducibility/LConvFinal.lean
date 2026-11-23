module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.DiscreteGroups.GlobalIrreducibility.LConv
public import Development.DiscreteGroups.GlobalIrreducibility.LConvBig
public import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
public import Development.DiscreteGroups.GlobalIrreducibility.LConvDens
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGlue
public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrr
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKM
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKir
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSep
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnitOf
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

namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue

end DiscreteGroups.sglob.LConv
