module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CoordLInjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentCoprimeSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeFlagExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeUnimodular
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PartnerVectorExists
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem rowSurj_of_genus (hJ : UnimodOneGenus) : RowSurj :=
  rowSurj_of hJ partner_vector_exists lattice_integral lamUnimod lattice_flag_exists local_genus_exists

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
