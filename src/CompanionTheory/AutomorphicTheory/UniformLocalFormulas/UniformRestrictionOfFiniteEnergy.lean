module

public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfEnergy
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.RankOneTermInvariant
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

namespace Formalism.MainStatements.RowRest

theorem uniqOfPin : UniqOfPin := fun _ _ _ _ C hB u u' νl hP => use₇ C hB u u' νl hP

theorem uniform_restriction_of_finite_energy (hE : EnergyFin) : Formalism.L2.SG.Pf.ThmBChain6.AmplitudeBoundsAllChoicesUniform :=
  uniform_restriction_of_energy covariance_formula uniqOfPin hE

end Formalism.MainStatements.RowRest
