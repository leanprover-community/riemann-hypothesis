module

public import Formalism.PeriodIntegrals.ScRefExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PrincipalIdealRingAtPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WFrameOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
