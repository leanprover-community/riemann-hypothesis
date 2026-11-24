module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds
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

namespace PI.VolStabS

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabS
