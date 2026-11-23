module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictValC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.CayleyIsometry
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivisorClosedHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.HighExistenceHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.HighestWeightVectorUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.IsUnitDetOfUnitary
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

@[expose] public section

namespace Formalism.L2.SG.Pf

theorem valuation_character_irreducible : ColDictPf.ValCIrr :=
  ColDictValCPf.valCIrr_of ColDictValCPf.transfer_holds
    (ColDictValCPf.divisor_closed_holds ColDictValCPf.density_holds)
    ColDictValCPf.high_existence_holds ColDictValCPf.highest_weight_vector_unique ColDictValCPf.generation_holds

end Formalism.L2.SG.Pf
