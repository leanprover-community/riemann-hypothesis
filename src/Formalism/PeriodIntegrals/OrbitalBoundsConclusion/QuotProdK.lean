module

public import Formalism.PeriodIntegrals.QuotProdK
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.BruhatDecomposition
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LocalWeilRepresentation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ProdSetIsClosed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.QuotProdKOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
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

theorem quotient_product_compact : PI.QuotProdK.QuotProdK :=
  QPK.quotProdK_of QPK.weil_quotient_global_assumptions QPK.haar_measure_uniqueness
    (QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition'
      QPK.local_weil_representation)
