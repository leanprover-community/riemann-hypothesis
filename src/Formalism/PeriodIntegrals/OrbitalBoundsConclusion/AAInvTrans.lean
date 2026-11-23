module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.DetTransposeApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.LyQminorLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OfFnProdIntertwine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OperatorModel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OperatorsCommuteTranslationsOfLeftRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SubsetUpperHessenberg
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.HkConjTranspose

@[expose] public section

theorem operators_commute_translations : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations :=
  AAInvW.operators_commute_translations_of_left_right AAInvW.left_aa
    (AAInvW.rightAA_of AAInvW.operator_model AAInvW.algebra_aa AAInvW.algebra_aa_vector AAInvW.hpk_involution
      AAInvW.subset_upper_hessenberg AAInvW.subset_inverse_column AAInvW.subset_row_star)
    AAInvW.subset_upper_hessenberg
