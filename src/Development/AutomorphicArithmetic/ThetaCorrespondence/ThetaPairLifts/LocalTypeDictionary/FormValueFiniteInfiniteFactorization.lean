module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleGoodFormValuesBoundedByClassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLevelQuotientGroupLeProdAbsNormPowSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGoodFormValuesMemScaledDualWeylLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FormVal
theorem form_value_eq_finite_mul_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := fun _ =>
  form_fin_inf_of GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice GlobalTheory.T.baseTupleGoodForm_values_bounded_by_classSum GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp
end GlobalTheory.FormVal
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.form_value_finite_infinite_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinFormK ∧ InfFormK := by
  first | exact @_root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | exact _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite | (intros; apply _root_.GlobalTheory.FormVal.form_value_eq_finite_mul_infinite <;> assumption)
end
