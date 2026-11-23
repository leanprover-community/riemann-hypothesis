module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

@[expose] public section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.finite_gaussianExtension_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  first | exact @GlobalTheory.GaussExt.finite_units_quot_units | exact GlobalTheory.GaussExt.finite_units_quot_units | (intros; apply GlobalTheory.GaussExt.finite_units_quot_units <;> assumption)
