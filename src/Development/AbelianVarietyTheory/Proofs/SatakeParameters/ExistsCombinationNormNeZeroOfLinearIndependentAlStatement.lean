module

public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAl
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent : ∀ {B A : Type} [inst : CommRing B] [IsDomain B] [inst_2 : CommRing A] [inst_3 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ}, Module.finrank B A = d → ∀ (y : Fin d → A), LinearIndependent B y → ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | exact GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent <;> assumption)
