module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTrace
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


theorem _root_.GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ), ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k, ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  first | exact @GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | exact GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | (intros; apply GlobalTheory.exists_algHom_trace_eq_sum_mult_trace <;> assumption)
