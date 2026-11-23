module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

theorem UpperTheory.measurable_matrix_inv :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by
  intro n
  have hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  have hdet : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det) := hc.matrix_det.measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hadj : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j) :=
    (hc.matrix_adjugate.matrix_elem i j).measurable
  have h := hdet.inv.mul hadj
  convert h using 1
  funext x
  simp only [Matrix.of_symm_apply, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv,
    smul_eq_mul, Pi.mul_apply, Pi.inv_apply]
