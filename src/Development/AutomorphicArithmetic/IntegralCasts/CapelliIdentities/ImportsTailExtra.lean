module

public import Mathlib.Algebra.Group.End
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

theorem UpperTheory.Reformulated.B.Yvb3.main :
    ∀ (g : ℤ → ENNReal) (n : ℕ), ∑' (m : Fin n → ℤ), ∏ i : Fin n, g (m i) = (∑' (k : ℤ), g k) ^ n := by
  intro g n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq]
    have h : ∀ p : ℤ × (Fin n → ℤ),
        (∏ i : Fin (n+1), g ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) p i)) = g p.1 * ∏ i : Fin n, g (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [h]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => g a * ∏ i : Fin n, g (b i))]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, pow_succ']
