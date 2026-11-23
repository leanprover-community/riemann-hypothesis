module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

namespace GlobalTheory

theorem norm_eigenvalue_le_one_of_integral_matrix (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] (emb : O →+* K) (hemb : ∀ c, ‖emb c‖ ≤ 1) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K) (hc : c ≠ 0)
    (hM : (M.map emb).mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨j₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖c k‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hj₀) (hk j₀ (Finset.mem_univ _))
  have hrow : (M.map emb).mulVec c k = μ * c k := by
    rw [hM]; simp
  have hsum : ‖(M.map emb).mulVec c k‖ ≤ ‖c k‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖emb (M k j)‖ * ‖c j‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul (hemb _) (hk j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖c k‖ := one_mul _
  rw [hrow, norm_mul] at hsum
  have : ‖μ‖ * ‖c k‖ ≤ 1 * ‖c k‖ := by rwa [one_mul]
  exact le_of_mul_le_mul_right this hpos

theorem eigenvalue_integral_matrix_norm_le_one :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K),
      (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K),
      c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 :=
  fun O K _ _ _ emb hemb n M μ c hc hM =>
    norm_eigenvalue_le_one_of_integral_matrix O K emb hemb n M μ c hc hM

end GlobalTheory
