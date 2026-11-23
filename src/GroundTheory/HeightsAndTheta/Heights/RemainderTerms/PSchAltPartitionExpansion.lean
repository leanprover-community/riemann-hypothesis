module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAltPartitionExpansion.alt_partition_add_stair_eq {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by
  unfold Comb.alt
  rw [← Matrix.det_transpose, mul_comm]
  exact Schur.det_pow_add_staircase_eq lam

theorem SchAltPartitionExpansion.strictAnti_partition_add_stair {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega

theorem SchAltPartitionExpansion.proof (h1 : SchStrictAntiSplit.Statement) :
    SchAltPartitionExpansion.Statement := by
  intro r n P hP hhom
  set e : (Fin r → ℕ) → (Fin r →₀ ℕ) := fun lam =>
    Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)) with he
  have e_inj : Set.InjOn e (partitionsOf r n : Set (Fin r → ℕ)) := by
    intro a _ b _ hab
    funext i
    have := congrArg (fun f : Fin r →₀ ℕ => f i) hab
    simp only [he, Finsupp.coe_equivFunOnFinite_symm] at this
    omega

  have hR : ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (e lam)) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam) =
      ∑ d ∈ (partitionsOf r n).image e, AddMonoidAlgebra.coeff P d • Comb.alt (⇑d) := by
    rw [Finset.sum_image e_inj]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [C_mul', ← SchAltPartitionExpansion.alt_partition_add_stair_eq]
    simp [he]
  rw [hR]
  conv_lhs => rw [Comb.IsAlt.eq_sum_alt hP]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hsum : ∑ i, d i = r * (r - 1) / 2 + n := by
      have := hhom (mem_support_iff.mp hd.1)
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact this
    obtain ⟨hge, hmem⟩ := h1 r n (⇑d) hd.2 hsum
    refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
    ext i
    simp only [he, Finsupp.coe_equivFunOnFinite_symm]
    have := hge i
    omega
  · intro d hd hnot
    obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hd
    have hz : AddMonoidAlgebra.coeff P (e lam) = 0 := by
      by_contra hne
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨mem_support_iff.mpr hne, ?_⟩
      simpa [he] using SchAltPartitionExpansion.strictAnti_partition_add_stair hlam
    rw [hz, zero_smul]

end

end GroundTheory.Heights₂.Heights.RestTerms
