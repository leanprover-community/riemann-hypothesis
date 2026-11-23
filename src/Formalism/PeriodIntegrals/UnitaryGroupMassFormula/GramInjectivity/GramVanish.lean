module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial

theorem gram_vanish {σ ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (f : ι → MvPolynomial σ ℤ) (ph : MvPolynomial σ K →ₗ[K] K)
    (h : ∑ i, ph (map (Int.castRingHom K) (f i)) • map (Int.castRingHom K) (f i) = 0)
    (i : ι) : ph (map (Int.castRingHom K) (f i)) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ι → MvPolynomial σ K, ∀ j, g j = map (Int.castRingHom K) (f j) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hg] at h ⊢
  have key : ∀ l : Module.Dual ℚ K, ∀ j, l (ph (g j)) = 0 := by
    intro l
    have lin : ∀ (x : K) (n : ℤ), algebraMap ℚ K (l x) * (n : K) = algebraMap ℚ K (l (x * n)) := by
      intro x n
      rw [show x * (n : K) = n • x by rw [zsmul_eq_mul, mul_comm], map_zsmul, zsmul_eq_mul,
        map_mul, map_intCast, mul_comm]
    have hrel : ∑ j, algebraMap ℚ K (l (ph (g j))) • g j = 0 := by
      ext s
      have hs := congrArg (fun p => l (AddMonoidAlgebra.coeff p s)) h

      simp only [coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_sum, map_zero] at hs
      have e : ∀ j, AddMonoidAlgebra.coeff (g j) s = ((AddMonoidAlgebra.coeff (f j) s : ℤ) : K) := fun j => by
        rw [hg, coeff_map, eq_intCast]
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul]
      calc ∑ j, algebraMap ℚ K (l (ph (g j))) * AddMonoidAlgebra.coeff (g j) s
          = ∑ j, algebraMap ℚ K (l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [e j, lin]
        _ = algebraMap ℚ K (∑ j, l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by rw [map_sum]
        _ = 0 := by rw [hs, map_zero]
    have hsum : ∑ j, l (ph (g j)) ^ 2 = 0 := by
      have h1 : l (ph (∑ j, algebraMap ℚ K (l (ph (g j))) • g j)) = 0 := by
        rw [hrel, map_zero, map_zero]

      rw [map_sum, map_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul, sq]
    intro j
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ l (ph (g k)) ^ 2 := fun k _ => sq_nonneg _
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ j)
    exact (pow_eq_zero_iff two_ne_zero).mp hj
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (ph (g i))).mp (fun l => key l i)

end PI.WwInjectiveWork
