module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Formalism.LocalToGlobal.IndefiniteReal.EigenDecomposition
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.SimDiag

theorem exists_unitary_isDiag {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ A ∈ S, Aᴴ = A) (hC : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
    fun M => Matrix.toEuclideanLin M
  have hL : ∀ M v, L M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := fun _ _ => rfl
  obtain ⟨m, b, hb⟩ := Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting (L '' S)
    (by
      rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      refine LinearMap.ext fun v => ?_
      change L M (L N v) = L N (L M v)
      simp only [hL, Matrix.mulVec_mulVec, hC M hM N hN])
    (by
      rintro _ ⟨M, hM, rfl⟩
      refine ⟨M, hM, ?_⟩
      change Matrix.toEuclideanLin M = LinearMap.adjoint (Matrix.toEuclideanLin M)
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH M hM])
  have hm : m = n := by
    have := Module.finrank_eq_card_basis b.toBasis
    simpa [finrank_euclideanSpace] using this.symm
  subst hm
  have hinner : ∀ j k, ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i =
      if j = k then 1 else 0 := by
    intro j k
    have := orthonormal_iff_ite.1 b.orthonormal j k
    rw [PiLp.inner_apply] at this
    simpa [RCLike.inner_apply, mul_comm] using this
  let U : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i k => WithLp.ofLp (b k) i
  refine ⟨U, ?_, fun A hA => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, U, Matrix.of_apply]
    exact hinner j k
  · intro j k hjk
    obtain ⟨μ, hμ⟩ := hb k (L A) ⟨A, hA, rfl⟩
    have hv : A *ᵥ WithLp.ofLp (b k) = μ • WithLp.ofLp (b k) := by
      have := congrArg WithLp.ofLp hμ
      simpa [hL] using this
    have hAU : ∀ i, (A * U) i k = μ * WithLp.ofLp (b k) i := by
      intro i
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, U] using this
    have h0 := hinner j k
    rw [if_neg hjk] at h0
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hAU]
    calc ∑ i, Uᴴ j i * (μ * WithLp.ofLp (b k) i)
        = μ * ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.conjTranspose_apply, U, Matrix.of_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]

end GlobalTheory.CompanionTheory.SimDiag
