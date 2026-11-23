module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem inverseDifferent_multiple (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) := by
  classical
  set b := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  obtain ⟨δ, hδ, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image bd)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hsum := bd.sum_repr z
  have key : (δ : E) * z = ∑ i, (bd.repr z i) • ((δ : E) * bd i) := by
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]; ring
  rw [key]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨n, hn⟩ := hz (RingOfIntegers.basis E i)
  have hr : bd.repr z i = (n : ℚ) := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply,
      mul_comm, hn]
  rw [hr, show ((n : ℚ) • ((δ : E) * bd i)) = (n : ℤ) • ((δ : E) * bd i) by
    rw [← Int.cast_smul_eq_zsmul ℚ]]
  refine IsIntegral.smul _ ?_
  have := hint (bd i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rwa [zsmul_eq_mul] at this

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualLatticeMultiple.proof (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by
  intro D
  obtain ⟨δ, hδ, hdiff⟩ := inverseDifferent_multiple E
  refine ⟨δ * (D.factorial : ℤ), mul_ne_zero hδ (by exact_mod_cast D.factorial_ne_zero),
    fun La hLa => ⟨fun x hx y hy => ?_, fun y hy => ?_⟩⟩
  · have hi : IsIntegral ℤ (Algebra.trace ℚ E (h.toSesq x y)) :=
      Algebra.isIntegral_trace ((mem_integralClosure_iff ℤ E).mp (hLa.integral x hx y hy))
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨n, by rw [← hn]; simp⟩
  ·
    have hdual : δ • y ∈ dualLattice h La := by
      intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := hy _ (hLa.isLattice.smul_mem a x hx)
      exact ⟨n, by rw [← hn, LinearMap.map_smul, smul_eq_mul]⟩

    have hm := AddSubgroup.nsmul_relIndex_mem La hdual
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
    have : (D.factorial : ℤ) • (δ • y) ∈ La := by
      rw [hc, natCast_zsmul, mul_comm, mul_nsmul]
      rw [smul_comm]
      exact AddSubgroup.nsmul_mem _ hm _
    rwa [smul_smul, mul_comm] at this

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
