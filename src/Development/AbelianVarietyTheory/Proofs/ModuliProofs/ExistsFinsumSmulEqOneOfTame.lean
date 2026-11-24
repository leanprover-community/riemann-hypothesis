module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
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
public import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.exists_finsum_smul_eq_one_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B],
      (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) →
        ∃ b : B, ∑ᶠ g : Γ, g • b = 1 := by
  intro Γ _ _ B _ _ htame
  classical
  haveI := Fintype.ofFinite Γ
  let A := FixedPoints.subring B Γ
  haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI := Algebra.IsInvariant.isIntegral A B Γ
  have tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A := by
    intro b h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)
  let T : Ideal A := Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}
  have hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ht
    | zero => exact ⟨0, by simp⟩
    | add t u _ _ htb hub =>
      obtain ⟨b, hb⟩ := htb
      obtain ⟨c, hc⟩ := hub
      exact ⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩
    | smul a t _ htb =>
      obtain ⟨b, hb⟩ := htb
      refine ⟨(a : B) * b, ?_⟩
      simp only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [a.2 g]
  suffices h1 : (1 : A) ∈ T by
    obtain ⟨b, hb⟩ := hT 1 h1
    exact ⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩
  by_contra h1
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)
  have hker : RingHom.ker (algebraMap A B) ≤ m := by
    intro z hz
    have : z = 0 := Subtype.ext hz
    rw [this]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  obtain ⟨n, c, d, s, hs, hsep⟩ := _root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime
  have trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q := by
    intro j
    have hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T :=
      Ideal.subset_span ⟨c j, rfl⟩
    have := hTm hmemT
    rw [← hQm, Ideal.mem_comap] at this
    exact this
  have hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q := by
    rw [Finset.sum_comm]
    exact Q.sum_mem fun j _ => by
      rw [← Finset.mul_sum]
      exact Q.mul_mem_left _ (trace_mem j)
  have hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q := by
    refine Q.sum_mem fun g _ => ?_
    split_ifs with hg
    · exact (hsep g).1 hg
    · simpa using (hsep g).2 hg
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hdiff
  have hcs := Q.sub_mem hz hdiff
  rw [sub_sub_cancel] at hcs
  rcases hQ.isPrime.mem_or_mem hcs with hc | hc
  · apply htame Q hQ.isPrime
    convert hc using 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · exact hs hc

end GlobalTheory
