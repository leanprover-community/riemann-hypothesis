module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.alg_pf :
    UpperTheory.Gal.Gen.HB → UpperTheory.Gal.Gen.GroupDet → UpperTheory.Gal.Gen.Alg := by
  intro hHB hGD k _ _ l _ H _ _ hH P hP hN
  classical
  have hl0 : 0 ≤ ‖(l : k)‖ := norm_nonneg _
  have hl1 : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hdN : Module.finrank k P ≤ Fintype.card H := by
    have h := Submodule.finrank_le P
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have key : ∀ a : H → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) →
      ‖∑ i, a i * (fun _ => (1 : k)) i‖ ≤ Real.sqrt ‖(l : k)‖ := by
    intro a ha hperp
    have hker : P ≤ LinearMap.ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin := by
      intro c hc
      rw [LinearMap.mem_ker]
      funext g
      have h0 := hperp (fun h => c (h * g)) (hP c hc g)
      have h1 : ∑ h, a (h * g⁻¹) * c h = ∑ i, a i * c (i * g) :=
        Fintype.sum_equiv (Equiv.mulRight g⁻¹) _ _ (fun x => by simp)
      change ∑ h, a (h * g⁻¹) * c h = 0
      rw [h1]
      exact h0
    have hrank : (Matrix.of fun h g : H => a (h * g⁻¹)).rank ≤
        Fintype.card H - Module.finrank k P := by
      have h2 := LinearMap.finrank_range_add_finrank_ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h2
      have h3 := Submodule.finrank_mono hker
      rw [← Matrix.rank_transpose]
      have h4 : (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.rank =
          Module.finrank k (LinearMap.range
            (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin) := (Matrix.finrank_range_mulVecLin _).symm
      omega
    have h1 := hGD k l H hH a _ ha hrank
    rw [Nat.sub_sub_self hdN] at h1
    simp only [mul_one]
    rw [Real.le_sqrt (norm_nonneg _) hl0]
    have hne : Fintype.card H ≠ 0 := Fintype.card_ne_zero
    refine (pow_le_pow_iff_left₀ (by positivity) hl0 hne).mp ?_
    calc (‖∑ i, a i‖ ^ 2) ^ Fintype.card H
        = (‖∑ i, a i‖ ^ Fintype.card H) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (‖(l : k)‖ ^ Module.finrank k P) ^ 2 := by gcongr
      _ = ‖(l : k)‖ ^ (2 * Module.finrank k P) := by rw [← pow_mul, mul_comm]
      _ ≤ ‖(l : k)‖ ^ Fintype.card H := pow_le_pow_of_le_one hl0 hl1 hN
  obtain ⟨c, hc, hcv⟩ := hHB k H P (fun _ => 1) (Real.sqrt ‖(l : k)‖) key
  refine ⟨c, hc, fun h => ?_⟩
  have h5 : ‖(1 : k) - c h‖ ≤ Real.sqrt ‖(l : k)‖ := hcv h
  exact (Real.le_sqrt (norm_nonneg _) hl0).mp h5
