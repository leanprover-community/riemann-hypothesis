module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [CommRing k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) : IsUp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]

theorem UpperTheory.V.Ws.X1.adFacts :
    ∀ {k Γ : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), ((∀ i j, IsLocallyConstant fun g => r g i j) → IsOpen ((adSp r h).ker : Set Γ) ∧ ∀ X, IsLocallyConstant fun g => adSp r h g X) ∧ ∀ (n : M4 k) (s : Γ), IsGSp 1 n → IsUp (adj n * r s * n) → IsUp (adj n * r s⁻¹ * n) → ∀ X ∈ bor n, adSp r h s X ∈ bor n := by
  intro k Γ _ _ _ _ r h
  refine ⟨fun hloc => ?_, fun n s hn h1 h2 X hX => ?_⟩
  · have hr : IsLocallyConstant fun g => r g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro M
      have hset : (fun g => r g) ⁻¹' {M} = ⋂ i, ⋂ j, (fun g => r g i j) ⁻¹' {M i j} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
        exact ⟨fun e i j => by rw [e], fun e => Matrix.ext e⟩
      rw [hset]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hloc i j).isOpen_fiber _
    refine ⟨?_, fun X => ?_⟩
    · have hker : IsOpen ((r.ker : Subgroup Γ) : Set Γ) := by
        have : ((r.ker : Subgroup Γ) : Set Γ) = (fun g => r g) ⁻¹' {1} := by
          ext g
          simp [MonoidHom.mem_ker]
        rw [this]
        exact hr.isOpen_fiber _
      refine Subgroup.isOpen_mono ?_ hker
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      apply LinearMap.ext
      intro Y
      apply Subtype.ext
      have hgi : r g⁻¹ = 1 := by
        have e := r.map_mul g⁻¹ g
        rw [inv_mul_cancel, r.map_one, hg, mul_one] at e
        exact e.symm
      rw [adSp_val, hg, hgi]
      simp
    · have hinv : IsLocallyConstant fun g => r g⁻¹ := hr.comp_continuous continuous_inv
      have hprod : IsLocallyConstant fun g => r g * (X : M4 k) * r g⁻¹ :=
        IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ hr (IsLocallyConstant.const (X : M4 k)) (· * ·)) hinv (· * ·)
      refine IsLocallyConstant.desc _ (fun Y : sp4 k => (Y : M4 k)) ?_ Subtype.val_injective
      convert hprod using 1
      funext g
      simp [adSp_val]
  · have hn' : n * adj n = 1 := by
      have e : adj n * n = 1 := by simpa [IsGSp] using hn
      exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.mp e
    show IsUp (adj n * ((adSp r h s X : sp4 k) : M4 k) * n)
    rw [adSp_val]
    have key : adj n * (r s * (X : M4 k) * r s⁻¹) * n
        = (adj n * r s * n) * (adj n * (X : M4 k) * n) * (adj n * r s⁻¹ * n) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul, ← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul]
    rw [key]
    exact up_mul (up_mul h1 hX) h2
