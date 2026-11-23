module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isSplit_injective_and_exists (O k S : Type) [CommRing O] [Field k] [Fintype S]
    (χ : S → (O →+* k)) (h : IsSplit χ) :
    Function.Injective χ ∧ ∀ ψ : O →+* k, ∃ s, χ s = ψ := by
  classical
  unfold IsSplit at h
  set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x := by
    intro a x s
    simp [hF, Algebra.ofId_apply]
  constructor
  · intro s t hst
    by_contra hne
    obtain ⟨y, hy⟩ := h.2 (Pi.single s 1)
    have key : ∀ y : TensorProduct ℤ k O, F y s = F y t := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rw [hv, hv, hst]
      | add u v hu hv' => simp [map_add (f := _), hu, hv']
    have h1 := key y
    rw [hy] at h1
    simp [Pi.single_apply, Ne.symm hne] at h1
  · intro ψ
    let Ψ : TensorProduct ℤ k O →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)
    choose y hy using fun s => h.2 (Pi.single s (1 : k))
    have hsum : ∑ s, y s = 1 := by
      apply h.1

      rw [map_sum, map_one]
      simp only [hy]
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hne : ∑ s, Ψ (y s) ≠ 0 := by

      rw [← map_sum, hsum, map_one]
      exact one_ne_zero
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨s, ?_⟩
    have hmul : ∀ z, z * y s = (F z s) • y s := by
      intro z
      apply h.1
      rw [map_mul, map_smul, hy]
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
    ext o
    have h1 := congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))
    have h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o := by
      simp [Ψ]
    rw [map_mul, map_smul, hv, h2, smul_eq_mul, one_mul] at h1
    exact (mul_right_cancel₀ hs h1).symm

end GlobalTheory.CompanionTheory.Ar.Crv
