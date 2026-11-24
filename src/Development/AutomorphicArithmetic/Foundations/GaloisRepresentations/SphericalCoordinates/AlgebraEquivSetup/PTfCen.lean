module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfCen :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → TfCen := by
  intro hsum hadm X M _ _ T z hz V _ _ Φ hΦ g
  have hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x) := ⟨_, fun _ => rfl⟩
  have hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x := by
    intro k hk x
    have h1 := ((hadm X M T z hz.2).2 k hk x).2
    have h2 := hΦ k hk (g * x)
    rw [hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  have hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z := by
    rw [finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K z
      rw [hk]
      exact hinv k k.2 z
    · intro y hy
      have h0 : dosetInd ℂ T.K z y.out = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp hm
        have e' : y.out = z * (a * b) := by
          rw [e, ← hz.1 a, mul_assoc]
        have h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K) := by
          rw [e']
          exact QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)
        exact hy ((QuotientGroup.out_eq' y).symm.trans h2)
      rw [hΨ, TyLev.tf, h0, mul_zero, zero_smul]
  have hty : tyFn T.J T.ψ 1 = 1 := by
    unfold tyFn
    rw [dite_eq_left T.J.one_mem]
    have h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1 := rfl
    rw [h1, map_one]
    simp
  have hdz : dosetInd ℂ T.K z z = 1 := by
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]
    rfl
  have hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
    rw [TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]
  have hs := hsum X V T.K T.K₀ T.le T.idx Ψ hinv
  unfold hAct
  simp only [hΨ] at hs hsingle
  rw [hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]
