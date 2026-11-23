module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denupper
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Ratprod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_prodint :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ M : ℤ, M ≠ 0 ∧ Real.log |(M : ℝ)| ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, (den N k : Ω) * Bprim k χ = (M : Ω) := by
  intro N _ k P hk hP
  obtain ⟨q, hq⟩ := b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by
    intro K Ω _ _ _ _ f χ
    simp only [map_mul, map_natCast]
    rw [b_primmap f f.injective])
  have hfin : (charSet ℂ P).Finite := Set.toFinite _
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]
    exact IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1
  have hint' : IsIntegral ℤ q := by
    have : (q : ℂ) = algebraMap ℚ ℂ q := rfl
    rw [this] at hint
    exact (isIntegral_algebraMap_iff ).mp hint
  obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hM' : (M : ℚ) = q := by simpa using hM
  subst hM'
  have hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ) := by
    rw [hC]; simp
  have hM0 : M ≠ 0 := by
    have : (M : ℂ) ≠ 0 := by
      rw [← hC']
      refine Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero ?_ ?_
      · exact Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne'
      · have hχ' : χ.toUnitHom.ker ∈ P := hfin.mem_toFinset.mp hχ
        exact (b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1
    exact_mod_cast this
  refine ⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩
  · have hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard := by
      have h1 : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
      rw [h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle
  · rw [hq Ω]; simp
