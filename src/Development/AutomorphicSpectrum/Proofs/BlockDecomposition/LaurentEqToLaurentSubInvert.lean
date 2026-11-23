module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Algebra.Polynomial.Laurent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
