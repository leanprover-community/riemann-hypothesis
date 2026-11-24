module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  intro Λ R _ _ _ _ h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff Λ R).mp h
  let y : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  let φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R := MvPolynomial.aeval y
  have hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
  let P : Ideal (MvPolynomial (Fin σ.card) Λ) := (maximalIdeal R).comap φ₀
  have hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b) := by
    intro b
    by_contra hb
    exact b.2 ((mem_maximalIdeal _).mpr hb)
  refine ⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩
  intro r
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [hrange] at ht hrt
  obtain ⟨b, rfl⟩ := ht
  obtain ⟨a, ha⟩ := hrt
  have hb : b ∈ P.primeCompl := fun hbP => (mem_maximalIdeal _).mp hbP htu
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change φ₀ a = φ₀ b * r
  exact ha.trans (mul_comm _ _)

end GlobalTheory
