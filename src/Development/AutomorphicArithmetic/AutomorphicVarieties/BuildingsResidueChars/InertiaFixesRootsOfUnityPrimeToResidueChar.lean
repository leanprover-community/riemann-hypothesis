module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    IsPlaceOver A w → ∀ M : ℕ, (M : 𝓞 F) ∉ w.asIdeal → ∀ s ∈ Ine (F := F) A, ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ w A hA M hM s hs ζ hζ
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simpa using w.asIdeal.zero_mem)
  have hvM : A.valuation (M : Ω) = 1 := by
    have h1 := (hA (M : 𝓞 F)).not.mpr hM
    have h2 : (algebraMap F Ω) ((M : 𝓞 F) : F) = (M : Ω) := by simp
    rw [h2] at h1
    refine le_antisymm ?_ (not_lt.mp h1)
    simpa using A.valuation_le_one (M : A)
  have hvz : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ M = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with h | h | h
    · exact absurd hp (pow_lt_one₀ zero_le' h hM0).ne
    · exact h
    · exact absurd hp (one_lt_pow₀ h hM0).ne'
  have hI : s ∈ Inertia A := hs
  unfold Inertia at hI
  obtain ⟨-, hI⟩ := hI
  have hd : A.valuation (s ζ - ζ) < 1 := hI ζ hvz.le
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hvz
  set η := s ζ / ζ with hηdef
  have hsz : s ζ = η * ζ := (div_mul_cancel₀ _ hζ0).symm
  have hη : η ^ M = 1 := by
    rw [hηdef, div_pow, ← map_pow, hζ, map_one, div_one]
  have hη1 : A.valuation (η - 1) < 1 := by
    have e : s ζ - ζ = (η - 1) * ζ := by rw [hsz]; ring
    rw [e, map_mul, hvz, mul_one] at hd
    exact hd
  have hvη : A.valuation η = 1 := by
    have e : η = 1 + (η - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hη1
  by_contra hne
  have hne' : η ≠ 1 := by
    intro h1
    apply hne
    rw [hsz, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, η ^ i = 0 := by
    have e := mul_geom_sum η M
    rw [hη, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne')
  have hMsum : (M : Ω) = ∑ i ∈ Finset.range M, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  have hlt : A.valuation (M : Ω) < 1 := by
    rw [hMsum]
    refine Valuation.map_sum_lt _ one_ne_zero ?_
    intro i _
    have e := mul_geom_sum η i
    have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
      refine Valuation.map_sum_le _ ?_
      intro j _
      rw [map_pow, hvη, one_pow]
    rw [Valuation.map_sub_swap, ← e, map_mul]
    calc A.valuation (η - 1) * A.valuation (∑ j ∈ Finset.range i, η ^ j)
        ≤ A.valuation (η - 1) * 1 := by gcongr
      _ = A.valuation (η - 1) := mul_one _
      _ < 1 := hη1
  rw [hvM] at hlt
  exact lt_irrefl _ hlt
