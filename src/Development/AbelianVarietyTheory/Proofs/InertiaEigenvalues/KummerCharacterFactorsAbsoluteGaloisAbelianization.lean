module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.KummerAb

theorem kummer_char_eq_of_toAb_eq : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  intro E' Ω _ _ _ _ _ m hm ζ hζ c hc y hy σ τ he
  have hc' : algebraMap E' Ω c ≠ 0 := (map_ne_zero_iff _ (algebraMap E' Ω).injective).mpr hc
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact hc' hy.symm
  haveI : NeZero m := ⟨hm.ne'⟩
  have hζ' : IsPrimitiveRoot (algebraMap E' Ω ζ) m := hζ.map_of_injective (algebraMap E' Ω).injective
  have key : ∀ ρ : G E' Ω, ∃ e : E', ρ y = algebraMap E' Ω e * y := by
    intro ρ
    have h1 : (ρ y / y) ^ m = 1 := by
      rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    refine ⟨ζ ^ i, ?_⟩
    rw [map_pow, hi, div_mul_cancel₀ _ hy0]
  let φ : G E' Ω →* Ωˣ := MonoidHom.mk' (fun ρ => Units.mk0 (ρ y / y)
      (div_ne_zero ((map_ne_zero_iff _ ρ.injective).mpr hy0) hy0)) (by
    intro a b
    ext
    obtain ⟨e, he⟩ := key b
    simp only [Units.val_mul, Units.val_mk0, AlgEquiv.mul_apply, he, map_mul, AlgEquiv.commutes]
    field_simp)
  have hφ : ∀ ρ, (φ ρ : Ω) = ρ y / y := fun ρ => rfl
  have hint : IsIntegral E' y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E' (IntermediateField.adjoin E' {y}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen (φ.ker : Set (G E' Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin E' {y}).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)
    intro ρ hρ
    have : ρ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ y
      (IntermediateField.subset_adjoin E' {y} rfl)
    rw [MonoidHom.mem_ker]
    ext
    rw [hφ, this, div_self hy0, Units.val_one]
  have hclosed : IsClosed (φ.ker : Set (G E' Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  have hle : (commutator (G E' Ω)).topologicalClosure ≤ φ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ) hclosed
  have hmem : σ⁻¹ * τ ∈ (commutator (G E' Ω)).topologicalClosure := QuotientGroup.eq.mp he
  have h2 := hle hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← hφ, ← hφ, h2]

end GlobalTheory.KummerAb
