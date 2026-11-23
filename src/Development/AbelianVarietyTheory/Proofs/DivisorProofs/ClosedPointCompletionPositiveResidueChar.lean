module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalkOfArithBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
