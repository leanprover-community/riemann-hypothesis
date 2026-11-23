module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

private theorem exists_algHom_complex_ker_eq_maximal (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (m : Ideal A) [m.IsMaximal] : ∃ e : A →ₐ[ℂ] ℂ, ∀ x, e x = 0 ↔ x ∈ m := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A ⧸ m)
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun x => ?_⟩
  show φ.symm (Ideal.Quotient.mkₐ ℂ m x) = 0 ↔ _
  rw [map_eq_zero_iff _ φ.symm.injective, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

private theorem mem_of_reduced_vanishing_on_zeros (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (J : Ideal A) (hred : IsReduced (A ⧸ J)) (x : A)
    (hx : ∀ e : A →ₐ[ℂ] ℂ, (∀ y ∈ J, e y = 0) → e x = 0) : x ∈ J := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hj : x ∈ J.jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨hJm, hm⟩
    haveI := hm
    obtain ⟨e, he⟩ := exists_algHom_complex_ker_eq_maximal A m
    exact (he x).1 (hx e fun y hy => (he y).2 (hJm hy))
  rw [← Ideal.radical_eq_jacobson] at hj
  obtain ⟨n, hn⟩ := hj
  haveI := hred
  have hnil : IsNilpotent (Ideal.Quotient.mk J x) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 hnil.eq_zero

theorem UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (d : ℕ) (t : Fin d → A), IsReduced (A ⧸ Ideal.span (Set.range t)) → Finite {e : A →ₐ[ℂ] ℂ // ∀ j, e (t j) = 0} → ∀ e : A →ₐ[ℂ] ℂ, (∀ j, e (t j) = 0) → ∀ b : A, e b = 0 → ∃ (c : A) (g : Fin d → A), e c ≠ 0 ∧ c * b = ∑ l, g l * t l := by
  intro A _ _ _ d t hred hfin e he b hb
  have key : ∀ s : {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0},
      ∃ a : A, e a ≠ 0 ∧ (s.1 ≠ e → s.1 a = 0) := by
    intro s
    by_cases hs : s.1 = e
    · exact ⟨1, by simp, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ : ∃ y, e y ≠ s.1 y := by
        by_contra hcon
        push_neg at hcon
        exact hs (AlgHom.ext fun y => (hcon y).symm)
      refine ⟨y - algebraMap ℂ A (s.1 y), ?_, fun _ => ?_⟩
      · rw [map_sub, AlgHom.commutes]
        exact sub_ne_zero.2 hy
      · rw [map_sub, AlgHom.commutes]
        exact sub_self _
  choose f hf using key
  haveI := Fintype.ofFinite {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0}
  refine ⟨∏ s, f s, ?_⟩
  have hmem : (∏ s, f s) * b ∈ Ideal.span (Set.range t) := by
    apply mem_of_reduced_vanishing_on_zeros A _ hred
    intro e' he'
    have ht : ∀ j, e' (t j) = 0 := fun j => he' _ (Ideal.subset_span ⟨j, rfl⟩)
    by_cases hee : e' = e
    · subst hee
      rw [map_mul, hb, mul_zero]
    · rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨e', ht⟩) ((hf ⟨e', ht⟩).2 hee),
        zero_mul]
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨g, ?_, hg.symm⟩
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.2 fun s _ => (hf s).1
