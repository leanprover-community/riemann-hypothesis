module

public import Mathlib.RingTheory.RingHom.Flat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_coeffs_of_mem_mul_span {S : Type} [CommRing S] {r : ℕ} (J : Ideal S)
    (u : Fin r → S) {w : S} (hw : w ∈ J * Ideal.span (Set.range u)) :
    ∃ a : Fin r → S, (∀ i, a i ∈ J) ∧ ∑ i, u i * a i = w := by
  have hw' : w ∈ J • Submodule.span S (Set.range u) := hw
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J u w).1 hw'
  refine ⟨a, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype _ _ (fun i => zero_smul S (u i))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mem_map_maximalIdeal_of_flat {R : Type} [CommRing R] [IsLocalRing R] {S : Type}
    [CommRing S] [Algebra R S] [Module.Flat R S] {r : ℕ} (t : Fin r → R)
    (hmin : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (y a : Fin r → S) (h : ∑ i, algebraMap R S (t i) * y i = ∑ i, algebraMap R S (t i) * a i)
    (i : Fin r) : y i - a i ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  have hrel : ∑ j, t j • (y j - a j) = 0 := by
    simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, h, sub_self]
  obtain ⟨k, d, w, hw, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S)
    (f := t) (x := fun j => y j - a j) hrel
  have hwi : y i - a i = ∑ j, d i j • w j := hw i
  rw [hwi]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  refine hmin (fun i => d i j) ?_ i
  rw [← hd j]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem minimal_generators_flat_independent :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  intro R _ _ S _ c hc r t I hI hmin y hy i
  have hmap : (IsLocalRing.maximalIdeal R * I).map c
      = (IsLocalRing.maximalIdeal R).map c * Ideal.span (Set.range fun j => c (t j)) := by
    rw [Ideal.map_mul, ← hI, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hy
  obtain ⟨a, ha, hsum⟩ := exists_coeffs_of_mem_mul_span _ _ hy
  have hmin0 : ∀ x : Fin r → R, ∑ i, x i * t i = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal R :=
    fun x hx => hmin x (by rw [hx]; exact Ideal.zero_mem _)
  have h3 : y i - a i ∈ (IsLocalRing.maximalIdeal R).map c := by
    letI := c.toAlgebra
    haveI : Module.Flat R S := hc
    exact mem_map_maximalIdeal_of_flat t hmin0 y a hsum.symm i
  have h4 := Ideal.add_mem _ h3 (ha i)
  rwa [sub_add_cancel] at h4

end GlobalTheory.CompanionTheory.FewEq
