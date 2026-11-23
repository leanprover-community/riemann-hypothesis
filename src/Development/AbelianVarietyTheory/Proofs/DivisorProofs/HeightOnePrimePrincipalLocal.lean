module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem heightOne_prime_locallyPrincipal_of_factorial_localization : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S], P.IsPrime → P ≤ p → P ≠ ⊥ → (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) → ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r := by
  intro R S _ _ _ _ _ _ p P _ _ _ hP hPp hP0 hmin
  classical
  have hdisj : Disjoint (p.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]; intro x hx hxP; exact hx (hPp hxP)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors p)
  have hPSprime : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S P hP hdisj
  have hcomap : (P.map (algebraMap R S)).comap (algebraMap R S) = P :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    intro h
    have hx : algebraMap R S x ∈ P.map (algebraMap R S) := Ideal.mem_map_of_mem _ hxP
    rw [h, Ideal.mem_bot] at hx
    exact hx0 (hinj (by rw [hx, map_zero]))
  obtain ⟨w, hwPS, hw⟩ := hPSprime.exists_mem_prime_of_ne_bot hPS0
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl (S := S) w
  replace has : IsLocalization.mk' S a s = w := has
  have hwa : algebraMap R S a = w * algebraMap R S s := by
    have h := IsLocalization.mk'_spec S a s
    rw [has] at h
    exact h.symm
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hw.ne_zero).mpr hw
  have hQprime : ((Ideal.span {w}).comap (algebraMap R S)).IsPrime := inferInstance
  have haQ : a ∈ (Ideal.span {w}).comap (algebraMap R S) := by
    rw [Ideal.mem_comap, hwa]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self w)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hwa
    exact hw.ne_zero ((IsLocalization.map_units S s).mul_left_eq_zero.mp hwa.symm)
  have hQP : (Ideal.span {w}).comap (algebraMap R S) ≤ P := by
    rw [← hcomap]
    exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hwPS)
  have hQ0 : (Ideal.span {w}).comap (algebraMap R S) ≠ ⊥ := by
    intro h
    rw [h] at haQ
    exact ha0 (Ideal.mem_bot.mp haQ)
  have hQeq := hmin _ hQprime hQ0 hQP
  have haP : a ∈ P := by rw [← hQeq]; exact haQ
  have key : ∀ g : R, ∃ u : p.primeCompl, ∃ r : R, g ∈ P → (u : R) * g = a * r := by
    intro g
    by_cases hg : g ∈ P
    · have hgQ : g ∈ (Ideal.span {w}).comap (algebraMap R S) := by rw [hQeq]; exact hg
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hgQ
      obtain ⟨y, hy⟩ := hgQ
      obtain ⟨⟨r, u⟩, hru⟩ :=
        IsLocalization.mk'_surjective p.primeCompl (S := S) (y * IsLocalization.mk' S (1 : R) s)
      replace hru : IsLocalization.mk' S r u = y * IsLocalization.mk' S (1 : R) s := hru
      refine ⟨u, r, fun _ => hinj ?_⟩
      have h1 := IsLocalization.mk'_spec S r u
      have h2 := IsLocalization.mk'_spec' S (1 : R) s
      rw [map_one] at h2
      rw [hru] at h1
      rw [map_mul, map_mul, ← hy, hwa, ← h1]
      linear_combination (-(w * y * algebraMap R S u)) * h2
    · exact ⟨1, 0, fun h => absurd h hg⟩
  choose u r hur using key
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian P : P.FG)
  refine ⟨a, haP, ha0, ∏ x ∈ G, (u x : R), ?_, ?_⟩
  · show _ ∈ p.primeCompl
    exact Submonoid.prod_mem p.primeCompl fun x _ => (u x).2
  · intro g hg
    rw [← hG] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        have hxP : x ∈ P := by rw [← hG]; exact Submodule.subset_span hx
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (u x : R)) hx
        refine ⟨k * r x, ?_⟩
        rw [hk, mul_comm (u x : R) k, mul_assoc, hur x hxP]
        ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨r1, h1⟩ := hx
        obtain ⟨r2, h2⟩ := hy
        exact ⟨r1 + r2, by rw [mul_add, h1, h2, mul_add]⟩
    | smul c x _ hx =>
        obtain ⟨r1, h1⟩ := hx
        exact ⟨c * r1, by rw [smul_eq_mul, mul_left_comm, h1]; ring⟩

end GlobalTheory
