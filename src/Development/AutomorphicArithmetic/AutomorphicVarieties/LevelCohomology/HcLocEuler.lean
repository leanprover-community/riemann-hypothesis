module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.ZMod.LocalRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Mathlib.Data.FunLike.Fintype

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem ef_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have := v.isPrime
  have h1 := Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal
  have h2 := Ideal.inertiaDeg_pos v.asIdeal ℤ
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨v.asIdeal, inferInstance, ⟨rfl⟩⟩)
  rw [hsum] at hle
  exact le_antisymm hle (Nat.mul_pos h1 h2)

theorem UpperTheory.V.X.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := ℚ) A) M), ContAction ρ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + (if p = l then finrank k M else 0) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) ρ) := by
  intro hF hT hE0 Ω _ _ _ l _ p hp A hA k _ _ hc M _ _ _ _ _ ρ hρ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) A hA
  have hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := hw
  obtain ⟨hH1, hH2, hRamified, hUnramified, hDual⟩ :=
    UpperTheory.V.GC.locEuler hF hT hE0 ℚ Ω l w A hAw k M ρ hρ
  refine ⟨hH1, hH2, ?_, hDual⟩
  by_cases h : p = l
  · subst p
    have hd : locDeg w = 1 := ef_eq_one w
    simpa [hd] using hRamified hw
  · have hnot : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro hlw
      apply w.isPrime.ne_top
      have hl : l.Prime := Fact.out
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 h)).map
        (Int.castRingHom (𝓞 ℚ))
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw))
        (w.asIdeal.mul_mem_left _ (by simpa using hlw))
    simpa [h] using hUnramified hnot
