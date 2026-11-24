module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.BigOperators
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

private theorem flatAss_ann {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) (r : R) (h : a • r = 0) :
    r ∈ P.map (algebraMap A R) := by
  have h1 : ∑ _i : Fin 1, a • r = 0 := by
    rw [Fin.sum_univ_one]
    exact h
  obtain ⟨l, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a)
      (x := fun _ : Fin 1 => r) h1
  have hr : r = ∑ j, c 0 j • y j := hy 0
  rw [hr]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))
  have h2 := hc j
  rw [Fin.sum_univ_one] at h2
  rw [mul_comm]
  exact h2

private theorem flatAss_annih {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) :
    Module.annihilator R (Ideal.span {algebraMap A R a} : Ideal R) = P.map (algebraMap A R) := by
  apply le_antisymm
  · intro r hr
    have h0 : r * algebraMap A R a = 0 :=
      congrArg Subtype.val (Module.mem_annihilator.1 hr
        ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)
    refine flatAss_ann P a hmem r ?_
    rw [Algebra.smul_def, mul_comm]
    exact h0
  · refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hn
    apply Subtype.ext
    change algebraMap A R b * (c * algebraMap A R a) = 0
    rw [mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]

private theorem flatAss_alg {A R : Type} [CommRing A] [CommRing R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (Q : Ideal R) (hQ : Q.IsPrime)
    (hmin : ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R)
    (P : Ideal A) (hP : P ∈ associatedPrimes A A) (hPQ : P ≤ Q.comap (algebraMap A R)) :
    P ∈ minimalPrimes A := by
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  obtain ⟨hPp, a, hPa⟩ := isAssociatedPrime_iff.1 hP
  have hmem : ∀ b, b ∈ P ↔ b * a = 0 := fun b => by
    rw [hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hmapQ : P.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.2 hPQ
  haveI := hQ
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hmapQ
  have hQ'ass : Q' ∈ associatedPrimes R R := by
    have h1 := hQ'min
    rw [← flatAss_annih P a hmem] at h1
    exact associatedPrimes.subset_of_injective (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)
  have hQ'm := hmin Q' hQ'ass hQ'Q
  haveI hQ'p : Q'.IsPrime := hQ'min.1.1
  refine ⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩
  haveI := hp.1
  have hPc : P ≤ Q'.comap (algebraMap A R) := Ideal.map_le_iff_le_comap.1 hQ'min.1.2
  haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩
  obtain ⟨Q'', hle, hQ''p, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)
  have hge := hQ'm.2 ⟨hQ''p, bot_le⟩ hle
  have heq : Q'' = Q' := le_antisymm hle hge
  rw [hlies.over, heq]
  exact hPc

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatAss :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ Q : Ideal R, Q.IsPrime →
        (∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R) → ∀ P ∈ associatedPrimes A A, P ≤ Q.comap ι → P ∈ minimalPrimes A :=
  fun A R _ _ _ _ ι hι Q hQ hmin P hP hPQ =>
    @flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ
