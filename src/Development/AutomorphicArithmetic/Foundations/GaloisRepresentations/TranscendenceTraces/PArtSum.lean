module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_local (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [Module.Finite Ω R] [IsLocalRing R] : Module.length R R = Module.finrank Ω R := by
  have h1 := IsLocalRing.length_restrictScalars Ω R R
  have h2 : Module.length (IsLocalRing.ResidueField Ω) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (S := Ω) (M := IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective]
    haveI : Module.Finite Ω (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R)).toLinearMap
        IsLocalRing.residue_surjective
    rw [Module.length_eq_finrank,
      Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral]
    rfl
  rw [h2, mul_one, Module.length_eq_finrank] at h1
  exact h1.symm

theorem UpperTheory.Gal.TranscendenceTraces.artSum_of : ArtSum := by
  intro Ω B _ _ _ _ _
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum B))
  let e : B ≃ₗ[Ω] PrimeSpectrum.PiLocalization B :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization B).restrictScalars Ω).toLinearMap hbij
  haveI : Module.Finite Ω (PrimeSpectrum.PiLocalization B) := Module.Finite.equiv e
  haveI : ∀ P : PrimeSpectrum B, Module.Finite Ω (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := Ω) (φ := fun P : PrimeSpectrum B => Localization.AtPrime P.asIdeal) P)
      (fun x => ⟨Pi.single P x, by simp⟩)
  rw [finsum_eq_sum_of_fintype, e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [length_local Ω (Localization.AtPrime P.asIdeal)]
  rfl
