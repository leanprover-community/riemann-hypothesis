module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
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
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicLoc

theorem exists_away_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A) (p : Ideal A) [p.IsPrime], ∃ f ∉ p, CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1 := by
  intro A _ c p _
  letI := @Module.addCommMonoidToAddCommGroup A
  haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)
  refine ⟨f, hf, ?_⟩
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)

theorem exists_etale_faithfullyFlat_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  intro A _ c
  classical
  let T : Set A := {f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hf1⟩ := exists_away_mapAlgebra_eq_one A c m
    exact hf (hle (Ideal.subset_span hf1))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  let R : s → Type := fun i => Localization.Away (i : A)
  haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)
  have halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i) :=
    fun i => RingHom.ext fun _ => rfl
  refine ⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hs, Ideal.span_le]
      intro x hx
      exact h ⟨x, hx⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (R i) (i : A)]
      exact hi
    obtain ⟨q, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, halg]
  · apply GlobalTheory.PicPi.eq_one_of_forall
    intro i
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg,
      CommRing.Pic.mapRingHom_algebraMap]
    exact hsT i.2

end GlobalTheory.PicLoc
