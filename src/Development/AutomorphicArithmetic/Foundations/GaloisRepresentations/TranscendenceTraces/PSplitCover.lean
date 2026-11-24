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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_hom {R Ω : Type} [CommRing R] [Field Ω] (x : gp Ω ⟶ Spec (CommRingCat.of R)) :
    ∃ φ : R →+* Ω, x = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [Spec.map_preimage]

private lemma map_comp' {R S Ω : Type} [CommRing R] [CommRing S] [CommRing Ω] (a : R →+* S) (φ : S →+* Ω) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (φ.comp a)) := by
  rw [← Spec.map_comp]
  rfl

private lemma map_inj' {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

private lemma pt_map {R Ω : Type} [CommRing R] [Field Ω] (f : R →+* Ω) :
    (pt (Spec.map (CommRingCat.ofHom f))).asIdeal = RingHom.ker f := by
  ext a
  simp only [pt]
  show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem UpperTheory.Gal.TranscendenceTraces.splitCover_of :
    SplitField → GalTrans → SplitCover := by
  intro hsf hgt A B _ _ _ _ _ _
  obtain ⟨L, _, _, _, _, _, _, hfin, hsp⟩ := hsf A B
  set C := integralClosure A L
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    have h1 : algebraMap A L a = algebraMap A L b := by
      have := congrArg (fun c : C => (c : L)) hab
      simpa using this
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) L a,
      IsScalarTower.algebraMap_apply A (FractionRing A) L b] at h1
    exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)
  have key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω),
      RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥ := by
    intro Ω _ φ h
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    change Ideal.comap (algebraMap A C) (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker]
    exact h
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C),
    fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)),
    fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B),
    ?_, ?_, hfin, ?_, ?_, ?_⟩
  · exact IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  · refine ⟨fun p => ?_⟩
    have hp : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by
      rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
      exact bot_le)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  · intro j
    rw [map_comp']
    congr 2
    exact j.comp_algebraMap
  · intro Ω _ x x' hxx
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨φ', rfl⟩ := exists_hom x'
    simp only [map_comp'] at hxx
    obtain ⟨g, hg⟩ := hgt A L Ω φ φ' (map_inj' hxx)
    let e : (B →ₐ[A] C) ≃ (B →ₐ[A] C) :=
      { toFun := fun j => (g.symm : C →ₐ[A] C).comp j
        invFun := fun j => (g : C →ₐ[A] C).comp j
        left_inv := fun j => by
          ext b
          simp
        right_inv := fun j => by
          ext b
          simp }
    refine ⟨e, fun j => ⟨?_, ?_⟩⟩
    · simp only [map_comp']
      congr 2
      ext b
      simp [e, hg]
    · apply PrimeSpectrum.ext
      ext b
      simp [e]
  · intro Ω _ x z hz hbot
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨ζ, rfl⟩ := exists_hom z
    simp only [map_comp'] at hz
    rw [map_comp', pt_map] at hbot
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)
    have hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔
        φ.comp (j : B →+* C) = ζ := by
      intro j
      rw [map_comp']
      exact ⟨map_inj', fun h => by rw [h]⟩
    obtain ⟨j0, hj0, hu⟩ := hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)
    refine ⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩
    rw [hiff] at hj
    apply PrimeSpectrum.ext
    rw [pt_map, ← hj]
    ext b
    simp [map_eq_zero_iff _ hφ]
