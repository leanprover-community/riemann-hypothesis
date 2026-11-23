module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCompDim
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem homogeneousComponent_map_coeffs {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem SpecCompDim.proof (hCone : ConeDimOfChowForm.Statement) (hFib : FibreCompDim.Statement) :
    SpecCompDim.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : I.IsPrime := hI.isPrime
  let k := v.asIdeal.ResidueField
  let φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (𝓞 K) k)
  let ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap (𝓞 K) K)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hker : RingHom.ker φ = Ideal.map C v.asIdeal := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWprime : W.IsPrime := hWmin.1.1
  have hkerW : RingHom.ker φ ≤ W := hker ▸ le_sup_right.trans hWmin.1.2

  have hP : (integralModel I).IsPrime := Ideal.comap_isPrime ψ I
  have hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, integralModel, Ideal.mem_bot]
    constructor
    · intro h
      by_contra hc
      have hu : IsUnit (ψ (C c)) := by
        rw [show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]
        exact (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C
      exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    · rintro rfl
      simp
  have hPloc : (integralModel I).map ψ = I := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)
    have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K
    exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) K) I
  have hdim := hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin
  rw [hPloc, hCone K n (e + 1) I f hI hf] at hdim
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩
  ·
    have hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes := by
      change W.map φ ∈ ((integralModel I).map φ).minimalPrimes
      rw [Ideal.minimalPrimes_map_of_surjective hφ, hker]
      exact ⟨W, hWmin, rfl⟩
    refine MinimalPrimeHomog.proof k n _ _ ?_ hmin
    intro g hg d
    change g ∈ (integralModel I).map φ at hg
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hg
    rw [homogeneousComponent_map_coeffs]
    refine Ideal.mem_map_of_mem φ ?_
    change ψ (homogeneousComponent d p) ∈ I
    rw [← homogeneousComponent_map_coeffs]
    exact hI.isHomog _ hp d
  ·
    obtain ⟨j, hj⟩ := hWrel
    refine ⟨j, fun h => hj ?_⟩
    have h' : X j ∈ (W.map φ).comap φ := by
      rw [Ideal.mem_comap, map_X]
      exact h
    rwa [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerW] at h'

end

end GroundTheory.Heights₂.Heights.Vertical
