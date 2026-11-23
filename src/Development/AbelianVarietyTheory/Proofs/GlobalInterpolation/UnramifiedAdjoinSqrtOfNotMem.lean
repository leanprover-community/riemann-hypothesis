module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Unramified.Locus
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Polynomial

theorem GlobalTheory.unramified_adjoin_sqrt_of_not_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : 𝓞 (maximalRealSubfield L)) (δ : L), δ ^ 2 = ((a : maximalRealSubfield L) : L) → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), 2 * a ∉ (w.under (𝓞 (maximalRealSubfield L))).asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ a δ hδ hδK w ha

  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    exact (RingOfIntegers.isIntegral_coe a).algebraMap
  let d : 𝓞 L := ⟨δ, hint⟩
  have hd : algebraMap (𝓞 L) L d = δ := rfl
  have hdA : IsIntegral (𝓞 (maximalRealSubfield L)) d := Algebra.IsIntegral.isIntegral d
  have hδR : IsIntegral (maximalRealSubfield L) δ := Algebra.IsIntegral.isIntegral δ
  have hsq : d ^ 2 = algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hd, hδ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L]
    rfl

  have hfin : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hdegK : (minpoly (maximalRealSubfield L) δ).natDegree = 2 := by
    refine le_antisymm (hfin ▸ minpoly.natDegree_le δ) ?_
    rw [minpoly.two_le_natDegree_iff hδR]
    rintro ⟨x, hx⟩
    exact hδK (hx ▸ x.2)
  have hdeg : (minpoly (𝓞 (maximalRealSubfield L)) d).natDegree = 2 := by
    rw [← hdegK, ← hd, minpoly.isIntegrallyClosed_eq_field_fractions (maximalRealSubfield L) L hdA,
      (minpoly.monic hdA).natDegree_map]

  have hpoly : minpoly (𝓞 (maximalRealSubfield L)) d = X ^ 2 - C a := by
    have hm : (X ^ 2 - C a : (𝓞 (maximalRealSubfield L))[X]).Monic := monic_X_pow_sub_C a two_ne_zero
    have hroot : aeval d (X ^ 2 - C a) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hsq, sub_self]
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hdA) hm
      (minpoly.isIntegrallyClosed_dvd hdA hroot) ?_).symm
    rw [hdeg, natDegree_X_pow_sub_C _]

  have hadj : Algebra.adjoin (maximalRealSubfield L) {algebraMap (𝓞 L) L d} = ⊤ := by
    have htop : IntermediateField.adjoin (maximalRealSubfield L) {δ} = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_le le_top (by
        rw [IntermediateField.finrank_top', hfin, IntermediateField.adjoin.finrank hδR, hdegK])
    rw [hd, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hδR.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]

  have hmem : 2 * d ∈ differentIdeal (𝓞 (maximalRealSubfield L)) (𝓞 L) := by
    have := aeval_derivative_mem_differentIdeal (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L d hadj
    simpa [hpoly, derivative_X_pow, one_add_one_eq_two, map_ofNat] using this

  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  have h2d : 2 * d ∈ w.asIdeal := Ideal.dvd_iff_le.mp hdvd hmem
  have h4a : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) (2 * (2 * a)) ∈ w.asIdeal := by
    have := w.asIdeal.mul_mem_left (2 * d) h2d
    convert this using 1
    rw [map_mul, map_mul, map_ofNat, ← hsq]
    ring
  have h4a' : 2 * (2 * a) ∈ (w.under (𝓞 (maximalRealSubfield L))).asIdeal := h4a
  rcases (w.under (𝓞 (maximalRealSubfield L))).isPrime.mem_or_mem h4a' with h | h
  · exact ha (Ideal.mul_mem_right a _ h)
  · exact ha h
