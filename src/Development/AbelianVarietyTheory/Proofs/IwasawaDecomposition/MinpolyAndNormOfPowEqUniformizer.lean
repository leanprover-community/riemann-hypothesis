module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameEis

open Polynomial

theorem two_le_normV (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')
  omega

theorem minpoly_and_norm_of_pow_eq_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E)) (ϖ : 𝓞 E),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
      minpoly E π = Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E) ∧
      Algebra.norm E (IntermediateField.AdjoinSimple.gen E π) = (-1) ^ normV v * (ϖ : E) := by
  intro E Ω _ _ _ _ v ϖ hmem hnot π hπ
  have hq := two_le_normV E v
  set n := normV v - 1 with hn
  have hn1 : 0 < n := by omega
  have hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hn1.ne'
  have hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n := natDegree_X_pow_sub_C _
  have hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using v.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hn1.ne, ite_eq_left rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)
  have hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  have hirrE : Irreducible (X ^ n - C (ϖ : E)) := by
    rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr
  have hmonE : (X ^ n - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hn1.ne'
  have hroot : aeval π (X ^ n - C (ϖ : E)) = 0 := by
    simp [hπ]
  have hmin : minpoly E π = X ^ n - C (ϖ : E) :=
    (minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm
  refine ⟨hmin, ?_⟩
  have hx : IsIntegral E π := ⟨_, hmonE, hroot⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C _]
  rw [coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hn1.ne, ite_eq_left rfl, zero_sub]
  have : normV v = n + 1 := by omega
  rw [this, pow_succ]; ring

end GlobalTheory.TameEis
