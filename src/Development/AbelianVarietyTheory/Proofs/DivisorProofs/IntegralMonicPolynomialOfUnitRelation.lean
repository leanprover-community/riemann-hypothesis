module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.QuadraticAlgebra.Defs

@[expose] public section

open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNorm

theorem exists_eq_of_finite (O : Type) {S : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing S] [Algebra O S] [Module.Finite O S]
    (h2 : IsUnit (2 : O)) {m d : S} (hm : IsUnit m) (hd : IsUnit d) :
    ∃ a b : S, m = a * a - d * (b * b) := by
  let T := QuadraticAlgebra S d 0
  haveI : Module.Finite O T := Module.Finite.trans S T
  let I : Ideal T := (maximalIdeal O).map (algebraMap O T)
  have hI : I ≤ (⊥ : Ideal T).jacobson := by
    refine le_sInf fun M hM => Ideal.map_le_iff_le_comap.2 ?_
    haveI := hM.2
    exact (eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)).ge
  haveI : HenselianRing T I := GlobalTheory.henselianRing_of_finite O I hI
  haveI : Finite (O ⧸ maximalIdeal O) := inferInstanceAs (Finite (ResidueField O))
  haveI : Module.Finite O (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ I) := Module.finite_of_finite (O ⧸ maximalIdeal O)
  have hc : ∀ s : S, starRingEnd T (algebraMap S T s) = algebraMap S T s := by
    intro s
    ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hcO : (starRingEnd T).comp (algebraMap O T) = algebraMap O T := by
    ext1 r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply O S T, hc]
  have hcI : I ≤ I.comap (starRingEnd T) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcO]
    exact Ideal.le_comap_map
  have h2S : IsUnit (2 : S) := by
    simpa only [map_ofNat] using h2.map (algebraMap O S)
  obtain ⟨x, hx⟩ := GlobalTheory.HenselianNorm.exists_norm_eq T I (starRingEnd T)
    (fun x => star_star x) (fun x hx => hcI hx)
    ⟨⟨0, 1⟩, by
      have h : ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩) * ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩)
          = algebraMap S T (2 * 2 * d) := by
        ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
        ring
      exact isUnit_of_mul_isUnit_left (h ▸ ((h2S.mul h2S).mul hd).map (algebraMap S T))⟩
    (algebraMap S T m) (hc m) (hm.map _)
  refine ⟨x.re, x.im, ?_⟩
  have := congrArg QuadraticAlgebra.re hx
  simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
  linear_combination -this

theorem exists_eq_of_isIntegral (O : Type) {A : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    (h2 : IsUnit (2 : O)) {m m' d d' : A} (hm : m * m' = 1) (hd : d * d' = 1)
    (im : IsIntegral O m) (im' : IsIntegral O m') (id : IsIntegral O d) (id' : IsIntegral O d') :
    ∃ a b : A, m = a * a - d * (b * b) := by
  let S := Algebra.adjoin O ({m, m', d, d'} : Set A)
  haveI : Module.Finite O S := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _) (by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have h1 : m ∈ S := Algebra.subset_adjoin (by simp)
  have h1' : m' ∈ S := Algebra.subset_adjoin (by simp)
  have h3 : d ∈ S := Algebra.subset_adjoin (by simp)
  have h3' : d' ∈ S := Algebra.subset_adjoin (by simp)
  obtain ⟨a, b, h⟩ := exists_eq_of_finite O h2 (m := (⟨m, h1⟩ : S)) (d := ⟨d, h3⟩)
    (IsUnit.of_mul_eq_one ⟨m', h1'⟩ (Subtype.ext hm)) (IsUnit.of_mul_eq_one ⟨d', h3'⟩ (Subtype.ext hd))
  exact ⟨a, b, congrArg Subtype.val h⟩

end GlobalTheory.OddLocalNorm
