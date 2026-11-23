module

import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.Linter.Style
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

namespace SecBGeneric

variable {K : Type*} [Field K] [NumberField K]

theorem parToFrac_comp_algebraMap (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (parToFrac e n v).comp (algebraMap (𝓞 K) (ParDVR e n v)) =
      (kToFrac K e n).comp (algebraMap (𝓞 K) K) := by
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem parToFrac_parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by
  rw [parY, parToFrac, IsLocalization.lift_eq, parYF]

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by

  simp [linForm, map_sum]

theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by
  apply GroundTheory.Heights₂.Heights.Vertical.SecBFinite.map_integralModel <;> assumption

theorem map_secIdeal {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (secIdeal (modelR e I v) (parY e n v)).map (MvPolynomial.map (parToFrac e n v)) =
      secIdeal (idealF e I) (parYF K e n) := by
  have h1 : (modelR e I v).map (MvPolynomial.map (parToFrac e n v)) = idealF e I := by
    have hc : (MvPolynomial.map (parToFrac e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) : MvPolynomial (Fin n) (𝓞 K) →+* _) =
        (MvPolynomial.map (kToFrac K e n)).comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply, MvPolynomial.map_map, parToFrac_comp_algebraMap]
    rw [modelR, Ideal.map_map, hc, ← Ideal.map_map, map_integralModel, idealF]
  have h2 : (Ideal.span (Set.range (secForm (parY e n v)))).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span (Set.range (secForm (parYF K e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [secForm, map_linForm, parToFrac_parY]
  have h3 : (Ideal.span {chartForm (parY e n v) - 1}).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span {chartForm (parYF K e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    simp only [parToFrac_parY]
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]

end SecBGeneric


open SecBGeneric in
theorem SecBGeneric.proof : SecBGeneric.Statement := by
  intro K _ _ n e I v _
  have hJ := map_secIdeal e I v
  let M : Submonoid (MvPolynomial (Fin n) (ParDVR e n v)) :=
    (nonZeroDivisors (ParDVR e n v)).map (MvPolynomial.C : ParDVR e n v →+* MvPolynomial (Fin n) (ParDVR e n v))
  let φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n) :=
    Ideal.quotientMap _ (MvPolynomial.map (parToFrac e n v)) (hJ ▸ Ideal.le_comap_map)
  refine ⟨φ, fun j => ?_, fun r => ?_, ?_⟩
  · simp [φ, secCoord, Ideal.quotientMap_mk]
  · have hr : algebraMap (ParDVR e n v) (SecB e I v) r =
        Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (C r) := rfl
    rw [hr]
    simp only [φ, Ideal.quotientMap_mk, map_C]
    rfl
  let := φ.toAlgebra
  let : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsFractionRing (ParDVR e n v) (ParFrac K e n) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl _ _
  let : Algebra (MvPolynomial (Fin n) (ParDVR e n v)) (MvPolynomial (Fin n) (ParFrac K e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (ParDVR e n v)) (ParFrac K e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (ParFrac K e n)) (S' := SecAlg (idealF e I) (parYF K e n))
    (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (idealF e I) (parYF K e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  have hM : Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)) =
      M.map (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) := by
    ext x
    simp only [M, Algebra.algebraMapSubmonoid, Submonoid.mem_map, exists_exists_and_eq_and]
    exact Iff.rfl
  rw [hM]
  exact key

end

end GroundTheory.Heights₂.Heights.Vertical
