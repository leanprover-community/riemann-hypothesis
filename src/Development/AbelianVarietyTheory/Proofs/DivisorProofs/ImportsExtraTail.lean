module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  apply GlobalTheory.RetractionLiftSection.exists_retraction <;> assumption

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
