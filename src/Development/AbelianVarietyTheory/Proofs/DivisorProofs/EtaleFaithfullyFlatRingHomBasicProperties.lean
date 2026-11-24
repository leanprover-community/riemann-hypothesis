module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro A
    change (RingHom.id A).Etale ∧ (RingHom.id A).FaithfullyFlat
    exact ⟨RingHom.Etale.of_bijective Function.bijective_id,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  · intro A B C f g hf hg
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
