module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SecRules

theorem secOn_zero {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) :
    SecOn f 0 := by
  haveI : Subsingleton (Localization.Away (0 : S)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : S)) (Submonoid.mem_powers 0)
  haveI : IsEmpty (Spec (CommRingCat.of (Localization.Away (0 : S)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (Localization.Away (0 : S))))
  exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _⟩

theorem secOn_mul {S : Type} [CommRing S] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of S)}
    (e e' : S) (h : SecOn f e) : SecOn f (e * e') := by
  obtain ⟨s, hs⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away e) (P := Localization.Away (e * e')) e e')) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom]
  exact IsLocalization.Away.awayToAwayRight_eq e e' a

theorem section_of_secOn_one {S : Type} [CommRing S] {Y : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of S)} (h : SecOn f 1) :
    ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨s, hs⟩ := h
  let eqv := IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  refine ⟨Spec.map (CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S)) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  have hid : CommRingCat.ofHom (Algebra.algebraMap S (Localization.Away (1 : S))) ≫
      CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S) = 𝟙 _ := by
    ext a
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.id_apply]
    exact eqv.symm.commutes a
  rw [hid, Spec.map_id]

theorem main : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)),
    SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧
      (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  intro S _ Y f
  exact ⟨secOn_zero Y f, fun e e' h => secOn_mul e e' h, section_of_secOn_one⟩

end GlobalTheory.CompanionTheory.SecRules
