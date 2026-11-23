module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIffStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem exists_section_of_etale (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O))
    [Etale f] [Surjective f] : ∃ s : Spec (CommRingCat.of O) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨y, hy⟩ := (Surjective.surj (f := f)) (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O)
  let U := Y.affineOpenCover
  obtain ⟨x, hx⟩ := U.covers y
  have hi : IsOpenImmersion (U.f (U.idx y)) := U.map_prop _
  let φ : CommRingCat.of O ⟶ U.X (U.idx y) := Spec.preimage (U.f (U.idx y) ≫ f)
  have hφ : Spec.map φ = U.f (U.idx y) ≫ f := Spec.map_preimage _
  have he : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hE : φ.hom.Etale := HasRingHomProperty.Spec_iff.mp he
  letI : Algebra O (U.X (U.idx y)) := φ.hom.toAlgebra
  haveI : Algebra.Etale O (U.X (U.idx y)) := hE
  have h1 : (Spec.map φ).base x = (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O) := by
    rw [hφ]
    change f (U.f (U.idx y) x) = _
    rw [hx, hy]
  let p : PrimeSpectrum (U.X (U.idx y)) := x
  obtain ⟨s, hs⟩ := (GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed O).mpr ⟨inferInstance, inferInstance⟩ (U.X (U.idx y)) p.asIdeal
    (congrArg PrimeSpectrum.asIdeal h1)
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ U.f (U.idx y), ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact s.commutes a

theorem UpperTheory.cohomology_subsingleton_pos_of_strictly_henselian :
    ∀ (R : Type) [CommRing R] (O : Type) [CommRing O], SH O → ∀ (F : Shv R) (n : ℤ), 0 < n → Subsingleton (H R (sp O) F n) := by
  intro R _ O _ hO F n hn
  obtain ⟨_, _⟩ := hO
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨Y, f, hf, hsurj, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R _ F n hn x
  obtain ⟨s, hs⟩ := exists_section_of_etale O f
  calc x = pull R (sch.map (s ≫ f)) F n x := by
        rw [hs, sch.map_id, pull_id]
    _ = 0 := by
        rw [sch.map_comp, pull_comp, hx, map_zero]
