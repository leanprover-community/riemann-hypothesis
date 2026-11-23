module

public import Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionBasicProperties
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.Lemma
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

namespace LateralTheory.EtaleFoundations.ResBasicPf

variable {R : Type} [CommRing R]

noncomputable def descH {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F)) 0⟩

lemma resMap_eq {F G : Shv R} (φ : F ⟶ G) : resMap R φ = (descH φ).hom' := rfl

lemma resι_eq (F : Shv R) : resι R F =
    (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

lemma kinj (F : Shv R) : (res R F).IsKInjective :=
  isKInjective_of_injective (injectiveResolution F).cochainComplex 0

lemma inj (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

lemma ge (F : Shv R) : (res R F).IsStrictlyGE 0 :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)

lemma qis (F : Shv R) : QuasiIso (resAug F) :=
  inferInstanceAs (QuasiIso (injectiveResolution F).ι')

lemma mono (F : Shv R) : Mono (resι R F) := by
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h2 : Mono ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := inferInstance
  rw [resι_eq]; exact @mono_comp _ _ _ _ _ _ h0 _ h2

lemma dzero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι_eq]
  change _ ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  erw [Category.assoc, Iso.inv_hom_id_assoc, InjectiveResolution.ι_f_zero_comp_complex_d_assoc, zero_comp]

lemma aug_nat {F G : Shv R} (φ : F ⟶ G) :
    resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G := by
  rw [resMap_eq]; exact InjectiveResolution.Hom.ι'_comp_hom' _

lemma ι_nat {F G : Shv R} (φ : F ⟶ G) : resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  have h := congrArg (fun f => sglι F ≫ HomologicalComplex.Hom.f f 0) (aug_nat φ)
  simp only [HomologicalComplex.comp_f] at h
  change resι R F ≫ _ = _ at h
  rw [h]
  simp [sglι, resι, resAug, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self]

end LateralTheory.EtaleFoundations.ResBasicPf

open LateralTheory.EtaleFoundations.ResBasicPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_properties_of_mathlib : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties := by
  intro R _ F
  exact ⟨kinj F, inj F, ge F, qis F, rfl, mono F, dzero F, fun G φ => ⟨aug_nat φ, ι_nat φ⟩⟩
