module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
