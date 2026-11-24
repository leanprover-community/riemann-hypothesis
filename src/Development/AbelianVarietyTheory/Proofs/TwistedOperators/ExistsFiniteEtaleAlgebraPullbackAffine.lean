module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_finiteEtale_algebra_pullback : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  intro X Y π hfin het R _ x
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := S)
    (e.hom ≫ pullback.snd π x)
  letI : Algebra R S := f.hom.toAlgebra
  have hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x := hf
  refine ⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  · have h1 : Etale (Spec.map f) := by rw [hf]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)
  · rw [hsp, Category.assoc, Category.assoc, pullback.condition]
  · intro hs
    have h1 : Surjective (Spec.map f) := by rw [hf]; infer_instance
    exact h1.surj
  · intro Ω _ φ w hw
    obtain ⟨g, hg⟩ := Spec.map_surjective (R := S) (S := CommRingCat.of Ω)
      (pullback.lift w (spMap φ) hw ≫ e.inv)
    have key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔
        spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ := by
      intro χ
      rw [← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      constructor
      · intro h; rw [h]
      · intro h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv := hg
    refine ⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · rintro χ ⟨h1, h2⟩
      have h3 : spMap χ = spMap g.hom := by
        rw [hg', Iso.eq_comp_inv]
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.assoc]; exact h2
        · rw [pullback.lift_snd, Category.assoc]; exact (key _).1 h1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)

end GlobalTheory.HeckeEx
