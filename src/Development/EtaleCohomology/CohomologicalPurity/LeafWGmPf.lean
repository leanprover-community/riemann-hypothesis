module

public import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem intPoly_smooth : (algebraMap ℤ (Polynomial ℤ)).Smooth := by
  haveI : Algebra.FormallySmooth ℤ (Polynomial ℤ) :=
    inferInstance
  haveI : Algebra.Smooth ℤ (Polynomial ℤ) := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem laurent_smooth : (algebraMap ℤ (LaurentPolynomial ℤ)).Smooth := by
  have h2 : (algebraMap (Polynomial ℤ) (LaurentPolynomial ℤ)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (LaurentPolynomial ℤ) (Polynomial.X : Polynomial ℤ)
  have := RingHom.Smooth.comp intPoly_smooth h2
  convert this
  exact RingHom.ext_int _ _

theorem gm_from_smooth : Smooth (specZIsTerminal.from Gm) := by
  have e : specZIsTerminal.from Gm =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := specZIsTerminal.hom_ext _ _
  rw [e, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact laurent_smooth

theorem gmU_smooth (X : Scheme.{0}) : Smooth (prod.fst : X ⨯ Gm ⟶ X) := by
  have hp := IsPullback.of_is_product (limit.isLimit (pair X Gm)) specZIsTerminal
  have := gm_from_smooth
  exact MorphismProperty.of_isPullback (P := @Smooth) hp.flip this

theorem gmU_surj (X : Scheme.{0}) : Surjective (prod.fst : X ⨯ Gm ⟶ X) := by
  let pt : Spec (CommRingCat.of ℤ) ⟶ Gm :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1))
  let s : X ⟶ X ⨯ Gm := prod.lift (𝟙 X) (specZIsTerminal.from X ≫ pt)
  have hs : s ≫ prod.fst = 𝟙 X := prod.lift_fst _ _
  have : Surjective (s ≫ prod.fst) := by rw [hs]; infer_instance
  exact Surjective.of_comp s prod.fst

theorem LeafWGm_of : LeafWGm := fun _ _ _ _ => ⟨gmU_smooth _, gmU_surj _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
