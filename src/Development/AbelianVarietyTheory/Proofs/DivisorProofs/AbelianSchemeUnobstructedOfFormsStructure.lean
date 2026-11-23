module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLiftStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem unobDim_of_formSt : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  intro hF hP hA R _ I hI R₀ _ π hπ hk A₀ _ g hab hsm
  obtain ⟨X, i, hpb, hsmX⟩ := GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero hF hP R R₀ I hI π hπ hk A₀ g hab hsm
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
  have h1 : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ A₀.hom = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀)
  obtain ⟨e, he, he'⟩ := GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb hsmX _ h1
  have P := IsPullback.of_hasPullback X.hom X.hom
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    simp only [Category.assoc, hpb.w]
    rw [← Category.assoc, ← Category.assoc, Over.w (fst A₀ A₀), Over.w (snd A₀ A₀)]
  let l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left := P.lift _ _ w
  have l1 : l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := P.lift_fst _ _ w
  have l2 : l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := P.lift_snd _ _ w
  obtain ⟨m, hm⟩ := GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift hF hA R R₀ I hI π hπ hk A₀ g hab hsm X i hpb hsmX e he he' l l1 l2
  obtain ⟨G, hG, hab'⟩ := GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hab X i hpb hsmX e he he'
    l l1 l2 m hm
  exact ⟨X, G, i, hG, hab'⟩

end GlobalTheory.Obs
