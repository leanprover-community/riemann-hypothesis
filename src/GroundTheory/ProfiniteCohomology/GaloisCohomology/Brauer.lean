module

public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.ColimitDefs
import GroundTheory.ProfiniteCohomology.Colimit
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology IntermediateField

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

noncomputable def unitsInflation (E : IntermediateField K L) [FiniteDimensional K E] [Normal K E]
    (n : ℕ) : groupCohomology (galUnits.{u} K E) n ⟶ cohomology (galUnits.{u} K L) n :=
  HomologicalComplex.homologyMap (unitsInflationCochains E) n

noncomputable abbrev brauerInflation (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] : groupCohomology (galUnits.{u} K E) 2 ⟶ galoisBrauerGroup K L :=
  unitsInflation E 2

theorem quotientEquivGal_mk_eq_restrictNormalHom (U : OpenNormalSubgroup Gal(L/K))
    (σ : Gal(L/K)) :
    quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) =
      AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) σ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [quotientEquivGal_mk_apply]
  exact (AlgEquiv.restrictNormal_commutes σ _ x).symm

theorem inflation_galUnits_eq (U : OpenNormalSubgroup Gal(L/K)) (n : ℕ) :
    inflation (galUnits.{u} K L) U n =
      (groupCohomologyQuotientGalUnitsIso U n).hom ≫
        unitsInflation (fixedField (U : Subgroup Gal(L/K))) n := by
  rw [groupCohomologyQuotientGalUnitsIso, groupCohomology.mapIso_hom]
  unfold inflation unitsInflation
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K L)).f m), HomologicalComplex.comp_f,
    Category.assoc]
  ext x : 2
  funext g
  have hq : ∀ i, (quotientEquivGal U).symm
      (AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) (g i)) =
        (g i : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) := fun i =>
    (MulEquiv.symm_apply_eq _).2 (quotientEquivGal_mk_eq_restrictNormalHom U (g i)).symm
  change ((x fun i => (g i : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))).1 : Additive Lˣ) =
    (unitsRestrictHom (fixedField (U : Subgroup Gal(L/K)))).hom
      (invariantsGalUnitsAddEquiv (U : Subgroup Gal(L/K))
        (x fun i => (quotientEquivGal U).symm
          (AlgEquiv.restrictNormalHom (fixedField (U : Subgroup Gal(L/K))) (g i))))
  simp only [hq]
  exact Additive.toMul.injective (Units.ext rfl)

theorem exists_unitsInflation_eq (n : ℕ) (x : cohomology (galUnits.{u} K L) n) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : groupCohomology (galUnits.{u} K E.toIntermediateField) n),
      (unitsInflation E.toIntermediateField n).hom y = x := by
  obtain ⟨U, y, rfl⟩ := exists_inflation_eq (galUnits.{u} K L) n x
  refine ⟨fixedFiniteGalois U, (groupCohomologyQuotientGalUnitsIso U n).hom.hom y, ?_⟩
  rw [inflation_galUnits_eq]
  rfl

theorem exists_brauerInflation_eq (x : galoisBrauerGroup K L) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : groupCohomology (galUnits.{u} K E.toIntermediateField) 2),
      (brauerInflation E.toIntermediateField).hom y = x :=
  exists_unitsInflation_eq 2 x

end GroundTheory.ProfCoh
