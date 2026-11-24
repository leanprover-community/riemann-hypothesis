module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
public import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLimitDefs
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolPrime
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLevels
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield

open scoped DirectSum

noncomputable section

variable (K : FiniteSubfield)

instance isDiscreteRep_idelesShortComplexRes_X₁ : IsDiscreteRep (idelesShortComplexRes K).X₁ :=
  inferInstanceAs (IsDiscreteRep (unitsLimitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₂ : IsDiscreteRep (idelesShortComplexRes K).X₂ :=
  inferInstanceAs (IsDiscreteRep (limitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₃ : IsDiscreteRep (idelesShortComplexRes K).X₃ :=
  inferInstanceAs (IsDiscreteRep (classLimitRep K))

abbrev unitsToIdeles (n : ℕ) : cohomology (unitsLimitRep K) n ⟶ cohomology (limitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).f n

abbrev idelesToClasses (n : ℕ) : cohomology (limitRep K) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).g n

abbrev classesToUnits (n : ℕ) : cohomology (classLimitRep K) n ⟶ cohomology (unitsLimitRep K) (n + 1) :=
  δ (idelesShortComplexRes_shortExact K) n (n + 1) rfl

theorem exists_unitsToIdeles_eq (n : ℕ) (y : cohomology (limitRep K) n)
    (hy : (idelesToClasses K n).hom y = 0) : ∃ x, (unitsToIdeles K n).hom x = y :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₂ (idelesShortComplexRes_shortExact K) n)) hy

theorem exists_classesToUnits_eq (n : ℕ) (x : cohomology (unitsLimitRep K) (n + 1))
    (hx : (unitsToIdeles K (n + 1)).hom x = 0) : ∃ c, (classesToUnits K n).hom c = x :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₁ (idelesShortComplexRes_shortExact K) n (n + 1) rfl)) hx

theorem injective_cohomologyMap_units_ideles : Function.Injective (unitsToIdeles K 2).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 1 x hx
  have h0 := isZero_cohomology_one_classLimitRep K
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  rw [Subsingleton.elim c 0, map_zero]

variable {K}

def brauerLocal (ι : LocalEmbeddings K) :
    cohomology (unitsLimitRep K) 2 →+ ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).toAddMonoidHom.comp
    (unitsToIdeles K 2).hom.toAddMonoidHom

theorem brauerLocal_apply (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2) :
    brauerLocal ι x = idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) ((unitsToIdeles K 2).hom x) :=
  rfl

theorem brauerLocal_injective (ι : LocalEmbeddings K) : Function.Injective (brauerLocal ι) :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).injective.comp
    (injective_cohomologyMap_units_ideles K)

theorem eq_zero_of_brauerLocal_apply_eq_zero (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2)
    (hx : ∀ v, brauerLocal ι x v = 0) : x = 0 :=
  brauerLocal_injective ι ((DFinsupp.ext hx).trans (map_zero _).symm)

def brauerSumInv (ι : LocalEmbeddings K) : cohomology (unitsLimitRep K) 2 →+ QZ :=
  (sumPlaceInv K).comp (brauerLocal ι)

end

end GroundTheory.ProfCoh
