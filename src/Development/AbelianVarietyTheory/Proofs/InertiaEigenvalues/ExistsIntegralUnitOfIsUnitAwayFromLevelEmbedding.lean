module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem unit_of_unitOff : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  intro O _ _ _ ε N t hN ⟨ht0, n, h1, h2⟩
  have hε : Function.Injective ε := ε.injective
  have key : ∀ s : FractionRing O, IsIntegral ℤ (ε s) → ∃ a : O, algebraMap O (FractionRing O) a = s := by
    intro s hs
    letI : Algebra ℤ (FractionRing O) := Ring.toIntAlgebra _
    have hs' : IsIntegral ℤ s := (isIntegral_algHom_iff (ε.toIntAlgHom) hε).mp hs
    have hO : IsIntegral O s := by
      have := IsIntegral.map_of_comp_eq (Int.castRingHom O) (RingHom.id (FractionRing O)) (RingHom.ext_int _ _) hs'
      simpa using this
    exact IsIntegrallyClosed.isIntegral_iff.mp hO
  have ht : t ≠ 0 := by rintro rfl; simp at ht0
  obtain ⟨a, ha⟩ := key (((N : FractionRing O)) ^ n * t) (by simpa [map_mul, map_pow, map_natCast] using h1)
  obtain ⟨b, hb⟩ := key (((N : FractionRing O)) ^ n * t⁻¹) (by simpa [map_mul, map_pow, map_natCast, map_inv₀] using h2)
  have hN' : (N : FractionRing O) ≠ 0 := by
    have := (hN.map (algebraMap O (FractionRing O))).ne_zero
    simpa using this
  have hab : a * b = (N : O) ^ (2 * n) := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_pow, map_natCast]
    field_simp
    ring
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ hN.pow _)
  have hinv : algebraMap O (FractionRing O) ((hN.unit⁻¹ : Oˣ) : O) = (N : FractionRing O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (FractionRing O)) N, ← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨hua.unit * hN.unit⁻¹ ^ n, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, hinv, ha]
  rw [mul_comm (_ ^ n) t, mul_assoc, ← mul_pow, mul_inv_cancel₀ hN', one_pow, mul_one]

end GlobalTheory.PlaceRead
