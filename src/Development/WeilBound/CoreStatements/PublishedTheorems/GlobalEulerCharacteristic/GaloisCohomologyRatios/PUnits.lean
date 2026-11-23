module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GEqAddOfExactOfFiniteCokernel
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem units_finite_modN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (ModN A n)] : Finite (ModN B n) := by
  have h : LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ B (n : ℤ))).comap e.toIntLinearEquiv.toLinearMap := by
    rintro _ ⟨y, rfl⟩
    exact ⟨e y, by simp⟩
  refine Finite.of_surjective (Submodule.mapQ _ _ e.toIntLinearEquiv.toLinearMap h) fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H b => exact ⟨Submodule.Quotient.mk (e.symm b), by simp⟩

theorem units_finite_torsN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (TorsN A n)] : Finite (TorsN B n) := by
  refine Finite.of_surjective (fun x : TorsN A n => (⟨e x.1, by
    have hx := (mem_ker_lsmul_iff n (x : A)).1 x.2
    exact (mem_ker_lsmul_iff n (e x.1)).2 (by rw [← map_nsmul, hx, map_zero])⟩ : TorsN B n)) fun y => ?_
  refine ⟨⟨e.symm y.1, (mem_ker_lsmul_iff n _).2 ?_⟩, ?_⟩
  · rw [← map_nsmul, (mem_ker_lsmul_iff n (y : B)).1 y.2, map_zero]
  · ext; simp

theorem S_units_euler_difference [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 0) ℓ)] :
    dMod hL d 0 - dTors hL d 0 = dPlaces (S := S) d + dInf d - d.one := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  haveI : Finite (ModN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_modN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  haveI : Finite (TorsN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_torsN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  have hU := conj_gsH0SUnits_eq hL d
  have hg : (letI := actA hL 0; d.g (AA hL 0)) = dMod hL d 0 - dTors hL d 0 := by
    letI := actA hL 0
    exact d.g_eq _
  have hS := d.g_sUnits (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
    (placesOver_stable (S := S) (K := K) (L := L))
  rw [← hg]
  exact hU.trans hS

theorem class_group_mod_eq_torsion [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 1) ℓ)] [Finite (TorsN (AA hL 1) ℓ)] :
    dMod hL d 1 = dTors hL d 1 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI := actA hL 1
  haveI : Finite (AA hL 1) := finite_gsH1SUnits hL
  have h1 := d.g_eq_zero_of_finite (AA hL 1)
  rw [d.g_eq (AA hL 1)] at h1
  unfold dMod dTors
  exact sub_eq_zero.1 h1

end PositivityTheory.Lit1.GEN.X
