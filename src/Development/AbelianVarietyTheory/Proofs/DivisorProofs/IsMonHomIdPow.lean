module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open GlobalTheory.DeRham (push push_comp push_congr push_id push_mul)
open GlobalTheory.AbDual (isMonHom_one push_one)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo
