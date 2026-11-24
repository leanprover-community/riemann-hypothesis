module

public import GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import GroundTheory.AutomorphicForms.ReductionIwasawa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.Reduction IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def modPow (x : IdeleGroup K) (s : ℂ) : ℂ := ((ideleModule K x : ℝ) : ℂ) ^ s

theorem modPow_mul (x y : IdeleGroup K) (s : ℂ) : modPow (x * y) s = modPow x s * modPow y s := by
  simp only [modPow, map_mul, Positive.val_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (ideleModule K x).2.le (ideleModule K y).2.le s

theorem modPow_add (x : IdeleGroup K) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (ideleModule K x).2.ne')

theorem modPow_one (s : ℂ) : modPow (1 : IdeleGroup K) s = 1 := by
  simp [modPow]

theorem modPow_ne_zero (x : IdeleGroup K) (s : ℂ) : modPow x s ≠ 0 := by
  simp [modPow, (ideleModule K x).2.ne']

abbrev detI (g : GL (Fin 2) 𝔸[K]) : IdeleGroup K := Matrix.GeneralLinearGroup.det g

def rightReg (h : GL (Fin 2) 𝔸[K]) (f : GL (Fin 2) 𝔸[K] → ℂ) : GL (Fin 2) 𝔸[K] → ℂ :=
  fun g ↦ f (g * h)

def IsKFinite (f : GL (Fin 2) 𝔸[K] → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)),
    F = rightReg k f})

theorem globalZeta_mul_right (F : 𝔸[K] → ℂ) (μ : HeckeCharacter K) (s : ℂ) (d : IdeleGroup K) :
    globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * globalZeta F μ s := by
  set G : IdeleGroup K → ℂ := fun x ↦ F x * (μ.toIdele x : ℂ) * modPow x s with hG
  have hpt : ∀ x : IdeleGroup K, F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) := by
    intro x
    have h1 : modPow d (-s) * modPow d s = 1 := by
      rw [← modPow_add, neg_add_cancel]; simp [modPow]
    have h2 : (((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    simp only [hG, Units.val_mul, map_mul, Circle.coe_mul, modPow_mul]
    linear_combination (-(F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s)) *
      ((((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) * h1 + h2)
  have : globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      ∫ x, (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) ∂ideleMeasure K := by
    simp only [globalZeta]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul]
  simp_rw [mul_comm _ d]
  rw [integral_mul_left_eq_self G d]
  rfl

def slice (Φ : (Fin 2 → 𝔸[K]) → ℂ) (g : GL (Fin 2) 𝔸[K]) : 𝔸[K] → ℂ :=
  fun t ↦ Φ (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]))

def godementSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (g : GL (Fin 2) 𝔸[K]) : ℂ :=
  (χ₁.toIdele (detI g) : ℂ) * modPow (detI g) s * globalZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)

end

end GroundTheory.Automorphic.GodementSection
