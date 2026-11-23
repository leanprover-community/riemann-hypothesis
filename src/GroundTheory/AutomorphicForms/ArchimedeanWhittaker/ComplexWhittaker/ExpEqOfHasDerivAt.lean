module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix NormedSpace Complex MeasureTheory
open scoped Matrix.Norms.L2Operator

abbrev GL2C : Subgroup (GL (Fin 2) ℂ) := ⊤

noncomputable def toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : GL2C :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (((toGLC A hA : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := rfl

theorem GL2C_ext {g g' : GL2C}
    (h : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ((g' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : GL2C :=
  toGLC !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] (by
    simp [Matrix.det_fin_two_of, h₁.ne', h₂.ne'])

@[simp] theorem coe_dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (((dC d₁ d₂ h₁ h₂ : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] := rfl

abbrev U2 : Type := unitaryGroup (Fin 2) ℂ

theorem det_ne_zero_of_U2 (k : U2) : ((k : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
  intro h
  have h1 : (star (k : Matrix (Fin 2) (Fin 2) ℂ) * k).det = 1 := by
    rw [Matrix.UnitaryGroup.star_mul_self, Matrix.det_one]
  rw [Matrix.det_mul, h, mul_zero] at h1
  exact zero_ne_one h1

noncomputable def kC : U2 →* GL2C where
  toFun k := toGLC (k : Matrix (Fin 2) (Fin 2) ℂ) (det_ne_zero_of_U2 k)
  map_one' := by apply GL2C_ext; rfl
  map_mul' k k' := by apply GL2C_ext; rfl

@[simp] theorem coe_kC (k : U2) :
    (((kC k : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem coe_kC_inv (k : U2) :
    ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      star (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 k.2)

theorem continuous_kC : Continuous kC := by
  have hval : Continuous fun k : U2 => ((kC k : GL (Fin 2) ℂ)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : (fun k : U2 => ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun k : U2 => star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext k; exact coe_kC_inv k
    rw [e]
    exact continuous_star.comp continuous_subtype_val
  exact continuous_induced_rng.2 hval

noncomputable def tC (a b : ℝ) : U2 :=
  ⟨!![Complex.exp (a * I), 0; 0, Complex.exp (b * I)], by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : ∀ r : ℝ, Complex.exp (r * I) * (starRingEnd ℂ) (Complex.exp (r * I)) = 1 := fun r => by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, h]⟩

@[simp] theorem coe_tC (a b : ℝ) : ((tC a b : U2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.exp (a * I), 0; 0, Complex.exp (b * I)] := rfl

end GroundTheory.Automorphic.ArchWhittakerC
