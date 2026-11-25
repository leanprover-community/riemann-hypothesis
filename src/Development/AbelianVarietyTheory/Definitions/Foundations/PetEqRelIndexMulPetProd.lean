module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

namespace GlobalTheory.Hk

def lev (N l : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l

def uOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))

def vOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (ofComplex ((q : ℂ) * τ))

def IsDia (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : Prop :=
  ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((σ 1 1 : ℤ) : ZMod N) = d

def dia (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] σ

def heckeT (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  uOp q f + ((q : ℂ) ^ (k - 1)) • vOp q (f ∣[k] σ)

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def pet (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Γ, ∫ z in ModularGroup.fd, petersson k f g (γ.out⁻¹ • z)

def pmGrp (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∨ -γ ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h : -a⁻¹ = (-a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; simp
      rw [h]; exact Γ.inv_mem ha

theorem le_pmGrp (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmGrp Γ := fun _ h => Or.inl h

instance pmGrp_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pmGrp Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pmGrp Γ)

end GlobalTheory.Hk
