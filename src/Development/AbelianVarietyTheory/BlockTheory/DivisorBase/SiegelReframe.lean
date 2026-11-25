module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

abbrev Fl (g : ℕ) : Type := Fin g ⊕ Fin g → ℝ

def riem {g : ℕ} (x y : Fl g) : ℝ :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))

def symp (g : ℕ) : Fl g [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := riem (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, add_mul, mul_add, Finset.sum_add_distrib] <;> ring
  map_update_smul' := by
    intro inst v i c x
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, ← Finset.sum_sub_distrib, Finset.mul_sum] <;>
      exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by
    unfold riem
    fun_prop
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simp only [riem, h01]
    exact Finset.sum_eq_zero fun _ _ => by ring

def stdLat (g : ℕ) : Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))

def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : Fin g → ℂ :=
  (fun i => (x (Sum.inl i) : ℂ)) ᵥ* τ + fun i => (x (Sum.inr i) : ℂ)

def flatOf {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : Fl g :=
  Sum.elim ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹)
    ((fun i => (z i).re) - ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re)

abbrev Sp (g : ℕ) : Type := Matrix.symplecticGroup (Fin g) ℝ

section Family

abbrev Pt (E : Type) (g : ℕ) : Type := E × (Fin g → ℂ)

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ}

abbrev Form2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) : Type :=
  Pt E g [⋀^Fin 2]→L[ℝ] ℝ

def IsPeriodMap (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  IsOpen B ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) ∧ ∀ b ∈ B, IsSiegel (τ b)

def cov (B : Set E) (g : ℕ) : Set (Pt E g) := B ×ˢ Set.univ

def flat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Fl g := flatOf (τ P.1) P.2

def dflat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Pt E g →L[ℝ] Fl g :=
  fderiv ℝ (flat τ) P

def om0 (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Form2 E g :=
  (symp g).compContinuousLinearMap (dflat τ P)

def pull (f : Pt E g → Pt E' g) (α : Pt E' g → Form2 E' g) (P : Pt E g) : Form2 E g :=
  (α (f P)).compContinuousLinearMap (fderiv ℝ f P)

def transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 + per (τ P.1) x)

def IsFactor (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  (∀ l ∈ M, DifferentiableOn ℂ (j l) (cov B g) ∧ ∀ P ∈ cov B g, j l P ≠ 0) ∧
  ∀ l ∈ M, ∀ l' ∈ M, ∀ P ∈ cov B g, j (l + l') P = j l (transl τ l' P) * j l' P

def IsMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (cov B g) ∧ (∀ P ∈ cov B g, 0 < h P) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, h (transl τ l P) * ‖j l P‖ ^ 2 = h P

end Family

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
