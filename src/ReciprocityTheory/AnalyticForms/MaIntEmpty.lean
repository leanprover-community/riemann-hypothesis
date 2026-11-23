module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.AnForm

open MeasureTheory

noncomputable section

section Levi

variable {ι : Type*} [Fintype ι]

def levi (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4

end Levi

section MongeAmpere

variable {D : ℕ}

def hessC (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4

def mdisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det

def maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (φ k) z).re

def maInt (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)) : ℝ :=
  ∫ z in U, g z * maDens φ z

theorem mdisc_zero (A : Fin 0 → Matrix (Fin 0) (Fin 0) ℂ) : mdisc A = 1 := by
  simp [mdisc]

end MongeAmpere

end

end ReciprocityTheory.AnForm
