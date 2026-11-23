module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CoefDiff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.curve :
    ∀ (n : ℕ) (Ξ : Pre n) (c : ℂ → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ), c 0 = 1 →
      (∀ a b, HasDerivAt (fun t => c t a b) (X a b) 0) → ∀ i j, HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.D X i j) 0 := by
  intro n Ξ c X h0 hd i j
  have hγ : HasDerivAt (fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) (of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hd a b
  have hγ0 : (of.symm (c 0) : Fin n → Fin n → ℂ) = oneM n := by
    rw [h0]
  have hf : HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n))
      ((fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) 0) := by
    show HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n)) (of.symm (c 0))
    rw [hγ0]
    exact ((coefDiff n Ξ i j) (oneM n)).hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hγ
