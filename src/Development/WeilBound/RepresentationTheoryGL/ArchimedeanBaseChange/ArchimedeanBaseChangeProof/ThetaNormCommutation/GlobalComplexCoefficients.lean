module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
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

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

def GlobalComplexCoefficients : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (l₁ : ∀ i, InfinitePlace E → DomWeight (a i))
    (l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)) (sg : ι → ℂ),
    (∀ i, sg i ≠ 0 ∧ a i ≤ n ∧ ∀ v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
      (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
      (φ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
      GlobalTheory.BCT.IsTest (KL n) K' f → (∀ a ≤ n, IsTestP (φ a) ∧ ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (φ a w)) →
      geomU S lam f = ∑ i, sg i * geomSt2 S (l₁ i) (l₂ i) (φ (a i))

end PositivityTheory.Rg.BcB.G8

end
