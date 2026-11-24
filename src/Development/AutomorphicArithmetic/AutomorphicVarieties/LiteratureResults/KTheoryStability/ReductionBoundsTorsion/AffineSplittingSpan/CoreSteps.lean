module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

def SplitA : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (q : ℕ) (b : (Fin (q + 2) → Q) → ℝ), dc b = 0 →
    Wtop pr b = dv (zz pr b 1 (q + 1))

def SplitS : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (p q : ℕ) (b : (Fin (p + q + 3) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (p + 1) (q + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 2) (q + 1))

def SplitB : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (N : ℕ) (b : (Fin (N + 2) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (N + 1) 1) = (-1 : ℝ) ^ (N + 1) • (fun x _ => b x : Bi P Q (N + 2) 1)

def ZInv : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (n a c : ℕ) (b : (Fin n → Q) → ℝ), a + c = n →
    (∀ (g : Q) x, b (fun i => g * x i) = b x) → PInv pr (zz pr b a c)

def E2VanishingFirstColumn : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q 1 (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ x = dv e

def E2VanishingOtherColumns : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ p q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q (p + 2) (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
        PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ x = dh w + dv e

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
