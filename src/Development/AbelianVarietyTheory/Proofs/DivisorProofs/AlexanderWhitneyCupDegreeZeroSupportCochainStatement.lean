module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochain
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain : ∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k), μ.IsAW hk α β γ → (∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0) → ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U), ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
  first | (exact @GlobalTheory.AWFront.ev_of_front) | (exact GlobalTheory.AWFront.ev_of_front) | (intros; apply GlobalTheory.AWFront.ev_of_front  <;> assumption)
