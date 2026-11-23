module

public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_lowDegree_coords_mod_mul : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  first | exact @GlobalTheory.exists_lowDegree_coords_mod | exact GlobalTheory.exists_lowDegree_coords_mod | (intros; apply GlobalTheory.exists_lowDegree_coords_mod <;> assumption)
