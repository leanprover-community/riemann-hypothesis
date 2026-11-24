module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.iwasawa_decomposition_admissible_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  first | exact @GlobalTheory.iwasawa_family | exact GlobalTheory.iwasawa_family | (intros; apply GlobalTheory.iwasawa_family <;> assumption)
