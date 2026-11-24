module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Prod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyInnerReEqStrictLowerAddDiagIm
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

open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.skew_family_inner_re_eq_strictLower_add_diagIm : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  first | exact @GlobalTheory.skew_family_inner_re_split | exact GlobalTheory.skew_family_inner_re_split | (intros; apply GlobalTheory.skew_family_inner_re_split <;> assumption)
