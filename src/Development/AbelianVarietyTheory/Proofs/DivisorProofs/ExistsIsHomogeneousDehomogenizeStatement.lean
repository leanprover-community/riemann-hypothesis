module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenize
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

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by
  first | exact @GlobalTheory.exists_isHomogeneous_dehomogenize | exact GlobalTheory.exists_isHomogeneous_dehomogenize | (intros; apply GlobalTheory.exists_isHomogeneous_dehomogenize <;> assumption)
