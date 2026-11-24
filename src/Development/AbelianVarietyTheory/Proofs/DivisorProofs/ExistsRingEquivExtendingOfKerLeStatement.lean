module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLe
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


theorem _root_.GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  first | exact @GlobalTheory.exists_ringEquiv_extending_of_ker_le | exact GlobalTheory.exists_ringEquiv_extending_of_ker_le | (intros; apply GlobalTheory.exists_ringEquiv_extending_of_ker_le <;> assumption)
