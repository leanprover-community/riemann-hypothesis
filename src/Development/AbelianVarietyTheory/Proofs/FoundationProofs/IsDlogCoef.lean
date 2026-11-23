module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5 Polynomial

noncomputable section
namespace GlobalTheory.K5.DlogCoef

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem smul_mk (J : Ideal (On p n)) (a b : On p n) :
    a • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (a * b) := by
  first
  | rfl
  | exact (Submodule.Quotient.mk_smul _ _ _).symm
  | simp [Algebra.smul_def]

theorem deriv_pow (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (r c : On p n) (h : D r = Ideal.Quotient.mk J (c * r)) (i : ℕ) :
    D (r ^ i) = Ideal.Quotient.mk J ((i : On p n) * c * r ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, h, smul_mk, smul_mk, ← (Ideal.Quotient.mk J).map_add]
    congr 1
    push_cast
    ring

end GlobalTheory.K5.DlogCoef
