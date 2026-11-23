module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamily
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


theorem _root_.GlobalTheory.T.exists_linearMap_limit_of_compatible_approximations : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
  (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
  (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y → ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
  (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
    R n (a • b + a' • b') (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
  ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x, R n b x →
    ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  first | exact @GlobalTheory.exists_linear_limit_of_compatible_family | exact GlobalTheory.exists_linear_limit_of_compatible_family | (intros; apply GlobalTheory.exists_linear_limit_of_compatible_family <;> assumption)
