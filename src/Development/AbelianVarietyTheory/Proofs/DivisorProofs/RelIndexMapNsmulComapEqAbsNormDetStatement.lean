module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
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

open NumberField

theorem _root_.GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det : ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  first | exact @GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | exact GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | (intros; apply GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det <;> assumption)
