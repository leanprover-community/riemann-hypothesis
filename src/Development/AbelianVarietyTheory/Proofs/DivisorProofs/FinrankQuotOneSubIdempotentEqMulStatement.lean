module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMul
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

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  first | (exact @GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (exact GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (intros; apply GlobalTheory.finrank_quot_one_sub_idem_eq_mul  <;> assumption)
