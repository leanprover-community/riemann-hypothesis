module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfGaloisTraceRelation
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

theorem _root_.GlobalTheory.T.finite_of_galois_trace_relation : ∀ (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  first | (exact @GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (exact GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (intros; apply GlobalTheory.GoodEtaleFinite.finite_of_trace_relation  <;> assumption)
