module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsRangeIdempotentOfRetract
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

universe u

theorem _root_.GlobalTheory.T.exists_coords_range_idempotent_of_retract : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  first | exact @GlobalTheory.idem_retract_coords | exact GlobalTheory.idem_retract_coords | (intros; apply GlobalTheory.idem_retract_coords <;> assumption)
