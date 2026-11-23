module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Matrix

theorem _root_.GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  first | exact @GlobalTheory.Hk3.SkewLift.skew_lift | exact GlobalTheory.Hk3.SkewLift.skew_lift | (intros; apply GlobalTheory.Hk3.SkewLift.skew_lift <;> assumption)
