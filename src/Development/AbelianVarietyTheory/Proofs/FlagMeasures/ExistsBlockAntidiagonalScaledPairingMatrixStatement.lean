module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockAntidiagonalScaledPairingMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

theorem _root_.GlobalTheory.T.exists_blockAntidiagonal_scaled_pairing_matrix : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  first | exact @GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | exact GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | (intros; apply GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing <;> assumption)
