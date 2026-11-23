module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedFormOrthogonalFinrankDetUnitary
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.signedFormOrthogonal_finrank_det_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Submodule ℂ (Fin n → ℂ)), (∀ y, y ∈ V' ↔ ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) → Module.finrank ℂ V' + Module.finrank ℂ V = n ∧ (∀ x, (∀ y ∈ V', star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) → x ∈ V) ∧ ∀ m : Formalism.REAL.UJ ε, ‖(uMat m).det‖ = 1 ∧ ((∀ y ∈ V, uMat m *ᵥ y ∈ V) → (∀ y ∈ V', uMat m *ᵥ y ∈ V') ∧ detOn (uMat m) V' = detOn (uMat m) V ∧ 0 < detOn (uMat m) V) := by
  first | exact @GlobalTheory.PerpModulus.perp_modulus | exact GlobalTheory.PerpModulus.perp_modulus | (intros; apply GlobalTheory.PerpModulus.perp_modulus <;> assumption)
