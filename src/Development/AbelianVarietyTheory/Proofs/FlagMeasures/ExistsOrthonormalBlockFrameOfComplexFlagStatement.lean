module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ → (∀ b, m ≤ b → W b = ⊤) → (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) → ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧ ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  first | exact @GlobalTheory.RadCov.exists_orthonormal_block_frame | exact GlobalTheory.RadCov.exists_orthonormal_block_frame | (intros; apply GlobalTheory.RadCov.exists_orthonormal_block_frame <;> assumption)
