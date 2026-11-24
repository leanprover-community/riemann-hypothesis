module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlag
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_orthonormal_frame_of_flag_alt : ∀ (n a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) → ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  first | exact @GlobalTheory.exists_orthonormal_frame_of_flag | exact GlobalTheory.exists_orthonormal_frame_of_flag | (intros; apply GlobalTheory.exists_orthonormal_frame_of_flag <;> assumption)
