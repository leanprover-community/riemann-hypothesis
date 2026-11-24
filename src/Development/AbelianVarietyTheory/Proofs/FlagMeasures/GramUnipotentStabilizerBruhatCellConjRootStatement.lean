module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
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

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.gramUnipotentStabilizer_bruhatCell_conj_root : ∀ (K : Type) [Field K] (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N), IsLoUni L → IsUpUni U → (∀ a, a ∈ stabU (L * ptMat p * U) ↔ U * a * U⁻¹ ∈ stabU (ptMat p)) ∧ (∀ x, x ∈ lieU (L * ptMat p * U) ↔ U * x * U⁻¹ ∈ lieU (ptMat p)) ∧ (∀ a, a ∈ stabU (ptMat p) ↔ IsUpUni a ∧ ∀ i j, i < j → (i, j) ∉ roots (ptMat p) → a i j = 0) ∧ (∀ x, x ∈ lieU (ptMat p) ↔ ∀ i j, (i, j) ∉ roots (ptMat p) → x i j = 0) := by
  first | exact @GlobalTheory.LoopV.Cell.stab_cell | exact GlobalTheory.LoopV.Cell.stab_cell | (intros; apply GlobalTheory.LoopV.Cell.stab_cell <;> assumption)
