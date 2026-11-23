module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockPerpEmbeddingOfDiagonalFrame
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.blockPerpEmbedding_of_diagonal_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  first | exact @GlobalTheory.PerpSort.isPerpEmb_of_sorts | exact GlobalTheory.PerpSort.isPerpEmb_of_sorts | (intros; apply GlobalTheory.PerpSort.isPerpEmb_of_sorts <;> assumption)
