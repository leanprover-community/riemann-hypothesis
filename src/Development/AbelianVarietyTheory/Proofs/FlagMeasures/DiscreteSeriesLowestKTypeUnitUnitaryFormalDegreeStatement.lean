module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

theorem _root_.GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  first | exact @GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | exact GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | (intros; apply GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf <;> assumption)
