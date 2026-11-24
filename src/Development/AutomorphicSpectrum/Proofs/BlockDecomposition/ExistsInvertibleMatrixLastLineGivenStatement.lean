module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGiven
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import GroundTheory.LocalFields.Interface

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.exists_invertible_matrix_last_line_given : ∀ (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k), a ≠ 0 → ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | exact GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq <;> assumption)
