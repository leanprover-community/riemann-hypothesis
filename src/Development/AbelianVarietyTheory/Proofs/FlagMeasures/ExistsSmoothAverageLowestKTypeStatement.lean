module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_average_lowest_KType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  first | exact @GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | exact GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | (intros; apply GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf <;> assumption)
