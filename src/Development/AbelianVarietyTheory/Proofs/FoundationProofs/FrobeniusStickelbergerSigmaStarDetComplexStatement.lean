module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  first | exact @GlobalTheory.FrobStick.sgStar_cube_det_cplx | exact GlobalTheory.FrobStick.sgStar_cube_det_cplx | (intros; apply GlobalTheory.FrobStick.sgStar_cube_det_cplx <;> assumption)
