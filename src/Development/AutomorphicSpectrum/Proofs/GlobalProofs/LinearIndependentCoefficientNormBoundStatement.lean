module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.linearIndependent_coefficient_norm_bound : ∀ {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hli : LinearIndependent ℝ b), ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm <;> assumption)
