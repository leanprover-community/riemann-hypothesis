module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoices
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselRootMeasure_independent_of_choices : ∀ (D : Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : Mat D.R.k D.R.rS) (p p' : Point ℂ (D.R.rS + 1)) (μ μ' : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → γ ∈ GG D.R.k D.R.rS → Gf D.R.k D.R.rS z z' γ ≠ 0 → 0 < D.host.ka → Formalism.MainNotions.S.IsRootMeasR D z z' p γ μ → Formalism.MainNotions.S.IsRootMeasR D z z' p' γ μ' → p = p' ∧ μ = μ' ∧ IsHaarOn (Rset D.R.k D.R.rS γ) μ := by
  first | exact @GlobalTheory.SnMass.RootUniq.rootMeas_unique | exact GlobalTheory.SnMass.RootUniq.rootMeas_unique | (intros; apply GlobalTheory.SnMass.RootUniq.rootMeas_unique <;> assumption)
