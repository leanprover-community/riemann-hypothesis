module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasure
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

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  first | exact @GlobalTheory.Amp.RootNormal.rootMeas_normR | exact GlobalTheory.Amp.RootNormal.rootMeas_normR | (intros; apply GlobalTheory.Amp.RootNormal.rootMeas_normR <;> assumption)
