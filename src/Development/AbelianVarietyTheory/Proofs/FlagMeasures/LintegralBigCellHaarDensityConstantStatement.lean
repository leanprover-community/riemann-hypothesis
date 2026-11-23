module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstant
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

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_bigCell_haar_density_constant : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  first | exact @GlobalTheory.CellDens.bigCell_integral | exact GlobalTheory.CellDens.bigCell_integral | (intros; apply GlobalTheory.CellDens.bigCell_integral <;> assumption)
