module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBody
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  first | exact @GlobalTheory.IwConstBox.prod_gauge_body | exact GlobalTheory.IwConstBox.prod_gauge_body | (intros; apply GlobalTheory.IwConstBox.prod_gauge_body <;> assumption)
