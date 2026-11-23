module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  first | exact @GlobalTheory.DFrame.congr_at_d | exact GlobalTheory.DFrame.congr_at_d | (intros; apply GlobalTheory.DFrame.congr_at_d <;> assumption)
