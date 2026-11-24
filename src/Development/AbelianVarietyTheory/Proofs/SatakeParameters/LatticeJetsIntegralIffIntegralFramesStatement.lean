module

public import Formalism.GaussJetBounds.StatementN
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.latticeJetsIntegral_iff_integralFrames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  first | exact @GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | exact GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | (intros; apply GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames <;> assumption)
