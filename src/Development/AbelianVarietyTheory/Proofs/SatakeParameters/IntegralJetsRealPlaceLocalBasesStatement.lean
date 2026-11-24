module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.StatementN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases
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

theorem _root_.GlobalTheory.T.integral_jets_realPlace_local_bases : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  first | exact @GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | exact GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | (intros; apply GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR <;> assumption)
