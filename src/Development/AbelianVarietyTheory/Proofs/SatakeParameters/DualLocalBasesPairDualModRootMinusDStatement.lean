module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusD
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

theorem _root_.GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  first | exact @GlobalTheory.DFrame.dual_local_bases_pair | exact GlobalTheory.DFrame.dual_local_bases_pair | (intros; apply GlobalTheory.DFrame.dual_local_bases_pair <;> assumption)
