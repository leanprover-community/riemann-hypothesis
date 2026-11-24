module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r n M : ℕ) [NeZero n], 1 ≤ s → ∀ (t τ : PowerSeries ↥LL.1), PowerSeries.constantCoeff t = 0 → (1 + PowerSeries.X) * PowerSeries.derivative t = 1 → XX l ↥LL.1 s * τ = t → ∀ (U : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1)) (Pm : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL))) (Cm : ZMod n → Matrix (Fin r) (Fin r) ↥LL.1) (ρ : ℝ), 0 < ρ → (∀ i, QQ l ↥LL.1 s ^ M • U i = (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * (U (i - 1)).map (phi l ↥LL.1) * (Cm i).map PowerSeries.C) → (∀ i a b, (∀ r : ℝ, 0 < r → r < ρ → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0))) → ∀ i a b, (∀ r : ℝ, 0 < r → r < 1 → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (τ ^ M * U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  first | exact @GlobalTheory.Cyc.continuation_to_open_disc | exact GlobalTheory.Cyc.continuation_to_open_disc | (intros; apply GlobalTheory.Cyc.continuation_to_open_disc <;> assumption)
