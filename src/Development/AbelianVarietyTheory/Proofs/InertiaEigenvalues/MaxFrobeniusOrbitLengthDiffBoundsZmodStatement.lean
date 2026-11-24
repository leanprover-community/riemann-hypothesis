module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
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

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ), (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N → 1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  first | exact @GlobalTheory.BK.maxPeriod_bounds | exact GlobalTheory.BK.maxPeriod_bounds | (intros; apply GlobalTheory.BK.maxPeriod_bounds <;> assumption)
