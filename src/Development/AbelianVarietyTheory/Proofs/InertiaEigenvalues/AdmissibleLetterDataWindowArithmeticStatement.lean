module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.admissibleLetterData_window_arithmetic : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  first | exact @GlobalTheory.WindowArith.windows | exact GlobalTheory.WindowArith.windows | (intros; apply GlobalTheory.WindowArith.windows <;> assumption)
