module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
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

open scoped InnerProductSpace

namespace GlobalTheory.TraceCycWord

theorem etr_succ_eq_sum_cycWord : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ),
    Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  intro A _ n E m
  rw [GlobalTheory.PhiEigenfun.sum_cycWord, Formalism.REAL.etr]
  exact Finset.sum_congr rfl fun c _ => GlobalTheory.PhiEigenfun.epow_eq E (m + 1) c c

end GlobalTheory.TraceCycWord
