module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Rat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsExtra
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
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace GlobalTheory

theorem exists_addMonoidHom_of_linear_relations : ∀ (M ι T : Type) [AddCommGroup T] [Module ℚ T] (Y : ι → M → ℚ) (t : ι → T), (∀ (s : Finset ι) (c : ι → ℚ), ∑ i ∈ s, c i • Y i = 0 → ∑ i ∈ s, c i • t i = 0) → ∃ Ξ : (M → ℚ) →+ T, ∀ i, Ξ (Y i) = t i := by
  first
  | exact @_root_.GlobalTheory.NormBoundTheorem.main
  | exact _root_.GlobalTheory.NormBoundTheorem.main
  | (apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundTheorem.main ..)

end GlobalTheory
