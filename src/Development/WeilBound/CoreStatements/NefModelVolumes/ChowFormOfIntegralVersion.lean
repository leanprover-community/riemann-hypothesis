module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
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

open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_of_integral_version : ∀ (k : Type) [Field k] (N e d : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f : MvPolynomial (Fin (e + 1) × Fin N) k), GlobalTheory.ChowHt.IsChowFormInt I e d f → GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  intro k _ N e d I f h
  refine ⟨h.ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · exact h.dvd_of_forall_aeval_eq_zero fun u hu => hg u ((h.zero_iff u).1 hu)
  · rintro ⟨a, rfl⟩ u hu
    rw [map_mul, (h.zero_iff u).2 hu, zero_mul]

end ChowFormCompatibility
