module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
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


theorem _root_.GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
