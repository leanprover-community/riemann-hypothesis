module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRing
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


theorem _root_.GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ), (∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → (∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧ (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧ ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  first | exact @GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | exact GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | (intros; apply GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple <;> assumption)
