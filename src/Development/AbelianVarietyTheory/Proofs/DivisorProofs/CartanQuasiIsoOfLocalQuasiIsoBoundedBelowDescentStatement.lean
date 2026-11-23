module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescent
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) → Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ → ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  first | (exact @GlobalTheory.CartanOne.cartan_one) | (exact GlobalTheory.CartanOne.cartan_one) | (intros; apply GlobalTheory.CartanOne.cartan_one <;> assumption)
