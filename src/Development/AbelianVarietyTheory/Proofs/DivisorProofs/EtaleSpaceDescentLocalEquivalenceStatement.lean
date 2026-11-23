module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalence
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

theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
