module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsion
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

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X)) (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion | exact GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion | (intros; apply GlobalTheory.TorusPiTorsion.finite_of_isClosed_of_no_pi_torsion <;> assumption)
