module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCover
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  first | exact @GlobalTheory.GlueClosed.exists_glue_isClosedImmersion | exact GlobalTheory.GlueClosed.exists_glue_isClosedImmersion | (intros; apply GlobalTheory.GlueClosed.exists_glue_isClosedImmersion <;> assumption)
