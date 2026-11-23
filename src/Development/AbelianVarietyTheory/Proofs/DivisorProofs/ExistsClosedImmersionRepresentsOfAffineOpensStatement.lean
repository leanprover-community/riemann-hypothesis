module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpens
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_closedImmersion_represents_of_affineOpens_alt : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  first | exact @GlobalTheory.exists_closedImmersion_represents_of_affineOpens | exact GlobalTheory.exists_closedImmersion_represents_of_affineOpens | (intros; apply GlobalTheory.exists_closedImmersion_represents_of_affineOpens <;> assumption)
