module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulAppEqZeroNearOfRepresented
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  first | exact @GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | exact GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | (intros; apply GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented; all_goals assumption)
