module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowKillsOnCompactOfLocal
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  first | exact @GlobalTheory.pow_kills_on_compact_of_local | exact GlobalTheory.pow_kills_on_compact_of_local | (intros; apply GlobalTheory.pow_kills_on_compact_of_local; all_goals assumption)
