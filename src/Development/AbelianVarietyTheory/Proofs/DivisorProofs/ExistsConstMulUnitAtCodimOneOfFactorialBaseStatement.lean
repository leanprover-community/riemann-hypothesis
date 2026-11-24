module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulUnitAtCodimOneOfFactorialBase
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  first | exact @GlobalTheory.VerticalUnit.exists_const_mul_unitAt_coheight_one | exact GlobalTheory.VerticalUnit.exists_const_mul_unitAt_coheight_one | (intros; apply GlobalTheory.VerticalUnit.exists_const_mul_unitAt_coheight_one <;> assumption)
