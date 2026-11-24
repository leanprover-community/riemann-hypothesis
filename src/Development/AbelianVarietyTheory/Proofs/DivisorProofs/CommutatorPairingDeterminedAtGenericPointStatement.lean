module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.commutatorPairing_determined_at_genericPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  first | exact @GlobalTheory.WeilGeneric.weilIs_of_generic | exact GlobalTheory.WeilGeneric.weilIs_of_generic | (intros; apply GlobalTheory.WeilGeneric.weilIs_of_generic <;> assumption)
