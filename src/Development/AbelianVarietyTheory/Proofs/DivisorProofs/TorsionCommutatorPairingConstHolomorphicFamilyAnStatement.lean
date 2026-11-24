module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  first | exact @GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | exact GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | (intros; apply GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB <;> assumption)
