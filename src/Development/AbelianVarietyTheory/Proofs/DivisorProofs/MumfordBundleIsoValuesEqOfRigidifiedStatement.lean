module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValuesEqOfRigidified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem _root_.GlobalTheory.T.mumfordBundleIso_values_eq_of_rigidified : ∀ {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}, M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (w₁ w₂ : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), w₁.IsGen → w₂.IsGen → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₁ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B').left) (z : Z) J J', Good M z J → Good M' z J' → lamVal w₁ p z J J' = lamVal w₂ p z J J' := by
  first | exact @GlobalTheory.TautUniq.lamVal_eq_of_rig | exact GlobalTheory.TautUniq.lamVal_eq_of_rig | (intros; apply GlobalTheory.TautUniq.lamVal_eq_of_rig <;> assumption)
