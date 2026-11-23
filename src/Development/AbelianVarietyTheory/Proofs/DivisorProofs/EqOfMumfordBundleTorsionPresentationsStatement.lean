module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentations
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  first | exact @GlobalTheory.PresRigid.eq_of_lam_of_torsion | exact GlobalTheory.PresRigid.eq_of_lam_of_torsion | (intros; apply GlobalTheory.PresRigid.eq_of_lam_of_torsion <;> assumption)
