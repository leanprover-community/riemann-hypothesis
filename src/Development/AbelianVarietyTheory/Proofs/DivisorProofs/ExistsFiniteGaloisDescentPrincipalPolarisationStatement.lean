module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisation
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_galois_descent_principal_polarisation : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  first | exact @GlobalTheory.MumDescent.exists_galois_polAV | exact GlobalTheory.MumDescent.exists_galois_polAV | (intros; apply GlobalTheory.MumDescent.exists_galois_polAV <;> assumption)
