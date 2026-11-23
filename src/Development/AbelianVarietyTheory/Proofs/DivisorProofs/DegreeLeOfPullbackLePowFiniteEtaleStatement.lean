module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale
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

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  first | exact @GlobalTheory.degree_le_of_pull_le_pow | exact GlobalTheory.degree_le_of_pull_le_pow | (intros; apply GlobalTheory.degree_le_of_pull_le_pow <;> assumption)
