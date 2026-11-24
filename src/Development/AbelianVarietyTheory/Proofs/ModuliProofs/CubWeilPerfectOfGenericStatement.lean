module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  first | exact @GlobalTheory.cubWeil_perfect_of_generic | exact GlobalTheory.cubWeil_perfect_of_generic | (intros; apply GlobalTheory.cubWeil_perfect_of_generic <;> assumption)
