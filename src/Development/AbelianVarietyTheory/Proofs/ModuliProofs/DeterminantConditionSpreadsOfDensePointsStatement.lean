module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.determinantCondition_spreads_of_dense_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  first | exact @GlobalTheory.DetSpread.detCond_of_dense | exact GlobalTheory.DetSpread.detCond_of_dense | (intros; apply GlobalTheory.DetSpread.detCond_of_dense <;> assumption)
