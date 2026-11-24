module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GoodReductionAdaptedBasis
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.good_reduction_adapted_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  first | exact @GlobalTheory.ZH.RedGood.good_reduction | exact GlobalTheory.ZH.RedGood.good_reduction | (intros; apply GlobalTheory.ZH.RedGood.good_reduction <;> assumption)
