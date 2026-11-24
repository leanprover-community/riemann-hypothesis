module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisTermsAtOtherClassMembers
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

theorem _root_.GlobalTheory.T.adaptedBasis_terms_at_other_class_members : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  first | exact @GlobalTheory.ZH.Shift.main | exact GlobalTheory.ZH.Shift.main | (intros; apply GlobalTheory.ZH.Shift.main <;> assumption)
