module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_iso_pull_cancel {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} (hL : L.IsLB)
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {φ₁ : X'' ⟶ X} {φ₂ : X' ⟶ X} {θ : X'' ⟶ X'} (h : θ ≫ φ₂ = φ₁)
    (w₁ : LB.Iso L'' (L.pull φ₁)) (w₂ : LB.Iso L' (L.pull φ₂)) (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ (wθ : LB.Iso L'' (L'.pull θ)) (w₁' : LB.Iso L'' (L.pull (θ ≫ φ₂))),
      wθ.IsGen ∧ HEq w₁' w₁ ∧ Tri w₂ wθ w₁' := by
  subst h
  obtain ⟨wθ, T⟩ := exists_cancel hL w₂ w₁ ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁) hL' hL''
  exact ⟨wθ, w₁, (isGen_iff _).2 (T.pgen_cancel hL ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁)), HEq.rfl, T⟩

end GlobalTheory
