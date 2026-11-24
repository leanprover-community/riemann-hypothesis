module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LeviLogFlat.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (P u : (J → ℂ) → ℝ) (z w : J → ℂ),
    ContDiffAt ℝ 2 P z → ContDiffAt ℝ 2 u z → 0 < P z → u z = 0 → fderiv ℝ u z w = 0 →
    fderiv ℝ u z (Complex.I • w) = 0 → leviForm u z w = 0 →
    leviForm (fun x => Real.log (P x + u x)) z w = leviForm (fun x => Real.log (P x)) z w

def LeviHolPerturb.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (ξ : (J → ℂ) → ℝ) (a φ : (J → ℂ) → ℂ) (z w : J → ℂ),
    ContDiffAt ℝ 2 ξ z → AnalyticAt ℂ a z → AnalyticAt ℂ φ z → φ z = 0 → fderiv ℂ φ z w = 0 →
    ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z ∧
      ξ z * (‖a z + φ z‖ ^ 2 - ‖a z‖ ^ 2) = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z (Complex.I • w) = 0 ∧
      leviForm (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0

def LeviCompHol.Statement : Prop :=
  ∀ (E F : Type) [Fintype E] [Fintype F] (g : (E → ℂ) → (F → ℂ)) (φ : (F → ℂ) → ℝ) (x w : E → ℂ),
    AnalyticAt ℂ g x → ContDiffAt ℝ 2 φ (g x) →
    leviForm (fun y => φ (g y)) x w = leviForm φ (g x) (fderiv ℂ g x w)

def LeviFSInvariant.Statement : Prop :=
  ∀ (M : Type) [Fintype M] (a b : M → ℂ) (c μ : ℂ), a ≠ 0 → c ≠ 0 →
    leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) (c • a) (c • b + μ • a) =
      leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) a b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
