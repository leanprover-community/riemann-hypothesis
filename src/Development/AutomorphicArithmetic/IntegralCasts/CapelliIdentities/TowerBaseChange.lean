module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAlt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.LocalSmoothExtension.exists_smooth_eq : ∀ {K : Type} [Field K] [NumberField K] {n : ℕ}
    {U : Set (GlobalTheory.CuspRep.Lie K n)}, IsOpen U →
    ∀ {F : GlobalTheory.CuspRep.Lie K n → ℂ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U →
    ∀ {x : GlobalTheory.CuspRep.Lie K n}, x ∈ U →
      ∃ G : GlobalTheory.CuspRep.Lie K n → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro K _ _ n U hU F hF x hx
  exact UpperTheory.Reformulated.B.ContDiffOnLocalExtension.abs hU hF hx
