module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
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

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt), ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


namespace Line

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
