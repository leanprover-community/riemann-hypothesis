module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
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

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpIntegrandLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ q → ∃ t₂ : ℝ, 0 < t₂ ∧ ∀ t : ℝ, 0 < t → t ≤ t₂ →
      ∃ (N : Set ((Σ k, ι k) → ℂ)) (C t'₀ : ℝ), 0 < t'₀ ∧ IsPtsNull (mCoordIdeal D.y) D.n N ∧
        (∀ t' : ℝ, 0 < t' → t' < t'₀ →
          (∀ z ∈ mcPts (mCoordIdeal D.y), |X.wSt B p q t t' z| ≤ C) ∧
          ContinuousOn (X.wSt B p q t t') (mcPts (mCoordIdeal D.y) \ N)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
          Tendsto (fun t' => X.wSt B p q t t' z) (𝓝[>] 0)
            (𝓝 (cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))))

end GroundTheory.Heights₂.Heights.LowerBoundFree
