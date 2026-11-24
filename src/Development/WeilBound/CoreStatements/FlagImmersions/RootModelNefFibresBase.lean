module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem geoNum_zero_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W a := by
  rw [geoNum]
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 W (fun _ => a) := by
  rw [geoNum]
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun V => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg' _ _)
  · exact le_rfl

end RootFieldNumerics

theorem RootFieldNumerics.root_model_nef_fibres_base : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  intro Ψ _ N M hA p _ W _
  unfold GlobalTheory.CompanionTheory.Ar.Top.RootModel.curveDeg
  refine Finset.sum_nonneg fun j _ => ?_
  rcases j with _ | r
  · have hk : (0:ℝ) < M.kA := by exact_mod_cast M.kA_pos
    have hg := RootFieldNumerics.geoNum_one_nonneg' W M.A.a hA
    simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef, GlobalTheory.CompanionTheory.Ar.Top.RootModel.line]
    exact mul_nonneg (by positivity) (by exact_mod_cast hg)
  · simp [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef]
