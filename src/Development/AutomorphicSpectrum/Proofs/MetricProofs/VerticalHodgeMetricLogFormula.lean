module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

private theorem zpow_finset_sum_divisor {α : Type*} (s : Finset α) (f : α → ℤ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (∑ p ∈ s, f p) = ∏ p ∈ s, x ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem log_muVert_h_of_mem : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (B : ℕ), ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muVert Hd B).h z) = Real.log ((muLine Hd).h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd B z hz
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal D.y) := D.arith.2.1.2.1
  have hpos := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorPos.proof
  have hsmooth := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorSmooth.proof hpos
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.mp hp).1
  have hnz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hLpos : 0 < (muLine Hd).h z := (muLine Hd).pos z hnz
  have hVpos : ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun p hp => hpos II Ψ K J Ω W D p (hSB p hp) z hz
  have hPpos : 0 < ∏ p ∈ D.SB B, D.vertFactor p z := Finset.prod_pos hVpos
  have hF : (muVert Hd B).h z = (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z := by
    unfold muVert
    refine GroundTheory.Heights₂.Heights.LowerBoundFree.NbarSmooth.hermOfFun_h_of_mem hP ?_ hz (mul_pos hLpos hPpos)
    intro w hw c hc
    have hc' : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h1 : (muLine Hd).h (torusSmul c w) = (∏ k, ‖c k‖ ^ Hd.aMu k) * (muLine Hd).h w :=
      (muLine Hd).smul c w hc
    have h2 : ∀ p ∈ D.SB B, D.vertFactor p (torusSmul c w) =
        (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p w :=
      fun p hp => (hsmooth II Ψ K J Ω W D p (hSB p hp)).1 w hw c hc
    have h3 : ∏ k, ‖c k‖ ^ muTwDeg Hd B k =
        (∏ k, ‖c k‖ ^ Hd.aMu k) * ∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k := by
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [muTwDeg, Pi.add_apply, Finset.sum_apply]
      rw [zpow_add₀ (hc' k), zpow_finset_sum_divisor _ _ (hc' k)]
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, h3]
    ring
  rw [hF, Real.log_mul hLpos.ne' hPpos.ne', Real.log_prod fun p hp => (hVpos p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
