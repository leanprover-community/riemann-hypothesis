module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SysPull

theorem finite_bound {ι : Type} [Finite ι] (f : ι → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem finite_scale {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := finite_bound fun a => (f a)⁻¹
  by_cases he : Nonempty ι
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    exact ⟨M⁻¹, inv_pos.2 hM0, fun a => inv_le_of_inv_le₀ (hf a) (hM a)⟩
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem pullback_common : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  intro e e' σ _ S X' _ _ _ A' Θ' L' s' nb m W q hq hP pΘ' posΘ' pL' sec' snc' nrm hL hs
  have key : ∀ p : Fin 2 × σ, ∃ C' t' : ℝ,
      IsSingWeight A' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1) S.C₅ ∧
      IsRegFamily A' Θ' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1)
        (fun t => S.phT p.2 t ∘ q p.1) C' t' ∧
      IsRegFamilyC2 A' s' (S.ph p.2 ∘ q p.1) (fun t => S.phT p.2 t ∘ q p.1) := by
    rintro ⟨i, a⟩
    have snc_i : IsSNC A' (S.L.pullback (q i) (hq i).1) (fun x y => S.s (q i x) (q i y)) m W := by
      rw [hL i, hs i]
      exact snc'
    obtain ⟨C', t', h1, h2, h3⟩ := hP S.A A' (q i) (hq i) S.Θ S.L Θ' S.s S.m S.W m W S.potΘ S.posΘ pΘ' posΘ'
      S.potL S.sec S.snc S.norm_le snc_i (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
    rw [hL i, hs i] at h1 h2
    rw [hs i] at h3
    exact ⟨C', t', h1, h2, h3⟩
  choose C' t' h1 h2 h3 using key
  by_cases hσ : Nonempty σ
  · obtain ⟨a₀⟩ := hσ
    obtain ⟨D, hD⟩ := finite_bound fun p => |C' p|
    obtain ⟨T₀, hT₀, hT⟩ := finite_scale t' fun p => (h2 p).1
    have hS : 0 < S.t₀ := (S.reg a₀).1
    refine ⟨S.C₅, D, min (min T₀ S.t₀) (Real.exp (-1)),
      (min_le_left _ _).trans (min_le_right _ _), fun i a => ⟨h1 (i, a), ?_, h3 (i, a)⟩⟩
    exact (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e' X' A' Θ' L' s' nb m W pL' sec' snc' nrm pΘ' posΘ').2.1 _ _ _ _ _ _ _ (hD (i, a))
      (lt_min (lt_min hT₀ hS) (Real.exp_pos _)) ((min_le_left _ _).trans ((min_le_left _ _).trans (hT (i, a))))
      (min_le_right _ _) (h2 (i, a)) (h1 (i, a)).1
  · exact ⟨0, 0, S.t₀, le_rfl, fun _ a => absurd ⟨a⟩ hσ⟩

end GlobalTheory.CompanionTheory.Ar.PB.SysPull
