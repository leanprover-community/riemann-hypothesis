module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveProperClosedFinite
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffFinite.proof (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩

end GroundTheory.Heights₂.Heights
