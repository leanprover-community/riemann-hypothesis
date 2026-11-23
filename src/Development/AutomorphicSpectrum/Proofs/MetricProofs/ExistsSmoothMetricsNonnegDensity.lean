module

public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem isSheet_bot_of_isSetSheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hγ : IsSetSheet S Ψ y w γ) : IsSheet ⊥ Ψ y w γ := by
  refine ⟨hγ.1, hγ.2.mono fun y' hy' => ⟨hy'.1, ⟨hS _ hy'.2.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  intro K _ ι _ e L hL
  classical
  choose T hTs hTp hLTp using fun j =>
    GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof K ι (L j) (hL j)
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hTs j)
  refine ⟨fun j => ((L j).tensor (T j)).tensor (T j), fun j => isSmoothHerm_tensor (hLT j) (hTs j), ?_⟩
  intro S Ψ hS
  have hab : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ → |maDensity (fun j y' => pot L j (γ y')) y| ≤
        3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp
      (isSheet_bot_of_isSetSheet hS hγ)
  have hnn : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ →
        0 ≤ maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hab hγ)) (by positivity)
  refine ⟨fun g y w hg => ?_, fun g g' y w hgg => ?_⟩
  · unfold setSheetDensity
    split_ifs with hγ
    · exact mul_nonneg (hg _) (hnn hγ.choose_spec)
    · exact le_rfl
  · unfold setSheetDensity
    by_cases hγ : ∃ γ, IsSetSheet S Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hs := hγ.choose_spec
      have hmem : hγ.choose y ∈ S := hs.2.self_of_nhds.2.1
      have hg := hgg _ hmem
      rw [abs_mul]
      calc |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y|
          ≤ g' (hγ.choose y) * (3 ^ e * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) :=
            mul_le_mul hg (hab hs) (abs_nonneg _) ((abs_nonneg _).trans hg)
        _ = 3 ^ e * (g' (hγ.choose y) * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) := by ring
    · rw [dite_eq_right hγ, dite_eq_right hγ]
      simp

end GlobalTheory.CompanionTheory.Ar.Pub.CxTwist
