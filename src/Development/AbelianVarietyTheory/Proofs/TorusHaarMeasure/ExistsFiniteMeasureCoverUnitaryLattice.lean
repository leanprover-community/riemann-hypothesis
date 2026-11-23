module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimumStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.FiniteCovolume

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : X.p0 = 0 ∨ X.p0 = r
  · haveI : CompactSpace H := GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite r X H hH hp
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : X.p0 < r := lt_of_le_of_ne X.p0_le fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := (GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH
    have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      GlobalTheory.T.exists_drift_function_realUnitaryGroup r X H hH hp0 hpr (x0F X) hx0
    obtain ⟨U, hU, hU1⟩ := GlobalTheory.GamDisc.gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum r X H hH (x0F X) hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end GlobalTheory.FiniteCovolume
