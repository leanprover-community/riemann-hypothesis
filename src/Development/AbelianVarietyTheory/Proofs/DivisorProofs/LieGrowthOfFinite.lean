module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothinStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem GlobalTheory.AutGrowth.tame_of_autForm (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hφ : IsAutForm φ) : φ ∈ tame E a := by
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

theorem GlobalTheory.AutGrowth.lie_growth_of_finite : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ →
    ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤
      C * GlobalTheory.CuspRep.height y ^ N := by
  intro hP E _ _ _ a X φ hφ
  exact growth_of_tame (lie_mem_tame X (GlobalTheory.AutGrowth.tame_of_autForm hP E a φ hφ))
