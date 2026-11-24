module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro h4 E _ _ _ N W hW
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
        ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
      intro U _ _ _ _ _ _ hU
      obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
        fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
      exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
    · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
      refine ⟨Ω, hΩ, fun K hK => ?_⟩
      obtain ⟨Θ, hΘ, h'⟩ := h K hK
      refine ⟨Θ, hΘ, ?_⟩
      intro U hs ha hg hn hc hi hU
      obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
      exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
