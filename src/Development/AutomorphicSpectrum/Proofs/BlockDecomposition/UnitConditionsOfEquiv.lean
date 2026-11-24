module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitTransport

theorem unitConds_of_homeo : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  unfold GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, (hK d).2 h2, ?_, ?_⟩
  · funext x
    rw [hf x, h1]
    simp only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]
  · unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    rw [SetLike.mem_coe, hK t]
    have hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d) := by
      have htd : t * d = d * θ t := ht
      show e t * e d = e d * θ' (e t)
      rw [← hθ, ← map_mul e, ← map_mul e, htd]
    have hcl : closure (Subgroup.zpowers (e t) : Set G') =
        e '' closure (Subgroup.zpowers t : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        refine map_mem_closure e.symm.continuous hy ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩
      · rintro y ⟨x, hx, rfl⟩
        refine map_mem_closure e.continuous hx ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩
    have hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
      rw [hcl]
      exact hc.image e.continuous
    unfold GlobalTheory.BCT.cptPart at h3
    exact h3 (Subgroup.subset_closure (And.intro hte hce))
  · intro y hy
    have hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K' := by
      rw [← hθ, ← map_inv e, ← map_mul e, ← map_mul e]
      exact (hK _).1 hy
    obtain ⟨t', ht', k', hk', hyt⟩ := h4 (e y) hy'
    refine ⟨e.symm t', ?_, e.symm k', ?_, ?_⟩
    · show e.symm t' * d = d * θ (e.symm t')
      apply e.injective
      rw [map_mul, map_mul, hθ, e.apply_symm_apply]
      exact ht'
    · rw [hK, e.apply_symm_apply]
      exact hk'
    · apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hyt

end GlobalTheory.CompanionTheory.UnitTransport
