module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
