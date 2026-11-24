module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
