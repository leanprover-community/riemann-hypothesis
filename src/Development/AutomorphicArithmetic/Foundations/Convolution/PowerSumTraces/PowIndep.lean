module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private lemma powSum_eq_count (s : Multiset ℂ) (S : Finset ℂ) (h : ∀ z ∈ s, z ∈ S) (j : ℕ) :
    (s.map (· ^ j)).sum = ∑ z ∈ S, (s.count z : ℂ) * z ^ j := by
  classical
  rw [Finset.sum_multiset_map_count]
  have hsub : s.toFinset ⊆ S := fun z hz => h z (Multiset.mem_toFinset.1 hz)
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]
  · intro z _ hz
    have : s.count z = 0 := Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)
    simp [this]

theorem UpperTheory.ConvolutionTheory.C.powIndep :
    UpperTheory.ConvolutionTheory.C.PowIndep := by
  classical
  intro ι _ c Z hZ hev ζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Finset ℂ := Finset.univ.biUnion fun i => (Z i).toFinset
  let a : ℂ → ℂ := fun z => ∑ i, c i * ((Z i).count z : ℂ)
  have hmem : ∀ i, ∀ z ∈ Z i, z ∈ S := fun i z hz =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩
  have key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0 := by
    intro j hj
    have h0 := hN j hj
    simp only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [a, Finset.sum_mul, mul_assoc]
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)
  have lin : LinearIndependent ℂ (fun z : S => (powersHom ℂ (z : ℂ) : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powersHom ℂ (z : ℂ))
      ((powersHom ℂ).injective.comp Subtype.val_injective)
  rw [Fintype.linearIndependent_iff] at lin
  have hb := lin (fun z => a z * (z : ℂ) ^ N) (by
    funext n
    have := key (N + n.toAdd) (Nat.le_add_right _ _)
    rw [← Finset.sum_coe_sort S] at this
    simpa [pow_add, mul_assoc, Finset.sum_apply] using this)
  have ha : a ζ = 0 := by
    by_cases hζ : ζ ∈ S
    · have := hb ⟨ζ, hζ⟩
      exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (Z i).count ζ = 0 := Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)
      simp [this]
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Multiset.filter_eq', Multiset.card_replicate]
