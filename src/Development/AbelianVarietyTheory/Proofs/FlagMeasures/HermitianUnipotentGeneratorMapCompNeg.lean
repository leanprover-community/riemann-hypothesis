module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
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

open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

theorem gen_comp_gen_neg {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K)
    (he : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0)
    (hc : ∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) (v : V) :
    gen H J e ρ c (gen H J e (-ρ) c' v) = v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  set u := gen H J e (-ρ) c' v with hu
  have hue : ∀ b, H.B u (e b) = H.B v (e b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, he, hρe]
  have huρ : ∀ b, H.B u (ρ b) = H.B v (ρ b) - ∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, heρ, sub_eq_add_neg]
  have h4 : ∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b =
      ∑ b ∈ J, ∑ a ∈ J, (H.B (ρ b) (ρ a) * H.B v (e b)) • e a := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have key : (∑ b ∈ J, ∑ a ∈ J, (c' a b * H.B v (e b)) • e a) +
      (∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b) +
      ∑ b ∈ J, ∑ a ∈ J, (c a b * H.B v (e b)) • e a = 0 := by
    rw [h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← add_smul, ← add_smul, ← add_mul, ← add_mul,
      show c' a b + H.B (ρ b) (ρ a) + c a b = 0 by linear_combination hc a b, zero_mul, zero_smul]
  rw [gen_apply H J e ρ c u]
  simp only [hue, huρ]
  rw [hu, gen_apply H J e (-ρ) c' v]
  simp only [map_neg, Pi.neg_apply, neg_smul, smul_neg, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linear_combination (norm := module) key

end GlobalTheory.RowStab
