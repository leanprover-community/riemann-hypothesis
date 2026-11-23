module

public import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom
import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

section Gen

variable {σ R : Type*} [CommRing R]

theorem X_mul_mono (v : σ) (mo : σ →₀ ℕ) (c : R) : X v * monomial mo c = monomial (mo + Finsupp.single v 1) c := by
  rw [X, monomial_mul, one_mul, add_comm]

theorem pderiv_add_single (w : σ) (L : σ →₀ ℕ) (c : R) :
    pderiv w (monomial (L + Finsupp.single w 1) c) = monomial L (c * ((L w : R) + 1)) := by
  rw [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  push_cast
  rfl

theorem pderiv_mono_zero (w : σ) (L : σ →₀ ℕ) (c : R) (h : L w = 0) : pderiv w (monomial L c) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (w : σ) (L : σ →₀ ℕ) (h : L w ≠ 0) : ∃ L', L = L' + Finsupp.single w 1 := ⟨L - Finsupp.single w 1,
  (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩

end Gen

section PolS

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem multideg_add_single (mo : ι × Fin n →₀ ℕ) (x0 : ι) (a : Fin n) (i : ι) :
    multideg (mo + Finsupp.single (x0, a) 1) i = multideg mo i + if i = x0 then 1 else 0 := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = x0
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mem_Pol' {d : ι → ℕ} {F : MvPolynomial (ι × Fin n) R} :
    F ∈ Pol R n d ↔ ∀ m ∈ F.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    exact h hm
  · intro h m hm
    exact h m hm

theorem mono_mem_Pol {d : ι → ℕ} (m : ι × Fin n →₀ ℕ) (c : R) (h : ∀ i, multideg m i = d i) :
    monomial m c ∈ Pol R n d := by
  rw [mem_Pol']
  intro m' hm'
  have h1 := support_monomial_subset hm'
  rw [Finset.mem_singleton] at h1
  rw [h1]
  exact h

theorem Pol_pderiv {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d' x0 = d x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : pderiv (x0, a) H ∈ Pol R n d := by
  rw [mem_Pol'] at hH

  rw [H.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hz : m (x0, a) = 0
  · rw [pderiv_mono_zero _ _ _ hz]
    exact Submodule.zero_mem _
  · obtain ⟨m', rfl⟩ := exists_add_single _ m hz
    rw [pderiv_add_single]
    apply mono_mem_Pol
    intro i
    have hi := hH _ hm i
    rw [multideg_add_single] at hi
    by_cases hix : i = x0
    · subst hix
      simp at hi
      omega
    · simp [hix] at hi
      rw [hi, h1 i hix]

theorem Pol_X_mul {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = d' x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : X (x0, a) * H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [X_mul_mono]
  apply mono_mem_Pol
  intro i
  rw [multideg_add_single, hH m hm i]
  by_cases hix : i = x0
  · subst hix
    simp
    omega
  · simp [hix]
    exact h1 i hix

end PolS

theorem valuation_ge_of_le_add_one {x y : WithTop ℤ} {t t' : ℝ} (h : x ≤ y + ((1 : ℤ) : WithTop ℤ)) (hx : geZ x t') (ht : t + 1 ≤ t') :
    geZ y t := by
  intro k hk
  rw [hk] at h
  have h' : x ≤ ((k + 1 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_add]
    exact h
  induction x using WithTop.recTopCoe with
  | top => simp at h'
  | coe k'' =>
    have h2 := hx k'' rfl
    have h3 : (k'' : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast WithTop.coe_le_coe.mp h'
    linarith

section ValOp

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

end ValOp

end Formalism.MainNotions.PairMembershipBlocks
