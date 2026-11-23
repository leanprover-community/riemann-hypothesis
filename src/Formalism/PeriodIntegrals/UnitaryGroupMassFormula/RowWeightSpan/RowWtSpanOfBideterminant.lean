module

public import Formalism.PeriodIntegrals.RowWtSpan
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
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.RWS

open PI.RW

def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0

theorem RE_eq_of_hom {K : Type} [CommRing K] {k : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin k) K) (d : ℕ)
    (h : IsWeightedHomogeneous (rowW a) f d) : RE K k a a f = (d : K) • f := by
  have h' := h.sum_weight_X_mul_pderiv
  unfold RE
  rw [Nat.cast_smul_eq_nsmul K d f, ← h']
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp [rowW]

theorem minor_hom {K : Type} [CommRing K] {k s : ℕ} (a : Fin k) (I : Fin s → Fin k) (hs : s ≤ k) :
    IsWeightedHomogeneous (rowW a) (initMinor K I hs)
      (Finset.univ.filter fun p => I p = a).card := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin k × Fin k) K))
    (fun i => rowW a (I (σ i), Fin.castLE hs i)) (w := rowW a)
    (fun i _ => isWeightedHomogeneous_X K (rowW a) _)
  have hdeg : ∑ i, rowW a (I (σ i), Fin.castLE hs i) =
      (Finset.univ.filter fun p => I p = a).card := by
    simp only [rowW]
    rw [Finset.card_filter]
    exact Equiv.sum_comp σ (fun p => if I p = a then 1 else 0)
  rw [hdeg] at hp
  rw [Units.smul_def, ← mem_weightedHomogeneousSubmodule] at *
  exact zsmul_mem hp _

theorem bidet_hom {K : Type} [CommRing K] {k N : ℕ} (a : Fin k) (sz : Fin N → ℕ)
    (hsz : ∀ j, sz j ≤ k) (I : ∀ j, Fin (sz j) → Fin k) :
    IsWeightedHomogeneous (rowW a) (bideterminant K sz hsz I)
      (∑ j, (Finset.univ.filter fun p => I j p = a).card) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => minor_hom a (I j) (hsz j)

theorem wt_le {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by
  unfold shapeDeg
  rw [ht0, Finset.card_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : 0 < sz j
  · rw [if_pos hj]
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (hI j).injective (hp.trans hq.symm)
  · rw [if_neg hj]
    have hem : (Finset.univ : Finset (Fin (sz j))) = ∅ :=
      Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩
    rw [hem]
    simp

theorem rowWtSpan_of_bideterminant (h1 : BideterminantMem) (h2 : BideterminantSpan) : PI.RowWtSpan := by
  intro K _ m ν _
  refine ⟨{d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
      (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)},
    fun d => bideterminant K d.1.2.1 d.2.1 d.1.2.2,
    fun d a => ∑ j, (Finset.univ.filter fun p => d.1.2.2 j p = a).card, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
      subst hsh
      exact h1 K (m + 1) (m + 1) N sz hsz I
    · refine le_trans (h2 K (m + 1) (m + 1) ν) (Submodule.span_mono ?_)
      rintro f ⟨N, sz, hsz, I, hsh, hmono, rfl⟩
      exact ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    exact RE_eq_of_hom a _ _ (bidet_hom a sz hsz I)
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    have hw := wt_le sz I hmono a 0 rfl
    rw [hsh] at hw
    exact hw

end PI.RWS
