module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dite_eq_left h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dite_eq_right hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dite_eq_right e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dite_eq_right fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dite_eq_right e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dite_eq_left e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dite_eq_right e]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
