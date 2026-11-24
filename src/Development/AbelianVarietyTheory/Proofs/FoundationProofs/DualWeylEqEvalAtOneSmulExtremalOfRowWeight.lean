module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open GlobalTheory.DualWeyl MvPolynomial NumberField Formalism.GradedWeylDivisibility

namespace GlobalTheory.DualWeyl

theorem rowDeg_dominated_of_mem_nabla {K : Type} [Field K] {N : ℕ} (la : Fin N → ℕ) (f : Pol N K)
    (hf : f ∈ nabla la K) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, la t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, la t := by
  classical
  unfold nabla at hf
  rw [standardMonomialSpanDomain K N N la] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance K N N k sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem eq_evalAt_one_smul_extremal_of_rowWeight (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ)
    (hla : Antitone la) (f : Pol N K) (hf : f ∈ nabla la K)
    (hw' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la) : f = evalAt 1 f • extremal la K := by
  obtain ⟨c, hc⟩ : ∃ c : K, f = c • extremal la K := by
    apply hwLine K N N le_rfl la hla f hf
    intro a b hab k hk
    by_contra hne
    have hmem := rowDivStable K N N la a b k f hf
    have hht : IsWeightedHomogeneous (lhwinHt N N) f (∑ a : Fin N, (a.val : ℤ) * (la a : ℤ)) := by
      intro d hd
      rw [lhwin_weight_ht, hw' hd]
    have hsh := lhwin_rowDiv_shift K _ a b k f hht
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    have e := hsh hd
    rw [lhwin_weight_ht] at e
    simp only [ldrow_weight_rowW] at e
    have dom := rowDeg_dominated_of_mem_nabla la _ hmem d (mem_support_iff.mpr hd)
    have hle := Formalism.BranchingDeterminantCap.bs_height_le N (rowDeg d) la dom.1 dom.2
    have hab' : (a.val : ℤ) - b.val ≤ -1 := by
      have : a.val < b.val := hab
      omega
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h1 : evalAt 1 f = c := by
    rw [hc, map_smul, evalAt_one_extremal, smul_eq_mul, mul_one]
  rw [h1]
  exact hc

end GlobalTheory.DualWeyl
