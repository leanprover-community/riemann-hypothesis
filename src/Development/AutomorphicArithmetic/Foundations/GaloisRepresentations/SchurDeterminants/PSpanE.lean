module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
