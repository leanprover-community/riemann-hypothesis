module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

private theorem lex_cases (t : β ⊕ₗ κ) : (∃ i, t = inlE i) ∨ ∃ l, t = inrE l := by
  rcases t with i | l
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

private theorem mem_uni_l (b : Finset β) (L : Finset κ) (i : β) :
    (inlE i : β ⊕ₗ κ) ∈ uni b L ↔ i ∈ b := by
  simp [uni, inlE]

private theorem mem_uni_r (b : Finset β) (L : Finset κ) (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ uni b L ↔ l ∈ L := by
  simp [uni, inrE]

private theorem mem_lft (s : Finset (β ⊕ₗ κ)) (i : β) : i ∈ lft s ↔ (inlE i : β ⊕ₗ κ) ∈ s := by
  simp [lft, inlE]

private theorem mem_rgt (s : Finset (β ⊕ₗ κ)) (l : κ) : l ∈ rgt s ↔ (inrE l : β ⊕ₗ κ) ∈ s := by
  simp [rgt, inrE]

private theorem l_lt_r (i : β) (l : κ) : (inlE i : β ⊕ₗ κ) < inrE l := Sum.Lex.inl_lt_inr i l

private theorem not_r_lt_l (i : β) (l : κ) : ¬ (inrE l : β ⊕ₗ κ) < inlE i := Sum.Lex.not_inr_lt_inl

private theorem card_uni (b : Finset β) (L : Finset κ) : (uni b L).card = b.card + L.card := by
  simp [uni]

private theorem sum_uni {M : Type} [AddCommMonoid M] (b : Finset β) (L : Finset κ) (f : β ⊕ₗ κ → M) :
    ∑ t ∈ uni b L, f t = ∑ i ∈ b, f (inlE i) + ∑ l ∈ L, f (inrE l) := by
  rw [uni, Finset.sum_map, Finset.sum_disjSum]
  rfl

private theorem erase_l [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (i : β) :
    (uni b L).erase (inlE i) = uni (b.erase i) L := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l, Finset.mem_erase, inlE.injective.ne_iff]
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r]
    exact and_iff_right (l_lt_r i m).ne'

private theorem erase_r [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (l : κ) :
    (uni b L).erase (inrE l) = uni b (L.erase l) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l]
    exact and_iff_right (l_lt_r j l).ne
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r, Finset.mem_erase, inrE.injective.ne_iff]

private theorem sign_l (b : Finset β) (L : Finset κ) (i : β) :
    GlobalTheory.cubeSign (uni b L) (inlE i) = GlobalTheory.cubeSign b i := by
  unfold GlobalTheory.cubeSign
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [not_r_lt_l]

private theorem sign_r (b : Finset β) (L : Finset κ) (l : κ) :
    GlobalTheory.cubeSign (uni b L) (inrE l) = (-1 : ℤ) ^ b.card * GlobalTheory.cubeSign L l := by
  unfold GlobalTheory.cubeSign
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [l_lt_r]

private theorem wd_app {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

end

theorem UpperTheory.Gal.productCup_of_system.wdUni_of :
    WdUni := by
  intro β κ E _ _ _ _ w c b L
  refine ⟨?_, ?_, ?_, card_uni b L, ?_⟩
  · rw [wd_app, wd_app, wd_app, sum_uni, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [sign_l, erase_l]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [sign_r, erase_r, mul_smul]
  · ext i
    rw [mem_lft, mem_uni_l]
  · ext l
    rw [mem_rgt, mem_uni_r]
  · intro s
    ext t
    rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · rw [mem_uni_l, mem_lft]
    · rw [mem_uni_r, mem_rgt]
