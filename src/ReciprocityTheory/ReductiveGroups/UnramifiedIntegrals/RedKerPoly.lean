module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProj
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSeries
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSqrt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedVeluAlg

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem wpNum_coeff_mem (k : Subfield ℂ) {g2 g3 : ℂ} (h2 : g2 ∈ k) (h3 : g3 ∈ k) (n : ℕ) :
    PowerSeries.coeff n (wpNum g2 g3) ∈ k := by
  have h := (seriesMap k ℂ k.subtype ⟨g2, h2⟩ ⟨g3, h3⟩ 0 0).1
  have h' : wpNum g2 g3 = PowerSeries.map k.subtype (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩) := h.symm
  rw [h', PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩)).2

theorem kerPoly_mem (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (k : Subfield ℂ) (h2 : L.g₂ ∈ k) (h3 : L.g₃ ∈ k) (hk : α ∈ k) :
    ∀ i, (rootPoly (xsOf L T)).coeff i ∈ k := by
  apply sqrt_poly k _ (rootPoly_monic _)
  refine proj_trick k (wpNum L.g₂ L.g₃) (PowerSeries.rescale α (wpNum L.g₂ L.g₃))
    (wpNum_coeff_mem k h2 h3) ?_ ?_ (veluNum L.g₂ L.g₃ (xsOf L T)) (rootPoly (xsOf L T) ^ 2)
    (2 * (xsOf L T).card) (veluNum_natDegree_le _ _ _) ((rootPoly_monic _).pow 2) ?_
    (veluNum_coprime _ _ _ fun x hx => hT.fW_ne hx) (velu_series L α T hα hs hT)
  · intro n
    rw [PowerSeries.coeff_rescale]
    exact k.mul_mem (k.pow_mem hk n) (wpNum_coeff_mem k h2 h3 n)
  · simp [wpNum]
  · rw [(rootPoly_monic _).natDegree_pow, rootPoly_natDegree]

theorem prod_mem_of_rootPoly {E : Type} [Field E] (k : Subfield E) (xs : Finset E)
    (h : ∀ i, (rootPoly xs).coeff i ∈ k) : ∏ x ∈ xs, x ∈ k := by
  have h0 : (rootPoly xs).coeff 0 = (-1) ^ xs.card * ∏ x ∈ xs, x := by
    rw [Polynomial.coeff_zero_eq_eval_zero, rootPoly, Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => (neg_one_mul x).symm
  have h1 : ∏ x ∈ xs, x = (-1) ^ xs.card * (rootPoly xs).coeff 0 := by
    rw [h0, ← mul_assoc, ← mul_pow]
    simp
  rw [h1]
  exact k.mul_mem (k.pow_mem (k.neg_mem k.one_mem) _) (h 0)

end ReciprocityTheory.ChartRestriction.L1
