module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets
open scoped nonZeroDivisors

noncomputable section

theorem SliceMassFinite.exists_projClosure {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ),
      IsProjPrime W ∧ IsChowForm W (e + 2) F ∧ linForm ℓ ∉ W ∧ W ⊔ Ideal.span {linForm ℓ - 1} = I := by
  obtain ⟨W, hW, hℓW, hWI, -⟩ := ChartHomogenise.proof ℂ n I ℓ hI hℓ
  have hP := hW.isPrime

  have hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_
    have h00 := hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0
    rw [homogeneousComponent_zero] at h00
    have hc : AddMonoidAlgebra.coeff (linForm ℓ - 1) 0 = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h00
    exact (Ideal.eq_top_iff_one W).mpr h00
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have eq := DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at eq
  rw [ringKrullDim_eq_of_ringEquiv eq, hWI, hdim] at h1

  have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞) := by
    have := ringKrullDim_quotient_le W
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at this

  have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    generalize hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2
    induction D using WithBot.recBotCoe with
    | bot => simp at h1
    | coe b =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h2
        exact ENat.natCast_ne_top _ (top_le_iff.mp h3)
      | coe m =>
        have hm1 : e + 1 + 1 ≤ m := by exact_mod_cast h1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1) := ⟨hP, by rw [hD]; rfl⟩
        have h3 := IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW
        rw [hWI, hdim] at h3
        have hk : k ≤ e + 1 := by exact_mod_cast h3
        have hke : k + 1 = e + 1 + 1 := by omega
        rw [hke]
        rfl
  obtain ⟨F, hFW⟩ := (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩
  exact ⟨W, F, hW, hFW, hℓW, hWI⟩

end

end GroundTheory.Heights₂.Heights
