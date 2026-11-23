module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorChartGeneric
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
public import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
