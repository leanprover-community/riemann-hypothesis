module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField NumberField.ComplexEmbedding

namespace GlobalTheory.CMFieldCriterion

theorem isTotallyReal_fixedField (K : Type) [Field K] [NumberField K] {σ : Gal(K/ℚ)}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsTotallyReal (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
  dsimp only
  rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
    ComplexEmbedding.isReal_iff]
  ext x
  have hx : σ (x : K) = x :=
    (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)
  have h := (hσ W.embedding).eq (x : K)
  rw [hx] at h
  rw [conjugate_coe_eq]
  exact h.symm

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    {σ : Gal(K/ℚ)} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : σ ≠ 1 :=
    (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hne
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact isConj_apply_apply (hσ φ) x
  have hreal := isTotallyReal_fixedField K hσ
  have hquad :
      Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K :=
    { finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }
  exact IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K

end GlobalTheory.CMFieldCriterion
