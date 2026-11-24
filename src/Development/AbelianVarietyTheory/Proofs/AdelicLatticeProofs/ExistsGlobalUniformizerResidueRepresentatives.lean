module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_uniformizer_and_residue_representatives :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  intro F _ _ v
  classical
  have h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.Idele.exists_valued_sub_le v hx 1
    refine ⟨a, lt_of_le_of_lt ha ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨?_, h2, h3, ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    exact ⟨π, hπ, (h2 π).trans hπ⟩
  · haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)
    refine ⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal =>
      algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      rw [h2]
      exact v.valuation_le_one (s q)
    · intro x hx
      obtain ⟨a, ha⟩ := h3 x hx
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩
      have hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal := Ideal.Quotient.eq.1 (hs _).symm
      have hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1 :=
        (v.valuation_lt_one_iff_mem _).2 hm
      rw [← h2, map_sub, map_sub] at hl
      rw [← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)

end GlobalTheory.QNorm
