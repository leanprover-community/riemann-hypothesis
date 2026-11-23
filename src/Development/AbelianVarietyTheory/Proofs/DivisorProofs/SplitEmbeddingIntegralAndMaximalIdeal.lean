module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
