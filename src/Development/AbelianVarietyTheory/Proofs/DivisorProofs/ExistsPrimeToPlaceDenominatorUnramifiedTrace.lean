module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.UnramTraceDenom

theorem exists_not_mem_mul_isIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  intro F E _ _ _ _ _ hU v e h
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hU
  haveI := v.isPrime
  let b := NumberField.RingOfIntegers.basis E
  have hloc : ∀ i, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F s * Algebra.trace F E ((b i : E) * e) = algebraMap (𝓞 F) F r := by
    intro i
    apply GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
    have hi := h (b i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hi
    have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Algebra.trace F E ((b i : E) * e))
    exact e1 ▸ hi
  choose s hs r hr using hloc
  refine ⟨∏ i, s i, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hs i hi
  · have key : ∀ i, algebraMap (𝓞 F) F (∏ j, s j) * Algebra.trace F E ((b i : E) * e) ∈
        (algebraMap (𝓞 F) F).range := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap (𝓞 F) F (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    have htr : ∀ a : 𝓞 E, Algebra.trace F E (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * a) ∈
        (algebraMap (𝓞 F) F).range := by
      intro a
      have ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : E) * (b i : E) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr a)

        simpa [map_sum, zsmul_eq_mul] using this.symm

      rw [ha, Finset.mul_sum, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      have e2 : algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * (((b.repr a i : ℤ) : E) * (b i : E)) =
          algebraMap F E (((b.repr a i : ℤ) : F) * algebraMap (𝓞 F) F (∏ j, s j)) * ((b i : E) * e) := by
        have hc : ((∏ i, s i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∏ j, s j) := rfl
        rw [hc, map_mul, map_intCast]; ring
      rw [e2, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_assoc]
      exact Subring.mul_mem _ (intCast_mem _ _) (key i)
    obtain ⟨y, hy⟩ := GlobalTheory.InertSelfDual.mem_of_trace (F := F) (E := E)
      (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e) htr
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y

end GlobalTheory.UnramTraceDenom
