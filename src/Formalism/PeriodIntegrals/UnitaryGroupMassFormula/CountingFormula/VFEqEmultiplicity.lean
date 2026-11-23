module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem vF_eq_emultiplicity {F : Type} [Field F] [NumberField F] (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) (α : 𝓞 F) (hα : α ≠ 0) :
    ((vF 𝔭 α : ℕ) : ℕ∞) = emultiplicity 𝔭 (Ideal.span {α}) := by
  have hs : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hfm : FiniteMultiplicity 𝔭 (Ideal.span {α}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime h0 h𝔭) hs
  rw [hfm.emultiplicity_eq_multiplicity]
  congr 1
  unfold vF
  have hset : {e : ℕ | α ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {α})) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← hfm.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset, csSup_Iic]

end

theorem countExt_single (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : 𝓞 F) (h𝔭 : 𝔭.IsMaximal)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭) (hα : α ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (α : F))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * vF 𝔭 α : ℕ) : ℤ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  haveI : P.asIdeal.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hP]⟩
  set β : 𝓞 K := algebraMap (𝓞 F) (𝓞 K) α
  have hβ : β ≠ 0 := by
    intro h
    apply hα
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [map_zero]; exact h)
  have hsβ : Ideal.span {β} ≠ ⊥ := by simpa using hβ
  have hsα : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hK : algebraMap F K (α : F) = algebraMap (𝓞 K) K β := rfl
  rw [hK, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P hsβ,
    Ideal.count_associates_factors_eq hsβ P.isPrime P.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hsβ P]
  congr 1
  have hfmP : FiniteMultiplicity P.asIdeal (Ideal.span {β}) :=
    FiniteMultiplicity.of_prime_left P.prime hsβ
  have hmap : Ideal.span {β} = (Ideal.span {α}).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hsα
    (Ideal.prime_of_isPrime h0 h𝔭.isPrime).irreducible P.irreducible P.ne_bot
  rw [← hmap, hfmP.emultiplicity_eq_multiplicity, ← vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 α hα,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P.asIdeal h0] at he
  exact_mod_cast he

theorem count_extension : CountExt := by
  intro K F _ _ _ _ _ n 𝔭 P α h𝔭 hP hα
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hprod : (∏ j, ((α j : 𝓞 F) : F)) = ((∏ j, α j : 𝓞 F) : F) := by simp
  have hne : (∏ j, α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hα j
  rw [hprod, countExt_single K F 𝔭 P _ h𝔭 hP hne]
  congr 2
  have key : ((vF 𝔭 (∏ j, α j) : ℕ) : ℕ∞) = ((∑ j, vF 𝔭 (α j) : ℕ) : ℕ∞) := by
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ hne, ← Ideal.prod_span_singleton, Nat.cast_sum]
    rw [Finset.emultiplicity_prod (Ideal.prime_of_isPrime h0 h𝔭.isPrime)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ (hα j)]
  exact_mod_cast key

end PI.UnitaryGroupMassFormula.CntFormula.R6
