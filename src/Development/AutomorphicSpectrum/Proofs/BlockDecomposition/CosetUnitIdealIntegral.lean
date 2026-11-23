module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
