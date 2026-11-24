module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_valuation_aut (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧
      ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
  have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    exact σ.commutes (a : F)
  refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    ext a
    change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
    rw [hfix]
  · intro y
    exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y

theorem sUnits_over_and_aut : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ (τ : E ≃ₐ[F] E) (y : Eˣ), y ∈ sUnits E SE → Units.map (τ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ _ S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun σ y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := exists_place_valuation_aut F E σ w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.CNorm
