module

public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct



namespace GlobalTheory.DivInt
open GlobalTheory.AdeleBaseChange Formalism.UG.P

theorem exists_nat_mul_div_pow_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  intro F E _ _ _ _ _ w z hz ℓ hℓ
  obtain ⟨ι, hι⟩ := exists_toAd F E
  obtain ⟨x, r, hr, hzr⟩ := exists_approx z
  obtain ⟨D, hD, hDx⟩ := exists_nat_mul_integral ({x} : Finset E)
  obtain ⟨o, ho⟩ := hDx x (Finset.mem_singleton_self x)
  have hDz : algebraMap E _ (D : E) * ι z ∈ intAd E := by
    rw [hzr, map_add (f := _), map_tmul_one hι, mul_add, ← map_mul, ← nsmul_eq_mul, ← ho]
    exact add_mem (algebraMap_int_mem o) (mul_mem (by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact algebraMap_int_mem _) (map_mem_int hι hr))
  refine ⟨D, hD, fun n => mem_int_of_map hι ?_⟩
  intro P
  rw [map_mul, map_tmul_one hι]
  change algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P ∈ P.adicCompletionIntegers E
  by_cases hP : P.under (𝓞 F) = w
  · have hv : Valued.v (algebraMap E (P.adicCompletion E) (ℓ : E)) = 1 := by
      rw [levelaf_valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      apply hℓ
      rw [← hP, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
      exact hm
    have h1 := hDz P
    change algebraMap E (P.adicCompletion E) (D : E) * ι z P ∈ P.adicCompletionIntegers E at h1
    have e : algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P =
        (algebraMap E (P.adicCompletion E) (ℓ : E))⁻¹ ^ n *
          (algebraMap E (P.adicCompletion E) (D : E) * ι z P) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, inv_pow]; ring
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [e, map_mul, map_pow, map_inv₀, hv, inv_one, one_pow, one_mul]
    exact h1
  · have h0 : ι z P = 0 := (prV_eq_zero_iff hι (P.under (𝓞 F)) z).1 (hz _ hP) P rfl
    rw [h0, mul_zero]
    exact zero_mem _

end GlobalTheory.DivInt
