module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.Adele.Approximation

@[expose] public section

open NumberField IsDedekindDomain

theorem UpperTheory.V.Lit.Dr.finField : UpperTheory.V.Lit.Dr.FinField := by
  intro E _ _ C T hT
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hdE : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    ((∑ w : InfinitePlace E, w (algebraMap (𝓞 E) E d)) * C)
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 E) E d * x) (hfin.subset ?_)
    (mul_right_injective₀ hdE).injOn
  rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · have h := hd _ hxT
    rw [← map_mul] at h
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (algebraMap (𝓞 E) E d * x) fun v => by
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        exact GroundTheory.Global.mem_integralFiniteAdeles.1 h v
    beta_reduce
    rw [← hz]
    exact RingOfIntegers.isIntegral_coe _
  · beta_reduce
    rw [← InfinitePlace.apply, map_mul]
    exact mul_le_mul
      (Finset.single_le_sum (f := fun w : InfinitePlace E => w (algebraMap (𝓞 E) E d))
        (fun w _ => apply_nonneg w _) (Finset.mem_univ _))
      (hx _) (apply_nonneg _ _) (Finset.sum_nonneg fun w _ => apply_nonneg w _)
