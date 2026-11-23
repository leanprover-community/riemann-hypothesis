module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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
public import ReciprocityTheory.SemistableReduction.LogNormCoeffSubLeBlockSphereLogMean

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

theorem heightLowerBound_of_sj_of_sphereLogIntegrable (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) :
    HeightLowerBoundStatement := by
  intro K _ _ B n a f hn hf hmh
  classical
  obtain ⟨s, hs⟩ : ∃ s, s ∈ f.support :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have h1 := neg_log_norm_coeff_le_finitePlaces f s hs
  have h2 : ∀ σ : K →+* ℂ, Real.log ‖σ (f.coeff s)‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤
      blockSphereMean B n (MvPolynomial.map σ f) := by
    intro σ
    have hmap : IsMultiHomogeneous a (MvPolynomial.map σ f) := by
      intro t ht b
      rw [MvPolynomial.support_map_of_injective _ σ.injective] at ht
      exact hmh t ht b
    exact log_norm_coeff_sub_le_blockSphereLogMean hSJ hInt hn hmap s
      (by rw [MvPolynomial.coeff_map]; exact (map_ne_zero σ).mpr hc)
  have h3 := Finset.sum_le_sum fun (σ : K →+* ℂ) (_ : σ ∈ Finset.univ) ↦ h2 σ
  rw [Finset.sum_sub_distrib, sum_log_norm_embedding_eq _ hc, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul] at h3
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold h0
  rw [le_div_iff₀ hd]
  linarith

end ReciprocityTheory.MultiplicativeHeights
