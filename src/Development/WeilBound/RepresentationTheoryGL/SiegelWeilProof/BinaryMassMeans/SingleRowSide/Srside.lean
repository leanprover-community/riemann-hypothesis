module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegralStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.Mass.LiteralAutomorphy

open PositivityTheory.Rg.Mass

theorem srside : MeanVal → LocMass → RSide := by
  intro hMV hLM F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨C, hC⟩ := hLM F E σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm
  have hfin := Filter.eventually_cofinite.1 hC
  refine ⟨hfin.toFinset, fun S hS φ A hT => ?_⟩
  obtain ⟨hφc, hφs, hφ0, hφU, hAS, hAL⟩ := hT
  obtain ⟨hGc, hGs, hGl, hGi⟩ := GlobalTheory.T.archimedean_binary_gram_density F E σ hCM J hJ d b li hli mi hmi φ hφc hφs hφ0 hφU
  have hG0 : ∀ y : Ainf F, 0 ≤ ∫ X, φ X ∂(mi (hermScal (Ainf F) σ y)) := fun y => integral_nonneg fun X => hφ0 X
  have hP := fun v (hv : v ∉ S) => not_not.1 (fun h => hv (hS (hfin.mem_toFinset.2 h)))
  have key := hMV F hCM.1 θ hθ li lam hli hlam S (fun s => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))
    (fun v s => (m v (hermScal (Fv F v) σ s) (A v)).toReal) C hGc hGs hG0 (fun v y => ENNReal.toReal_nonneg)
    (fun v hv => by
      obtain ⟨h1, h2, h3⟩ := hAS v hv
      obtain ⟨c1, c2, -⟩ := GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3
      exact ⟨c1, c2⟩)
    (fun v hv => by
      obtain ⟨p1, p2, p3⟩ := hP v hv
      obtain ⟨l1, l2⟩ := GlobalTheory.T.local_binary_gram_density F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v)
      simp only [hAL v hv]
      refine ⟨l1, fun s hs => ?_, p2, p3, l2⟩
      have hs0 : s ≠ 0 := fun h => hs (h ▸ (v.adicCompletionIntegers F).zero_mem)
      rw [p1 s hs hs0]
      rfl)
  beta_reduce at key
  have hlim : ENNReal.ofReal ((∫ y, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ y))) ∂li) *
      ∏ v ∈ S, ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) = vol b li lam S φ A := by
    rw [ENNReal.ofReal_mul (integral_nonneg fun s => hG0 s),
      ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg fun s => ENNReal.toReal_nonneg), hGi]
    unfold vol
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨h1, h2, h3⟩ := hAS v hv
    exact (GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3).2.2
  rw [hlim] at key
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε) using Set.mem_Ioi.2 (pow_pos hε 2)
  refine (key.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  simp only [Function.comp_apply]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun β => ?_
  have h1 := GlobalTheory.T.archimedean_binary_gram_integral F E σ hCM J hJ d b li hli mi hmi θ hθ ε hε (algebraMap F (Ainf F) β.1) φ hφc
  rw [← mul_assoc, h1, hGl, mul_assoc, ← ENNReal.ofReal_mul (hG0 _), map_pow]

end PositivityTheory.Rg.Mass.LiteralAutomorphy
