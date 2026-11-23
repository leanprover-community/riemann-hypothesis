module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem eventually_valued_algebraMap_eq_one (F : Type) [Field F] [NumberField F] (β : F) (hβ : β ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (Fv F v) β) = 1 := by
  rw [Filter.eventually_cofinite]
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) β).union
    (HeightOneSpectrum.Support.finite (𝓞 F) β⁻¹)).subset ?_
  intro v hv
  have e : Valued.v (algebraMap F (Fv F v) β) = v.valuation F β :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) β
  rw [Set.mem_ofPred_eq, e] at hv
  rcases lt_or_gt_of_ne hv with h | h
  · refine Set.mem_union_right _ ?_
    show 1 < v.valuation F β⁻¹
    exact ((v.valuation F).one_lt_val_iff (inv_ne_zero hβ)).mpr (by rwa [inv_inv])
  · exact Set.mem_union_left _ h

theorem multipliable_localFactors :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  intro F _ _ S C g hg β hβ
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
    (GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖g v (algebraMap F (Fv F v) β) - 1‖ ≤ C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    filter_upwards [eventually_valued_algebraMap_eq_one F β hβ,
      Set.Finite.compl_mem_cofinite S.finite_toSet] with v hv hvS
    rw [Real.norm_eq_abs, mul_one_div]
    exact hg v hvS _ hv
  have hf : Summable fun v : HeightOneSpectrum (𝓞 F) => g v (algebraMap F (Fv F v) β) - 1 :=
    Summable.of_norm_bounded_eventually hsum hev
  simpa using Real.multipliable_one_add_of_summable hf

end GlobalTheory.CompanionTheory.Mass.MeanV
