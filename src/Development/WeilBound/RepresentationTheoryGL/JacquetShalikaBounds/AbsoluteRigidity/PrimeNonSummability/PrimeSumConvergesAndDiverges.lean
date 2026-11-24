module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
public import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
public import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace PositivityTheory.RgJS.PrimeSumConvergence

variable {E : Type} [Field E] [NumberField E]

theorem two_le (S : Finset (HeightOneSpectrum (𝓞 E))) (w : Off E S) : 2 ≤ nq w :=
  GroundTheory.Global.two_le_absNorm_of_prime w.1.prime

theorem conv (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : ℝ) (hσ : 1 < σ) :
    Summable fun w : Off E S => (nq w : ℝ) ^ (-σ) :=
  (GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hσ).subtype (fun w => w ∉ S)

theorem not_summable_all : ¬ Summable fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
  intro h
  have ht := GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop (K := E)
  set C : ℝ := ∑' w : (Set.univ : Set (HeightOneSpectrum (𝓞 E))), (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ with hC
  have hb : ∀ s : ℝ, 1 < s → (Set.univ : Set (HeightOneSpectrum (𝓞 E))).primeIdealZetaSum s ≤ C := by
    intro s hs
    rw [Set.primeIdealZetaSum_def]
    refine Summable.tsum_le_tsum (fun w => ?_)
      ((GroundTheory.Global.summable_absNorm_rpow_neg (L := E) hs).subtype _) (h.subtype _)
    have h1 : (1 : ℝ) ≤ Ideal.absNorm w.1.asIdeal := by exact_mod_cast GroundTheory.Global.one_le_absNorm w.1
    show (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  obtain ⟨s, hlt, hs⟩ := ((ht.eventually (eventually_gt_atTop C)).and self_mem_nhdsWithin).exists
  exact absurd (hb s hs) (not_le.2 hlt)

theorem div (S : Finset (HeightOneSpectrum (𝓞 E))) : ¬ Summable fun w : Off E S => (nq w : ℝ)⁻¹ := by
  intro h
  apply not_summable_all (E := E)
  have h' : Summable fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ (S : Set (HeightOneSpectrum (𝓞 E)))} =>
      (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ := h
  have hf : Summable fun w : (S : Set (HeightOneSpectrum (𝓞 E))) => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ :=
    S.finite_toSet.summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹)
  exact (summable_subtype_and_compl (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹)
    (s := (S : Set (HeightOneSpectrum (𝓞 E))))).1 ⟨hf, h'⟩

end PositivityTheory.RgJS.PrimeSumConvergence

namespace PositivityTheory.RgJS

theorem prime_sum_converges_and_diverges : PrimeOff := fun _ _ _ S =>
  ⟨PrimeSumConvergence.two_le S, PrimeSumConvergence.conv S, PrimeSumConvergence.div S⟩

end PositivityTheory.RgJS
