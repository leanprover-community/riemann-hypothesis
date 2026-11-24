module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField InfinitePlace IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_places {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    nrRealPlaces F = Module.finrank ℚ F ∧ nrComplexPlaces F = 0 ∧ nrRealPlaces E = 0 ∧
      nrComplexPlaces E = Module.finrank ℚ F := by
  obtain ⟨hF, hE, h2, -⟩ := h
  have hcF : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  have hrE : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have kF := card_add_two_mul_card_eq_rank F
  have kE := card_add_two_mul_card_eq_rank E
  have ht := Module.finrank_mul_finrank ℚ F E
  rw [h2] at ht
  refine ⟨by omega, hcF, hrE, by omega⟩

theorem eSp_zpow (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    PositivityTheory.SiegelWeilFormula.Gen.eSp E v ^ j = if Even j then 1 else PositivityTheory.SiegelWeilFormula.Gen.eSp E v := by
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs with h1 h2 h2
  · exact h2.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h2).neg_one_zpow
  · exact one_zpow j
  · exact one_zpow j

end PositivityTheory.Lord
