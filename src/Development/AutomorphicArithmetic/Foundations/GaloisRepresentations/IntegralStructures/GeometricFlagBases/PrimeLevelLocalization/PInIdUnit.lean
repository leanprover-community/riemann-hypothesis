module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.StGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem isUnit_algebraMap_adicCompletionIntegers_of_not_mem (E : Type) [Field E] [NumberField E] (w : Plc E) (s : 𝓞 E)
    (hs : s ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w) s) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v ((algebraMap (𝓞 E) E s : E) : HeightOneSpectrum.adicCompletion E w) = 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact hs

theorem inIdUnit_holds : InIdUnit := by
  intro E _ _ w b c hc y
  obtain ⟨s, hsc, hsw⟩ := hc
  have htop : Ideal.map (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w)) c = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsc) (isUnit_algebraMap_adicCompletionIntegers_of_not_mem E w s hsw)
  unfold InId
  rw [Ideal.map_mul, htop, Ideal.mul_top]

end UpperTheory.Gal.Int.Geo.Pl

end
