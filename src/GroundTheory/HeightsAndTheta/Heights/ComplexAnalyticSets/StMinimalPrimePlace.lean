module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def MinimalPrimePlace.Statement : Prop :=
  ∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → J ∈ I.minimalPrimes → J ≤ RingHom.ker (eval q) →
    ∀ P' : MaximalSpectrum (curveNormalisation J q), ∃ P : MaximalSpectrum (curveNormalisation I q),
      ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
