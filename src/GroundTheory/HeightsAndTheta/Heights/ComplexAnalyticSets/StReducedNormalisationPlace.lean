module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))

end

end GroundTheory.Heights₂.Heights
