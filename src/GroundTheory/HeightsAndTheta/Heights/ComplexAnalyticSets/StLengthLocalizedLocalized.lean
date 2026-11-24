module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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

universe u v

def LengthLocalizedLocalized.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M],
    P ≤ Q →
      Module.length (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (LocalizedModule (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
            (LocalizedModule Q.primeCompl M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

theorem LengthLocalizedLocalized.map_isPrime (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP
    (Set.disjoint_left.mpr fun _ hx hxP => hx (h hxP))

end GroundTheory.Heights₂.Heights
