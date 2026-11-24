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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem isPrime_map_quotient_localization {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)

def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))

end

end GroundTheory.Heights₂.Heights
