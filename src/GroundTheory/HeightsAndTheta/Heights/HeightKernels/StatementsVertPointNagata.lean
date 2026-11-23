module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

instance isPrime_map_C_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).2 inferInstance

abbrev nagataRing (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R))

def VertPointNagata.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : T → curveRing y)
          (hb : ∀ u, b u ∉ curvePtIdeal y W), (∀ u, (b u : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a u) →
          ∃ Φ : Localization.AtPrime W →+* nagataRing (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing (fun _ : Unit => T)) _) ∧
            ∀ f : MRing (fun _ : Unit => T), Φ (algebraMap _ _ f) =
              algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p.2)
                  (⟨b p.2, hb p.2⟩ : (curvePtIdeal y W).primeCompl)) * Polynomial.X) f)

end

end GroundTheory.Heights₂.Heights
