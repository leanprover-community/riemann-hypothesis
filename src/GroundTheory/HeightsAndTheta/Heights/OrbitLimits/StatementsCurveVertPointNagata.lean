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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance isPrime_map_C_maximalIdeal_mv (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R)).IsPrime := by
  rw [← Ideal.mk_ker (I := IsLocalRing.maximalIdeal R), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

abbrev mNagataRing (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R))

def CurveVertPointNagata.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : (Σ k, ι k) → curveRing y)
          (hb : ∀ p, b p ∉ curvePtIdeal y W), (∀ p, (b p : Ω) * (y p / y ⟨p.1, c p.1⟩) = a p) →
          ∃ Φ : Localization.AtPrime W →+* mNagataRing K (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing ι) _) ∧
            ∀ f : MRing ι, Φ (algebraMap _ _ f) =
              algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ k, ι k) => MvPolynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p)
                  (⟨b p, hb p⟩ : (curvePtIdeal y W).primeCompl)) * MvPolynomial.X p.1) f)

end

end GroundTheory.Heights₂.Heights.Targets
