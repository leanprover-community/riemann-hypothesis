module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {σ : Type*}

instance isPrime_ker_eval_point (w : σ → ℂ) : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

def pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Type _ :=
  Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : CommRing (pointLocalRing I w) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Algebra (MvPolynomial σ ℂ) (pointLocalRing I w) :=
  inferInstanceAs (Algebra (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))

theorem isUnit_algebraMap_pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : eval w f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) f) :=
    IsLocalization.map_units _
      (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

def NormalModelPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal → IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
          Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
