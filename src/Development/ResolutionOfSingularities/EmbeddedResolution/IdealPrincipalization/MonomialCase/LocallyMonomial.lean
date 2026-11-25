module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
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

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def IsMonomialNear {X : Scheme.{u}} (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι =
      (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤

structure IsLocallyMonomialTriple (T : MarkedIdealWithBoundary.{u}) : Prop where
  valid : T.IsAdmissible
  monomialNear : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, IsMonomialNear T.boundary T.ideal x

structure IsLocallyMonomialPrincipalization (P : ℕ → Prop) (F : PrincipalizationAssignment.{u}) : Prop where
  cert :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        PrincipalizationCertificate ((F T).schemeAt i) (MarkedSequenceOfBlowups.projectionToSpec (F T) i) ((F T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (F T) i) ((F T).center i)
  center_nonempty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length, (↑((F T).center i).support : Set ↥((F T).schemeAt i)).Nonempty
  resolves :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      MarkedSequenceOfBlowups.IsResolution (F T)
  trivial_of_coSupport_empty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      orderAtLeastLocus T.ideal T.mult = ∅ → (F T).length = 0

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
