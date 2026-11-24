module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchPlace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrderBranchesMeet
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceHasBranch
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdDeterminesPlace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
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

open MvPolynomial ComplexSets Filter Topology

theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
