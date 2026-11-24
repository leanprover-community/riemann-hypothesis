module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.ReductionMahler
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne (K := E) (n := a)) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL (K := E) (n := a)) : GA E a)

theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL (K := E) (n := a)) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := a))
      (Quotient.out (RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne (K := E) (n := a))).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) = fun x : normOneGL (K := E) (n := a) => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
