module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
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

theorem isNilpotent_of_minimalPrimes_eq_singleton {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B

theorem length_localizedModule_self {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq

theorem LengthLocalizedQuotient.proof (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm

end GroundTheory.Heights₂.Heights
