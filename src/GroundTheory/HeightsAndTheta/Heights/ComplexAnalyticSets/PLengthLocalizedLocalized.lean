module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedLocalized
public import Mathlib.RingTheory.Localization.LocalizationLocalization
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem LengthLocalizedLocalized.isLocalization_atPrime_map (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by
  have h : Ideal.under B (P.map (algebraMap B (Localization.AtPrime Q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hP
      (Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP))
  have key : IsLocalization ((P.map (algebraMap B (Localization.AtPrime Q))).comap
        (algebraMap B (Localization.AtPrime Q))).primeCompl
      (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime Q.primeCompl _
  rw [Ideal.under] at h
  have e : P.primeCompl = ((P.map (algebraMap B (Localization.AtPrime Q))).comap
      (algebraMap B (Localization.AtPrime Q))).primeCompl :=
    Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h]
  rw [e]
  exact key

theorem LengthLocalizedLocalized.proof : LengthLocalizedLocalized.Statement.{u, v} := by
  intro B _ P Q _ _ _ M _ _ hPQ
  have hloc := LengthLocalizedLocalized.isLocalization_atPrime_map B P Q hPQ

  let σ : Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B]
      Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl _ _
  let : Algebra (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) := σ.toRingHom.toAlgebra
  let : Module (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P))
  have : IsScalarTower (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap _ (Localization.AtPrime P) r • (l • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    ⟨fun b r x => by
      show algebraMap _ (Localization.AtPrime P) (b • r) • x =
        b • (algebraMap _ (Localization.AtPrime P) r • x)
      rw [Algebra.smul_def, map_mul, mul_smul]
      rw [show algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (Localization.AtPrime P) (algebraMap B _ b) = algebraMap B (Localization.AtPrime P) b from
          σ.commutes b, algebraMap_smul]⟩

  have hf : IsBaseChange (Localization.AtPrime Q) (LocalizedModule.mkLinearMap Q.primeCompl M) :=
    IsLocalizedModule.isBaseChange Q.primeCompl _ _
  have hg : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
        (LocalizedModule Q.primeCompl M)) :=
    IsLocalizedModule.isBaseChange (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl _ _
  have hfg := hf.comp hg
  have h0 : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap P.primeCompl M) :=
    IsLocalizedModule.isBaseChange P.primeCompl _ _
  rw [← (h0.equiv.symm.trans hfg.equiv).length_eq]
  exact Module.length_eq_of_surjective σ.surjective

end GroundTheory.Heights₂.Heights
