module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutMultPosSt
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

open IsLocalRing

def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  have := IsLocalization.linearMap_compatibleSMul q.primeCompl
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _

theorem CutMultPos.proof : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.1.1
  let J' : Ideal (Localization.AtPrime qq) :=
    J.localized' (Localization.AtPrime qq) qq.primeCompl
      (Algebra.linearMap (Poly S N) (Localization.AtPrime qq))
  have hJ' : J' = J.map (algebraMap (Poly S N) (Localization.AtPrime qq)) := by
    simp only [J', Submodule.localized'_eq_span, Ideal.map]
    rfl
  have hmin : maximalIdeal (Localization.AtPrime qq) ∈ J'.minimalPrimes := by
    rw [hJ', IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hne : J' ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hmin.1.2
  have : Nontrivial (Localization.AtPrime qq ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsArtinianRing (Localization.AtPrime qq ⧸ J') :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J' hmin
  have : IsArtinian (Localization.AtPrime qq) (Localization.AtPrime qq ⧸ J') :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J'))
  have : IsNoetherianRing (Localization.AtPrime qq) :=
    IsLocalization.isNoetherianRing qq.primeCompl _ inferInstance
  unfold cutMult
  rw [← (locQuotEquiv qq J).length_eq]
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
