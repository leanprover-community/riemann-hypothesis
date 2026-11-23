module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HalfPoint

theorem holomorphic_curve : ∀ (Z : Scheme.{0}) (T : ℝ) (yT : Sp (Conv.halfRing T) ⟶ Z) (yw : ℂ → (Sp ℂ ⟶ Z)), (∀ w (hw : T < w.im), yw w = spMap (Conv.ev T w hw).toRingHom ≫ yT) → IsHolTo {w : ℂ | T < w.im} yw ∧ ∀ (U : Z.Opens), ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U → (∃ T' ≥ T, ∀ (T'' : ℝ) (i : Conv.halfRing T →+* Conv.halfRing T''), T' ≤ T'' → (∀ r, (i r : ℂ⸨X⸩) = r) → ⊤ ≤ (spMap i ≫ yT) ⁻¹ᵁ U) ∧ ∀ f : Γ(Z, U), ∃ T' ≥ T, ∃ h : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f ∈ Conv.halfRing T', ∀ w (hw : T' < w.im), ⊤ ≤ yw w ⁻¹ᵁ U ∧ valAt' (yw w) U f = Conv.ev T' w hw ⟨_, h⟩ := by
  intro Z T yT yw hyw
  have hc : ∀ w, T < w.im → yw w = Conv.halfCurve yT w := fun w hw =>
    (hyw w hw).trans (Conv.halfCurve_eq yT hw).symm
  refine ⟨fun U f => ?_, fun U hU => ?_⟩
  · have e : {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ yw b ⁻¹ᵁ U} =
        {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ Conv.halfCurve yT b ⁻¹ᵁ U} := by
      ext b
      exact and_congr_right fun hb => by rw [hc b hb]
    rw [e]
    obtain ⟨h1, h2⟩ := Conv.isHolTo_halfCurve yT U f
    exact ⟨h1, h2.congr fun b hb => by rw [hc b hb.1]⟩
  · have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
        spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
          (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
      rw [← Category.assoc, ← spMap_comp]
      rfl
    have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
      intro p _
      rw [hfac] at hU
      obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
        Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
      exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
    refine ⟨?_, fun f => ?_⟩
    · obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
      refine ⟨T', h, fun T'' i hle hi => ?_⟩
      have hi' : i = (Subalgebra.inclusion (Conv.halfRing_mono hle) :
          Conv.halfRing T' →+* Conv.halfRing T'').comp
          (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
        RingHom.ext fun r => Subtype.ext (hi r)
      rw [hi', spMap_comp, Category.assoc]
      exact fun p _ => hT' (x := spMap _ p) trivial
    · obtain ⟨T', h, h1, h2⟩ := Conv.exists_valAt'_halfCurve rfl hU'
      obtain ⟨hf, hv⟩ := h2 f
      have e : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f =
          ((valR (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) U f :
            Conv.convLaurent) : ℂ⸨X⸩) := by
        rw [hfac, HolHom.valR_spMap _ _ U hU']
        rfl
      refine ⟨T', h, e ▸ hf, fun w hw => ?_⟩
      rw [hc w (h.trans_lt hw)]
      exact ⟨h1 w hw, (hv w hw).trans (Conv.ev_congr hw hw e.symm)⟩

end GlobalTheory.HalfPoint
