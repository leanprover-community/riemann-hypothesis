module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
