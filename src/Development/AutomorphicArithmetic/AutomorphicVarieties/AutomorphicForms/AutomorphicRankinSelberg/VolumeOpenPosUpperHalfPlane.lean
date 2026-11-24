module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set UpperHalfPlane in
private theorem UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  rw [pos_iff_ne_zero]
  intro h0
  have hac : (volume.comap UpperHalfPlane.coe : Measure ℍ) ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aemeasurable (Measurable.coe_nnreal_ennreal ?_)
      refine Continuous.measurable ?_
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact continuous_im.subtype_mk _
      · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
    · have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (one_div_ne_zero hz))
  have h1 := hac h0
  rw [measurableEmbedding_coe.comap_apply] at h1
  exact ((isOpenEmbedding_coe.isOpenMap U hU).measure_pos volume (hne.image _)).ne' h1

open MeasureTheory Set UpperHalfPlane in
theorem UpperTheory.V.Af.Rs.fdPos :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdPos := by
  intro _ φ hc h0 hint z hz hpos
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hint]
  have hV : IsOpen {w : ℍ | 0 < φ w} := isOpen_lt continuous_const hc
  rw [ModularGroup.fd_eq_closure_fdo] at hz
  have hne : ({w : ℍ | 0 < φ w} ∩ ModularGroup.fdo).Nonempty :=
    mem_closure_iff.mp hz _ hV hpos
  refine (UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane _ (hV.inter ModularGroup.isOpen_fdo) hne).trans_le
    (measure_mono ?_)
  rintro w ⟨hw, hw'⟩
  exact ⟨ne_of_gt hw, ModularGroup.fdo_subset_fd hw'⟩
