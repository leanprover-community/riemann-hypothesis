module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrsSecondCountableAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem adelic_regular_rep_unitary_continuous (X : CData) (hd : RegData X) (hu : UnimodA X) (hl : LocFinF X) : RepA X := by
  have hH : X.μf.IsHaarMeasure := hd.1
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SecondCountableTopology X.L2 := automorphic_L2_secondCountable X
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : IsLocallyFiniteMeasure (X.I.muA X.μf) := rr_muA_locFin X hl
  have : (X.I.muA X.μf).IsOpenPosMeasure := rr_muA_openPos X
  have hne : X.I.muA X.μf ≠ 0 := fun h0 =>
    isOpen_univ.measure_ne_zero (X.I.muA X.μf) (univ_nonempty (α := X.I.GA))
      (by rw [h0, FunLike.coe_zero, Pi.zero_apply])
  obtain ⟨h1, h2, h3⟩ := rightRegular_isometric_multiplicative X hd hu
  exact ⟨h1, h2, h3, fun F => rr_cont_of_meas' (μ := X.I.muA X.μf) hne h1 h2 h3 (regular_rep_coeff_measurable X hd hu) F⟩

end Formalism.MainNotions.LeviCoordinates

end
