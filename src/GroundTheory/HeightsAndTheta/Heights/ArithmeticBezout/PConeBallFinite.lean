module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeBallFinite.proof (hMass : ConeIntegralMass.Statement) : ConeBallFinite.Statement := by
  intro n e h W f hW hf
  obtain ⟨δ, hδ1, hδ⟩ := hf.exists_multiHomog hW
  have hm := hMass n e δ h W f hW hf hδ
  rw [lt_top_iff_ne_top]
  intro hinf
  unfold coneIntegral at hm
  change (∫ y in coneBall h W, (1 : ℝ) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / _ =
    (δ : ℝ) at hm
  rw [setIntegral_const, measureReal_def, hinf, ENNReal.toReal_top, zero_smul, zero_div] at hm
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (omega : δ ≠ 0)
  exact hδ0 hm.symm

end

end GroundTheory.Heights₂.Heights
