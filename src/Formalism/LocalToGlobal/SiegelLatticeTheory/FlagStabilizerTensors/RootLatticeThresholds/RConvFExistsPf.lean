module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPfAbs
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

theorem convergent_reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RConvFExists := by
  intro I μf _ _ hright hsc hborel fund hfund R hR f hf
  haveI := hsc
  haveI := hborel
  haveI : μf.IsMulRightInvariant := hright
  haveI : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  haveI : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  haveI : (I.muA μf).IsMulRightInvariant := rr_muA_right I μf
  have hfd := rr_FD_of I μf fund hfund
  have hreg := rr_IsReg_of I μf fund R hR

  have hemb : Measurable (fun g : I.Gf => ((1, g) : I.GA)) := by fun_prop
  obtain ⟨T, hT⟩ := wk_exists (μ := μf) (U := fun g => R (1, g))
    (fun g z => (rr_norm hfd hreg (1, g) z).le)
    (fun x y => ((rr_weak_meas hfd hreg x y).comp_measurable hemb).aestronglyMeasurable) hf
  exact ⟨T, hf, hT⟩

end Formalism.L2.SG.Pf.RConvFExistsPf
