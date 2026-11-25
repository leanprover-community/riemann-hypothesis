module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
namespace GlobalTheory.ExpTie
theorem atPts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (h' : _root_.GlobalTheory.BigOn.AtPtsAlt Q') : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (h.and h') fun Fm _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm =>
      ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm, hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩
theorem atPts_mono {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : _root_.GlobalTheory.BigOn.AtPtsAlt Q) (H : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i),
      Q Fm x hx i p → Q' Fm x hx i p) : _root_.GlobalTheory.BigOn.AtPtsAlt Q' :=
  Closed.imp h fun Fm _ _ ⟨a, ha⟩ => ⟨a, fun x hx hle i p hp hm => H Fm x hx i p (ha x hx hle i p hp hm)⟩
end GlobalTheory.ExpTie
end
end
