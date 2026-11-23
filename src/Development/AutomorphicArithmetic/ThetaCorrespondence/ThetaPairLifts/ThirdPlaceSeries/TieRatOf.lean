module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem tieRat_of_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hR : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) : _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  unfold _root_.GlobalTheory.BigOn.Exp.CompatibilityRational _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩
end GlobalTheory.BigOn.Exp
end
