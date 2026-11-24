module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.uok_pf :
    U.UAdj → HuHecke → UOk := by
  intro hA hH hR E _ _ _ n π S T F₀ F hE p
  have hB : ∀ {w : Pl E}, F.d.Good w → w ∉ F.d.B := by
    intro w hw
    obtain ⟨-, hT, hS, hB, -⟩ := hw
    simp [LocData.B, hT, hS, hB]
  have hok : ∀ x, (F.ug x).Ok F₀.Sec F.d.B := by
    intro x
    rcases x with _ | x | x
    · exact trivial
    · exact trivial
    · exact ⟨x.1.2.1, hB x.1.2.2, hH E n F.d F.ok _ x.1.2.2 x.2.1⟩
  obtain ⟨x, b⟩ := p
  have hadj := hA E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x) (hok x)
  cases b
  · simpa [ul] using hok x
  · simpa [ul] using hadj

end
