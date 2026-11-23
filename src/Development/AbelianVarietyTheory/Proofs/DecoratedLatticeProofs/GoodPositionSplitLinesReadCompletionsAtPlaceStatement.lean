module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
