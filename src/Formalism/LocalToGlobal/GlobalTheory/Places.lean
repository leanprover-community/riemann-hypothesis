module

public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
public import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

def PlaceConditionsFamily : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ), product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → SettingEventually Fm → TuSize Fm → J.MuRank Fm →
    LinkG Fm → LinkMu Fm → Lnk.PlacesF Fm

def SlopeBoundOfMuRank : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ), product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → SettingEventually Fm → TuSize Fm → J.MuRank Fm →
    LinkG Fm → LinkMu Fm → LocalQuadraticParts.SlopeLemmaFamily Fm

def LevelPrimeSettingFamily : Prop := ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → SettingEventually Fm

def SlopeLemmaLinkForm : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 crystallineComparison : ℝ), 0 < C0 → product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison → TuSize Fm →
    ChosenE Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 → LocalQuadraticParts.SlopeLemmaFamily Fm

end Formalism.L2.GlobalTheoryTheory.Places

end
