module

public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroBotOfEff
public import Development.WeilBound.CoreStatements.ResolutionCharZero.RqGend
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup

theorem principalisationCharZero_of_boundary (hB : GBoundary) : PrincipalisationCharZero :=
  principalisationCharZero_of_eff hB PositivityTheory.ResPlug.GEndGen.gEff

theorem principalisationCharZero_bot_closed :
    ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
      SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
      ∀ (I : X.IdealSheafData), (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
        ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
          IsSncBlowupSeq g ⊥ s E' ∧ Smooth (s ≫ g) ∧
          FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
          IsIso (s ∣_ I.support.compl) :=
  principalisationCharZero_bot_of_eff PositivityTheory.ResPlug.GEndGen.gEff

end PositivityTheory.ResPlug.WeightsCompactStabilizer
