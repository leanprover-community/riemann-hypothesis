module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PlaneGramTheoremOfLemmas
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrRenExpandMonomial
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.UnitLevelOne
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpan
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

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

theorem stmt (D : Formalism.BasicNotions.D7) {CH : ℝ} (hCH : 26 ≤ CH) : Formalism.MainNotions.PlaneGramData.Stmt D CH 2 24 60 := by
  intro p O _ _ _ _ hSet hAdm
  obtain ⟨⟨S⟩, n', hG⟩ := hSet
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hAdm
  exact Br.plane_gram_of_theorem_at S hG
    (plane_gram_theorem_of_five_lemmas le_rfl (second_valuation_of_admitted h2) (brSPAN S h3) (brPROJ S h4) (brDIG D S hG h5)
      (brDER S h6)) hCH

theorem stmtE (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.ClosedFormOfAdmitted D :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, fun _ hCH => stmt D hCH⟩

end Formalism.MainNotions.PlaneGram
