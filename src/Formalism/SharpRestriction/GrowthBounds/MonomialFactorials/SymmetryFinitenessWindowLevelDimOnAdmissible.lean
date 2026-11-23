module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthogonalityWindow
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg
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

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryFinitenessWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestLjjFin C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryFinitenessWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryFinitenessWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem orthogonal_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : OrthogonalityWindowLevelDimOnAdmissible D :=
  thr_mono_ge (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hCYb hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
    have hp2 : X.p ≠ 2 := by
      intro h2
      have := p25 hF
      have h3 : (X.L.p : ℝ) = 2 := by exact_mod_cast h2
      linarith
    exact ⟨restOrth_of CM hp2 hO a b, c, d⟩) h

theorem closed_of_symmetric_finite (D : Formalism.BasicNotions.D7) (hY : RestYbc) (hO : OrthLat) (h : SymmetryFinitenessWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  integrality_from_metric_of_orthogonality_window D hY (orthogonal_of_symmetric_finite D hO h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
