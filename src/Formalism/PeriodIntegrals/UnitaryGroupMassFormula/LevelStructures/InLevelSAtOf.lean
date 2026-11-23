module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS
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

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩

end MassDataLevelSSteps
