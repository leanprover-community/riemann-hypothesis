module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhIUnionTrans
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumGraphEqSumEntN
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrFirstPattern
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem tr_eJ_eq_tr_eJ' : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ →
      tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ hψ N k s hN χ hχ
  have key : ∀ i, i ≤ s →
      tr (GlobalTheory.GLm.ePat g N (GlobalTheory.GLm.phI k s i) (GlobalTheory.GLm.eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
    intro i
    induction i with
    | zero => intro _; exact GlobalTheory.GLm.FirstPattern.tr_first_pattern g ψ N k s hN χ hχ
    | succ n ih =>
      intro hn
      rw [GlobalTheory.RootExch.step g ψ hψ N k s (n + 1) hN (by omega) hn χ hχ]
      exact ih (by omega)
  rw [← GlobalTheory.GLm.ePat_last_eq_eJ g ψ N k s hN]
  exact key s le_rfl

end GlobalTheory.GLq
