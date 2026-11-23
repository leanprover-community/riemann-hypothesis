module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
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

@[expose] public section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  first | exact @GlobalTheory.MirAvg.tr_mirEl_indep | exact GlobalTheory.MirAvg.tr_mirEl_indep | (intros; apply GlobalTheory.MirAvg.tr_mirEl_indep <;> assumption)
