module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplier
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

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.Honda.heightTwo_unitTwist | exact GlobalTheory.Honda.heightTwo_unitTwist | (intros; apply GlobalTheory.Honda.heightTwo_unitTwist <;> assumption)
