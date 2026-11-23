module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  first | exact @GlobalTheory.FreeBallAt.freeBall_at | exact GlobalTheory.FreeBallAt.freeBall_at | (intros; apply GlobalTheory.FreeBallAt.freeBall_at <;> assumption)
