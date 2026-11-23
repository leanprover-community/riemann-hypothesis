module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
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

open MeasureTheory

theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
