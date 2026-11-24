module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormula
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.lower_unipotent_minor_formula : ∀ (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N), j ≤ N → IsBlockDiag j X → IsLowerUni X → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧ minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni <;> assumption)
