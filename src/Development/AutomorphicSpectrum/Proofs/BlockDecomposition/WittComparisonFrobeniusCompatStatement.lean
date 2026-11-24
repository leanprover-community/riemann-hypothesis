module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompat
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_comparison_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n), phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | exact GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | (intros; apply GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW <;> assumption)
