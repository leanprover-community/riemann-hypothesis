module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIrreducibleGeneralizations
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn


theorem _root_.GlobalTheory.T.exists_constant_cmEvaluation_fits_room : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  first | exact @GlobalTheory.room_of_constants | exact GlobalTheory.room_of_constants | (intros; apply GlobalTheory.room_of_constants <;> assumption)
