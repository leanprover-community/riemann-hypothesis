module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lie_algebra_of_linear_group_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧ (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧ (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧ (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra <;> assumption)
