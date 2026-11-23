module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.nelson_exists_word_growth_constant : ∀ {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a) (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C ^ (l.length + 1) * l.length.factorial * ‖u‖ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth <;> assumption)
