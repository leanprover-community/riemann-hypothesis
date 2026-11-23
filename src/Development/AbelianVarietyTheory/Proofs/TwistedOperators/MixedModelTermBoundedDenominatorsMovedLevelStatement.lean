module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  first | exact @GlobalTheory.MixedTermIntegral.integral | exact GlobalTheory.MixedTermIntegral.integral | (intros; apply GlobalTheory.MixedTermIntegral.integral <;> assumption)
